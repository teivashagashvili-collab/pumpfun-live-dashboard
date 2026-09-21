const http=require("http"),fs=require("fs"),path=require("path"),WebSocket=require("ws");const {URL}=require("url");
const PORT=Number(process.env.PORT||8787),PUBLIC=path.join(__dirname,"public"),clients=new Set(),tokens=new Map(),history=new Map(),learning={samples:0,positive:0,negative:0};
const send=(r,c,d,extra={})=>{r.writeHead(c,{"Content-Type":"application/json; charset=utf-8","Cache-Control":"no-store",...extra});r.end(JSON.stringify(d))};
const broadcast=(e,d)=>{const x=`event: ${e}\ndata: ${JSON.stringify(d)}\n\n`;for(const r of clients){try{r.write(x)}catch{}}};
const heartbeat=setInterval(()=>{for(const r of clients){try{r.write(`: heartbeat ${Date.now()}\n\n`)}catch{}}},10000);
async function getJSON(u){const r=await fetch(u,{headers:{accept:"application/json"}});if(!r.ok)throw Error(r.status);return r.json()}
function scoreSignal(p,r,trend={}){
 const pc=+p?.priceChange?.m5||0,h=+p?.priceChange?.h1||0,b=+p?.txns?.h1?.buys||0,s=+p?.txns?.h1?.sells||0,l=+p?.liquidity?.usd||0,f=b+s?b/(b+s):.5;
 let x=40+pc*1.35+h*.28+(f-.5)*42+Math.min(14,Math.log10(Math.max(1,l))*2.4)+Math.min(12,Math.log10(Math.max(1,+p?.volume?.h1||0))*2)+Math.max(-8,Math.min(8,+trend.accel||0));
 if(r?.scoreNormalized!=null)x-=Math.min(35,r.scoreNormalized*.34);
 x=Math.max(0,Math.min(100,x));
 const label=x>=80?"HIGH CONVICTION WATCH":x>=68?"EARLY BUY WATCH":x>=55?"MOMENTUM WATCH":"NO CALL";
 return{score:Math.round(x),label,side:x>=68?"BUY WATCH":"WAIT",reasons:[
   pc>4?"5m momentum is positive":pc<-5?"5m momentum is weak":null,
   h>8?"1h trend is strong":h<-10?"1h trend is weak":null,
   f>.58?"buyers currently dominate":f<.42?"sellers currently dominate":null,
   l>50000?"liquidity is meaningful":l<5000?"liquidity is thin":null,
   r?.rugged?"RugCheck flags the token":r?.scoreNormalized>=45?"risk score is elevated":null
 ].filter(Boolean).slice(0,4)}}
function updateLearning(t,p){
 const price=Number(p?.priceUsd);if(!Number.isFinite(price)||price<=0)return;
 const arr=history.get(t.mint)||[];const now=Date.now();arr.push({ts:now,price});while(arr.length>240)arr.shift();history.set(t.mint,arr);
 const old=arr.find(x=>now-x.ts>=300000);if(old){const ret=(price/old.price-1)*100;learning.samples++;if(ret>0)learning.positive++;else learning.negative++;}
}
function trendFor(t){
 const arr=history.get(t.mint)||[];if(arr.length<3)return{};
 const a=arr[arr.length-1],b=arr[Math.max(0,arr.length-5)];
 return{accel:(a.price/b.price-1)*100};
}
function candidateScore(t){
 const p=t.pair||{},s=t.signal||{},liq=+p.liquidity?.usd||0,vol=+p.volume?.h1||0,mc=+p.marketCap||+p.fdv||0,age=p.pairCreatedAt?Math.max(0,(Date.now()-p.pairCreatedAt)/3600000):9999,tx=(+p.txns?.h1?.buys||0)+(+p.txns?.h1?.sells||0),vl=liq?vol/liq:0;
 if(!p||s.score<62||liq<10000||vol<15000||tx<25)return -1;
 if(t.rug?.rugged||(+t.rug?.scoreNormalized||0)>=45)return -1;
 if(mc>25000000)return -1;
 if(vl<1)return -1;
 if(age<0)return -1;
 return s.score + Math.min(12,Math.log10(Math.max(1,vol))) + (mc>0&&mc<5000000?7:0) + (age<=24?4:0) + (vl>=5?4:0);
}
function classify(t){
 const p=t.pair||{},mc=+p.marketCap||+p.fdv||0,age=p.pairCreatedAt?Math.max(0,(Date.now()-p.pairCreatedAt)/3600000):9999;
 if(t.rug?.rugged||+t.rug?.scoreNormalized>=45)return "RISK";
 if(mc>25000000)return "ESTABLISHED";
 if(age<=24)return "EARLY";
 if(age<=72)return "DEVELOPING";
 return "MOMENTUM";
}
function quality(t){
 const p=t.pair||{};
 return !!p && !!t.name && t.name!=="Unknown" && !!t.symbol && t.symbol!=="TOKEN";
}
async function enrich(t){
 try{
  const a=await getJSON(`https://api.dexscreener.com/token-pairs/v1/solana/${encodeURIComponent(t.mint)}`);
  const pairs=Array.isArray(a)?a:(Array.isArray(a?.pairs)?a.pairs:[]);
  const p=pairs.filter(x=>x?.chainId==="solana").sort((a,b)=>(+b?.liquidity?.usd||0)-(+a?.liquidity?.usd||0))[0]||null;
  let meta={};
  // PumpPortal's URI is often the best first-party launch metadata source.
  if(t.uri){try{const m=await getJSON(t.uri);if(m&&typeof m==="object")meta=m}catch{}}
  let r=null;
  try{
   const z=await getJSON(`https://api.rugcheck.xyz/v1/tokens/${encodeURIComponent(t.mint)}/report`);
   const raw=+z?.score;
   r={scoreRaw:Number.isFinite(raw)?raw:null,scoreNormalized:Number.isFinite(raw)?Math.max(0,Math.min(100,raw>100?raw/200:raw)):null,rugged:!!z?.rugged};
  }catch{}
  const name=(p?.baseToken?.name&&p.baseToken.name!=="Unknown"?p.baseToken.name:null)||(meta.name&&String(meta.name).trim())||(t.name&&t.name!=="Unknown"?t.name:null);
  const symbol=(p?.baseToken?.symbol&&p.baseToken.symbol!=="TOKEN"?p.baseToken.symbol:null)||(meta.symbol&&String(meta.symbol).trim())||(t.symbol&&t.symbol!=="TOKEN"?t.symbol:null);
  const merged={...t,name:name||"Metadata pending",symbol:symbol||"—",metadataImage:meta.image||meta.image_url||p?.info?.imageUrl||"",metadataDescription:meta.description||"",pair:p,rug:r};
  updateLearning(merged,p);
  return{...merged,signal:scoreSignal(p,r,trendFor(merged)),category:classify(merged),quality:quality(merged),chart:(history.get(t.mint)||[]).slice(-60),updatedAt:Date.now()};
 }catch{return{...t,pair:null,rug:null,quality:false,category:"UNVERIFIED",signal:scoreSignal(null,null,trendFor(t)),updatedAt:Date.now()}}
}
async function add(e){
 if(!e?.mint)return;
 const t={mint:String(e.mint),name:String(e.name||"Unknown"),symbol:String(e.symbol||"TOKEN"),creator:String(e.traderPublicKey||e.creator||""),uri:String(e.uri||""),createdAt:Number(e.created_timestamp||Date.now())};
 if(tokens.has(t.mint))return;
 tokens.set(t.mint,t);while(tokens.size>500)tokens.delete(tokens.keys().next().value);
 const z=await enrich(t);tokens.set(t.mint,z);broadcast("update",z);
}
function getCalls(){
 return [...tokens.values()].filter(t=>candidateScore(t)>=72&&quality(t)).map(t=>({...t,callType:t.signal.score>=82?"A-TIER WATCH":t.signal.score>=74?"QUALIFIED WATCH":"MOMENTUM WATCH"})).sort((a,b)=>candidateScore(b)-candidateScore(a)).slice(0,30);
}
function getRadar(){
 return [...tokens.values()].filter(t=>t.pair&&quality(t)).sort((a,b)=>(b.signal?.score||0)-(a.signal?.score||0)).slice(0,100);
}
async function walletData(address){
 if(!/^[1-9A-HJ-NP-Za-km-z]{32,44}$/.test(address))throw Error("Invalid Solana address");
 const rpc=process.env.SOLANA_RPC_URL||"https://api.mainnet-beta.solana.com";
 const body=JSON.stringify({jsonrpc:"2.0",id:1,method:"getBalance",params:[address,{commitment:"confirmed"}]});
 const r=await fetch(rpc,{method:"POST",headers:{"content-type":"application/json"},body});if(!r.ok)throw Error("RPC "+r.status);const j=await r.json();
 return{address,balanceSol:((j?.result?.value||0)/1e9),network:"mainnet-beta"};
}
function agentAnswer(question){
 const c=getCalls(),q=String(question||"").trim().toLowerCase(),top=c[0],high=c.slice(0,10),all=getRadar();
 const risks=all.filter(x=>x.rug?.rugged||x.rug?.scoreNormalized>=45);
 const early=all.filter(x=>x.category==="EARLY"&&candidateScore(x)>=60).slice(0,8);
 const established=all.filter(x=>x.category==="ESTABLISHED").slice(0,5);
 let answer="",focus=top?{token:top.symbol,name:top.name,mint:top.mint,score:top.signal.score,call:top.callType,reasons:top.signal.reasons,metrics:top.signal.metrics}:null;
 if(!q)answer="I’m the market research layer. I can explain a token, compare candidates, inspect risk, explain a chart, describe the current market regime, or tell you why a token was rejected. I track evidence first and avoid inventing certainty.";
 else if(q.includes("learn")||q.includes("study")||q.includes("how do you"))answer="I learn in a bounded way from observed outcomes: rolling price history, volume/liquidity, transaction flow, momentum and safety results. Right now I have "+tokens.size+" live tracked tokens and "+learning.samples+" completed 5-minute outcome samples ("+learning.positive+" positive / "+learning.negative+" negative). This process is not persistent across a server restart yet, so the next architecture step is durable market memory.";
 else if(q.includes("risk")||q.includes("rug")||q.includes("scam"))answer="I treat safety as a gate, not a small score bonus. A RugCheck rug flag or elevated normalized risk can remove a token from qualified calls. I also reject thin liquidity, weak activity, weak volume/liquidity, and very large caps from the early-opportunity board. "+risks.length+" tracked tokens currently show elevated safety risk.";
 else if(q.includes("market")||q.includes("regime")||q.includes("economy"))answer="The scanner is watching the micro-regime: fresh-token flow, 5m/1h momentum, buyer/seller imbalance, volume relative to liquidity, pair age and market-cap expansion room. These are market-structure signals, not a claim about macroeconomic causality. I can also explain theories such as momentum, reflexivity, liquidity preference, attention/volume feedback and risk-of-ruin.";
 else if(q.includes("call")||q.includes("buy")||q.includes("pick")||q.includes("interesting")||q.includes("100x"))answer=top?"My current qualified research set is "+high.map(x=>x.symbol+" ("+x.signal.score+"/100)").join(", ")+". I am explicitly filtering out large-cap established tokens, weak liquidity, low activity and elevated safety risk from this board. A 100x outcome is not something the data can reliably predict; the useful question is whether the current evidence shows asymmetric upside with survivable downside.":"No token currently clears the full quality gate. That is intentional: a blank board is preferable to promoting a weak or dangerous setup.";
 else if(q.includes("chart"))answer="Chart analysis is not just the line. I combine the recent price path with 5m/1h change, transaction count, buy/sell balance, volume-to-liquidity, pair age and safety. A sharp rise with deteriorating flow or weak liquidity is treated differently from a rise supported by broader activity.";
 else if(q.includes("early")||q.includes("new"))answer=early.length?"Early candidates right now: "+early.map(x=>x.symbol+" ("+x.signal.score+")").join(", ")+". These are fresh, active candidates that still need safety and liquidity confirmation.":"There are no fresh candidates currently clearing the early-opportunity gates.";
 else if(q.includes("established")||q.includes("large"))answer=established.length?"Established movers are kept separate from early opportunities: "+established.map(x=>x.symbol).join(", ")+".":"No established movers are currently enriched.";
 else answer=top?"The strongest qualified setup I currently see is "+top.name+" ("+top.symbol+") at "+top.signal.score+"/100. Evidence: "+top.signal.reasons.join("; ")+". Key metrics: liquidity "+Math.round(+top.pair.liquidity?.usd||0)+", 1h volume "+Math.round(+top.pair.volume?.h1||0)+", buy ratio "+((top.signal.metrics?.buyRatio||0)*100).toFixed(0)+"%, age "+(top.signal.metrics?.ageHours||0).toFixed(1)+"h. Ask me for the token mint if you want a full breakdown.":"Nothing currently clears the quality gate.";
 return{answer,focus,market:{tracked:tokens.size,candidates:high.length,riskFlags:risks.length,early:early.length,established:established.length,learningSamples:learning.samples},method:"Multi-factor market research: metadata verification, liquidity, volume/liquidity, transaction breadth, buy/sell flow, 5m/1h momentum, pair age, market-cap room and RugCheck safety gates. No guaranteed-profit or 100x prediction."};
}
function connect(){
 try{const w=new WebSocket("wss://pumpportal.fun/api/data",{handshakeTimeout:15000});w.on("open",()=>{console.log("PumpPortal connected");w.send(JSON.stringify({method:"subscribeNewToken"}));w.send(JSON.stringify({method:"subscribeMigration"}));broadcast("status",{ok:true})});w.on("message",d=>{try{add(JSON.parse(String(d)))}catch{}});w.on("close",()=>{broadcast("status",{ok:false});setTimeout(connect,3000)});w.on("error",()=>broadcast("status",{ok:false}))}catch{setTimeout(connect,3000)}
}
setInterval(async()=>{for(const t of [...tokens.values()].slice(0,35)){const z=await enrich(t);tokens.set(t.mint,z);broadcast("update",z)}},15000);
http.createServer(async(req,res)=>{
 const u=new URL(req.url,`http://${req.headers.host||"localhost"}`);
 if(u.pathname==="/api/tokens")return send(res,200,[...tokens.values()]);
 if(u.pathname==="/api/radar")return send(res,200,getRadar());
 if(u.pathname==="/api/health")return send(res,200,{ok:true,tracked:tokens.size,qualified:getCalls().length,learningSamples:learning.samples,now:Date.now()});
 if(u.pathname==="/api/calls")return send(res,200,getCalls());
 if(u.pathname==="/api/wallet"){try{return send(res,200,await walletData(u.searchParams.get("address")||""))}catch(e){return send(res,400,{error:e.message})}}
 if(u.pathname==="/api/agent"){return send(res,200,agentAnswer(u.searchParams.get("q")||""))}
 if(u.pathname==="/events"){res.writeHead(200,{"Content-Type":"text/event-stream; charset=utf-8","Cache-Control":"no-cache, no-transform","Connection":"keep-alive","Access-Control-Allow-Origin":"*","X-Accel-Buffering":"no"});res.write(`event: snapshot\ndata: ${JSON.stringify([...tokens.values()])}\n\n`);clients.add(res);req.on("close",()=>clients.delete(res));return}
 const f=path.join(PUBLIC,u.pathname==="/"?"index.html":u.pathname);if(!f.startsWith(PUBLIC))return send(res,403,{error:"forbidden"});
 fs.readFile(f,(e,d)=>{if(e)return send(res,404,{error:"not found"});const ct=path.extname(f)===".html"?"text/html; charset=utf-8":path.extname(f)===".js"?"text/javascript; charset=utf-8":"text/plain; charset=utf-8";res.writeHead(200,{"Content-Type":ct,"Cache-Control":"no-cache"});res.end(d)})
}).listen(PORT,"0.0.0.0",()=>{console.log("PumpScope on "+PORT);connect()});