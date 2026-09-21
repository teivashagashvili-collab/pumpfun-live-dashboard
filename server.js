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
 const p=t.pair||{},s=t.signal||{},liq=+p.liquidity?.usd||0,vol=+p.volume?.h1||0,mc=+p.marketCap||+p.fdv||0;
 if(!p||s.score<62||liq<5000||vol<10000)return -1;
 if(t.rug?.rugged||(+t.rug?.scoreNormalized||0)>=60)return -1;
 return s.score+Math.min(10,Math.log10(Math.max(1,vol)))+(mc>0&&mc<5000000?8:0);
}
async function enrich(t){
 try{
  const a=await getJSON(`https://api.dexscreener.com/token-pairs/v1/solana/${encodeURIComponent(t.mint)}`);
  const p=Array.isArray(a)?a.filter(x=>x?.chainId==="solana").sort((a,b)=>(+b?.liquidity?.usd||0)-(+a?.liquidity?.usd||0))[0]:null;
  let r=null;try{const z=await getJSON(`https://api.rugcheck.xyz/v1/tokens/${encodeURIComponent(t.mint)}/report`);const raw=+z?.score;r={scoreRaw:Number.isFinite(raw)?raw:null,scoreNormalized:Number.isFinite(raw)?Math.max(0,Math.min(100,raw>100?raw/200:raw)):null,rugged:!!z?.rugged};}catch{}
  updateLearning(t,p);return{...t,pair:p,rug:r,signal:scoreSignal(p,r,trendFor(t)),updatedAt:Date.now()}
 }catch{return{...t,pair:null,rug:null,signal:scoreSignal(null,null,trendFor(t)),updatedAt:Date.now()}}
}
async function add(e){
 if(!e?.mint)return;
 const t={mint:String(e.mint),name:String(e.name||"Unknown"),symbol:String(e.symbol||"TOKEN"),creator:String(e.traderPublicKey||""),uri:String(e.uri||""),createdAt:Number(e.created_timestamp||Date.now())};
 if(tokens.has(t.mint))return;
 tokens.set(t.mint,t);while(tokens.size>100)tokens.delete(tokens.keys().next().value);broadcast("token",t);
 const z=await enrich(t);tokens.set(t.mint,z);broadcast("update",z);
}
function getCalls(){
 return [...tokens.values()].filter(t=>candidateScore(t)>=70).map(t=>({...t,callType:t.signal.score>=82?"HIGH UPSIDE WATCH":t.signal.score>=74?"EARLY OPPORTUNITY":"MOMENTUM WATCH"})).sort((a,b)=>candidateScore(b)-candidateScore(a)).slice(0,20);
}
async function walletData(address){
 if(!/^[1-9A-HJ-NP-Za-km-z]{32,44}$/.test(address))throw Error("Invalid Solana address");
 const rpc=process.env.SOLANA_RPC_URL||"https://api.mainnet-beta.solana.com";
 const body=JSON.stringify({jsonrpc:"2.0",id:1,method:"getBalance",params:[address,{commitment:"confirmed"}]});
 const r=await fetch(rpc,{method:"POST",headers:{"content-type":"application/json"},body});if(!r.ok)throw Error("RPC "+r.status);const j=await r.json();
 return{address,balanceSol:((j?.result?.value||0)/1e9),network:"mainnet-beta"};
}
function agentAnswer(question){
 const c=getCalls();const q=String(question||"").toLowerCase();
 const top=c[0],high=c.filter(x=>x.signal.score>=68),risks=c.filter(x=>x.rug?.rugged||x.rug?.scoreNormalized>=60);
 let focus=top?{token:top.symbol,mint:top.mint,score:top.signal.score,call:top.callType,reasons:top.signal.reasons}:null;
 let answer=top?`Current scanner leader: ${top.symbol} at ${top.signal.score}/100. This is a BUY-WATCH signal, not a guaranteed buy. ${top.signal.reasons.join("; ")}.`: "No token currently meets the scanner's watch threshold.";
 if(q.includes("learn")||q.includes("study")||q.includes("market"))answer="I am tracking "+tokens.size+" tokens and "+learning.samples+" completed 5-minute outcome samples. Positive outcomes: "+learning.positive+". Negative outcomes: "+learning.negative+". More observations are used to calibrate the scanner over time; this is statistical learning, not a guarantee.";
 if(q.includes("chart"))answer="I study rolling price history plus momentum, 1h volume, liquidity, buy/sell flow, market cap and risk for each enriched token.";
 if(q.includes("risk")||q.includes("rug"))answer=`${risks.length} tracked tokens currently have elevated/flagged risk. Avoid treating a high momentum score as a safety signal; risk checks should override momentum.`;
 if(q.includes("call")||q.includes("buy")||q.includes("pick")||q.includes("interesting")||q.includes("100x"))answer=top?"Current high-upside watchlist: "+high.slice(0,5).map(x=>x.symbol+" ("+x.signal.score+")").join(", ")+" . The scanner cannot know which token will 100x; it ranks setups using liquidity, volume, momentum, flow, market-cap room and risk.":"There are no current high-upside candidates.";
 return{answer,focus,market:{tracked:tokens.size,candidates:high.length,riskFlags:risks.length,learningSamples:learning.samples},method:"Liquidity + volume + momentum + buyer/seller flow + market-cap room + RugCheck risk screening with rolling outcome learning. No predictive guarantee."};
}
function connect(){
 try{const w=new WebSocket("wss://pumpportal.fun/api/data",{handshakeTimeout:15000});w.on("open",()=>{console.log("PumpPortal connected");w.send(JSON.stringify({method:"subscribeNewToken"}));w.send(JSON.stringify({method:"subscribeMigration"}));broadcast("status",{ok:true})});w.on("message",d=>{try{add(JSON.parse(String(d)))}catch{}});w.on("close",()=>{broadcast("status",{ok:false});setTimeout(connect,3000)});w.on("error",()=>broadcast("status",{ok:false}))}catch{setTimeout(connect,3000)}
}
setInterval(async()=>{for(const t of [...tokens.values()].slice(0,35)){const z=await enrich(t);tokens.set(t.mint,z);broadcast("update",z)}},15000);
http.createServer(async(req,res)=>{
 const u=new URL(req.url,`http://${req.headers.host||"localhost"}`);
 if(u.pathname==="/api/tokens")return send(res,200,[...tokens.values()]);
 if(u.pathname==="/api/calls")return send(res,200,getCalls());
 if(u.pathname==="/api/wallet"){try{return send(res,200,await walletData(u.searchParams.get("address")||""))}catch(e){return send(res,400,{error:e.message})}}
 if(u.pathname==="/api/agent"){return send(res,200,agentAnswer(u.searchParams.get("q")||""))}
 if(u.pathname==="/events"){res.writeHead(200,{"Content-Type":"text/event-stream; charset=utf-8","Cache-Control":"no-cache, no-transform","Connection":"keep-alive","Access-Control-Allow-Origin":"*","X-Accel-Buffering":"no"});res.write(`event: snapshot\ndata: ${JSON.stringify([...tokens.values()])}\n\n`);clients.add(res);req.on("close",()=>clients.delete(res));return}
 const f=path.join(PUBLIC,u.pathname==="/"?"index.html":u.pathname);if(!f.startsWith(PUBLIC))return send(res,403,{error:"forbidden"});
 fs.readFile(f,(e,d)=>{if(e)return send(res,404,{error:"not found"});const ct=path.extname(f)===".html"?"text/html; charset=utf-8":path.extname(f)===".js"?"text/javascript; charset=utf-8":"text/plain; charset=utf-8";res.writeHead(200,{"Content-Type":ct,"Cache-Control":"no-cache"});res.end(d)})
}).listen(PORT,"0.0.0.0",()=>{console.log("PumpScope on "+PORT);connect()});