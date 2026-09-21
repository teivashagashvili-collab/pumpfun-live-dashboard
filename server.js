const http=require("http"),fs=require("fs"),path=require("path"),WebSocket=require("ws");const {URL}=require("url");const {Pool}=require("pg");
const PORT=Number(process.env.PORT||8787),PUBLIC=path.join(__dirname,"public"),clients=new Set(),tokens=new Map(),history=new Map(),learning={samples:0,positive:0,negative:0};
const pool=process.env.DATABASE_URL?new Pool({connectionString:process.env.DATABASE_URL,ssl:{rejectUnauthorized:false},max:5}):null;
let dbReady=false;
async function initDB(){
 if(!pool)return;
 try{await pool.query(`CREATE TABLE IF NOT EXISTS token_observations(id BIGSERIAL PRIMARY KEY,mint TEXT NOT NULL,ts TIMESTAMPTZ NOT NULL DEFAULT now(),price NUMERIC,market_cap NUMERIC,liquidity NUMERIC,volume_h1 NUMERIC,buys_h1 INTEGER,sells_h1 INTEGER,risk NUMERIC,signal NUMERIC,name TEXT,symbol TEXT,category TEXT);
 CREATE INDEX IF NOT EXISTS token_observations_mint_ts ON token_observations(mint,ts DESC);
 CREATE TABLE IF NOT EXISTS agent_memory(id BIGSERIAL PRIMARY KEY,ts TIMESTAMPTZ NOT NULL DEFAULT now(),kind TEXT NOT NULL,mint TEXT,content TEXT NOT NULL);
 CREATE INDEX IF NOT EXISTS agent_memory_ts ON agent_memory(ts DESC);`);
 dbReady=true; console.log("Postgres learning store ready");
 }catch(e){console.error("DB init failed:",e.message)}
}
async function persistObservation(t,p){
 if(!dbReady||!p)return;
 try{await pool.query(`INSERT INTO token_observations(mint,price,market_cap,liquidity,volume_h1,buys_h1,sells_h1,risk,signal,name,symbol,category) VALUES($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11,$12)`,
 [t.mint,+p.priceUsd||null,+p.marketCap||+p.fdv||null,+p.liquidity?.usd||null,+p.volume?.h1||null,+p.txns?.h1?.buys||0,+p.txns?.h1?.sells||0,t.rug?.scoreNormalized??null,t.signal?.score??null,t.name||null,t.symbol||null,t.category||null]);}
 catch(e){console.error("DB observation failed:",e.message)}
}
async function persistentStats(){
 if(!dbReady)return {observations:0,tokens:0,outcomes5m:0};
 try{
  const a=await pool.query("SELECT COUNT(*)::int n,COUNT(DISTINCT mint)::int tokens FROM token_observations");
  const b=await pool.query(`SELECT COUNT(*)::int n FROM token_observations a WHERE EXISTS(SELECT 1 FROM token_observations b WHERE b.mint=a.mint AND b.ts BETWEEN a.ts+interval '5 minutes' AND a.ts+interval '7 minutes' AND b.price>a.price)`);
  return{observations:a.rows[0].n,tokens:a.rows[0].tokens,outcomes5m:b.rows[0].n};
 }catch{return{observations:0,tokens:0,outcomes5m:0}}
}
async function recentMemory(){
 if(!dbReady)return[];
 try{const r=await pool.query("SELECT ts,kind,mint,content FROM agent_memory ORDER BY ts DESC LIMIT 30");return r.rows}catch{return[]}
}
async function remember(kind,content,mint=null){
 if(!dbReady)return;
 try{await pool.query("INSERT INTO agent_memory(kind,mint,content) VALUES($1,$2,$3)",[kind,mint,content])}catch{}
}
const send=(r,c,d,extra={})=>{r.writeHead(c,{"Content-Type":"application/json; charset=utf-8","Cache-Control":"no-store",...extra});r.end(JSON.stringify(d))};
const broadcast=(e,d)=>{const x=`event: ${e}\ndata: ${JSON.stringify(d)}\n\n`;for(const r of clients){try{r.write(x)}catch{}}};
const heartbeat=setInterval(()=>{for(const r of clients){try{r.write(`: heartbeat ${Date.now()}\n\n`)}catch{}}},10000);
async function getJSON(u){const r=await fetch(u,{headers:{accept:"application/json"}});if(!r.ok)throw Error(r.status);return r.json()}
function scoreSignal(p,r,trend={}){
 const pc=+p?.priceChange?.m5||0,h=+p?.priceChange?.h1||0,b=+p?.txns?.h1?.buys||0,s=+p?.txns?.h1?.sells||0,l=+p?.liquidity?.usd||0,v=+p?.volume?.h1||0,f=b+s?b/(b+s):.5,mc=+p?.marketCap||+p?.fdv||0;
 const ageH=p?.pairCreatedAt?Math.max(0,(Date.now()-p.pairCreatedAt)/3600000):9999,vl=l>0?v/l:0,trades=b+s;
 let x=38+pc*1.05+h*.20+(f-.5)*34+Math.min(15,Math.log10(Math.max(1,l))*2.6)+Math.min(15,Math.log10(Math.max(1,v))*2.2)+Math.max(-8,Math.min(8,+trend.accel||0));
 if(ageH<=1)x+=4;else if(ageH>72)x-=5;
 if(vl<1)x-=10;else if(vl>8)x+=5;
 if(trades<25)x-=8;
 if(mc>25000000)x-=18;if(mc>100000000)x-=28;
 if(r?.rugged)x-=60;if(r?.scoreNormalized!=null)x-=Math.min(45,r.scoreNormalized*.55);
 x=Math.max(0,Math.min(100,x));
 const label=x>=82?"A-TIER WATCH":x>=72?"QUALIFIED WATCH":x>=62?"MOMENTUM WATCH":"NO CALL";
 return{score:Math.round(x),label,side:x>=72?"WATCH":"WAIT",reasons:[
  pc>4?"5m momentum positive":pc<-5?"5m momentum weak":null,
  h>10?"1h trend strong":h<-10?"1h trend weak":null,
  f>.60?"buyers dominate":f<.40?"sellers dominate":null,
  l>=25000?"liquidity has depth":l<10000?"thin liquidity":null,
  vl>=5?"strong volume/liquidity ratio":vl<1?"weak volume relative to liquidity":null,
  ageH<=24?"fresh market":ageH>72?"older pair":null,
  mc>25000000?"large-cap penalty":mc>0&&mc<5000000?"small-cap room":null,
  r?.rugged?"rug flag":r?.scoreNormalized>=45?"elevated safety risk":null
 ].filter(Boolean).slice(0,5),metrics:{ageHours:ageH,volumeLiquidity:vl,buyRatio:f,marketCap:mc,trades}};
}
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
  updateLearning(merged,p); persistObservation(merged,p);
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
function usd(x){x=+x;if(!Number.isFinite(x))return"—";if(x>=1e9)return"$"+(x/1e9).toFixed(2)+"B";if(x>=1e6)return"$"+(x/1e6).toFixed(2)+"M";if(x>=1e3)return"$"+(x/1e3).toFixed(1)+"K";return"$"+x.toPrecision(4)}
function findToken(q){
 const s=String(q||"").toLowerCase().trim();
 return [...tokens.values()].find(t=>t.mint.toLowerCase()===s||t.symbol?.toLowerCase()===s||t.name?.toLowerCase()===s)||[...tokens.values()].find(t=>s&&(t.symbol?.toLowerCase().includes(s)||t.name?.toLowerCase().includes(s)));
}
function tradePlan(t){
 const p=t?.pair||{},price=+p.priceUsd||0,mc=+p.marketCap||+p.fdv||0,liq=+p.liquidity?.usd||0,score=+t?.signal?.score||0,risk=+t?.rug?.scoreNormalized||0;
 if(!price||!mc)return{status:"NO_DATA"};
 const eligible=score>=72&&liq>=10000&&risk<45&&candidateScore(t)>=72;
 const buyRatio=+(t?.signal?.metrics?.buyRatio||0.5),h1=+p.priceChange?.h1||0,m5=+p.priceChange?.m5||0;
 const entryLow=price*(m5>8?0.97:0.985),entryHigh=price*(m5>8?1.01:1.02);
 const exits=[{multiple:1.5,sellPct:20,mc:mc*1.5},{multiple:2,sellPct:20,mc:mc*2},{multiple:3,sellPct:20,mc:mc*3},{multiple:5,sellPct:20,mc:mc*5},{multiple:null,sellPct:20,mc:null}];
 return{status:eligible?"RESEARCH_ENTRY":"NO_ENTRY",eligible,score,risk,price,marketCap:mc,liquidity:liq,entry:{low:entryLow,high:entryHigh,reason:m5>8?"avoid chasing; prefer pullback":"narrow band near current price"},invalidation:{price:price*0.88,percent:-12},exits,runner:{pct:20,rule:"keep only while structure stays constructive; reconsider if 1h momentum rolls over, sellers dominate, or liquidity deteriorates"},signals:{m5,h1,buyRatio},note:"Rules-based research scenario, not a guarantee or personalized financial recommendation."};
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
async function llmAgent(question){
 const key=process.env.OPENAI_API_KEY;
 if(!key)return null;
 const candidates=getCalls().slice(0,12).map(t=>({mint:t.mint,name:t.name,symbol:t.symbol,category:t.category,score:t.signal.score,reasons:t.signal.reasons,metrics:t.signal.metrics,price:t.pair?.priceUsd,mc:t.pair?.marketCap||t.pair?.fdv,liquidity:t.pair?.liquidity?.usd,volume1h:t.pair?.volume?.h1,buys:t.pair?.txns?.h1?.buys,sells:t.pair?.txns?.h1?.sells,risk:t.rug?.scoreNormalized,plan:tradePlan(t)}));
 const mem=await recentMemory(),stats=await persistentStats();
 const system=`You are PumpScope's live crypto market research agent. Speak naturally, deeply and clearly like a strong research analyst. Never invent live facts. The supplied market data is the source of truth. Explain evidence, uncertainty, risk, liquidity, market structure and alternative interpretations. Do not promise profits or claim a token will 100x. Distinguish observation from inference. If evidence is insufficient, say so. The scanner's qualified candidates are research candidates, not guaranteed buys. When asked for an entry or exit call, give a clearly labeled rules-based research plan from the supplied live data. Give NO ENTRY when eligibility fails. For exits, provide staged percentages and market-cap multiples as a mechanical scenario, never as a prediction or certainty. Persistent observations: ${stats.observations}; tracked historical tokens: ${stats.tokens}; positive 5m outcome observations: ${stats.outcomes5m}. Recent agent memory: ${JSON.stringify(mem)}. Current qualified candidates: ${JSON.stringify(candidates)}`;
 try{
  const r=await fetch("https://api.openai.com/v1/responses",{method:"POST",headers:{"content-type":"application/json","authorization":"Bearer "+key},body:JSON.stringify({model:process.env.OPENAI_MODEL||"gpt-5.6-luna",instructions:system,input:question,reasoning:{effort:"medium"},max_output_tokens:900})});
  if(!r.ok)throw Error("LLM "+r.status);
  const j=await r.json();const text=j.output_text||j.output?.flatMap(x=>x.content||[]).map(x=>x.text||"").join("")||"";
  if(!text)throw Error("empty LLM response");
  await remember("conversation",JSON.stringify({q:question,a:text}));
  return text;
 }catch(e){console.error("LLM agent failed:",e.message);return null}
}
async function agentAnswer(question){
 const requested=findToken(question),plan=requested?tradePlan(requested):null;
 const ai=await llmAgent(question); if(ai)return{answer:ai,mode:"llm",plan,market:{tracked:tokens.size,candidates:getCalls().length,learningSamples:learning.samples}};
 const c=getCalls(),q=String(question||"").trim().toLowerCase(),top=c[0],high=c.slice(0,10),all=getRadar(),risks=all.filter(x=>x.rug?.rugged||x.rug?.scoreNormalized>=45),early=all.filter(x=>x.category==="EARLY"&&candidateScore(x)>=60).slice(0,8);
 let answer;
 if(!q)answer="I’m the market research layer. Ask me about a token, risk, charts, the current regime, qualified setups, or what the historical observations are learning.";
 else if(q.includes("risk")||q.includes("rug")||q.includes("scam"))answer="Safety is a hard gate here. I exclude RugCheck flags/elevated risk, thin liquidity, weak activity and weak volume/liquidity from qualified opportunities. "+risks.length+" tracked tokens currently show elevated risk.";
 else if(q.includes("learn")||q.includes("study")){const ps=await persistentStats();answer="The learning system now persists market observations in PostgreSQL. It has "+ps.observations+" observations across "+ps.tokens+" tokens, with "+ps.outcomes5m+" positive 5-minute follow-through observations in the persistent store. In-process learning currently has "+learning.samples+" samples. The next layer is calibration: measure which features actually predict future outcomes instead of assuming a feature is useful.";}
 else if(q.includes("market")||q.includes("regime"))answer="I’m monitoring fresh-token flow, momentum, buyer/seller balance, liquidity, volume/liquidity, pair age and market-cap expansion room. Those are observable microstructure signals; they are not proof of a macroeconomic causal relationship.";
 else if(q.includes("call")||q.includes("buy")||q.includes("pick")||q.includes("entry")||q.includes("exit")||q.includes("sell")||q.includes("100x")){ if(requested&&plan){ const ladder=(plan.exits||[]).slice(0,4).map(x=>"+"+((x.multiple-1)*100).toFixed(0)+"%: sell "+x.sellPct+"% at MC "+usd(x.mc)).join("; "); answer=plan.eligible?"ENTRY WATCH for "+requested.name+" ("+requested.symbol+"). Score "+plan.score+"/100. Entry band: "+usd(plan.entry.low)+"–"+usd(plan.entry.high)+". Invalidation reference: "+usd(plan.invalidation.price)+" ("+plan.invalidation.percent+"%). Profit-taking scenario: "+ladder+". Keep "+plan.runner.pct+"% as a runner only while structure remains constructive; reconsider if 1h momentum rolls over, sellers dominate or liquidity deteriorates. This is a rules-based research scenario, not a guarantee.":"NO ENTRY for "+requested.name+" ("+requested.symbol+") right now. Score "+plan.score+"/100, risk "+plan.risk+", liquidity "+usd(plan.liquidity)+". Wait for the scanner gates to improve rather than forcing an entry.";} else answer=top?"Current qualified research candidates: "+high.map(x=>x.symbol+" ("+x.signal.score+"/100)").join(", ")+". Ask me for the exact token name/symbol or mint and I can generate an entry/invalidation/profit-taking scenario.":"No token currently clears the full quality gate. The system intentionally prefers no call to a low-quality call.";}
 else answer=top?"The strongest current qualified candidate is "+top.name+" ("+top.symbol+") at "+top.signal.score+"/100. Evidence: "+top.signal.reasons.join("; ")+". Ask me for a specific mint for a deeper breakdown.":"Nothing currently clears the quality gate.";
 return{answer,mode:"rules",market:{tracked:tokens.size,candidates:c.length,riskFlags:risks.length,early:early.length,learningSamples:learning.samples},method:"Live market data + risk gates + persistent observations + calibrated feature research."};
}
function connect(){
 try{const w=new WebSocket("wss://pumpportal.fun/api/data",{handshakeTimeout:15000});w.on("open",()=>{console.log("PumpPortal connected");w.send(JSON.stringify({method:"subscribeNewToken"}));w.send(JSON.stringify({method:"subscribeMigration"}));broadcast("status",{ok:true})});w.on("message",d=>{try{add(JSON.parse(String(d)))}catch{}});w.on("close",()=>{broadcast("status",{ok:false});setTimeout(connect,3000)});w.on("error",()=>broadcast("status",{ok:false}))}catch{setTimeout(connect,3000)}
}
setInterval(async()=>{for(const t of [...tokens.values()].slice(0,35)){const z=await enrich(t);tokens.set(t.mint,z);broadcast("update",z)}},15000);
initDB().catch(()=>{});
http.createServer(async(req,res)=>{
 const u=new URL(req.url,`http://${req.headers.host||"localhost"}`);
 if(u.pathname==="/api/tokens")return send(res,200,[...tokens.values()]);
 if(u.pathname==="/api/radar")return send(res,200,getRadar());
 if(u.pathname==="/api/health")return send(res,200,{ok:true,tracked:tokens.size,qualified:getCalls().length,learningSamples:learning.samples,now:Date.now()});
 if(u.pathname==="/api/calls")return send(res,200,getCalls().map(t=>({...t,tradePlan:tradePlan(t)})));
 if(u.pathname==="/api/plan"){const t=findToken(u.searchParams.get("q")||u.searchParams.get("mint")||"");return send(res,200,t?{token:{mint:t.mint,name:t.name,symbol:t.symbol},plan:tradePlan(t)}:{error:"Token not found"});}
 if(u.pathname==="/api/wallet"){try{return send(res,200,await walletData(u.searchParams.get("address")||""))}catch(e){return send(res,400,{error:e.message})}}
 if(u.pathname==="/api/agent"){return send(res,200,await agentAnswer(u.searchParams.get("q")||""))}
 if(u.pathname==="/api/learning"){return send(res,200,{persistent:await persistentStats(),inProcess:learning})}
 if(u.pathname==="/events"){res.writeHead(200,{"Content-Type":"text/event-stream; charset=utf-8","Cache-Control":"no-cache, no-transform","Connection":"keep-alive","Access-Control-Allow-Origin":"*","X-Accel-Buffering":"no"});res.write(`event: snapshot\ndata: ${JSON.stringify([...tokens.values()])}\n\n`);clients.add(res);req.on("close",()=>clients.delete(res));return}
 const f=path.join(PUBLIC,u.pathname==="/"?"index.html":u.pathname);if(!f.startsWith(PUBLIC))return send(res,403,{error:"forbidden"});
 fs.readFile(f,(e,d)=>{if(e)return send(res,404,{error:"not found"});const ct=path.extname(f)===".html"?"text/html; charset=utf-8":path.extname(f)===".js"?"text/javascript; charset=utf-8":"text/plain; charset=utf-8";res.writeHead(200,{"Content-Type":ct,"Cache-Control":"no-cache"});res.end(d)})
}).listen(PORT,"0.0.0.0",()=>{console.log("PumpScope on "+PORT);connect()});
// Railway deployment verification: deploy current main commit.
