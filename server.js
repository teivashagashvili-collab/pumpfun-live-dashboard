const http=require("http"),fs=require("fs"),path=require("path"),WebSocket=require("ws");const {URL}=require("url");
const PORT=Number(process.env.PORT||8787),PUBLIC=path.join(__dirname,"public"),clients=new Set(),tokens=new Map();
const send=(r,c,d,extra={})=>{r.writeHead(c,{"Content-Type":"application/json; charset=utf-8","Cache-Control":"no-store",...extra});r.end(JSON.stringify(d))};
const broadcast=(e,d)=>{const x=`event: ${e}\ndata: ${JSON.stringify(d)}\n\n`;for(const r of clients){try{r.write(x)}catch{}}};\nconst heartbeat=setInterval(()=>{for(const r of clients){try{r.write(`: heartbeat ${Date.now()}\\n\\n`)}catch{}}},10000);
async function getJSON(u){const r=await fetch(u,{headers:{accept:"application/json"}});if(!r.ok)throw Error(r.status);return r.json()}
function scoreSignal(p,r){
 const pc=+p?.priceChange?.m5||0,h=+p?.priceChange?.h1||0,b=+p?.txns?.h1?.buys||0,s=+p?.txns?.h1?.sells||0,l=+p?.liquidity?.usd||0,f=b+s?b/(b+s):.5;
 let x=50+pc*1.1+h*.22+(f-.5)*38+Math.min(12,Math.log10(Math.max(1,l))*2);
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
async function enrich(t){
 try{
  const a=await getJSON(`https://api.dexscreener.com/token-pairs/v1/solana/${encodeURIComponent(t.mint)}`);
  const p=Array.isArray(a)?a.filter(x=>x?.chainId==="solana").sort((a,b)=>(+b?.liquidity?.usd||0)-(+a?.liquidity?.usd||0))[0]:null;
  let r=null;try{const z=await getJSON(`https://api.rugcheck.xyz/v1/tokens/${encodeURIComponent(t.mint)}/report`);const raw=+z?.score;r={scoreRaw:Number.isFinite(raw)?raw:null,scoreNormalized:Number.isFinite(raw)?Math.max(0,Math.min(100,raw>100?raw/200:raw)):null,rugged:!!z?.rugged};}catch{}
  return{...t,pair:p,rug:r,signal:scoreSignal(p,r),updatedAt:Date.now()}
 }catch{return{...t,pair:null,rug:null,signal:scoreSignal(null,null),updatedAt:Date.now()}}
}
async function add(e){
 if(!e?.mint)return;
 const t={mint:String(e.mint),name:String(e.name||"Unknown"),symbol:String(e.symbol||"TOKEN"),creator:String(e.traderPublicKey||""),uri:String(e.uri||""),createdAt:Number(e.created_timestamp||Date.now())};
 if(tokens.has(t.mint))return;
 tokens.set(t.mint,t);while(tokens.size>100)tokens.delete(tokens.keys().next().value);broadcast("token",t);
 const z=await enrich(t);tokens.set(t.mint,z);broadcast("update",z);
}
function getCalls(){
 return [...tokens.values()].filter(t=>t.pair&&t.signal).map(t=>({...t,callType:t.signal.score>=80?"HIGH CONVICTION WATCH":t.signal.score>=68?"EARLY BUY WATCH":"WAIT"})).sort((a,b)=>b.signal.score-a.signal.score).slice(0,20);
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
 if(q.includes("risk")||q.includes("rug"))answer=`${risks.length} tracked tokens currently have elevated/flagged risk. Avoid treating a high momentum score as a safety signal; risk checks should override momentum.`;
 if(q.includes("call")||q.includes("buy"))answer=top?`The current BUY-WATCH candidates are ${high.slice(0,5).map(x=>x.symbol+" ("+x.signal.score+")").join(", ")||"none"}. These are screening candidates only; verify liquidity, holder concentration, creator activity and the live transaction before acting.`:"There are no current BUY-WATCH candidates.";
 return{answer,focus,market:{tracked:tokens.size,candidates:high.length,riskFlags:risks.length},method:"Momentum + buyer/seller flow + liquidity + RugCheck risk screening. No predictive guarantee."};
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
}).listen(PORT,()=>{console.log("PumpScope on "+PORT);connect()});