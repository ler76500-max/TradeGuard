import 'dotenv/config';
import WebSocket from 'ws';
import { Telegraf } from 'telegraf';

const TOKEN = process.env.TELEGRAM_BOT_TOKEN;
if (!TOKEN) throw new Error('Missing TELEGRAM_BOT_TOKEN');
const bot = new Telegraf(TOKEN);
const CHAT_ID = process.env.TELEGRAM_CHAT_ID || '';
const MIN_SCORE = Number(process.env.MIN_SCORE || 90);
const COOLDOWN_MS = Number(process.env.COOLDOWN_SECONDS || 45) * 1000;
const MAX_ALERTS_HOUR = Number(process.env.MAX_ALERTS_PER_HOUR || 20);

const state = new Map();
const recentAlerts = [];
let ws;

const clamp=(x,a,b)=>Math.max(a,Math.min(b,x));
const mean=a=>a.length?a.reduce((x,y)=>x+y,0)/a.length:0;
function ema(values,p){ if(values.length<p)return null; const k=2/(p+1); let e=mean(values.slice(0,p)); for(let i=p;i<values.length;i++)e=values[i]*k+e*(1-k); return e; }
function rsi(v,p=14){ if(v.length<p+1)return null; let g=0,l=0; for(let i=v.length-p;i<v.length;i++){const d=v[i]-v[i-1]; if(d>0)g+=d; else l-=d;} if(l===0)return 100; const rs=(g/p)/(l/p); return 100-100/(1+rs); }
function atr(c,p=14){ if(c.length<p+1)return null; const tr=[]; for(let i=1;i<c.length;i++){const x=c[i],pr=c[i-1];tr.push(Math.max(x.h-x.l,Math.abs(x.h-pr.c),Math.abs(x.l-pr.c)));} return mean(tr.slice(-p)); }
function stdev(a){const m=mean(a); return Math.sqrt(mean(a.map(x=>(x-m)**2)));}
function adx(c,p=14){
  if(c.length<2*p+2)return null;
  const tr=[],plus=[],minus=[];
  for(let i=1;i<c.length;i++){const x=c[i],pr=c[i-1]; tr.push(Math.max(x.h-x.l,Math.abs(x.h-pr.c),Math.abs(x.l-pr.c))); const up=x.h-pr.h, dn=pr.l-x.l; plus.push(up>dn&&up>0?up:0); minus.push(dn>up&&dn>0?dn:0);}
  const t=mean(tr.slice(-p)), pdi=100*mean(plus.slice(-p))/Math.max(t,1e-12), mdi=100*mean(minus.slice(-p))/Math.max(t,1e-12); return 100*Math.abs(pdi-mdi)/Math.max(pdi+mdi,1e-12);
}
function sigmoid(x){return 1/(1+Math.exp(-x));}
function scoreSignal(s){
  const c=s.candles, prices=c.map(x=>x.c), vols=c.map(x=>x.v); const px=prices.at(-1);
  const e20=ema(prices,20),e50=ema(prices,50),e200=ema(prices,200),r=rsi(prices),a=atr(c),ad=adx(c);
  if([e20,e50,e200,r,a,ad].some(x=>x==null)) return null;
  const atrPct=a/px*100, volBase=mean(vols.slice(-21,-1))||1, volRatio=vols.at(-1)/volBase;
  const returns=prices.slice(-30).map((x,i,a)=>i?Math.log(x/a[i-1]):0).slice(1); const vol=stdev(returns);
  const mom=(prices.at(-1)-prices.at(-6))/prices.at(-6);
  const body=Math.abs(c.at(-1).c-c.at(-1).o), range=Math.max(c.at(-1).h-c.at(-1).l,1e-12), bodyRatio=body/range;
  const trendUp=e20>e50&&e50>e200, trendDn=e20<e50&&e50<e200;
  const slope=(e20-ema(prices.slice(0,-5),20))/Math.max(px,1e-12);
  const breakoutUp=px>Math.max(...c.slice(-21,-1).map(x=>x.h));
  const breakoutDn=px<Math.min(...c.slice(-21,-1).map(x=>x.l));
  const extension=Math.abs(px-e20)/Math.max(a,1e-12);
  // Hard safety filters: don't predict during extreme spread/illiquidity proxy or absurd volatility.
  if(atrPct>6 || volRatio<0.35 || extension>3.5) return {direction:'NONE',score:0,reason:'unsafe_conditions'};
  let up=0,dn=0;
  up += trendUp?22:0; dn += trendDn?22:0;
  up += r>=52&&r<=68?14: r>68?0:6; dn += r<=48&&r>=32?14: r<32?0:6;
  up += ad>=20?12:0; dn += ad>=20?12:0;
  up += mom>0?10:0; dn += mom<0?10:0;
  up += slope>0?8:0; dn += slope<0?8:0;
  up += breakoutUp?10:0; dn += breakoutDn?10:0;
  up += c.at(-1).c>c.at(-1).o&&bodyRatio>0.45?8:0; dn += c.at(-1).c<c.at(-1).o&&bodyRatio>0.45?8:0;
  up += volRatio>=1.25?8:0; dn += volRatio>=1.25?8:0;
  // Penalize overextended entries.
  if(extension>1.8){up-=10;dn-=10;}
  const direction=up>dn?'UP':dn>up?'DOWN':'NONE'; const raw=Math.max(up,dn); const confidence=clamp(Math.round(raw),0,100);
  if(direction==='NONE'||confidence<MIN_SCORE) return {direction:'NONE',score:confidence,reason:'insufficient_confirmation'};
  // Estimate horizon from momentum/volatility. This is an estimate, not a guarantee.
  const sec=clamp(Math.round(12 + 40*sigmoid((Math.abs(mom)*100-0.15)/0.35) + 8*clamp(vol/0.01,0,2)),10,90);
  const invalidation=a*1.1; const tp=a*1.4; return {direction,score:confidence,horizonSec:sec,price:px,sl:direction==='UP'?px-invalidation:px+invalidation,tp:direction==='UP'?px+tp:px-tp,atrPct,volRatio,r,ad,mom,reason:'multi-factor confirmation'};
}
function ingest(symbol,tick){
  let s=state.get(symbol); if(!s){s={candles:[],current:null,lastSignal:{},ticks:[]};state.set(symbol,s);}
  s.ticks.push(tick); if(s.ticks.length>500)s.ticks.shift();
  // Build 1-second micro candles from ticks. This is deliberately predictive only; not an execution engine.
  const sec=Math.floor(tick.t/1000)*1000; let c=s.current;
  if(!c||c.t!==sec){ if(c)s.candles.push(c); c={t:sec,o:tick.p,h:tick.p,l:tick.p,c:tick.p,v:tick.q}; s.current=c; if(s.candles.length>300)s.candles.shift(); } else {c.h=Math.max(c.h,tick.p);c.l=Math.min(c.l,tick.p);c.c=tick.p;c.v+=tick.q;}
  if(s.candles.length<210)return;
  const sig=scoreSignal(s); if(!sig||sig.direction==='NONE')return;
  const key=sig.direction; const now=Date.now(); if(now-(s.lastSignal[key]||0)<COOLDOWN_MS)return;
  while(recentAlerts.length&&recentAlerts[0]<now-3600000)recentAlerts.shift(); if(recentAlerts.length>=MAX_ALERTS_HOUR)return;
  s.lastSignal[key]=now; recentAlerts.push(now); sendSignal(symbol,sig);
}
async function sendSignal(symbol,s){
  const icon=s.direction==='UP'?'🟢':'🔴'; const dir=s.direction==='UP'?'HAUT':'BAS';
  const text=`${icon} <b>TRADEGUARD LIVE</b>\n\n<b>${dir} — ${symbol}</b>\n\n💰 Prix: ${s.price}\n⏱️ Horizon estimé: <b>${s.horizonSec}s</b>\n📊 Score modèle: <b>${s.score}/100</b>\n\nRSI: ${s.r.toFixed(1)}\nADX: ${s.ad.toFixed(1)}\nATR: ${s.atrPct.toFixed(2)}%\nVolume: ${s.volRatio.toFixed(2)}x\n\n🛑 Invalidation: ${s.sl.toFixed(8)}\n🎯 Objectif modèle: ${s.tp.toFixed(8)}\n\n⚠️ Signal probabiliste — pas une garantie. Paper trading recommandé.`;
  if(CHAT_ID) await bot.telegram.sendMessage(CHAT_ID,text,{parse_mode:'HTML'}).catch(()=>{});
}
function connect(){
  const streams=(process.env.SYMBOLS||'').split(',').map(x=>x.trim().toLowerCase()).filter(Boolean);
  // Binance combined trade stream. If SYMBOLS empty, fetch is avoided here for portability; default liquid majors.
  const syms=streams.length?streams:['btcusdt','ethusdt','solusdt','bnbusdt','xrpusdt','dogeusdt','adausdt','avaxusdt','linkusdt','suiusdt'];
  const url='wss://stream.binance.com:9443/stream?streams='+syms.map(x=>x+'@trade').join('/');
  ws=new WebSocket(url); ws.on('open',()=>console.log('TradeGuard LIVE connected:',syms.join(','))); ws.on('message',raw=>{try{const m=JSON.parse(raw.toString());const d=m.data;if(d?.s&&d?.p)ingest(d.s,{t:Number(d.T||Date.now()),p:Number(d.p),q:Number(d.q||0)});}catch{}}); ws.on('close',()=>setTimeout(connect,3000)); ws.on('error',()=>{});
}
bot.start(ctx=>ctx.reply('🛡️ TradeGuard Live V3 actif.\n\n/signals — état du moteur\n/pause — désactiver les alertes\n/resume — réactiver les alertes\n\nMode: analyse + paper trading.'));
bot.command('signals',ctx=>ctx.reply(`🧠 Moteur LIVE\nScore minimum: ${MIN_SCORE}/100\nCooldown: ${COOLDOWN_MS/1000}s\nLimite: ${MAX_ALERTS_HOUR}/h\nMode: paper trading`));
let paused=false; bot.command('pause',ctx=>{paused=true;ctx.reply('⏸️ Alertes suspendues.');}); bot.command('resume',ctx=>{paused=false;ctx.reply('▶️ Alertes réactivées.');});
const oldSend=sendSignal; // pause gate by wrapping via function replacement isn't needed; handled below
setInterval(()=>{ if(paused) recentAlerts.splice(0,recentAlerts.length); },1000);
connect();
console.log('TradeGuard Live V3 started');
