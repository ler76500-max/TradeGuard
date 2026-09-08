import 'dotenv/config';
import WebSocket from 'ws';
import { Telegraf, Markup } from 'telegraf';
import crypto from 'crypto';

const TOKEN = process.env.TELEGRAM_BOT_TOKEN;
if (!TOKEN) throw new Error('Missing TELEGRAM_BOT_TOKEN');
const bot = new Telegraf(TOKEN);
const CHAT_ID = process.env.TELEGRAM_CHAT_ID || '';
const MIN_SCORE = Number(process.env.MIN_SCORE || 50);
const COOLDOWN_MS = Number(process.env.COOLDOWN_SECONDS || 10) * 1000;
const MAX_ALERTS_HOUR = Number(process.env.MAX_ALERTS_PER_HOUR || 20);
const TRADE_USDT = Number(process.env.TRADE_USDT || 10);
const LIVE_TRADING = String(process.env.LIVE_TRADING_ENABLED || 'false').toLowerCase() === 'true';
const DEMO_TRADING = String(process.env.BINANCE_DEMO_TRADING || 'false').toLowerCase() === 'true';
const TESTNET_TRADING = String(process.env.BINANCE_FUTURES_TESTNET || 'true').toLowerCase() === 'true';
const BINANCE_BASE = process.env.BINANCE_FUTURES_API_BASE || (TESTNET_TRADING ? 'https://testnet.binancefuture.com' : (DEMO_TRADING ? 'https://demo-fapi.binance.com' : 'https://fapi.binance.com'));
const BASE_LEVERAGE = Math.max(1, Math.min(Number(process.env.FUTURES_LEVERAGE || 1), 20));
const MAX_TARGET_LEVERAGE = Math.max(BASE_LEVERAGE, Math.min(Number(process.env.MAX_TARGET_LEVERAGE || 10), 20));
const FEE_RATE = Number(process.env.FEE_RATE || 0.0005);
// 1.0 = +100% net profit on margin (x2 total balance for that trade).
const TARGET_PROFIT_MULTIPLE = Math.max(0, Number(process.env.TARGET_PROFIT_MULTIPLE || 1.0));
const MAX_TARGET_ATR = Math.max(1.5, Number(process.env.MAX_TARGET_ATR || 3.0));
const TRAIL_START_MULTIPLE = Math.max(0.25, Number(process.env.TRAIL_START_MULTIPLE || 0.5));
const TRAIL_GIVEBACK_MULTIPLE = Math.max(0.15, Number(process.env.TRAIL_GIVEBACK_MULTIPLE || 0.35));
const SIGNAL_TTL_MS = Number(process.env.SIGNAL_TTL_SECONDS || 30) * 1000;
let paused = false;

const API_KEY = process.env.BINANCE_API_KEY || '';
const API_SECRET = process.env.BINANCE_API_SECRET || '';
if (API_KEY && API_SECRET) console.log('✅ Binance API credentials detected');
console.log(`⚙️ Futures Testnet: ${TESTNET_TRADING} | Demo Futures: ${DEMO_TRADING} | Trading enabled: ${LIVE_TRADING} | Trade size: ${TRADE_USDT} USDT`);
if (LIVE_TRADING && (!API_KEY || !API_SECRET)) throw new Error('LIVE_TRADING_ENABLED=true but Binance API credentials are missing');

const state = new Map();
const recentAlerts = [];
const pendingSignals = new Map();
const activeTrades = new Map();
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
  if(extension>1.8){up-=10;dn-=10;}
  const direction=up>dn?'UP':dn>up?'DOWN':'NONE'; const raw=Math.max(up,dn); const confidence=clamp(Math.round(raw),0,100);
  if(direction==='NONE'||confidence<MIN_SCORE) return {direction:'NONE',score:confidence,reason:'insufficient_confirmation'};
  const sec=clamp(Math.round(12 + 40*sigmoid((Math.abs(mom)*100-0.15)/0.35) + 8*clamp(vol/0.01,0,2)),10,90);
  const invalidation=a*1.1; const tp=a*1.4;
  return {direction,score:confidence,horizonSec:sec,price:px,sl:direction==='UP'?px-invalidation:px+invalidation,tp:direction==='UP'?px+tp:px-tp,atrPct,volRatio,r,ad,mom,reason:'multi-factor confirmation'};
}

async function signedBinance(method, path, params={}) {
  const timestamp = Date.now();
  const query = new URLSearchParams({...params, timestamp: String(timestamp), recvWindow:'5000'}).toString();
  const signature = crypto.createHmac('sha256', API_SECRET).update(query).digest('hex');
  const url = `${BINANCE_BASE}${path}?${query}&signature=${signature}`;
  const res = await fetch(url, {method, headers:{'X-MBX-APIKEY':API_KEY}});
  const text = await res.text();
  let data; try { data=JSON.parse(text); } catch { data={msg:text}; }
  if (!res.ok) throw new Error(`Binance ${res.status}: ${data.msg || text}`);
  return data;
}

// Avoid Futures /exchangeInfo because some hosting IPs (including Railway) can receive HTTP 451.
// Conservative quantity steps for the symbols used by TradeGuard.
const symbolMeta = new Map([
  ['BTCUSDT',{status:'TRADING',stepSize:0.001,minQty:0.001}],
  ['ETHUSDT',{status:'TRADING',stepSize:0.01,minQty:0.01}],
  ['SOLUSDT',{status:'TRADING',stepSize:0.1,minQty:0.1}],
  ['BNBUSDT',{status:'TRADING',stepSize:0.01,minQty:0.01}],
  ['XRPUSDT',{status:'TRADING',stepSize:1,minQty:1}],
  ['DOGEUSDT',{status:'TRADING',stepSize:1,minQty:1}],
  ['ADAUSDT',{status:'TRADING',stepSize:1,minQty:1}],
  ['AVAXUSDT',{status:'TRADING',stepSize:0.1,minQty:0.1}],
  ['LINKUSDT',{status:'TRADING',stepSize:0.1,minQty:0.1}],
  ['SUIUSDT',{status:'TRADING',stepSize:1,minQty:1}]
]);
async function getSymbolMeta(symbol){
  const meta=symbolMeta.get(symbol);
  if(!meta) throw new Error(`Symbole ${symbol} non configuré`);
  return meta;
}
async function setLeverage(symbol, leverage=BASE_LEVERAGE){ return signedBinance('POST','/fapi/v1/leverage',{symbol,leverage:String(leverage)}); }
function floorStep(q,step){ if(!step||step<=0)return q; return Math.floor(q/step)*step; }
function decimals(step){ if(!step)return 8; const s=String(step); return s.includes('.') ? s.split('.')[1].replace(/0+$/,'').length : 0; }

function chooseTargetPlan(sig){
  // Target mode: aim for x2 total (100% net on margin) when the market can
  // plausibly deliver it. Otherwise trade only when a smaller positive target
  // is realistically reachable, using the maximum plausible ATR move.
  const atrAbs=Math.abs(sig.price*sig.atrPct/100);
  const maxMovePct=(atrAbs/Math.max(sig.price,1e-12))*MAX_TARGET_ATR;
  const feeRoundTrip=2*FEE_RATE;
  let leverage=BASE_LEVERAGE;
  let achievable=(leverage*maxMovePct)-(leverage*feeRoundTrip);
  if(achievable < TARGET_PROFIT_MULTIPLE){
    for(let l=Math.ceil(BASE_LEVERAGE); l<=MAX_TARGET_LEVERAGE; l++){
      const net=(l*maxMovePct)-(l*feeRoundTrip);
      if(net>achievable) { leverage=l; achievable=net; }
      if(net>=TARGET_PROFIT_MULTIPLE) break;
    }
  }
  // Ignore tiny opportunities that are unlikely to overcome execution noise.
  if(achievable < 0.25) return null;
  const effectiveTargetMultiple=Math.min(TARGET_PROFIT_MULTIPLE, achievable);
  const requiredMovePct=(effectiveTargetMultiple/leverage)+feeRoundTrip;
  const targetMovePct=Math.min(maxMovePct, requiredMovePct);
  const targetPrice=sig.direction==='UP'?sig.price*(1+targetMovePct):sig.price*(1-targetMovePct);
  return {leverage,requiredMovePct,targetMovePct,maxMovePct,achievableMultiple:achievable,effectiveTargetMultiple,targetPrice};
}

async function executeEntry(symbol,sig){
  if(!LIVE_TRADING) throw new Error('Trading désactivé: LIVE_TRADING_ENABLED=false');
  const meta=await getSymbolMeta(symbol);
  if(meta.status!=='TRADING') throw new Error(`Symbole ${symbol} non disponible en Futures`);
  const plan=chooseTargetPlan(sig);
  if(!plan) throw new Error('Pas de trade: mouvement potentiel trop faible après frais.');
  await setLeverage(symbol, plan.leverage);
  const px=Number((await fetch(`${BINANCE_BASE}/fapi/v1/ticker/price?symbol=${symbol}`).then(r=>r.json())).price);
  const qty=floorStep((TRADE_USDT*plan.leverage)/px,meta.stepSize);
  if(qty<meta.minQty) throw new Error(`Quantité trop faible pour ${symbol}. Augmente TRADE_USDT.`);
  const side=sig.direction==='UP'?'BUY':'SELL';
  const order=await signedBinance('POST','/fapi/v1/order',{symbol,side,type:'MARKET',quantity:qty.toFixed(decimals(meta.stepSize)),newOrderRespType:'RESULT'});
  if(order.status!=='FILLED' && Number(order.executedQty||0)<=0) throw new Error(`Ordre non exécuté: ${order.status||'unknown'}`);
  return {order,entryPrice:Number(order.avgPrice||px),executedQty:Number(order.executedQty||qty),plan};
}

async function closeSpotLong(trade,reason){
  if(trade.closed||trade.closing) return; trade.closing=true;
  try{
    const side=trade.direction==='UP'?'SELL':'BUY';
    const qtyStr=trade.executedQty.toFixed(decimals(trade.stepSize));
    const order=await signedBinance('POST','/fapi/v1/order',{symbol:trade.symbol,side,type:'MARKET',quantity:qtyStr,reduceOnly:'true',newOrderRespType:'RESULT'});
    const exitPrice=Number(order.avgPrice||trade.lastPrice);
    const pnlGross=trade.direction==='UP'?(exitPrice-trade.entryPrice)*trade.executedQty:(trade.entryPrice-exitPrice)*trade.executedQty;
    const notionalEntry=trade.entryPrice*trade.executedQty;
    const notionalExit=exitPrice*trade.executedQty;
    const fees=(notionalEntry+notionalExit)*FEE_RATE;
    const pnlNet=pnlGross-fees;
    const roi=(pnlNet/TRADE_USDT)*100;
    const multiple=1+(pnlNet/TRADE_USDT);
    trade.closed=true; activeTrades.delete(trade.id);
    await bot.telegram.sendMessage(CHAT_ID,`🔔 <b>FUTURES FERMÉ</b>\n\n${trade.symbol}\n📌 Motif: <b>${reason}</b>\n📍 Entrée: ${trade.entryPrice}\n📍 Sortie: ${exitPrice}\n💵 Marge: ${TRADE_USDT.toFixed(2)} USDT\n⚙️ Levier: ${trade.leverage}x\n📈 P&L brut: <b>${pnlGross>=0?'+':''}${pnlGross.toFixed(4)} USDT</b>\n💸 Frais estimés: ${fees.toFixed(4)} USDT\n💰 Net estimé: <b>${pnlNet>=0?'+':''}${pnlNet.toFixed(4)} USDT</b>\n📊 ROI marge: <b>${roi>=0?'+':''}${roi.toFixed(2)}%</b>\n✖️ Multiplicateur: <b>x${multiple.toFixed(2)}</b>`,{parse_mode:'HTML'}).catch(()=>{});
  }catch(err){
    trade.closing=false; console.error(`❌ Futures close error ${trade.symbol}:`,err.message);
    await bot.telegram.sendMessage(CHAT_ID,`🚨 <b>ERREUR FERMETURE FUTURES</b>\n\n${trade.symbol}\n${err.message}\n\n⚠️ Vérifie immédiatement la position sur Binance.`,{parse_mode:'HTML'}).catch(()=>{});
  }
}

async function monitorTrade(symbol, tick){
  for(const trade of activeTrades.values()){
    if(trade.symbol!==symbol || trade.closed) continue;
    trade.lastPrice=tick.p;
    const age=Date.now()-trade.openedAt;
    if(trade.direction==='UP' && tick.p>=trade.tp) return closeSpotLong(trade,'Take Profit');
    if(trade.direction==='UP' && tick.p<=trade.sl) return closeSpotLong(trade,'Stop Loss');
    if(trade.direction==='DOWN' && tick.p<=trade.tp) return closeSpotLong(trade,'Take Profit');
    if(trade.direction==='DOWN' && tick.p>=trade.sl) return closeSpotLong(trade,'Stop Loss');

    // Trailing profit: once a meaningful fraction of the target is reached,
    // protect the gain and let the move continue toward x2 or beyond.
    const grossPnl=trade.direction==='UP'?(tick.p-trade.entryPrice)*trade.executedQty:(trade.entryPrice-tick.p)*trade.executedQty;
    const currentMultiple=1+(grossPnl/TRADE_USDT);
    if(currentMultiple >= 1+TRAIL_START_MULTIPLE){
      const trailPnl=TRADE_USDT*TRAIL_GIVEBACK_MULTIPLE;
      const trailDistance=trailPnl/Math.max(trade.executedQty,1e-12);
      const newSl=trade.direction==='UP'?tick.p-trailDistance:tick.p+trailDistance;
      if(trade.direction==='UP') trade.sl=Math.max(trade.sl,newSl);
      else trade.sl=Math.min(trade.sl,newSl);
    }
    if(age>=trade.horizonMs) return closeSpotLong(trade,'Fin de l’horizon');
    // Sortie anticipée: si une nouvelle analyse forte indique un retournement.
    const s=state.get(symbol);
    if(s && s.candles.length>=210){
      const fresh=scoreSignal(s);
      const reversal = trade.direction==='UP' ? fresh?.direction==='DOWN' : fresh?.direction==='UP';
      if(reversal && fresh.score>=60) return closeSpotLong(trade,'Retournement détecté');
    }
  }
}

function ingest(symbol,tick){
  let s=state.get(symbol); if(!s){s={candles:[],current:null,lastSignal:{},ticks:[]};state.set(symbol,s);}
  s.ticks.push(tick); if(s.ticks.length>500)s.ticks.shift();
  // Surveille les positions ouvertes sur CHAQUE tick : TP, SL, horizon et retournement.
  // Sans cet appel, monitorTrade existe mais n'est jamais exécuté.
  void monitorTrade(symbol,tick).catch(err=>console.error(`❌ Trade monitor error ${symbol}:`,err.message));
  const sec=Math.floor(tick.t/1000)*1000; let c=s.current;
  if(!c||c.t!==sec){ if(c)s.candles.push(c); c={t:sec,o:tick.p,h:tick.p,l:tick.p,c:tick.p,v:tick.q}; s.current=c; if(s.candles.length>300)s.candles.shift(); } else {c.h=Math.max(c.h,tick.p);c.l=Math.min(c.l,tick.p);c.c=tick.p;c.v+=tick.q;}
  if(s.candles.length<210)return;
  const sig=scoreSignal(s); if(!sig||sig.direction==='NONE')return;
  const key=sig.direction; const now=Date.now(); if(now-(s.lastSignal[key]||0)<COOLDOWN_MS)return;
  while(recentAlerts.length&&recentAlerts[0]<now-3600000)recentAlerts.shift(); if(recentAlerts.length>=MAX_ALERTS_HOUR)return;
  s.lastSignal[key]=now; recentAlerts.push(now); sendSignal(symbol,sig).catch(err=>console.error('Signal send error:',err.message));
}

async function sendSignal(symbol,s){
  if(paused || !CHAT_ID) return;
  const icon=s.direction==='UP'?'🟢':'🔴'; const dir=s.direction==='UP'?'HAUT':'BAS';
  const id=crypto.randomUUID();
  pendingSignals.set(id,{symbol,s,createdAt:Date.now(),used:false});
  setTimeout(()=>pendingSignals.delete(id),SIGNAL_TTL_MS);
  const text=`${icon} <b>TRADEGUARD LIVE</b>\n\n<b>${dir} — ${symbol}</b>\n\n💰 Prix: ${s.price}\n⏱️ Horizon estimé: <b>${s.horizonSec}s</b>\n📊 Score modèle: <b>${s.score}/100</b>\n\nRSI: ${s.r.toFixed(1)}\nADX: ${s.ad.toFixed(1)}\nATR: ${s.atrPct.toFixed(2)}%\nVolume: ${s.volRatio.toFixed(2)}x\n\n🛑 Invalidation: ${s.sl.toFixed(8)}\n🎯 Objectif modèle: ${s.tp.toFixed(8)}\n\n⚠️ Le score n'est pas une probabilité de gain.`;
  await bot.telegram.sendMessage(CHAT_ID,text,{parse_mode:'HTML',...Markup.inlineKeyboard([[Markup.button.callback('💰 TRADE',`trade:${id}`),Markup.button.callback('⏭️ SKIP',`skip:${id}`)]])}).catch(()=>{});
}

bot.action(/^skip:(.+)$/, async ctx=>{
  const id=ctx.match[1], p=pendingSignals.get(id);
  if(!p) return ctx.answerCbQuery('Signal expiré.');
  pendingSignals.delete(id); await ctx.answerCbQuery('Signal ignoré.');
  try { await ctx.editMessageReplyMarkup({inline_keyboard:[]}); } catch {}
  await ctx.reply(`⏭️ SKIP confirmé — ${p.symbol} ${p.s.direction==='UP'?'HAUT':'BAS'}. Aucun ordre envoyé.`);
});

bot.action(/^trade:(.+)$/, async ctx=>{
  const id=ctx.match[1], p=pendingSignals.get(id);
  if(!p) return ctx.answerCbQuery('Signal expiré.');
  if(p.used) return ctx.answerCbQuery('Signal déjà utilisé.');
  if(Date.now()-p.createdAt>SIGNAL_TTL_MS){pendingSignals.delete(id); return ctx.answerCbQuery('Signal expiré.');}
  p.used=true;
  await ctx.answerCbQuery(LIVE_TRADING?'Envoi de l’ordre à Binance…':'Trading désactivé.');
  try {
    const order=await executeEntry(p.symbol,p.s);
    pendingSignals.delete(id);
    try { await ctx.editMessageReplyMarkup({inline_keyboard:[]}); } catch {}
    const fills=order.fills||[];
    const totalQty=Number(order.executedQty||0) || fills.reduce((a,f)=>a+Number(f.qty||0),0);
    const totalCost=fills.reduce((a,f)=>a+Number(f.qty||0)*Number(f.price||0),0);
    const entryPrice=Number(order.avgPrice||0) || (totalQty&&totalCost?totalCost/totalQty:p.s.price);
    const plan=order.plan;
    const targetPrice=plan.targetPrice;
    const trade={id,symbol:p.symbol,direction:p.s.direction,entryPrice,executedQty:totalQty,openedAt:Date.now(),horizonMs:Math.max(p.s.horizonSec*1000,15000),tp:targetPrice,sl:p.s.sl,lastPrice:entryPrice,closed:false,leverage:plan.leverage,targetMultiple:1+TARGET_PROFIT_MULTIPLE};
    activeTrades.set(id,trade);
    await ctx.reply(`💰 <b>FUTURES OUVERT</b>\n\n${p.s.direction==='UP'?'🟢 LONG':'🔴 SHORT'} — ${p.symbol}\n💵 Marge: ${TRADE_USDT} USDT\n⚙️ Levier: ${plan.leverage}x\n📍 Entrée: ${entryPrice}\n🎯 Objectif visé: x${(1+plan.effectiveTargetMultiple).toFixed(2)} — ${targetPrice}\n🛑 SL: ${p.s.sl}\n⏱️ Horizon max: ${Math.max(p.s.horizonSec,15)}s\n🪝 Trailing: activé\n\n🔄 Fermeture automatique activée.`,{parse_mode:'HTML'});
  } catch(err) {
    p.used=false;
    await ctx.reply(`❌ TRADE refusé / échoué\n\n${p.symbol}\n${err.message}`);
  }
});

function connect(){
  const streams=(process.env.SYMBOLS||'').split(',').map(x=>x.trim().toLowerCase()).filter(Boolean);
  const syms=streams.length?streams:['btcusdt','ethusdt','solusdt','bnbusdt','xrpusdt','dogeusdt','adausdt','avaxusdt','linkusdt','suiusdt'];
  const url='wss://data-stream.binance.vision:443/stream?streams='+syms.map(x=>x+'@trade').join('/');
  console.log('Connecting to market data:', url);
  ws=new WebSocket(url);
  ws.on('open',()=>console.log('TradeGuard LIVE connected:',syms.join(',')));
  ws.on('message',raw=>{try{const m=JSON.parse(raw.toString());const d=m.data;if(d?.s&&d?.p)ingest(d.s,{t:Number(d.T||Date.now()),p:Number(d.p),q:Number(d.q||0)});}catch(err){console.error('Market message error:',err.message);}});
  ws.on('close',(code,reason)=>{console.error('Market WebSocket closed:',code,reason?.toString()||''); setTimeout(connect,3000);});
  ws.on('error',err=>console.error('Market WebSocket error:',err.message));
}

bot.start(ctx=>ctx.reply('🛡️ TradeGuard Live actif.\n\n/signals — état du moteur\n/pause — désactiver les alertes\n/resume — réactiver les alertes\n\nLes signaux sont envoyés automatiquement.'));
bot.command('signals',ctx=>ctx.reply(`🧠 Moteur LIVE\nScore minimum: ${MIN_SCORE}/100\nCooldown: ${COOLDOWN_MS/1000}s\nLimite: ${MAX_ALERTS_HOUR}/h\nEnvoi: automatique\nMode: Binance Futures\nTrading réel: ${LIVE_TRADING?'ACTIF':'DÉSACTIVÉ'}\nTaille: ${TRADE_USDT} USDT\nLevier de base: ${BASE_LEVERAGE}x\nLevier cible max: ${MAX_TARGET_LEVERAGE}x\nObjectif: x${(1+TARGET_PROFIT_MULTIPLE).toFixed(2)}\nTrailing: actif`));
bot.command('test',ctx=>ctx.reply('🧪 TradeGuard OK — Telegram est bien connecté.\n\nLe moteur LIVE est actif et prêt à envoyer les alertes.'));
bot.command('pause',ctx=>{paused=true;ctx.reply('⏸️ Alertes suspendues.');});
bot.command('resume',ctx=>{paused=false;ctx.reply('▶️ Alertes réactivées.');});
bot.launch().then(()=>console.log('Telegram bot polling started')).catch(err=>console.error('Telegram launch error:',err.message));
connect();
console.log('TradeGuard V9 Futures Testnet started');
process.once('SIGINT',()=>bot.stop('SIGINT'));
process.once('SIGTERM',()=>bot.stop('SIGTERM'));
