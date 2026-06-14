'use strict';

// ─── DEPS ───────────────────────────────────────────────────────────────────
const express  = require('express');
const { WebSocket } = require('ws');
// Node 18+ has built-in fetch — no import needed
const { ethers } = require('ethers');
const crypto   = require('crypto');   // built-in, for HMAC-SHA256
const fs       = require('fs');
const path     = require('path');

// ─── POLYMARKET CLOB V2 SDK ─────────────────────────────────────────────────
// CLOB V1 was deprecated April 28, 2026. py-clob-client/clob-client (V1) are archived.
// V2 SDK handles all auth (L1 EIP-712 + L2 HMAC), order signing (new struct with
// timestamp/metadata/builder), and balance sync (/balance-allowance/update).
const { ClobClient, Chain, Side: V2Side, OrderType: V2OrderType, SignatureTypeV2, ApiError } = require('@polymarket/clob-client-v2');
const { createWalletClient, http } = require('viem');
const { privateKeyToAccount } = require('viem/accounts');
const { polygon } = require('viem/chains');

// ─── CONFIG ─────────────────────────────────────────────────────────────────
const PORT             = process.env.PORT || 3000;
const STATE_FILE       = path.join(__dirname, 'state.json');
const POLY_GAMMA       = 'https://gamma-api.polymarket.com';
const POLY_CLOB        = 'https://clob.polymarket.com';
const POLY_DATA        = 'https://data-api.polymarket.com';   // публичный Data API (история сделок кошельков)
const POLY_INTERVAL    = 'btc-updown-5m';
const POLY_WINDOW_SEC  = 300;

// ── КОПИТРЕЙДИНГ POLYMARKET (независимая от BTC фича) ─────────────────────────
const COPY_MAX_WALLETS   = 15;                // максимум кошельков на копитрейдинге
// Период опроса истории сделок кошелька (фолбэк-режим). Настраивается env COPY_POLL_MS.
// Пол — 1000мс: чаще раза в секунду публичный Data API не имеет смысла дёргать.
const COPY_POLL_MS       = Math.max(1000, parseInt(process.env.COPY_POLL_MS || '2500', 10) || 2500);
const COPY_POLL_RECON_MS = 20000;             // когда ТУРБО (ончейн-WS) активен — опрос только для сверки, реже
const COPY_FETCH_LIMIT   = 20;                // сколько последних сделок тянуть за опрос
const COPY_MARK_MS       = 20000;             // как часто маркуем открытые позиции по midpoint
const COPY_BACKOFF_429   = 60000;             // пауза по кошельку после rate-limit (429)
const COPY_BACKOFF_ERR   = 12000;             // пауза по кошельку после прочей ошибки сети
const COPY_SAVE_MS       = 8000;              // не чаще раза в 8с пишем состояние из быстрого цикла
const COPY_START_BALANCE = 1000;              // стартовый баланс копи-счёта (demo и real-paper)
// Мастер-предохранитель реального исполнения копитрейда. По умолчанию ВЫКЛ:
// реальный режим считается как «бумажный» (paper), пока явно не включить флаг.
const COPY_REAL_LIVE     = ['true','1','yes','on'].includes((process.env.COPY_REAL_LIVE||'false').toLowerCase().trim());
// ТУРБО-режим: ончейн-вотчер фиксированных событий OrderFilled на Polygon.
// Нужен WSS-RPC (Alchemy/Infura/QuickNode) в env POLYGON_WSS. Push, без задержки Data API.
const COPY_WSS_URL       = (process.env.POLYGON_WSS || '').trim();
// Адреса бирж Polymarket на Polygon (CTF Exchange + Neg-Risk CTF Exchange).
const COPY_EXCHANGES     = ['0x4bFb41d5B3570DeFd03C39a9A4D8dE6Bd8B8982E', '0xC5d563A36AE78145C45a50134d48A1215220f80a'];
let   COPY_WALLETS       = [];                 // массив кошельков (см. _copyMakeWallet)
let   _copyPollBusy      = false;
let   _copyDirty         = false;              // были ли изменения, требующие сохранения
let   _copyLastSave      = 0;
let   _turbo             = { provider: null, connected: false, listeners: [], reconnectMs: 3000, lastEventTs: 0, started: false };
const CHAINLINK_ADDR   = '0xc907E116054Ad103354f2D350FD2514433D57F6f'; // BTC/USD Polygon
const POLYGON_RPCS     = [
  'https://polygon-bor-rpc.publicnode.com',
  'https://polygon.llamarpc.com',
  'https://rpc.ankr.com/polygon',
  'https://1rpc.io/matic',
];
const CHAINLINK_ABI    = ['function latestAnswer() view returns (int256)'];

// ─── REAL TRADING CONFIG (CLOB V2) ────────────────────────────────────────────
// To enable: set REAL_TRADING=true and POLY_PRIVATE_KEY=0x... in Railway env vars
// V2 SDK auto-derives API credentials — env-set POLY_API_KEY/SECRET/PASSPHRASE
// are honored if present, otherwise SDK calls createOrDeriveApiKey internally.
const REAL_TRADING  = ['true','1','yes'].includes((process.env.REAL_TRADING || '').toLowerCase().trim());
const POLY_PK       = process.env.POLY_PRIVATE_KEY || '';
const POLY_FUNDER   = process.env.POLY_FUNDER_ADDRESS || '';
// Polymarket CTF Exchange contract on Polygon mainnet (settles all prediction markets)
const CTF_EXCHANGE  = '0xE111180000d2663C0091e4f400237545B87B996B';
const POLY_CHAIN_ID = 137;
// Signature type (V2 SDK uses the same numeric scheme as V1):
//   0 = EOA              — plain MetaMask/Phantom, no Polymarket proxy
//   1 = POLY_PROXY       — EOA owning a Polymarket Proxy wallet (Magic/email login)
//   2 = POLY_GNOSIS_SAFE — EOA owning a Polymarket Gnosis Safe (Phantom/MetaMask
//                          users who deposited via Polymarket UI → Safe deployed)
//   3 = POLY_1271        — smart contract wallets / vaults (EIP-1271)
const SIG_TYPE      = parseInt(process.env.SIGNATURE_TYPE || '0', 10);

// ─── TELEGRAM NOTIFICATIONS ───────────────────────────────────────────────────
// Set TELEGRAM_BOT_TOKEN (from @BotFather) and TELEGRAM_CHAT_ID (from
// https://api.telegram.org/bot<TOKEN>/getUpdates) to enable real-trade alerts.
// Notifications fire on: startup, real-order open, real-order close, auth fail.
const TG_TOKEN = (process.env.TELEGRAM_BOT_TOKEN || '').trim();
const TG_CHAT  = (process.env.TELEGRAM_CHAT_ID   || '').trim();
const TG_ON    = !!(TG_TOKEN && TG_CHAT);

/**
 * Send a Telegram message. Silent fail-safe — never throws, never blocks the
 * caller. Returns true on success, false on error or if Telegram is disabled.
 */
async function sendTg(text) {
  if (!TG_ON) return false;
  try {
    const r = await fetch(`https://api.telegram.org/bot${TG_TOKEN}/sendMessage`, {
      method:  'POST',
      headers: { 'Content-Type': 'application/json' },
      body:    JSON.stringify({
        chat_id:                  TG_CHAT,
        text:                     text,
        parse_mode:               'HTML',
        disable_web_page_preview: true,
      }),
      signal: AbortSignal.timeout(5000),
    });
    if (!r.ok) {
      const txt = await r.text().catch(() => '');
      console.warn(`[tg] HTTP ${r.status}: ${txt.slice(0, 200)}`);
      return false;
    }
    return true;
  } catch (e) {
    console.warn('[tg] send error:', e.message);
    return false;
  }
}

/** HTML-escape user-supplied values before embedding in Telegram messages. */
function _tgEsc(s) {
  return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

// ─── STATE ───────────────────────────────────────────────────────────────────
let ticks        = [];   // { time, price, qty, isBuyerMaker }
let cvd          = 0;
let cvdSeries    = [];   // { t, v }
let book         = { bids: new Map(), asks: new Map() };
let bookHistory  = [];   // snapshots for OFI
let bestBid      = null;
let bestAsk      = null;
let clobQuotes   = {};   // tokenId → {bid, ask} последних котировок CLOB (для калибровки спреда)
// Калибровочный лог: по каждому входу — условия входа + фактический исход окна.
// Нужен, чтобы на РЕАЛЬНЫХ данных посчитать, в каком диапазоне цены входа есть
// эдж после спреда (на симуляции шэров это считать нельзя).
let calibLog = [];
const CALIB_MAX = 4000;
let sessionStart = null;
let wsStatus     = 'disconnected';
let isSim        = false;

// Polymarket
let poly = {
  autoFetch: true,
  market: null,
  prices: { up: null, down: null, ts: null },
  status: 'off',
  lastErr: null,
  windowOpeningBTC: null,
  windowOpeningSource: null,
  // История окон для стрик/волатильность-фильтров (только новые стратегии используют).
  winHist: [],        // [{slug, winner:'UP'|'DOWN', move, range}] — самые свежие в конце
  winHi: null,        // max BTC в текущем окне (для range)
  winLo: null,        // min BTC в текущем окне
};
const WINHIST_MAX = 40;
// FIX: победители завершённых окон ПО КНИГЕ (slug → 'UP'/'DOWN') — для честной
// разметки calibLog. Заполняется в fetchPolyMarket при смене окна.
let winnerBySlug = {};
let polyClobOk = true;

// Chainlink
let chain = {
  enabled: true,
  available: false,
  currentPrice: null,
  lastUpdate: null,
  lastRpcIdx: 0,
  lastErr: null,
};

// Strategies (initialised after load)
let STRATEGIES = {};

// ─── SSE CLIENTS ─────────────────────────────────────────────────────────────
const sseClients = new Set();
function broadcast(data) {
  const msg = `data: ${JSON.stringify(data)}\n\n`;
  for (const res of sseClients) {
    try { res.write(msg); } catch (_) { sseClients.delete(res); }
  }
}

// ─── PERSISTENCE ─────────────────────────────────────────────────────────────
function saveState() {
  try {
    const out = {};
    for (const id in STRATEGIES) {
      const s = STRATEGIES[id];
      out[id] = {
        demoEnabled: s.demoEnabled,
        realEnabled: s.realEnabled,
        schedEnabled: s.schedEnabled, schedFrom: s.schedFrom, schedTo: s.schedTo,
        demo: {
          balance:     s.demo.balance,
          peakBalance: s.demo.peakBalance,
          open:        s.demo.open,
          log:         s.demo.log.slice(-500),
        },
        real: {
          balance:     s.real.balance,
          peakBalance: s.real.peakBalance,
          open:        s.real.open,
          log:         s.real.log.slice(-500),
        },
        params: s.params,
        customEnabled: s.customEnabled,
        customParams:  s.customParams,
        name: s.def.name, desc: s.def.desc, manual: !!s.def.manual,
        underdogHoldAutoBlocked: s.underdogHoldAutoBlocked ?? false,
      };
    }
    out.__global = {
      invertSignal: INVERT_SIGNAL, tpAbsPrice: TP_ABS_PRICE, minEntryPrice: MIN_ENTRY_PRICE,
      dailyLossCap: REAL_DAILY_LOSS_CAP, minBalance: REAL_MIN_BALANCE,
      demoDelaySec: DEMO_ENTRY_DELAY_MS / 1000, demoMaxChasePct: DEMO_MAX_CHASE * 100,
      demoRealSpread: DEMO_REAL_SPREAD,
      schedEnabled: SCHEDULE_ENABLED, schedFrom: SCHEDULE_FROM, schedTo: SCHEDULE_TO,
    };
    out.__calib = calibLog.slice(-CALIB_MAX);
    out.__copy = {
      wallets: COPY_WALLETS.map(w => ({
        id: w.id, address: w.address, label: w.label, copyUSD: w.copyUSD,
        demoEnabled: w.demoEnabled, realEnabled: w.realEnabled,
        startTs: w.startTs, createdAt: w.createdAt,
        feed: w.feed.slice(0, 30), seen: [...w.seen].slice(-2000),
        demo: { balance: w.demo.balance, positions: w.demo.positions, log: w.demo.log.slice(-500) },
        real: { balance: w.real.balance, positions: w.real.positions, log: w.real.log.slice(-500) },
      })),
    };
    fs.writeFileSync(STATE_FILE, JSON.stringify(out, null, 2));
  } catch (e) { console.error('[state] save error:', e.message); }
}

function loadState() {
  try {
    if (!fs.existsSync(STATE_FILE)) return;
    const stored = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
    for (const id in stored) {
      const s = STRATEGIES[id];
      if (!s) continue;
      const st = stored[id];
      if (st.demo !== undefined) {
        // New dual-account format
        s.demoEnabled      = st.demoEnabled      ?? false;
        s.realEnabled      = st.realEnabled      ?? false;
        s.schedEnabled     = st.schedEnabled     ?? false;
        s.schedFrom        = st.schedFrom        ?? 7;
        s.schedTo          = st.schedTo          ?? 24;
        s.demo.balance     = st.demo.balance     ?? 1000;
        s.demo.peakBalance = st.demo.peakBalance ?? 1000;
        s.demo.open        = st.demo.open        ?? null;
        s.demo.log         = st.demo.log         ?? [];
        s.real.balance     = st.real.balance     ?? 1000;
        s.real.peakBalance = st.real.peakBalance ?? 1000;
        s.real.open        = st.real.open        ?? null;
        s.real.log         = st.real.log         ?? [];
      } else {
        // Migrate from old format — move data into demo account
        s.demoEnabled      = st.enabled          ?? false;
        s.demo.balance     = st.balance          ?? 1000;
        s.demo.peakBalance = st.peakBalance      ?? 1000;
        s.demo.open        = st.open             ?? null;
        s.demo.log         = st.log              ?? [];
        console.log(`[state] migrated ${id} to dual-account format`);
      }
      s.params = { ...s.params, ...(st.params ?? {}) };
      s.customEnabled = st.customEnabled ?? false;
      s.customParams  = { ...s.def.defaults, ...(st.customParams ?? {}) };
      s.underdogHoldAutoBlocked = st.underdogHoldAutoBlocked ?? false;
      applyParams(s);
    }
    if (stored.__global && typeof stored.__global.invertSignal === 'boolean') {
      INVERT_SIGNAL = stored.__global.invertSignal;
    }
    if (stored.__global && isFinite(Number(stored.__global.tpAbsPrice))) {
      TP_ABS_PRICE = Math.max(0.50, Math.min(0.99, Number(stored.__global.tpAbsPrice)));
    }
    if (stored.__global && isFinite(Number(stored.__global.minEntryPrice))) {
      MIN_ENTRY_PRICE = Math.max(0.0, Math.min(0.50, Number(stored.__global.minEntryPrice)));
    }
    if (stored.__global && isFinite(Number(stored.__global.dailyLossCap))) {
      REAL_DAILY_LOSS_CAP = Math.max(0.1, Math.min(10000, Number(stored.__global.dailyLossCap)));
    }
    if (stored.__global && isFinite(Number(stored.__global.minBalance))) {
      REAL_MIN_BALANCE = Math.max(0, Math.min(1000000, Number(stored.__global.minBalance)));
    }
    if (stored.__global) {
      const g = stored.__global;
      if (isFinite(Number(g.demoDelaySec)))    DEMO_ENTRY_DELAY_MS = Math.max(0, Math.min(30000, Math.round(Number(g.demoDelaySec) * 1000)));
      if (isFinite(Number(g.demoMaxChasePct))) DEMO_MAX_CHASE      = Math.max(0.01, Math.min(2.0, Number(g.demoMaxChasePct) / 100));
      if (typeof g.schedEnabled === 'boolean')  SCHEDULE_ENABLED   = g.schedEnabled;
      if (typeof g.demoRealSpread === 'boolean') DEMO_REAL_SPREAD  = g.demoRealSpread;
      if (isFinite(Number(g.schedFrom)))        SCHEDULE_FROM      = Math.max(0, Math.min(24, parseInt(g.schedFrom, 10)));
      if (isFinite(Number(g.schedTo)))          SCHEDULE_TO        = Math.max(0, Math.min(24, parseInt(g.schedTo, 10)));
    }
    if (Array.isArray(stored.__calib)) calibLog = stored.__calib.slice(-CALIB_MAX);
    if (stored.__copy && Array.isArray(stored.__copy.wallets)) {
      COPY_WALLETS = stored.__copy.wallets.filter(w => w && w.address).map(w => ({
        id: w.id || _copyId(), address: String(w.address).toLowerCase(),
        label: w.label || (String(w.address).slice(0, 6) + '…' + String(w.address).slice(-4)),
        copyUSD: Math.max(1, Number(w.copyUSD) || 20),
        demoEnabled: w.demoEnabled ?? true, realEnabled: w.realEnabled ?? false,
        demo: { balance: w.demo?.balance ?? COPY_START_BALANCE, positions: w.demo?.positions || {}, log: w.demo?.log || [] },
        real: { balance: w.real?.balance ?? COPY_START_BALANCE, positions: w.real?.positions || {}, log: w.real?.log || [] },
        feed: Array.isArray(w.feed) ? w.feed : [], seen: new Set(w.seen || []),
        startTs: w.startTs || Date.now(), createdAt: w.createdAt || Date.now(),
        lastPollTs: 0, lastErr: null,
      })).slice(0, COPY_MAX_WALLETS);
    }
    console.log('[state] loaded');
  } catch (e) { console.error('[state] load error:', e.message); }
}

// ─── TICK HELPERS ────────────────────────────────────────────────────────────
function pushTick(price, qty, side) {
  const isBuyerMaker = side === 'SELL';
  ticks.push({ time: Date.now(), price, qty, isBuyerMaker });
  cvd += isBuyerMaker ? -qty : qty;
  cvdSeries.push({ t: Date.now(), v: cvd });
  if (ticks.length     > 5000) ticks.shift();
  if (cvdSeries.length > 3000) cvdSeries.shift();
  if (sessionStart === null) sessionStart = price;
}

// ─── L2 BOOK ─────────────────────────────────────────────────────────────────
function updateBookLevel(side, price, size) {
  const m = side === 'bid' ? book.bids : book.asks;
  if (size === 0) m.delete(price); else m.set(price, size);
}
function topBook(side, n) {
  const m = side === 'bid' ? book.bids : book.asks;
  return [...m.entries()].sort((a, b) => side === 'bid' ? b[0] - a[0] : a[0] - b[0]).slice(0, n);
}
function bookSnapshotDepth(levels = 10) {
  const tb = topBook('bid', levels), ta = topBook('ask', levels);
  return {
    bidDepth: tb.reduce((a, [, s]) => a + s, 0),
    askDepth: ta.reduce((a, [, s]) => a + s, 0),
    bestBid: tb[0]?.[0],
    bestAsk: ta[0]?.[0],
    t: Date.now(),
  };
}
function bookImbalance(levels = 10) {
  const snap = bookSnapshotDepth(levels);
  if (!snap.bidDepth && !snap.askDepth) return null;
  return (snap.bidDepth - snap.askDepth) / (snap.bidDepth + snap.askDepth);
}
function microPrice() {
  const tb = topBook('bid', 1), ta = topBook('ask', 1);
  if (!tb.length || !ta.length) return null;
  const [bp, bs] = tb[0], [ap, as_] = ta[0];
  return (bs + as_ === 0) ? null : (ap * bs + bp * as_) / (bs + as_);
}
function orderFlowImbalance(secAgo = 10) {
  if (bookHistory.length < 2) return null;
  const cutoff = Date.now() - secAgo * 1000;
  const past = bookHistory.find(s => s.t >= cutoff) || bookHistory[0];
  const cur  = bookHistory[bookHistory.length - 1];
  if (!past || !cur) return null;
  const dBid  = cur.bidDepth - past.bidDepth;
  const dAsk  = cur.askDepth - past.askDepth;
  const total = Math.abs(cur.bidDepth) + Math.abs(cur.askDepth);
  if (total === 0) return null;
  return (dBid - dAsk) / total;
}

// ─── INDICATORS ──────────────────────────────────────────────────────────────
const clip = x => Math.max(-1, Math.min(1, x));

function getMom(sec) {
  const c = Date.now() - sec * 1000;
  const r = ticks.filter(t => t.time >= c);
  if (r.length < 2) return null;
  return ((r[r.length - 1].price - r[0].price) / r[0].price) * 100;
}
function getRSI(n = 20) {
  if (ticks.length < n + 1) return null;
  const p = ticks.slice(-n - 1).map(t => t.price);
  let g = 0, l = 0;
  for (let i = 1; i < p.length; i++) { const d = p[i] - p[i - 1]; d > 0 ? g += d : l -= d; }
  return l === 0 ? 100 : 100 - 100 / (1 + g / l);
}
function getBuyPressure(sec = 10) {
  const c = Date.now() - sec * 1000;
  const r = ticks.filter(t => t.time >= c);
  if (!r.length) return null;
  let bv = 0, sv = 0;
  r.forEach(t => t.isBuyerMaker ? sv += t.qty : bv += t.qty);
  return (bv + sv) > 0 ? bv / (bv + sv) * 100 : 50;
}
function getBB() {
  if (ticks.length < 20) return null;
  const p = ticks.slice(-20).map(t => t.price);
  const m = p.reduce((a, b) => a + b) / 20;
  const std = Math.sqrt(p.reduce((a, b) => a + (b - m) ** 2, 0) / 20);
  if (std === 0) return 50;
  return Math.max(0, Math.min(100, ((p[19] - (m - 2 * std)) / (4 * std)) * 100));
}
function getVWAP(sec = 60) {
  const c = Date.now() - sec * 1000;
  const r = ticks.filter(t => t.time >= c);
  if (r.length < 5) return null;
  const sv = r.reduce((a, t) => a + t.price * t.qty, 0);
  const v  = r.reduce((a, t) => a + t.qty, 0);
  if (!v) return null;
  return ((ticks[ticks.length - 1].price - sv / v) / (sv / v)) * 100;
}
function getTickDir(sec = 10) {
  const c = Date.now() - sec * 1000;
  const r = ticks.filter(t => t.time >= c);
  if (r.length < 2) return null;
  let u = 0, d = 0;
  for (let i = 1; i < r.length; i++) r[i].price > r[i - 1].price ? u++ : r[i].price < r[i - 1].price ? d++ : 0;
  return (u + d) ? u / (u + d) * 100 : 50;
}
function getTPS(sec = 5) { return ticks.filter(t => t.time >= Date.now() - sec * 1000).length / sec; }
function getCVDSlope(sec = 30) {
  const c = Date.now() - sec * 1000;
  const r = cvdSeries.filter(p => p.t >= c);
  if (r.length < 5) return null;
  const n = r.length, t0 = r[0].t;
  let sx = 0, sy = 0, sxx = 0, sxy = 0;
  for (const p of r) { const x = (p.t - t0) / 1000; sx += x; sy += p.v; sxx += x * x; sxy += x * p.v; }
  const den = n * sxx - sx * sx;
  return den ? (n * sxy - sx * sy) / den : null;
}
function getWhaleBias(sec = 30) {
  const c = Date.now() - sec * 1000;
  const r = ticks.filter(t => t.time >= c && t.qty >= 0.5);
  if (!r.length) return null;
  let bv = 0, sv = 0;
  r.forEach(t => t.isBuyerMaker ? sv += t.qty : bv += t.qty);
  return (bv + sv === 0) ? null : (bv - sv) / (bv + sv);
}
function getEMACross() {
  if (ticks.length < 10) return null;
  const now = Date.now();
  const ema = sec => {
    const r = ticks.filter(t => t.time >= now - sec * 1000);
    if (r.length < 2) return null;
    const a = 2 / (r.length + 1);
    let e = r[0].price;
    for (let i = 1; i < r.length; i++) e = a * r[i].price + (1 - a) * e;
    return e;
  };
  const fast = ema(15), slow = ema(60);
  return (fast === null || slow === null || slow === 0) ? null : ((fast - slow) / slow) * 100;
}
function getRegSlope(sec = 30) {
  const c = Date.now() - sec * 1000;
  const r = ticks.filter(t => t.time >= c);
  if (r.length < 5) return null;
  const t0 = r[0].time, n = r.length;
  let sx = 0, sy = 0, sxx = 0, sxy = 0;
  for (const p of r) { const x = (p.time - t0) / 1000; sx += x; sy += p.price; sxx += x * x; sxy += x * p.price; }
  const den = n * sxx - sx * sx;
  if (!den) return null;
  return ((n * sxy - sx * sy) / den / (sy / n)) * 10000;
}
function getATR(sec = 60) {
  const c = Date.now() - sec * 1000;
  const r = ticks.filter(t => t.time >= c);
  if (r.length < 5) return null;
  const p = r.map(t => t.price);
  return ((Math.max(...p) - Math.min(...p)) / p[p.length - 1]) * 10000;
}
function getDistFromHL(sec = 60) {
  const c = Date.now() - sec * 1000;
  const r = ticks.filter(t => t.time >= c);
  if (r.length < 5) return null;
  const p = r.map(t => t.price);
  const H = Math.max(...p), L = Math.min(...p), curr = p[p.length - 1];
  return { fromHi: ((H - curr) / curr) * 10000, fromLo: ((curr - L) / curr) * 10000 };
}
function getJumpCount(sec = 30, thresholdBps = 5) {
  const c = Date.now() - sec * 1000;
  const r = ticks.filter(t => t.time >= c);
  if (r.length < 2) return null;
  let upJumps = 0, dnJumps = 0;
  for (let i = 1; i < r.length; i++) {
    const dt = (r[i].time - r[i - 1].time) / 1000;
    if (dt > 2) continue;
    const moveBps = (r[i].price - r[i - 1].price) / r[i - 1].price * 10000;
    if (moveBps > thresholdBps) upJumps++; else if (moveBps < -thresholdBps) dnJumps++;
  }
  if (upJumps + dnJumps === 0) return null;
  return (upJumps - dnJumps) / (upJumps + dnJumps);
}
function getTPSAcceleration() {
  const recent = getTPS(5), past30 = getTPS(30);
  if (recent === null || past30 === null || past30 < 0.5) return null;
  return (recent - past30) / past30;
}
// ─── PREDICTION ENGINES ──────────────────────────────────────────────────────
function predictScalp() {
  let sc = 0, w = 0;
  const add = (v, wt, fn) => { if (v !== null && !isNaN(v)) { sc += fn(v) * wt; w += wt; } };
  add(bookImbalance(10), 0.18, v => clip(v * 1.5));
  add(orderFlowImbalance(10), 0.10, v => clip(v * 3));
  const mp = microPrice();
  if (mp !== null && bestBid && bestAsk) {
    const mid = (bestBid + bestAsk) / 2;
    sc += clip(((mp - mid) / mid * 10000) / 0.5) * 0.12; w += 0.12;
  }
  add(getCVDSlope(30), 0.10, v => clip(v / 0.2));
  add(getBuyPressure(10), 0.08, v => clip((v - 50) / 25));
  add(getWhaleBias(30), 0.07, v => clip(v));
  add(getJumpCount(30, 5), 0.06, v => clip(v));
  add(getTickDir(10), 0.05, v => clip((v - 50) / 25));
  add(getMom(5), 0.08, v => clip(v / 0.04));
  add(getRegSlope(30), 0.07, v => clip(v / 0.3));
  add(getRSI(20), 0.05, v => v > 75 ? -(v - 75) / 25 : v < 25 ? (25 - v) / 25 : 0);
  if (!w) return { dir: 'WAIT', conf: 0, raw: 0 };
  const raw = sc / w, conf = Math.abs(raw) * 100;
  return { dir: conf < 28 ? 'WAIT' : raw > 0 ? 'UP' : 'DOWN', conf, raw };
}

function predictPoly() {
  let sc = 0, w = 0;
  const add = (v, wt, fn) => { if (v !== null && !isNaN(v)) { sc += fn(v) * wt; w += wt; } };
  add(getMom(30), 0.10, v => clip(v / 0.10));
  add(getMom(60), 0.13, v => clip(v / 0.15));
  add(getMom(300), 0.17, v => clip(v / 0.30));
  add(getEMACross(), 0.10, v => clip(v / 0.03));
  add(getRegSlope(60), 0.08, v => clip(v / 0.4));
  add(getVWAP(300), 0.05, v => clip(v / 0.15));
  add(getCVDSlope(60), 0.06, v => clip(v / 0.15));
  add(getBuyPressure(60), 0.04, v => clip((v - 50) / 20));
  add(orderFlowImbalance(30), 0.05, v => clip(v * 3));
  add(getJumpCount(60, 5), 0.05, v => clip(v));
  add(getTPSAcceleration(), 0.03, v => clip(v * 1.5));
  const hl = getDistFromHL(60), r50 = getRSI(50);
  if (hl && r50 !== null) {
    if (hl.fromHi < 2 && r50 > 70) { sc -= 0.15; w += 0.05; }
    if (hl.fromLo < 2 && r50 < 30) { sc += 0.15; w += 0.05; }
  }
  add(r50, 0.04, v => v > 75 ? -(v - 75) / 25 : v < 25 ? (25 - v) / 25 : (v - 50) / 100);
  add(getBB(), 0.04, v => v > 85 ? -(v - 85) / 15 : v < 15 ? (15 - v) / 15 : 0);
  if (!w) return { dir: 'WAIT', conf: 0, raw: 0, prob: 0.5 };
  const raw = sc / w, conf = Math.abs(raw) * 100;
  const atr = getATR(60) || 5;
  const k = 2.5 / Math.max(1, atr / 5);
  const prob = 1 / (1 + Math.exp(-raw * k));
  return { dir: conf < 22 ? 'WAIT' : raw > 0 ? 'UP' : 'DOWN', conf, raw, prob };
}

function computeMainSignal() {
  const sigS = predictScalp();
  const sigP = predictPoly();
  if (sigS.dir === 'WAIT' && sigP.dir === 'WAIT') return { dir: 'WAIT', conf: 0, raw: 0 };
  if (sigS.dir !== 'WAIT' && sigP.dir !== 'WAIT' && sigS.dir === sigP.dir) {
    const conf = Math.max(sigS.conf, sigP.conf) * 1.15;
    return { dir: sigS.dir, conf, raw: (sigS.raw + sigP.raw) / 2 };
  }
  if (sigP.dir !== 'WAIT') return sigP;
  return sigS;
}

// ─── POLYMARKET ──────────────────────────────────────────────────────────────
function currentPolyWindow() {
  const now   = Math.floor(Date.now() / 1000);
  const start = now - (now % POLY_WINDOW_SEC);
  return { slug: `${POLY_INTERVAL}-${start}`, startTs: start * 1000, endTs: (start + POLY_WINDOW_SEC) * 1000 };
}

function parseStringifiedJson(v) {
  if (Array.isArray(v)) return v;
  if (typeof v === 'string') { try { return JSON.parse(v); } catch (_) { return null; } }
  return null;
}

async function fetchPolyEvent(slug) {
  const tries = [
    `${POLY_GAMMA}/events/slug/${encodeURIComponent(slug)}`,
    `${POLY_GAMMA}/events?slug=${encodeURIComponent(slug)}`,
  ];
  let lastErr;
  for (const url of tries) {
    try {
      const res = await fetch(url, { signal: AbortSignal.timeout(8000) });
      if (!res.ok) { lastErr = 'HTTP ' + res.status; continue; }
      const data = await res.json();
      const ev   = Array.isArray(data) ? data[0] : data;
      if (ev && (ev.id || ev.slug)) return ev;
    } catch (e) { lastErr = e.message || String(e); }
  }
  throw new Error(lastErr || 'event not found');
}

function parseEventMarket(ev) {
  const markets  = Array.isArray(ev.markets) ? ev.markets : [];
  if (!markets.length) throw new Error('empty markets[]');
  const m        = markets[0];
  const tokenIds = parseStringifiedJson(m.clobTokenIds);
  if (!Array.isArray(tokenIds) || tokenIds.length < 2) throw new Error('no clobTokenIds');
  const outcomes = parseStringifiedJson(m.outcomes) || ['Up', 'Down'];
  let upIdx = 0, dnIdx = 1;
  const o0 = String(outcomes[0] || '').toLowerCase();
  if (o0.includes('down') || o0 === 'no') { upIdx = 1; dnIdx = 0; }
  const prices = parseStringifiedJson(m.outcomePrices);
  let upPrice = null, dnPrice = null;
  if (Array.isArray(prices) && prices.length >= 2) {
    upPrice = parseFloat(prices[upIdx]);
    dnPrice = parseFloat(prices[dnIdx]);
  }
  return {
    eventSlug: ev.slug, eventId: ev.id, question: ev.title || m.question,
    endDate: m.endDate || ev.endDate,
    tokenIdUp: String(tokenIds[upIdx]), tokenIdDown: String(tokenIds[dnIdx]),
    outcomePriceUp: upPrice, outcomePriceDown: dnPrice,
    closed: !!m.closed, active: !!m.active,
  };
}

async function fetchClobMidpoint(tokenId) {
  // Polymarket's `/midpoint` endpoint returns (bid + ask) / 2. When the book
  // has limit orders sitting at 0.01 and 0.99 (which Polymarket sometimes
  // seeds itself for thin markets), that midpoint becomes 0.50 — even though
  // the *real* market (last trades, mid of the tight inner book) is at e.g.
  // 0.27. The bot then trades on stale 50/50 forever.
  //
  // Fix: pull the actual orderbook and compute midpoint from the BEST bid
  // and BEST ask (the inner quotes — what you'd actually trade against).
  // Fall back to /midpoint if the book is empty (shouldn't happen on active
  // markets but keeps us safe).
  try {
    const book = await fetchClobBook(tokenId);
    const bestBid = (Array.isArray(book.bids) && book.bids.length)
      ? Math.max(...book.bids.map(o => parseFloat(o.price)).filter(v => !isNaN(v)))
      : null;
    const bestAsk = (Array.isArray(book.asks) && book.asks.length)
      ? Math.min(...book.asks.map(o => parseFloat(o.price)).filter(v => !isNaN(v)))
      : null;

    if (bestBid !== null && bestAsk !== null) {
      // Sanity check: spread should not be insanely wide. If bid≈0 and ask≈1,
      // the inner quotes are degenerate — treat the book as effectively empty
      // and fall through to the midpoint endpoint.
      const spread = bestAsk - bestBid;
      if (spread < 0.50) {
        // ML-ЛОГ: размеры лучших уровней — фича ликвидности для обучающего лога
        let bidSz = null, askSz = null;
        try {
          const be = book.bids.find(x => parseFloat(x.price) === bestBid);
          const ae = book.asks.find(x => parseFloat(x.price) === bestAsk);
          bidSz = be ? parseFloat(be.size) : null;
          askSz = ae ? parseFloat(ae.size) : null;
        } catch (_) {}
        clobQuotes[tokenId] = { bid: bestBid, ask: bestAsk, bidSz, askSz };
        return (bestBid + bestAsk) / 2;
      }
    } else if (bestBid !== null) {
      return bestBid;
    } else if (bestAsk !== null) {
      return bestAsk;
    }
  } catch (_) { /* fall through to /midpoint */ }

  // Fallback: original /midpoint endpoint
  const res = await fetch(`${POLY_CLOB}/midpoint?token_id=${encodeURIComponent(tokenId)}`, { signal: AbortSignal.timeout(5000) });
  if (!res.ok) throw new Error('clob HTTP ' + res.status);
  const d = await res.json();
  const m = parseFloat(d.mid);
  if (isNaN(m)) throw new Error('bad mid');
  return m;
}

async function fetchClobBook(tokenId) {
  const res = await fetch(`${POLY_CLOB}/book?token_id=${encodeURIComponent(tokenId)}`, { signal: AbortSignal.timeout(5000) });
  if (!res.ok) throw new Error('book HTTP ' + res.status);
  return res.json();
}

async function determineWindowOpening() {
  if (chain.currentPrice) {
    poly.windowOpeningBTC    = chain.currentPrice;
    poly.windowOpeningSource = 'chainlink';
  } else if (ticks.length) {
    poly.windowOpeningBTC    = ticks[ticks.length - 1].price;
    poly.windowOpeningSource = 'coinbase-ws';
  }
}

async function fetchPolyMarket() {
  const win        = currentPolyWindow();
  const slugChanged = !poly.market || poly.market.eventSlug !== win.slug;
  let gammaUp = null, gammaDn = null;

  if (slugChanged) {
    poly.status = 'searching';
    // FIX: polyClobOk раньше «защёлкивался» после первого сбоя CLOB навсегда —
    // цены внутри окна переставали обновляться до рестарта. Теперь каждое новое
    // окно даёт CLOB новый шанс.
    polyClobOk = true;
    // ── Зафиксировать ЗАВЕРШЁННОЕ окно в историю (до перезаписи opening/prices) ──
    // Победитель — по последней цене книги (≥98¢, как настоящий резолв). Если окно
    // не дорезолвилось в книге — пропускаем запись (не засоряем историю догадкой).
    try {
      if (poly.market && poly.prices && poly.prices.up != null && poly.prices.down != null) {
        const u = poly.prices.up, d = poly.prices.down;
        const hi = Math.max(u, d), lo = Math.min(u, d);
        if (hi >= RESOLVE_CONFIRM && lo <= (1 - RESOLVE_CONFIRM)) {
          const curBTC = chain.currentPrice || (ticks.length ? ticks[ticks.length - 1].price : null);
          const move = (curBTC != null && poly.windowOpeningBTC != null) ? (curBTC - poly.windowOpeningBTC) : 0;
          const range = (poly.winHi != null && poly.winLo != null) ? (poly.winHi - poly.winLo) : Math.abs(move);
          poly.winHist.push({ slug: poly.market.eventSlug, winner: u > d ? 'UP' : 'DOWN',
                              move: +move.toFixed(2), range: +range.toFixed(2) });
          if (poly.winHist.length > WINHIST_MAX) poly.winHist.shift();
          // FIX: победитель окна по КНИГЕ — для resolveCalib (раньше calib
          // размечался по нашему BTC-фиду, который на тонких окнах ~4% времени
          // расходится с резолвом Polymarket → грязные метки калибровки).
          winnerBySlug[poly.market.eventSlug] = u > d ? 'UP' : 'DOWN';
          const wkeys = Object.keys(winnerBySlug);
          if (wkeys.length > 200) delete winnerBySlug[wkeys[0]];
        }
      }
    } catch (_) {}
    poly.winHi = null; poly.winLo = null;   // сброс экстремумов под новое окно
    try {
      const ev     = await fetchPolyEvent(win.slug);
      const parsed = parseEventMarket(ev);
      const endTs  = parsed.endDate ? new Date(parsed.endDate).getTime() : win.endTs;
      poly.market  = { ...parsed, endDate: new Date(endTs).toISOString(), windowEnd: endTs, windowStart: win.startTs };
      gammaUp      = parsed.outcomePriceUp;
      gammaDn      = parsed.outcomePriceDown;
      poly.status  = 'live';
      poly.lastErr = null;
      await determineWindowOpening();
      console.log(`[poly] new window: ${win.slug}`);
    } catch (e) {
      poly.status  = 'fail';
      poly.lastErr = e.message;
      console.error('[poly] event fetch error:', e.message);
      return;
    }
  }

  let up = null, dn = null;
  if (polyClobOk && poly.market) {
    try {
      const [u, d] = await Promise.all([
        fetchClobMidpoint(poly.market.tokenIdUp),
        fetchClobMidpoint(poly.market.tokenIdDown),
      ]);
      up = u; dn = d;
    } catch (e) {
      polyClobOk = false;
      up = gammaUp; dn = gammaDn;
    }
  } else {
    up = gammaUp; dn = gammaDn;
  }

  if (up !== null && dn !== null) {
    const qu = clobQuotes[poly.market?.tokenIdUp] || {};
    const qd = clobQuotes[poly.market?.tokenIdDown] || {};
    poly.prices = { up, down: dn, upBid: qu.bid ?? null, upAsk: qu.ask ?? null, dnBid: qd.bid ?? null, dnAsk: qd.ask ?? null, ts: Date.now() };
  }
}

// ─── CHAINLINK ───────────────────────────────────────────────────────────────
// Cache one provider per RPC so we don't re-detect network on every call.
const _rpcProviders = new Map();
function getRpcProvider(url) {
  if (!_rpcProviders.has(url)) {
    // staticNetwork skips the eth_chainId probe that causes "failed to detect network" spam
    _rpcProviders.set(url, new ethers.JsonRpcProvider(url, 137, { staticNetwork: ethers.Network.from(137) }));
  }
  return _rpcProviders.get(url);
}

async function refreshChainlinkPrice() {
  const rpc      = POLYGON_RPCS[chain.lastRpcIdx % POLYGON_RPCS.length];
  chain.lastRpcIdx++;
  try {
    const provider  = getRpcProvider(rpc);
    const contract  = new ethers.Contract(CHAINLINK_ADDR, CHAINLINK_ABI, provider);
    // Race against a 6-second timeout
    const answer    = await Promise.race([
      contract.latestAnswer(),
      new Promise((_, rej) => setTimeout(() => rej(new Error('timeout')), 6000)),
    ]);
    chain.currentPrice = Number(answer) / 1e8;
    chain.available    = true;
    chain.lastUpdate   = Date.now();
    chain.lastErr      = null;
  } catch (e) {
    chain.lastErr = e.message || String(e);
    // Only log once per RPC, not every 4 seconds
    if (chain.lastRpcIdx % POLYGON_RPCS.length === 1) {
      console.warn('[chainlink] error (will try next RPC):', (e.message || String(e)).slice(0, 120));
    }
    // Evict broken provider so next call gets a fresh one
    _rpcProviders.delete(rpc);
  }
}

// ─── REAL TRADING MODULE (POLYMARKET CLOB) ───────────────────────────────────
// Only active when REAL_TRADING=true and POLY_PRIVATE_KEY is set.
// Only the Momentum strategy places real orders; all others stay in simulation.

let polyWallet         = null;   // ethers.Wallet (kept for .address access in shared code paths)
let polyClob           = null;   // V2 ClobClient instance, fully authenticated (L1+L2)
let polyApiCreds       = null;   // { key, secret, passphrase } — exposed in /api/real/diagnose
let realBalance        = null;   // latest USDC balance fetched from CLOB
let _workingPolyAddress = null;  // kept for /api/real/diagnose UI (now always == polyWallet.address with V2)

// ═══════════════════════════════════════════════════════════════════════════
// POLYMARKET CLOB V2 INTEGRATION
// ═══════════════════════════════════════════════════════════════════════════
// CLOB V2 went live April 28, 2026; V1 SDKs were archived May 11, 2026.
// The /balance-allowance, /order, /auth/* endpoints exist on V2 too but the
// underlying validation (order struct, EIP-712 signing for orders, balance
// sync) is different. The official V2 SDK handles all of this.
//
// What we delegate to the SDK:
//   - L1 auth (EIP-712 signTypedData on ClobAuthDomain)
//   - L2 auth (HMAC-SHA256, base64url, timestamp+method+path+body)
//   - API key derivation (createOrDeriveApiKey)
//   - Order struct construction (new V2 fields: timestamp, metadata, builder)
//   - Order signing (EIP-712 with V2 domain version)
//   - /balance-allowance and /balance-allowance/update (sync on-chain balance)
//   - /order POST (place) and DELETE (cancel)
//
// What we still own:
//   - Wallet/account setup from POLY_PRIVATE_KEY
//   - Polling balance every 30s
//   - Translating between bot strategy events and CLOB orders
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Map our string side ("BUY"/"SELL") to V2 SDK Side enum.
 */
function _mapSide(side) {
  return side === 'BUY' ? V2Side.BUY : V2Side.SELL;
}

/**
 * Map our string orderType ("GTC"/"FOK"/"FAK"/"GTD") to V2 SDK OrderType enum.
 */
function _mapOrderType(t) {
  return V2OrderType[t] || V2OrderType.GTC;
}

/**
 * Resolve the SignatureTypeV2 to use. Honors SIG_TYPE env var; if 0 and
 * POLY_FUNDER is set, upgrades to POLY_GNOSIS_SAFE (most common case for
 * Phantom/MetaMask users who connected via Polymarket UI).
 */
function _resolveSigType() {
  if ([0, 1, 2, 3].includes(SIG_TYPE)) {
    // Auto-upgrade plain EOA to Gnosis Safe when funder is set (proxy detected)
    if (SIG_TYPE === 0 && POLY_FUNDER) return SignatureTypeV2.POLY_GNOSIS_SAFE;
    return SIG_TYPE;
  }
  return POLY_FUNDER ? SignatureTypeV2.POLY_GNOSIS_SAFE : SignatureTypeV2.EOA;
}

/**
 * Build the viem walletClient that V2 SDK uses for L1 signing.
 * Note: V2 SDK uses viem internally; we keep `polyWallet` (ethers) for the
 * address property and any code paths that haven't been migrated.
 */
function _buildViemWallet(pkHex) {
  const account = privateKeyToAccount(pkHex);
  return createWalletClient({ account, chain: polygon, transport: http() });
}

/**
 * Create a fully-configured V2 ClobClient (L1 only, no creds yet).
 * Used to bootstrap creds via createOrDeriveApiKey.
 */
function _buildBootClient(viemWallet, sigType, funderAddress) {
  return new ClobClient({
    host:          POLY_CLOB,
    chain:         Chain.POLYGON,
    signer:        viemWallet,
    signatureType: sigType,
    funderAddress: funderAddress || undefined,
  });
}

/**
 * Place an order on the Polymarket CLOB via V2 SDK.
 * Signature: { tokenId, side, size, price, orderType? }
 * - tokenId:   string (Polymarket conditional token ID)
 * - side:      'BUY' | 'SELL'
 * - size:      for BUY → USDC to spend; for SELL → shares to sell
 *              (V2 SDK's `size` field is always shares; we convert internally)
 * - price:     number (0.01..0.99)
 * - orderType: 'GTC' (default) | 'FOK' | 'FAK' | 'GTD'
 */
// Polymarket order minimums (verified empirically + per docs):
//   - Marketable BUY orders:   $1 USDC floor (caller's spend)
//   - Resting limit orders:    5 shares minimum (BUY & SELL)
// Since SELL orders are ALWAYS resting from our perspective (we own shares
// already and want to exit them), every SELL must be ≥ 5 shares.
// To guarantee we can SELL what we BUY, we enforce BUY ≥ 5 shares too.
const POLYMARKET_MIN_SHARES = 5;

async function placeClobOrder({ tokenId, side, size, price, orderType = 'GTC' }) {
  if (!polyClob)          throw new Error('CLOB client not initialised — wallet/creds missing');
  if (!tokenId)           throw new Error('tokenId is required');
  if (!price || price < 0.01 || price > 0.99) throw new Error(`invalid price: ${price}`);

  // ── Convert size to shares ───────────────────────────────────────────────
  // V2 SDK's `size` field is base units (shares). Our convention:
  //   BUY  → caller passes USDC, we convert: shares = USDC / price
  //   SELL → caller passes shares directly
  // Then enforce 5-share Polymarket minimum either way.
  let sizeShares = side === 'BUY' ? (size / price) : size;

  // Round UP to 2-decimal precision so we never undershoot the minimum
  sizeShares = Math.ceil(sizeShares * 100) / 100;

  // Polymarket floor: 5 shares per order
  if (sizeShares < POLYMARKET_MIN_SHARES) sizeShares = POLYMARKET_MIN_SHARES;

  const dollarValue = sizeShares * price;
  const userOrder = {
    tokenID: tokenId,
    price:   price,
    side:    _mapSide(side),
    size:    sizeShares,
  };
  console.log(`[real] order request: ${side} ${sizeShares} shares @ $${price.toFixed(4)} = $${dollarValue.toFixed(4)} (tokenId=${tokenId.slice(0, 12)}...)`);

  // ── Sync CLOB balance cache before SELL ──────────────────────────────────
  // After a BUY fills, Polymarket's CLOB cache still shows 0 conditional tokens
  // until updateBalanceAllowance is called. Without this sync, SELL returns:
  //   CLOB 400: not enough balance / allowance: balance: 0
  // We also re-sync COLLATERAL so the cache is fully up to date.
  if (side === 'SELL') {
    try {
      await polyClob.updateBalanceAllowance({ asset_type: 'CONDITIONAL', token_id: tokenId });
      console.log(`[real] conditional balance synced for tokenId=${tokenId.slice(0, 12)}...`);
    } catch (syncErr) {
      // Non-fatal: log and attempt the order anyway
      console.warn('[real] updateBalanceAllowance (CONDITIONAL) failed — attempting SELL anyway:', syncErr.message);
    }
  }

  try {
    const resp = await polyClob.createAndPostOrder(userOrder, {}, _mapOrderType(orderType));
    if (resp && (resp.error || resp.errorMsg)) {
      throw new Error(resp.errorMsg || resp.error);
    }
    return {
      orderID:            resp.orderID,
      status:             resp.status,
      success:            resp.success,
      actualShares:       sizeShares,   // ← what we actually sent; SELL must use this
      actualDollarValue:  dollarValue,  // ← real cost (BUY) / proceeds (SELL)
      transactionsHashes: resp.transactionsHashes || [],
      raw:                resp,
    };
  } catch (e) {
    if (e instanceof ApiError) {
      throw new Error(`CLOB ${e.status}: ${e.message}`);
    }
    throw e;
  }
}

/** Cancel an open order by ID. Returns the CLOB response (or null). */
async function cancelClobOrder(orderId) {
  if (!polyClob || !orderId) return null;
  try {
    const resp = await polyClob.cancelOrder({ orderID: orderId });
    console.log(`[real] cancel orderId=${orderId} →`, JSON.stringify(resp).slice(0, 200));
    return resp;
  } catch (e) {
    console.error('[real] cancel error:', e.message);
    return null;
  }
}

/** Get the status of a specific order. */
async function getClobOrderStatus(orderId) {
  if (!polyClob || !orderId) return null;
  try {
    return await polyClob.getOrder(orderId);
  } catch (e) {
    return null;
  }
}

/**
 * Fetch real USDC balance from the CLOB API via V2 SDK.
 * Returns balance in dollars (number) or null on error.
 *
 * V2 introduced /balance-allowance/update — if /balance-allowance returns 0
 * but wallet actually has funds on-chain, the CLOB cache is stale; calling
 * updateBalanceAllowance forces re-sync. This is critical right after a
 * deposit / approve.
 */
let _balanceUpdateAttempted = false;
async function fetchRealBalance() {
  if (!polyClob) return null;
  try {
    const res = await polyClob.getBalanceAllowance({ asset_type: 'COLLATERAL' });
    // res = { balance: "13021947", allowance: "...", asset_address: "0x..." }
    const balanceRaw = parseFloat(res?.balance || '0');
    const balance    = balanceRaw / 1e6;  // USDC has 6 decimals
    console.log(`[real] balance fetched: $${balance.toFixed(4)} (raw=${res?.balance}, allowance=${res?.allowance})`);

    // If balance == 0 but we expect funds, try updateBalanceAllowance once.
    // This is the V2-specific "sync cache" call.
    if (balance === 0 && !_balanceUpdateAttempted) {
      _balanceUpdateAttempted = true;
      console.log('[real] balance==0, calling updateBalanceAllowance to sync cache...');
      try {
        await polyClob.updateBalanceAllowance({ asset_type: 'COLLATERAL' });
        const res2  = await polyClob.getBalanceAllowance({ asset_type: 'COLLATERAL' });
        const bal2  = parseFloat(res2?.balance || '0') / 1e6;
        console.log(`[real] after updateBalanceAllowance: $${bal2.toFixed(4)}`);
        return isNaN(bal2) ? null : bal2;
      } catch (e) {
        console.warn('[real] updateBalanceAllowance failed:', e.message);
      }
    }

    return isNaN(balance) ? null : balance;
  } catch (e) {
    if (e instanceof ApiError) {
      console.warn(`[real] balance-allowance HTTP ${e.status}: ${e.message}`);
    } else {
      console.warn('[real] fetchRealBalance error:', e.message);
    }
    return null;
  }
}

/**
 * Boot: initialise wallet, derive API creds via V2 SDK, sync real USDC balance.
 * Must be called AFTER initStrategies() and loadState().
 */
async function initPolyWallet() {
  console.log(`[real] initPolyWallet called. REAL_TRADING=${REAL_TRADING}, POLY_PK_set=${!!POLY_PK}, POLY_FUNDER=${POLY_FUNDER || '(none)'}, SIG_TYPE=${SIG_TYPE}`);
  if (!REAL_TRADING) {
    console.log('[real] REAL_TRADING disabled — real account runs without on-chain orders');
    return;
  }
  if (!POLY_PK) {
    console.warn('[real] REAL_TRADING=true but POLY_PRIVATE_KEY is not set — real account in sim');
    return;
  }
  try {
    const pkNorm = POLY_PK.startsWith('0x') ? POLY_PK : '0x' + POLY_PK;

    // Keep ethers Wallet for .address access in shared code paths (chainlink, etc.)
    polyWallet = new ethers.Wallet(pkNorm);
    _workingPolyAddress = polyWallet.address;
    console.log(`[real] wallet address : ${polyWallet.address}`);
    if (POLY_FUNDER) console.log(`[real] funder address : ${POLY_FUNDER}`);

    // viem walletClient — required by V2 SDK
    const viemWallet = _buildViemWallet(pkNorm);
    const sigType    = _resolveSigType();
    const funderAddr = POLY_FUNDER || polyWallet.address;
    console.log(`[real] resolved sigType: ${sigType} (${SignatureTypeV2[sigType]}), funder: ${funderAddr}`);

    // ─── Step 1: bootstrap client (L1 only, no creds) ────────────────────────
    const bootClient = _buildBootClient(viemWallet, sigType, funderAddr);

    // ─── Step 2: get creds (env-provided OR derive via L1) ───────────────────
    let creds;
    if (process.env.POLY_API_KEY && process.env.POLY_API_SECRET && process.env.POLY_PASSPHRASE) {
      creds = {
        key:        process.env.POLY_API_KEY,
        secret:     process.env.POLY_API_SECRET,
        passphrase: process.env.POLY_PASSPHRASE,
      };
      console.log(`[real] using env-set API key: ${creds.key.slice(0, 8)}...`);
    } else {
      console.log('[real] no env creds — deriving via V2 SDK createOrDeriveApiKey...');
      creds = await bootClient.createOrDeriveApiKey();
      console.log(`[real] derived API key: ${creds.key.slice(0, 8)}...`);
    }
    polyApiCreds = creds;

    // ─── Step 3: build fully-authenticated client ────────────────────────────
    polyClob = new ClobClient({
      host:          POLY_CLOB,
      chain:         Chain.POLYGON,
      signer:        viemWallet,
      creds,
      signatureType: sigType,
      funderAddress: funderAddr,
      throwOnError:  true,  // surface ApiError instead of returning {error,status}
    });

    // ─── Step 4: smoke test L2 auth ──────────────────────────────────────────
    realBalance = await fetchRealBalance();
    if (realBalance !== null) {
      console.log(`[real] ✅ AUTH WORKING. USDC balance: $${realBalance.toFixed(2)}`);
      const mom = STRATEGIES.momentum;
      if (mom && realBalance > 0) {
        mom.real.balance     = realBalance;
        mom.real.peakBalance = Math.max(mom.real.peakBalance || 0, realBalance);
        saveState();
      }
      sendTg(
        `✅ <b>Бот запущен</b>\n` +
        `Кошелёк: <code>${_tgEsc(polyWallet.address)}</code>\n` +
        `Баланс USDC: <b>$${realBalance.toFixed(2)}</b>\n` +
        `Реальная торговля: <b>включена</b>`
      );
    } else {
      console.warn('[real] ⚠️  L2 auth or balance fetch failed — see prior logs');
      console.warn('[real] If this persists: check that POLY_PRIVATE_KEY matches the wallet you used to log into Polymarket UI');
      console.warn('[real] and that SIGNATURE_TYPE matches your account type (0=EOA, 1=Magic/email, 2=Phantom+Safe, 3=smart wallet)');
      sendTg(`⚠️ <b>Бот запущен, но auth/balance не работает</b>\nПроверь логи на Railway`);
    }
  } catch (e) {
    console.error('[real] init failed:', e.message);
    if (e.stack) console.error(e.stack.split('\n').slice(0, 5).join('\n'));
    sendTg(`❌ <b>Бот не смог запуститься</b>\n<code>${_tgEsc(e.message)}</code>`);
    polyWallet   = null;
    polyClob     = null;
    polyApiCreds = null;
    throw e;
  }
}

/**
 * Wrapper: попытка инициализации с автоматическим retry при сбое.
 * Каждые 90 секунд повторяет, пока кошелёк не будет готов.
 */
async function initPolyWalletWithRetry(attempt = 1) {
  try {
    await initPolyWallet();
    if (polyWallet && polyApiCreds) {
      console.log(`[real] ✓ wallet ready on attempt ${attempt}`);
    }
  } catch (e) {
    const nextDelay = Math.min(90_000, attempt * 15_000);
    console.warn(`[real] init attempt ${attempt} failed — retry in ${nextDelay / 1000}s: ${e.message}`);
    setTimeout(() => initPolyWalletWithRetry(attempt + 1), nextDelay);
  }
}

// ─── CLOB HEARTBEAT ──────────────────────────────────────────────────────────
// Polymarket auto-cancels all open orders if no heartbeat is received for ~30s.
// We send one every 15 seconds when real trading is active and a position is open.
setInterval(async () => {
  if (!REAL_TRADING || !polyClob) return;
  const hasOpenPosition = Object.values(STRATEGIES).some(s => s.real.open?.isReal);
  if (!hasOpenPosition) return;
  try {
    const resp = await polyClob.postHeartbeat();
    if (resp && resp.error_msg) console.warn('[real] heartbeat error:', resp.error_msg);
  } catch (e) { console.warn('[real] heartbeat error:', e.message); }
}, 15_000);
setInterval(async () => {
  if (!REAL_TRADING || !polyWallet || !polyApiCreds) return;
  const b = await fetchRealBalance();
  if (b !== null) {
    realBalance = b;
    // Sync ALL strategy real accounts when no position open
    for (const id in STRATEGIES) {
      const s = STRATEGIES[id];
      if (!s.real.open && !s.pendingReal) {
        s.real.balance = b;
      }
    }
    saveState();
  }
}, 30_000);

// ─── STRATEGIES ──────────────────────────────────────────────────────────────
function sizingByKelly(balance, prob, price, kellyFrac, maxFrac) {
  if (prob <= price) return 0;
  const b      = (1 - price) / price;
  const kelly  = Math.max(0, (prob * b - (1 - prob)) / b);
  const fraction = Math.min(kelly * kellyFrac, maxFrac);
  return balance * fraction;
}

const STRAT_MOMENTUM = {
  id: 'momentum',
  name: 'Momentum / Trend',
  desc: 'Высокая уверенность модели + edge ≥ 3pp',
  defaults: { minConf: 35, minEdge: 0.03, minTimeMs: 60000, tpPct: 0.50, slPct: 0.30, flipConf: 50, advMovePct: 0.25, kellyFrac: 0.25, maxFrac: 0.10 },
  shouldEnter(ctx, p) {
    if (ctx.sigP.dir === 'WAIT') return null;
    if (ctx.sigP.conf < p.minConf) return null;
    if (ctx.msToEnd < p.minTimeMs) return null;
    if (ctx.polyUp === null) return null;

    // Инверсия: торгуем ПРОТИВ модели — зеркалим направление и вероятность,
    // дальше вся логика (цена/edge/сайзинг) работает для перевёрнутой стороны.
    let dir  = ctx.sigP.dir;
    let prob = ctx.sigP.prob;
    if (INVERT_SIGNAL) {
      dir  = dir === 'UP' ? 'DOWN' : 'UP';
      prob = 1 - prob;
    }

    // Normalize prices so UP + DOWN = 1.0.
    // Raw CLOB midpoints can sum to >1 (e.g. 82¢ + 19¢ = 101¢) due to
    // bid/ask spread — this inflates edge by the spread amount. Normalizing
    // removes that artifact and gives us the true implied probability.
    const rawSum  = ctx.polyUp + ctx.polyDn;
    const normUp  = ctx.polyUp  / rawSum;
    const normDn  = ctx.polyDn  / rawSum;

    const polyPrice = dir === 'UP' ? normUp : normDn;
    const ourProb   = dir === 'UP' ? prob : (1 - prob);
    // Порог минимальной цены входа: дешёвую сторону вживую не залить — пропускаем.
    if (polyPrice < MIN_ENTRY_PRICE) return null;
    const edge      = ourProb - polyPrice;
    if (edge < p.minEdge) return null;
    return { side: dir, polyPrice, ourProb, edge, info: `conf=${ctx.sigP.conf.toFixed(0)}% edge=+${(edge * 100).toFixed(1)}pp${INVERT_SIGNAL ? ' [INV]' : ''} (sum=${(rawSum*100).toFixed(1)}¢)` };
  },
  shouldExit(ctx, pos, p) {
    const curMid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (curMid !== null) {
      const mv = (curMid - pos.polyEntryPrice) / pos.polyEntryPrice;
      // Абсолютный потолок TP: при высоком входе процентная цель недостижима
      // (токен ≤ 100¢). Фиксируем, как только цена дошла до уровня — выше почти
      // нет апсайда, а разворот оттуда крайне болезненный.
      if (curMid >= TP_ABS_PRICE) return { reason: 'TP', exitPrice: curMid };
      if (mv >= p.tpPct) return { reason: 'TP', exitPrice: curMid };
      if (mv <= -p.slPct) return { reason: 'SL', exitPrice: curMid };
    }
    // FLIP-выход: сигнал развернулся ПРОТИВ позиции. Учитываем инверсию —
    // иначе при INVERT каждая позиция «против сырого сигнала» и FLIP зациклится
    // (открыл → тут же закрыл → открыл …). Сравниваем с эффективным направлением.
    let effDir = ctx.sigP.dir;
    if (INVERT_SIGNAL && effDir !== 'WAIT') effDir = effDir === 'UP' ? 'DOWN' : 'UP';
    if (effDir !== 'WAIT' && effDir !== pos.side && ctx.sigP.conf > p.flipConf)
      return { reason: 'FLIP', exitPrice: curMid };
    // ADVERSE: BTC ушёл против позиции с МОМЕНТА ВХОДА. Берём цену входа позиции
    // (btcAtEntryCoinbase), а НЕ открытие окна (btcAtEntry) — иначе при повторном
    // входе в то же окно отсчёт не сбрасывается и ADVERSE срабатывает мгновенно
    // (петля «вышел → зашёл → тут же вышел», особенно при инверсии).
    const entryBTC = pos.btcAtEntryCoinbase || pos.btcAtEntry;
    if (ctx.curBTC && entryBTC && ctx.msToEnd > 90000) {
      const mvBTC = ((ctx.curBTC - entryBTC) / entryBTC) * 100;
      if (pos.side === 'UP'   && mvBTC < -p.advMovePct) return { reason: 'ADVERSE', exitPrice: curMid };
      if (pos.side === 'DOWN' && mvBTC > p.advMovePct)  return { reason: 'ADVERSE', exitPrice: curMid };
    }
    return null;
  },
};

// ── ХЕЛПЕРЫ ДЛЯ СТРАТЕГИЙ ─────────────────────────────────────────────────────
function _normPoly(ctx) {
  if (ctx.polyUp == null || ctx.polyDn == null) return null;
  const sum = ctx.polyUp + ctx.polyDn;
  if (sum <= 0) return null;
  return { up: ctx.polyUp / sum, dn: ctx.polyDn / sum, sum };
}
// Синтетическая вероятность для сайзинга там, где нет модельной prob — должна быть
// выше цены (иначе Kelly даст 0), но в разумных пределах.
function _clampProb(prob, price) { return Math.max(price + 0.02, Math.min(0.97, prob)); }
// Общий ценовой выход TP/SL (+ абсолютный потолок).
function _tpSlExit(ctx, pos, p) {
  const curMid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
  if (curMid == null) return null;
  const mv = (curMid - pos.polyEntryPrice) / pos.polyEntryPrice;
  if (curMid >= TP_ABS_PRICE) return { reason: 'TP', exitPrice: curMid };
  if (mv >= p.tpPct)          return { reason: 'TP', exitPrice: curMid };
  if (mv <= -p.slPct)         return { reason: 'SL', exitPrice: curMid };
  return null;
}
function _advExit(ctx, pos, p) {
  const curMid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
  const entryBTC = pos.btcAtEntryCoinbase || pos.btcAtEntry;
  if (ctx.curBTC && entryBTC && ctx.msToEnd > 90000) {
    const mvBTC = ((ctx.curBTC - entryBTC) / entryBTC) * 100;
    if (pos.side === 'UP'   && mvBTC < -p.advMovePct) return { reason: 'ADVERSE', exitPrice: curMid };
    if (pos.side === 'DOWN' && mvBTC > p.advMovePct)  return { reason: 'ADVERSE', exitPrice: curMid };
  }
  return null;
}
// Вход в стиле momentum (с возможной инверсией направления).
function _momentumEntry(ctx, p, invert) {
  if (ctx.sigP.dir === 'WAIT') return null;
  if (ctx.sigP.conf < p.minConf) return null;
  if (ctx.msToEnd < p.minTimeMs) return null;
  const np = _normPoly(ctx); if (!np) return null;
  let dir = ctx.sigP.dir, prob = ctx.sigP.prob;
  if (invert) { dir = dir === 'UP' ? 'DOWN' : 'UP'; prob = 1 - prob; }
  const polyPrice = dir === 'UP' ? np.up : np.dn;
  const ourProb   = dir === 'UP' ? prob : (1 - prob);
  if (polyPrice < MIN_ENTRY_PRICE) return null;
  const edge = ourProb - polyPrice;
  if (edge < p.minEdge) return null;
  return { side: dir, polyPrice, ourProb, edge, info: `conf=${ctx.sigP.conf.toFixed(0)}% edge=+${(edge*100).toFixed(1)}pp${invert ? ' [ANTI]' : ''}` };
}

// ── 1. MOMENTUM SCRATCH — momentum, но фиксируем малую прибыль, если до TP не
//       дотягиваем и импульс выдыхается (или мало времени до конца окна). ───────
const STRAT_MOM_SCRATCH = {
  id: 'momScratch',
  name: 'Momentum Scratch (ранний выход)',
  desc: 'momentum + фиксация малой прибыли, если TP недостижим',
  defaults: { minConf: 35, minEdge: 0.03, minTimeMs: 60000, tpPct: 0.50, slPct: 0.30, flipConf: 50, advMovePct: 0.25, kellyFrac: 0.25, maxFrac: 0.10, scratchMin: 0.08, scratchTimeMs: 120000 },
  shouldEnter(ctx, p) { return _momentumEntry(ctx, p, INVERT_SIGNAL); },
  shouldExit(ctx, pos, p) {
    const curMid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (curMid != null) {
      const mv = (curMid - pos.polyEntryPrice) / pos.polyEntryPrice;
      if (curMid >= TP_ABS_PRICE) return { reason: 'TP', exitPrice: curMid };
      if (mv >= p.tpPct)          return { reason: 'TP', exitPrice: curMid };
      // SCRATCH: в плюсе, но TP не достигнут и импульс уходит / времени мало.
      if (mv >= p.scratchMin && mv < p.tpPct) {
        let effDir = ctx.sigP.dir;
        if (INVERT_SIGNAL && effDir !== 'WAIT') effDir = effDir === 'UP' ? 'DOWN' : 'UP';
        const fading = (effDir !== pos.side) || (ctx.sigP.conf < p.minConf);
        if (fading || ctx.msToEnd < p.scratchTimeMs) return { reason: 'SCRATCH', exitPrice: curMid };
      }
      if (mv <= -p.slPct) return { reason: 'SL', exitPrice: curMid };
    }
    return _advExit(ctx, pos, p);
  },
};

// ── 2. ANTI-MOMENTUM — всегда против сырого сигнала модели (отдельная стратегия,
//       чтобы крутить momentum и его зеркало одновременно). ────────────────────
const STRAT_ANTI_MOM = {
  id: 'antiMom',
  name: 'Anti-Momentum (контр-сигнал)',
  desc: 'всегда ПРОТИВ сигнала модели — постоянное зеркало momentum',
  defaults: { minConf: 35, minEdge: 0.03, minTimeMs: 60000, tpPct: 0.50, slPct: 0.30, advMovePct: 0.25, kellyFrac: 0.25, maxFrac: 0.10 },
  shouldEnter(ctx, p) { return _momentumEntry(ctx, p, true); },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};

// ── 3. MEAN REVERSION — когда одна сторона перегрета (дорого), ставим против
//       на возврат. Входим в дорогой рынок → меньше трения, чем дешёвые рывки. ──
const STRAT_MEAN_REV = {
  id: 'meanRev',
  name: 'Mean Reversion (контр-перелёт)',
  desc: 'против перегретой стороны (>80¢) в середине окна',
  defaults: { mrHot: 0.80, revEdge: 0.08, minTimeMs: 60000, maxTimeMs: 240000, tpPct: 0.30, slPct: 0.30, kellyFrac: 0.20, maxFrac: 0.08 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs || ctx.msToEnd > p.maxTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const hotSide  = np.up >= np.dn ? 'UP' : 'DOWN';
    const hotPrice = Math.max(np.up, np.dn);
    if (hotPrice < p.mrHot) return null;
    const betSide  = hotSide === 'UP' ? 'DOWN' : 'UP';
    const betPrice = Math.min(np.up, np.dn);
    if (betPrice < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(betPrice + p.revEdge, betPrice);
    return { side: betSide, polyPrice: betPrice, ourProb, edge: ourProb - betPrice, info: `против ${hotSide} @${(hotPrice*100).toFixed(0)}¢` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p); },
};

// ── 4. LATE-WINDOW FAVORITE — под конец окна добираем явного фаворита по цене
//       Chainlink BTC, пока он ещё не у 1.0 (ловим оставшийся зазор). ───────────
const STRAT_LATE_FAV = {
  id: 'lateFav',
  name: 'Late Favorite (фаворит под закрытие)',
  desc: 'в конце окна берём фаворита по факту BTC, пока он < 93¢',
  defaults: { lateMs: 90000, minTimeMs: 8000, favMin: 0.62, favMax: 0.93, favEdge: 0.08, tpPct: 0.20, slPct: 0.40, kellyFrac: 0.20, maxFrac: 0.08 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd > p.lateMs || ctx.msToEnd < p.minTimeMs) return null;
    if (ctx.curBTC == null || ctx.openingBTC == null) return null;
    const fav = ctx.curBTC > ctx.openingBTC ? 'UP' : (ctx.curBTC < ctx.openingBTC ? 'DOWN' : null);
    if (!fav) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const favPrice = fav === 'UP' ? np.up : np.dn;
    if (favPrice < p.favMin || favPrice > p.favMax) return null;
    if (favPrice < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(favPrice + p.favEdge, favPrice);
    const d = ctx.curBTC - ctx.openingBTC;
    return { side: fav, polyPrice: favPrice, ourProb, edge: ourProb - favPrice, info: `фаворит ${fav} @${(favPrice*100).toFixed(0)}¢ (BTC ${d>=0?'+':''}${d.toFixed(0)})` };
  },
  shouldExit(ctx, pos, p) {
    const e = _tpSlExit(ctx, pos, p); if (e) return e;
    // фаворит потерян — BTC вернулся на другую сторону открытия окна
    const curMid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (ctx.curBTC != null && ctx.openingBTC != null) {
      const stillFav = pos.side === 'UP' ? ctx.curBTC > ctx.openingBTC : ctx.curBTC < ctx.openingBTC;
      if (!stillFav) return { reason: 'ADVERSE', exitPrice: curMid };
    }
    return null;
  },
};

// ── 5. ORDER-BOOK IMBALANCE — направление по перекосу стакана BTC (Coinbase
//       L2). Независимый микроструктурный сигнал, не зависит от модели. ─────────
const STRAT_BOOK_IMB = {
  id: 'bookImb',
  name: 'Order-Book Imbalance (стакан)',
  desc: 'направление по дисбалансу стакана BTC > порога',
  defaults: { imbThresh: 0.40, maxPerWindow: 2, minTimeMs: 30000, tpPct: 0.30, slPct: 0.30, advMovePct: 0.25, kellyFrac: 0.20, maxFrac: 0.08 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const imb = bookImbalance(10);
    if (imb == null || Math.abs(imb) < p.imbThresh) return null;
    const dir = imb > 0 ? 'UP' : 'DOWN';
    const np = _normPoly(ctx); if (!np) return null;
    const price = dir === 'UP' ? np.up : np.dn;
    if (price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + Math.min(0.20, Math.abs(imb) * 0.25), price);
    return { side: dir, polyPrice: price, ourProb, edge: ourProb - price, info: `imb=${(imb*100).toFixed(0)}% → ${dir}` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};

// ── 7. MOMENTUM STRONG — momentum только на сильных сигналах. ────────────────
const STRAT_MOM_HI = {
  id: 'momHi', name: 'Momentum Strong (высокая увер.)',
  desc: 'momentum, но только conf≥50 и edge≥6pp',
  defaults: { minConf: 50, minEdge: 0.06, minTimeMs: 60000, tpPct: 0.50, slPct: 0.30, flipConf: 55, advMovePct: 0.30, kellyFrac: 0.25, maxFrac: 0.10 },
  shouldEnter(ctx, p) { return _momentumEntry(ctx, p, INVERT_SIGNAL); },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};

// ── 8. EMA TREND — направление по пересечению EMA. ───────────────────────────
const STRAT_EMA_TREND = {
  id: 'emaTrend', name: 'EMA Trend (пересечение скользящих)',
  desc: 'направление по EMA fast vs slow',
  defaults: { emaThresh: 0.02, maxPerWindow: 2, minTimeMs: 60000, tpPct: 0.40, slPct: 0.35, advMovePct: 0.30, kellyFrac: 0.20, maxFrac: 0.08 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const e = getEMACross();
    if (e == null || Math.abs(e) < p.emaThresh) return null;
    const dir = e > 0 ? 'UP' : 'DOWN';
    const np = _normPoly(ctx); if (!np) return null;
    const price = dir === 'UP' ? np.up : np.dn;
    if (price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.07, price);
    return { side: dir, polyPrice: price, ourProb, edge: ourProb - price, info: `EMA ${e.toFixed(3)}% → ${dir}` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};

// ── 9. RSI REVERSION — экстремальный RSI → разворот. ─────────────────────────
const STRAT_RSI_REV = {
  id: 'rsiRev', name: 'RSI Reversion (перекуп/перепрод)',
  desc: 'RSI>70 → DOWN, RSI<30 → UP',
  defaults: { rsiHi: 70, rsiLo: 30, rsiN: 30, minTimeMs: 60000, tpPct: 0.30, slPct: 0.30, kellyFrac: 0.15, maxFrac: 0.06 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const r = getRSI(p.rsiN);
    if (r == null) return null;
    let dir = null;
    if (r > p.rsiHi) dir = 'DOWN'; else if (r < p.rsiLo) dir = 'UP';
    if (!dir) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const price = dir === 'UP' ? np.up : np.dn;
    if (price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.07, price);
    return { side: dir, polyPrice: price, ourProb, edge: ourProb - price, info: `RSI ${r.toFixed(0)} → ${dir}` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p); },
};

// ── 10. CVD MOMENTUM — направление по объёмному дисбалансу. ──────────────────
const STRAT_CVD = {
  id: 'cvdMom', name: 'CVD Momentum (поток объёма)',
  desc: 'направление по наклону CVD (покупки vs продажи)',
  defaults: { cvdThresh: 0.05, minTimeMs: 60000, tpPct: 0.40, slPct: 0.35, advMovePct: 0.30, kellyFrac: 0.20, maxFrac: 0.08 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const cv = getCVDSlope(60);
    if (cv == null || Math.abs(cv) < p.cvdThresh) return null;
    const dir = cv > 0 ? 'UP' : 'DOWN';
    const np = _normPoly(ctx); if (!np) return null;
    const price = dir === 'UP' ? np.up : np.dn;
    if (price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.07, price);
    return { side: dir, polyPrice: price, ourProb, edge: ourProb - price, info: `CVD ${cv.toFixed(3)} → ${dir}` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};

// ── 11. CONFLUENCE — вход только когда momentum, EMA и CVD согласны. ──────────
const STRAT_CONFLUENCE = {
  id: 'confluence', name: 'Trend Confluence (3 индикатора)',
  desc: 'вход только когда импульс, EMA и CVD смотрят в одну сторону',
  defaults: { maxPerWindow: 2, minTimeMs: 60000, tpPct: 0.45, slPct: 0.30, advMovePct: 0.30, kellyFrac: 0.22, maxFrac: 0.09 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const m = getMom(60), e = getEMACross(), cv = getCVDSlope(60);
    if (m == null || e == null || cv == null) return null;
    const sUp = m > 0 && e > 0 && cv > 0, sDn = m < 0 && e < 0 && cv < 0;
    if (!sUp && !sDn) return null;
    const dir = sUp ? 'UP' : 'DOWN';
    const np = _normPoly(ctx); if (!np) return null;
    const price = dir === 'UP' ? np.up : np.dn;
    if (price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.10, price);
    return { side: dir, polyPrice: price, ourProb, edge: ourProb - price, info: `3/3 → ${dir}` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};

// ── 12. UNDERDOG HOLD — дешёвая сторона (15–45¢), ДЕРЖИМ до SETTLE. ───────────
// Проверка калибровочного сигнала: дешёвые стороны выглядят чуть недооценёнными,
// НО только если додерживать до резолва (без раннего TP/SL). Высокая дисперсия.
const STRAT_UNDERDOG_HOLD = {
  id: 'underdogHold', name: 'Underdog Hold (дёшево, до резолва)',
  desc: 'покупка дешёвой стороны 15–35¢, держим до SETTLE, но фиксируем если дошла до 96¢',
  defaults: { lo: 0.15, hi: 0.35, minTimeMs: 60000, tpAbs: 0.96, maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    if (dogPrice < p.lo || dogPrice > p.hi || dogPrice < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(dogPrice + 0.10, dogPrice);
    return { side: dogSide, polyPrice: dogPrice, ourProb, edge: ourProb - dogPrice, info: `hold ${dogSide} @${(dogPrice*100).toFixed(0)}¢` };
  },
  // Держим до SETTLE, но если дешёвая сторона почти выиграла (цена дошла до tpAbs≈96¢)
  // — фиксируем: оставшийся апсайд (≤4¢) не стоит риска отката на последних секундах.
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// ── NEW: MOMENTUM HOLD — вход по моменту, держим до резолва (без TP/SL). ──────
const STRAT_MOM_HOLD = {
  id: 'momHold', name: 'Momentum Hold (до резолва)',
  desc: 'вход по сигналу момента, держим до SETTLE — даём выигрышу доехать',
  defaults: { minConf: 35, minEdge: 0.03, minTimeMs: 60000, kellyFrac: 0.20, maxFrac: 0.08 },
  shouldEnter(ctx, p) { return _momentumEntry(ctx, p, INVERT_SIGNAL); },
  shouldExit() { return null; },   // держим до конца окна (бэктест: додержка добавляет прибыль)
};

// ── NEW: MOMENTUM WIDE — momentum с широкими порогами (бэктест: лучший TP/SL). ─
const STRAT_MOM_WIDE = {
  id: 'momWide', name: 'Momentum Wide (TP60/SL40)',
  desc: 'momentum с широкими TP/SL — по симуляции на живых ценах даёт больше всего',
  defaults: { minConf: 35, minEdge: 0.03, minTimeMs: 60000, tpPct: 0.60, slPct: 0.40, flipConf: 50, advMovePct: 0.30, kellyFrac: 0.22, maxFrac: 0.09 },
  shouldEnter(ctx, p) { return _momentumEntry(ctx, p, INVERT_SIGNAL); },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};

// ── NEW: BREAKOUT — сильный устойчивый импульс (mom30 и mom120 согласны). ─────
const STRAT_BREAKOUT = {
  id: 'breakout', name: 'Breakout (устойчивый импульс)',
  desc: 'вход когда краткий и средний импульс BTC согласны и сильны',
  defaults: { momThresh: 0.05, maxPerWindow: 2, minTimeMs: 60000, tpPct: 0.50, slPct: 0.40, advMovePct: 0.30, kellyFrac: 0.20, maxFrac: 0.08 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const m30 = getMom(30), m120 = getMom(120);
    if (m30 == null || m120 == null) return null;
    if (Math.sign(m30) !== Math.sign(m120)) return null;     // импульс не разворачивается
    if (Math.abs(m30) < p.momThresh) return null;
    const dir = m30 > 0 ? 'UP' : 'DOWN';
    const np = _normPoly(ctx); if (!np) return null;
    const price = dir === 'UP' ? np.up : np.dn;
    if (price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.08, price);
    return { side: dir, polyPrice: price, ourProb, edge: ourProb - price, info: `brk m30=${m30.toFixed(2)}% → ${dir}` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};

// ── NEW: MOM CONFIRM — сигнал момента + согласие стакана (цена и стакан вместе). ─
const STRAT_MOM_CONFIRM = {
  id: 'momConfirm', name: 'Mom Confirm (момент + стакан)',
  desc: 'вход по моменту только если дисбаланс стакана подтверждает сторону',
  defaults: { minConf: 35, minEdge: 0.03, minTimeMs: 60000, imbMin: 0.15, maxPerWindow: 3, tpPct: 0.50, slPct: 0.40, flipConf: 50, advMovePct: 0.30, kellyFrac: 0.22, maxFrac: 0.09 },
  shouldEnter(ctx, p) {
    const e = _momentumEntry(ctx, p, INVERT_SIGNAL);
    if (!e) return null;
    const imb = bookImbalance(10);
    if (imb == null) return null;
    if (e.side === 'UP'   && imb <  p.imbMin) return null;    // стакан должен давить вверх
    if (e.side === 'DOWN' && imb > -p.imbMin) return null;    // ... или вниз
    return { ...e, info: e.info + ` +imb=${imb.toFixed(2)}` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};

// ── РУЧНЫЕ ПАРАМЕТРИЧЕСКИЕ СТРАТЕГИИ ──────────────────────────────────────────
// Вход чисто по условиям (без модели): окно времени от старта свечи, дельта BTC
// от открытия ($), цена шэра, фикс. сумма входа, TP/SL (с тумблерами), макс. раундов.
// Настраиваются с дашборда. По умолчанию active=0 (пустая, не торгует).
function makeManualStrat(i) {
  return {
    id: `manual${i}`,
    name: `Ручная #${i}`,
    desc: 'вход по параметрам (время · дельта BTC · цена шэра)',
    manual: true,
    defaults: {
      dir: 'UP', entryFromSec: 0, entryToSec: 0,
      btcDeltaMin: 0, btcDeltaMax: 9999, shareMin: 0.40, shareMax: 0.65,
      betUSD: 10, tpOn: 0, tpPct: 0.30, slOn: 0, slPct: 0.30,
      maxPerWindow: 1, active: 0,
    },
    shouldEnter(ctx, p) {
      if (!p.active) return null;
      const winLen = (typeof POLY_WINDOW_SEC === 'number' ? POLY_WINDOW_SEC : 300) * 1000;
      const elapsedSec = (winLen - ctx.msToEnd) / 1000;          // время от старта свечи
      if (elapsedSec < p.entryFromSec || elapsedSec > p.entryToSec) return null;
      if (ctx.curBTC == null || ctx.openingBTC == null) return null;
      const np = _normPoly(ctx); if (!np) return null;
      const delta = ctx.curBTC - ctx.openingBTC;
      // Проверка одной стороны: движение BTC в её пользу в [min,max] И цена шэра в коридоре.
      const trySide = (side) => {
        const move = side === 'UP' ? delta : -delta;             // движение «в сторону side», $
        if (move < p.btcDeltaMin || move > p.btcDeltaMax) return null;
        const price = side === 'UP' ? np.up : np.dn;
        if (price < p.shareMin || price > p.shareMax || price < MIN_ENTRY_PRICE) return null;
        const ourProb = _clampProb(price + 0.05, price);
        return { side, polyPrice: price, ourProb, edge: ourProb - price,
                 fixedUSD: p.betUSD, info: `manual ${side} Δ${move.toFixed(0)}$ @${(price*100).toFixed(0)}¢` };
      };
      // BOTH: BTC в каждый момент в одну сторону, берём ту, что подходит. Лимит входов
      // (maxPerWindow) общий на окно — обе стороны считаются вместе, плюс новый вход не
      // откроется, пока висит открытая позиция (так UP+DOWN одновременно не наберётся).
      if (p.dir === 'BOTH') return (delta >= 0 ? trySide('UP') : trySide('DOWN'));
      return trySide(p.dir);
    },
    shouldExit(ctx, pos, p) {
      const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
      if (mid == null) return null;
      const mv = (mid - pos.polyEntryPrice) / pos.polyEntryPrice;
      if (p.tpOn && mv >=  p.tpPct) return { reason: 'TP', exitPrice: mid };
      if (p.slOn && mv <= -p.slPct) return { reason: 'SL', exitPrice: mid };
      return null;   // оба тумблера выкл → держим до SETTLE
    },
  };
}
const MANUAL_STRATS = [1,2].map(makeManualStrat);  // 2 слота ручных стратегий

// ── НОВЫЕ СИГНАЛЬНЫЕ (обоснованы калибровкой/персистентностью на чистых данных) ─
// favHold — бэк сильного фаворита под закрытие, держим до резолва. Данные: рынок
// чуть недооценивает почти-верные исходы (85-95¢ дали +$0.05/сделку). Высокая
// дисперсия: редкий разворот = крупный минус. Тест.
const STRAT_FAV_HOLD = {
  id: 'favHold', name: 'Favorite Hold (бэк фаворита до резолва)',
  desc: 'покупка сильного фаворита 70-92¢ под закрытие, держим до SETTLE',
  defaults: { favLo: 0.70, favHi: 0.92, lateMs: 150000, maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd > p.lateMs) return null;            // только под закрытие
    const np = _normPoly(ctx); if (!np) return null;
    const side = np.up >= np.dn ? 'UP' : 'DOWN';
    const price = Math.max(np.up, np.dn);
    if (price < p.favLo || price > p.favHi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.03, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `favHold ${side} @${(price*100).toFixed(0)}¢` };
  },
  shouldExit() { return null; },
};
// longHold — очень дешёвый лонгшот рано, держим до резолва. Данные: 15-30¢ слегка
// недооценены (+$0.027). Очень высокая дисперсия (редкие крупные выигрыши).
const STRAT_LONG_HOLD = {
  id: 'longHold', name: 'Longshot Hold (дёшево рано, до резолва)',
  desc: 'покупка очень дешёвой стороны 12-28¢ при запасе времени, держим до SETTLE',
  defaults: { lo: 0.12, hi: 0.28, minTimeLeftMs: 120000, maxPerWindow: 1, kellyFrac: 0.06, maxFrac: 0.03 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeLeftMs) return null;     // нужен запас времени на разворот
    const np = _normPoly(ctx); if (!np) return null;
    const side = np.up <= np.dn ? 'UP' : 'DOWN';
    const price = Math.min(np.up, np.dn);
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.06, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `longHold ${side} @${(price*100).toFixed(0)}¢` };
  },
  shouldExit() { return null; },
};
// lateMom — сигнал момента, но вход только в последней трети окна (цена сформирована,
// исход яснее). Персистентность направления к концу выше.
const STRAT_LATE_MOM = {
  id: 'lateMom', name: 'Late Momentum (момент под закрытие)',
  desc: 'вход по сигналу момента только в последней трети окна',
  defaults: { minConf: 35, minEdge: 0.03, minTimeMs: 8000, lateMs: 120000, tpPct: 0.40, slPct: 0.40, flipConf: 50, advMovePct: 0.30, kellyFrac: 0.20, maxFrac: 0.08, maxPerWindow: 1 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd > p.lateMs) return null;            // только поздно
    return _momentumEntry(ctx, p, INVERT_SIGNAL);
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};
// momScratchHi — momHi (только сильные сигналы) + ранняя фиксация прибыли (scratch).
// Комбинация двух вещей, что помогали: селективность входа и ранний выход в плюс.
const STRAT_MOM_SCRATCH_HI = {
  id: 'momScratchHi', name: 'Mom Scratch HI (сильный сигнал + scratch)',
  desc: 'вход только на сильном сигнале (conf≥48), ранняя фиксация прибыли',
  defaults: { minConf: 48, minEdge: 0.05, minTimeMs: 60000, tpPct: 0.50, slPct: 0.30, flipConf: 55, advMovePct: 0.30, kellyFrac: 0.22, maxFrac: 0.09, scratchMin: 0.08, scratchTimeMs: 120000 },
  shouldEnter(ctx, p) { return _momentumEntry(ctx, p, INVERT_SIGNAL); },
  shouldExit(ctx, pos, p) {
    const curMid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (curMid != null) {
      const mv = (curMid - pos.polyEntryPrice) / pos.polyEntryPrice;
      if (curMid >= TP_ABS_PRICE) return { reason: 'TP', exitPrice: curMid };
      if (mv >= p.tpPct)          return { reason: 'TP', exitPrice: curMid };
      if (mv >= p.scratchMin && mv < p.tpPct) {
        let effDir = ctx.sigP.dir;
        if (INVERT_SIGNAL && effDir !== 'WAIT') effDir = effDir === 'UP' ? 'DOWN' : 'UP';
        const fading = (effDir !== pos.side) || (ctx.sigP.conf < p.minConf);
        if (fading || ctx.msToEnd < p.scratchTimeMs) return { reason: 'SCRATCH', exitPrice: curMid };
      }
      if (mv <= -p.slPct) return { reason: 'SL', exitPrice: curMid };
    }
    return _advExit(ctx, pos, p);
  },
};
// bigMove — вход в сторону КРУПНОГО движения BTC от открытия ($, не %). Идея:
// большие движения персистентнее мелких. Отличается от breakout (тот был по %).
const STRAT_BIG_MOVE = {
  id: 'bigMove', name: 'Big Move (крупное движение от открытия)',
  desc: 'вход в сторону движения BTC, если оно крупное ($ от открытия свечи)',
  defaults: { moveUSD: 30, minTimeMs: 30000, tpPct: 0.50, slPct: 0.40, advMovePct: 0.35, kellyFrac: 0.20, maxFrac: 0.08, maxPerWindow: 2 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    if (ctx.curBTC == null || ctx.openingBTC == null) return null;
    const delta = ctx.curBTC - ctx.openingBTC;
    if (Math.abs(delta) < p.moveUSD) return null;
    const dir = delta > 0 ? 'UP' : 'DOWN';
    const np = _normPoly(ctx); if (!np) return null;
    const price = dir === 'UP' ? np.up : np.dn;
    if (price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.07, price);
    return { side: dir, polyPrice: price, ourProb, edge: ourProb - price, info: `bigMove Δ${delta.toFixed(0)}$ → ${dir}` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};

// ── ЕЩЁ 6 АВТО-СТРАТЕГИЙ (без ручных настроек) ───────────────────────────────
// timeSession — momentum только в US-сессию (13:30–20:00 UTC, высокая волатильность).
const STRAT_TIME_SESSION = {
  id: 'timeSession', name: 'Time Session (US-часы)',
  desc: 'momentum только в активные часы (13:30–20:00 UTC)',
  defaults: { minConf: 35, minEdge: 0.03, minTimeMs: 60000, tpPct: 0.45, slPct: 0.35, flipConf: 50, advMovePct: 0.30, kellyFrac: 0.20, maxFrac: 0.08, maxPerWindow: 2 },
  shouldEnter(ctx, p) {
    const d = new Date(); const h = d.getUTCHours() + d.getUTCMinutes() / 60;
    if (h < 13.5 || h > 20) return null;                // только US-сессия
    return _momentumEntry(ctx, p, INVERT_SIGNAL);
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};
// fadeBigMove — фейд крупного рывка (обратная гипотеза к bigMove): ставка на откат.
const STRAT_FADE_BIG = {
  id: 'fadeBigMove', name: 'Fade Big Move (фейд рывка)',
  desc: 'после крупного движения BTC ставим ПРОТИВ него (на откат)',
  defaults: { moveUSD: 40, minTimeMs: 90000, tpPct: 0.30, slPct: 0.35, kellyFrac: 0.15, maxFrac: 0.06, maxPerWindow: 1 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    if (ctx.curBTC == null || ctx.openingBTC == null) return null;
    const delta = ctx.curBTC - ctx.openingBTC;
    if (Math.abs(delta) < p.moveUSD) return null;
    const dir = delta > 0 ? 'DOWN' : 'UP';              // против движения
    const np = _normPoly(ctx); if (!np) return null;
    const price = dir === 'UP' ? np.up : np.dn;
    if (price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.06, price);
    return { side: dir, polyPrice: price, ourProb, edge: ourProb - price, info: `fade Δ${delta.toFixed(0)}$ → ${dir}` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p); },
};
// bigMoveFav — крупное движение И цена шэра уже в зоне фаворита (двойное подтверждение).
const STRAT_BIGMOVE_FAV = {
  id: 'bigMoveFav', name: 'Big Move + Favorite (подтверждение)',
  desc: 'крупное движение BTC + сторона уже фаворит по цене (60-90¢)',
  defaults: { moveUSD: 30, favLo: 0.60, favHi: 0.90, minTimeMs: 30000, tpPct: 0.40, slPct: 0.40, advMovePct: 0.35, kellyFrac: 0.20, maxFrac: 0.08, maxPerWindow: 2 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    if (ctx.curBTC == null || ctx.openingBTC == null) return null;
    const delta = ctx.curBTC - ctx.openingBTC;
    if (Math.abs(delta) < p.moveUSD) return null;
    const dir = delta > 0 ? 'UP' : 'DOWN';
    const np = _normPoly(ctx); if (!np) return null;
    const price = dir === 'UP' ? np.up : np.dn;
    if (price < p.favLo || price > p.favHi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.05, price);
    return { side: dir, polyPrice: price, ourProb, edge: ourProb - price, info: `bigFav Δ${delta.toFixed(0)}$ @${(price*100).toFixed(0)}¢` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p) || _advExit(ctx, pos, p); },
};
// favHoldX — узкая зона фаворита 88-96¢ (где per-trade эдж был максимален), до резолва.
const STRAT_FAV_HOLD_X = {
  id: 'favHoldX', name: 'Favorite Hold X (88-96¢)',
  desc: 'бэк сильного фаворита 88-96¢ под закрытие, держим до SETTLE',
  defaults: { favLo: 0.88, favHi: 0.96, lateMs: 150000, maxPerWindow: 1, kellyFrac: 0.08, maxFrac: 0.04 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd > p.lateMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const side = np.up >= np.dn ? 'UP' : 'DOWN';
    const price = Math.max(np.up, np.dn);
    if (price < p.favLo || price > p.favHi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.02, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `favX ${side} @${(price*100).toFixed(0)}¢` };
  },
  shouldExit() { return null; },
};
// longHoldX — узкая зона лонгшота 12-20¢ (самая дешёвая), до резолва.
const STRAT_LONG_HOLD_X = {
  id: 'longHoldX', name: 'Longshot Hold X (12-20¢)',
  desc: 'покупка очень дешёвой стороны 12-20¢ при запасе времени, до SETTLE',
  defaults: { lo: 0.12, hi: 0.20, minTimeLeftMs: 120000, maxPerWindow: 1, kellyFrac: 0.05, maxFrac: 0.025 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeLeftMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const side = np.up <= np.dn ? 'UP' : 'DOWN';
    const price = Math.min(np.up, np.dn);
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.05, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `longX ${side} @${(price*100).toFixed(0)}¢` };
  },
  shouldExit() { return null; },
};
// calmRev — фейд дорогого фаворита при ШТИЛЕ (мало движения + дорогая сторона → возврат к 50/50).
const STRAT_CALM_REV = {
  id: 'calmRev', name: 'Calm Reversion (фейд при штиле)',
  desc: 'при малом движении BTC фейдим переоценённого фаворита (>78¢)',
  defaults: { maxMoveUSD: 15, hotMin: 0.78, minTimeMs: 90000, tpPct: 0.30, slPct: 0.30, kellyFrac: 0.12, maxFrac: 0.05, maxPerWindow: 1 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    if (ctx.curBTC == null || ctx.openingBTC == null) return null;
    if (Math.abs(ctx.curBTC - ctx.openingBTC) > p.maxMoveUSD) return null;   // только штиль
    const np = _normPoly(ctx); if (!np) return null;
    const hot = Math.max(np.up, np.dn);
    if (hot < p.hotMin) return null;
    const betSide = np.up >= np.dn ? 'DOWN' : 'UP';     // против дорогого
    const price = Math.min(np.up, np.dn);
    if (price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.07, price);
    return { side: betSide, polyPrice: price, ourProb, edge: ourProb - price, info: `calmRev fade @${(hot*100).toFixed(0)}¢` };
  },
  shouldExit(ctx, pos, p) { return _tpSlExit(ctx, pos, p); },
};

// ── РЕЗОЛВ ОКНА ПО РЫНКУ (Chainlink-следящая цена), НЕ по нашему BTC-фиду ──────
// Polymarket резолвит по потоку Chainlink BTC/USD. Наш Coinbase/Binance фид
// расходится с ним на десятки $ и на ТОНКИХ окнах переворачивает знак движения →
// в логах появлялись фантомные «победы» на SETTLE (доказано на реальной истории).
// Истина: на закрытии окна выигравшая сторона книги стоит ~1.0. Её и берём.
const RESOLVE_CONFIRM    = 0.98;    // сторона = ПОБЕДИТЕЛЬ только если её цена ≥ 98¢ И проигравший ≤ 2¢.
                                    // 90¢ — это НЕ резолв: на тонком окне сторона может коснуться
                                    // 90–95¢ и всё равно проиграть → раньше это давало фантомные победы.
const SETTLE_MAX_WAIT_MS = 60000;   // ждём ИСТИННОГО дорезолва (до ~1.0/0.0), затем фолбэк на фид (dirty=1)
function marketResolvedWinner(ctx) {
  const up = ctx.polyUp, dn = ctx.polyDn;
  if (up == null || dn == null) return null;
  const hi = Math.max(up, dn), lo = Math.min(up, dn);
  // Истинный резолв книги: победитель ~1.0 И проигравший ~0.0. Иначе окно ещё не решилось.
  if (hi < RESOLVE_CONFIRM || lo > (1 - RESOLVE_CONFIRM)) return null;
  return up > dn ? 'UP' : 'DOWN';
}

// ── UNDERDOG LOCK — как Underdog Hold, но за lockLeadMs до конца окна продаём
// по РЫНКУ (bid), фиксируя ИЗВЕСТНУЮ цену вместо непроверяемого SETTLE. Убирает
// фантомные исходы (всегда есть реальная цена выхода). Платой идёт асимметричный
// апсайд андердога (продаём просадку, не дожидаясь возможного разворота к 1.0) —
// поэтому это ОТДЕЛЬНАЯ стратегия для A/B-сравнения с Underdog Hold, а не замена.
const STRAT_UNDERDOG_LOCK = {
  id: 'underdogLock', name: 'Underdog Lock (фикс цены до резолва)',
  desc: 'вход как Underdog Hold (дёшево 15–35¢), но за lockLeadMs до конца продаём по рынку — фиксируем известную цену вместо SETTLE',
  defaults: { lo: 0.15, hi: 0.35, minTimeMs: 60000, tpAbs: 0.96, lockLeadMs: 20000, maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) { return STRAT_UNDERDOG_HOLD.shouldEnter(ctx, p); },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    if (ctx.msToEnd <= p.lockLeadMs) {
      const q = _sideQuote(pos.side);
      const px = (q && q.bid != null) ? q.bid : mid;
      return { reason: 'LOCK', exitPrice: px };
    }
    return null;
  },
};

// Вариант Underdog Lock с фиксацией за 10с до конца (A/B против 20с-версии). Только 5m.
// Ближе к концу — точнее цена, но выше риск, что продажа не зальётся до закрытия.
const STRAT_UNDERDOG_LOCK10 = {
  id: 'underdogLock10', name: 'Underdog Lock-10 (фикс за 10с)',
  desc: 'как Underdog Lock, но продаём по рынку за 10с до конца окна — A/B против 20с-версии',
  defaults: { ...STRAT_UNDERDOG_LOCK.defaults, lockLeadMs: 10000 },
  shouldEnter(ctx, p) { return STRAT_UNDERDOG_HOLD.shouldEnter(ctx, p); },
  shouldExit(ctx, pos, p) { return STRAT_UNDERDOG_LOCK.shouldExit(ctx, pos, p); },
};

// ─── НОВЫЕ UNDERDOG-ВАРИАЦИИ (A/B-тест ценовых коридоров и логики входа) ──────

// UDG-A: узкий горб 0.27–0.35 (рынок ещё не уверен, но уже не крайний лузер)
const STRAT_UDG_A = {
  id: 'udgA', name: 'UDG-A (0.27–0.35)',
  desc: 'underdog-вход в коридоре 27–35¢ — середина неопределённости',
  defaults: { lo: 0.27, hi: 0.35, minTimeMs: 60000, tpAbs: 0.96, maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const side  = np.up <= np.dn ? 'UP' : 'DOWN';
    const price = Math.min(np.up, np.dn);
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.10, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `udgA ${side} @${(price*100).toFixed(0)}¢` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// UDG-B: широкий коридор 0.15–0.40 (максимальное покрытие андердогов)
const STRAT_UDG_B = {
  id: 'udgB', name: 'UDG-B (0.15–0.40)',
  desc: 'underdog-вход 15–40¢ — широкий захват всего диапазона',
  defaults: { lo: 0.15, hi: 0.40, minTimeMs: 60000, tpAbs: 0.96, maxPerWindow: 1, kellyFrac: 0.09, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const side  = np.up <= np.dn ? 'UP' : 'DOWN';
    const price = Math.min(np.up, np.dn);
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.10, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `udgB ${side} @${(price*100).toFixed(0)}¢` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// UDG-C: 0.20–0.35 (чуть отрезаем совсем дешёвые, берём середину)
const STRAT_UDG_C = {
  id: 'udgC', name: 'UDG-C (0.20–0.35)',
  desc: 'underdog-вход 20–35¢ — без экстремально дешёвых',
  defaults: { lo: 0.20, hi: 0.35, minTimeMs: 60000, tpAbs: 0.96, maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const side  = np.up <= np.dn ? 'UP' : 'DOWN';
    const price = Math.min(np.up, np.dn);
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.10, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `udgC ${side} @${(price*100).toFixed(0)}¢` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// UDG-D: 0.22–0.35 (ещё один срез — чуть выше нижней границы)
const STRAT_UDG_D = {
  id: 'udgD', name: 'UDG-D (0.22–0.35)',
  desc: 'underdog-вход 22–35¢',
  defaults: { lo: 0.22, hi: 0.35, minTimeMs: 60000, tpAbs: 0.96, maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const side  = np.up <= np.dn ? 'UP' : 'DOWN';
    const price = Math.min(np.up, np.dn);
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.10, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `udgD ${side} @${(price*100).toFixed(0)}¢` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// UDG-E: 0.22–0.40 (срез D, но с расширенным верхом)
const STRAT_UDG_E = {
  id: 'udgE', name: 'UDG-E (0.22–0.40)',
  desc: 'underdog-вход 22–40¢ — от середины до верхней границы',
  defaults: { lo: 0.22, hi: 0.40, minTimeMs: 60000, tpAbs: 0.96, maxPerWindow: 1, kellyFrac: 0.09, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const side  = np.up <= np.dn ? 'UP' : 'DOWN';
    const price = Math.min(np.up, np.dn);
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.10, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `udgE ${side} @${(price*100).toFixed(0)}¢` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// UDG-FAV: Реверсионный — берём СИЛЬНУЮ сторону 0.63–0.73 (фаворит, но не экстремальный).
// Логика: рынок иногда переоценивает фаворита; входим против андердога, держим до резолва.
const STRAT_UDG_FAV = {
  id: 'udgFav', name: 'UDG-Fav (фаворит 0.63–0.73)',
  desc: 'реверсионная: берём сильную сторону 63–73¢ — фаворит, но не перегретый',
  defaults: { lo: 0.63, hi: 0.73, minTimeMs: 60000, tpAbs: 0.96, maxPerWindow: 1, kellyFrac: 0.09, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    // Берём сильную сторону (фаворита) — ту, у которой цена выше
    const favSide  = np.up >= np.dn ? 'UP' : 'DOWN';
    const favPrice = Math.max(np.up, np.dn);
    if (favPrice < p.lo || favPrice > p.hi) return null;
    if (favPrice < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(favPrice + 0.08, favPrice);
    return { side: favSide, polyPrice: favPrice, ourProb, edge: ourProb - favPrice, info: `udgFav ${favSide} @${(favPrice*100).toFixed(0)}¢` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// UDG-FLIP: «Первый разворот».
// «Первый удар» = одна из сторон зашла в диапазон hitLo–hitHi (0.35→0.15).
// Запоминаем эту сторону. Потом берём ДРУГУЮ сторону, когда она тоже зайдёт
// в диапазон entryLo–entryHi (0.15–0.35). Не заходим за 3 мин до конца.
const STRAT_UDG_FLIP = {
  id: 'udgFlip', name: 'UDG-Flip (первый разворот)',
  desc: 'одна сторона коснулась 0.15–0.35 в первые 2 мин (НЕ берём) → ждём → когда ПРОТИВОПОЛОЖНАЯ сторона входит в 0.15–0.35, берём её. Вход не в последние 60с.',
  defaults: { hitLo: 0.15, hitHi: 0.35, entryLo: 0.15, entryHi: 0.35, setupMaxElapsedMs: 120000, minTimeMs: 60000, tpAbs: 0.96, maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  _state: { slug: null, hitSide: null, entered: false },
  shouldEnter(ctx, p) {
    const np = _normPoly(ctx); if (!np) return null;
    const st = STRAT_UDG_FLIP._state;
    if (st.slug !== ctx.win?.slug) { st.slug = ctx.win?.slug; st.hitSide = null; st.entered = false; }  // новое окно → сброс
    if (st.entered) return null;
    const elapsed  = (POLY_WINDOW_SEC * 1000) - ctx.msToEnd;
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    // 1) АРМ: первый удар одной стороны в коридор — только в первые 2 мин, вход НЕ делаем
    if (st.hitSide === null) {
      if (elapsed <= p.setupMaxElapsedMs && dogPrice >= p.hitLo && dogPrice <= p.hitHi) st.hitSide = dogSide;
      return null;
    }
    // 2) РАЗВОРОТ: дешёвой стала ПРОТИВОПОЛОЖНАЯ сторона → берём её
    if (ctx.msToEnd < p.minTimeMs) return null;        // не входим в последние 60с
    if (dogSide === st.hitSide) return null;           // та же сторона ещё дешёвая — ждём флип
    if (dogPrice < p.entryLo || dogPrice > p.entryHi || dogPrice < MIN_ENTRY_PRICE) return null;
    st.entered = true;                                 // один вход за окно
    const ourProb = _clampProb(dogPrice + 0.10, dogPrice);
    return { side: dogSide, polyPrice: dogPrice, ourProb, edge: ourProb - dogPrice,
             info: `udgFlip ${dogSide} @${(dogPrice*100).toFixed(0)}¢ flip←${st.hitSide}` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// UDG-FLIP-FAV: «Первый удар → берём восстановившуюся сторону как ФАВОРИТА».
// Сторона коснулась 0.15–0.35 в первые 2 мин (первый удар), затем ТА ЖЕ сторона
// восстановилась в коридор фаворита 0.63–0.73 — берём её (ставка, что разворот держится).
const STRAT_UDG_FLIP_FAV = {
  id: 'udgFlipFav', name: 'UDG-Flip Fav (разворот → фаворит)',
  desc: 'сторона коснулась 0.15–0.35 в первые 2 мин, затем ВЫШЛА в 0.63–0.73 (восстановилась) — берём её. Вход не в последние 60с.',
  defaults: { hitLo: 0.15, hitHi: 0.35, favLo: 0.63, favHi: 0.73, setupMaxElapsedMs: 120000, minTimeMs: 60000, tpAbs: 0.96, maxPerWindow: 1, kellyFrac: 0.09, maxFrac: 0.05 },
  _state: { slug: null, hitSide: null, entered: false },
  shouldEnter(ctx, p) {
    const np = _normPoly(ctx); if (!np) return null;
    const st = STRAT_UDG_FLIP_FAV._state;
    if (st.slug !== ctx.win?.slug) { st.slug = ctx.win?.slug; st.hitSide = null; st.entered = false; }
    if (st.entered) return null;
    const elapsed  = (POLY_WINDOW_SEC * 1000) - ctx.msToEnd;
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    if (st.hitSide === null) {
      if (elapsed <= p.setupMaxElapsedMs && dogPrice >= p.hitLo && dogPrice <= p.hitHi) st.hitSide = dogSide;
      return null;
    }
    if (ctx.msToEnd < p.minTimeMs) return null;
    const hitPrice = st.hitSide === 'UP' ? np.up : np.dn;     // цена стороны первого удара
    if (hitPrice < p.favLo || hitPrice > p.favHi || hitPrice < MIN_ENTRY_PRICE) return null;  // ждём её восстановления в коридор фаворита
    st.entered = true;
    const ourProb = _clampProb(hitPrice + 0.08, hitPrice);
    return { side: st.hitSide, polyPrice: hitPrice, ourProb, edge: ourProb - hitPrice,
             info: `udgFlipFav ${st.hitSide} @${(hitPrice*100).toFixed(0)}¢ recovered` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// Активный набор: убраны мусорные стратегии (favHold/favHoldX/bigMove/bigMoveFav/
// fadeBigMove/calmRev/longHoldX/timeSession — стабильный минус на всех чистых данных).
// underdogLock/underdogLock10 исключены: стабильный убыток за 7 дней логов.
// longHold/lateMom/momScratchHi убраны по запросу (изображения на скриншотах).
// Ядро (опора): underdogHold, momentum. Новые UDG-вариации — A/B-тест коридоров.
// manual1/manual2 — 2 слота ручных стратегий.
// ── НОВЫЕ ТЕСТ-СТРАТЕГИИ (торгуют демо; рабочее ядро не трогают) ──────────────
// udgVol: тугой коридор 0.22–0.35 + НЕ входим в «штиль». Фильтр активности пред.
// окна подтверждён на твоих данных (ROI +8%→+16%). minPrevMove — порог |движения| $.
const STRAT_UDG_VOL = {
  id: 'udgVol', name: 'UDG-Vol (фильтр волатильности)',
  desc: 'underdog 0.22–0.35; вход ТОЛЬКО если предыдущее окно было активным (|move| ≥ minPrevMove). Пропускает штиль.',
  defaults: { lo: 0.22, hi: 0.35, minTimeMs: 60000, tpAbs: 0.96, minPrevMove: 60, maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    if (ctx.prevMove == null || ctx.prevMove < p.minPrevMove) return null;   // штиль / нет истории → пропуск
    const np = _normPoly(ctx); if (!np) return null;
    const side  = np.up <= np.dn ? 'UP' : 'DOWN';
    const price = Math.min(np.up, np.dn);
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.10, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `udgVol ${side} @${(price*100).toFixed(0)}¢ prev$${ctx.prevMove.toFixed(0)}` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// udgStreak: ЭКСПЕРИМЕНТ. Вход только когда серия одинаковых исходов подряд в полосе
// [minStreak..maxStreak]. Сигнал серии НЕСТАБИЛЕН на историч. данных (разные выборки —
// разный знак), поэтому это стратегия для сбора чистого форвард-теста. Всё настраивается.
const STRAT_UDG_STREAK = {
  id: 'udgStreak', name: 'UDG-Streak (по серии исходов)',
  desc: 'underdog 0.22–0.35; вход только если предыдущие исходы шли подряд в одну сторону: streak в [minStreak..maxStreak]. Тест «после серии — разворот».',
  defaults: { lo: 0.22, hi: 0.35, minTimeMs: 60000, tpAbs: 0.96, minStreak: 3, maxStreak: 6, maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    if (ctx.outcomeStreak < p.minStreak || ctx.outcomeStreak > p.maxStreak) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const side  = np.up <= np.dn ? 'UP' : 'DOWN';
    const price = Math.min(np.up, np.dn);
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.10, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `udgStreak ${side} @${(price*100).toFixed(0)}¢ strk${ctx.outcomeStreak}${ctx.streakDir||''}` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// udgBest: лучший коридор по бектесту — узкий центр 0.22–0.32 (ROI +23–26% за июнь).
const STRAT_UDG_BEST = {
  id: 'udgBest', name: 'UDG-Best (0.22–0.32)',
  desc: 'underdog-вход 0.22–0.32 — самый сильный коридор по бектесту (узкий центр).',
  defaults: { lo: 0.22, hi: 0.32, minTimeMs: 60000, tpAbs: 0.96, maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const side  = np.up <= np.dn ? 'UP' : 'DOWN';
    const price = Math.min(np.up, np.dn);
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
    const ourProb = _clampProb(price + 0.10, price);
    return { side, polyPrice: price, ourProb, edge: ourProb - price, info: `udgBest ${side} @${(price*100).toFixed(0)}¢` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// udgScore: КОМПЛЕКСНАЯ мультифакторная стратегия. Считает балл качества входа из
// трёх подтверждённых факторов (волатильность пред. окна + центральность цены в
// коридоре + US-сессия), штрафует слишком дешёвый андердог. Входит только если
// score ≥ minScore, а РАЗМЕР масштабируется баллом — через ourProb (его двигает Kelly):
// чем выше score, тем выше ourProb → больше ставка. Книжный дисбаланс (obi) пока не
// учитываем — он не считается вживую без доп. данных стакана.
const STRAT_UDG_SCORE = {
  id: 'udgScore', name: 'UDG-Score (мультифактор + Kelly)',
  desc: 'балл качества: волатильность пред. окна + центр коридора 0.22–0.32 + US-сессия (14–23 UTC). Вход при score ≥ minScore, размер растёт с баллом.',
  defaults: { lo: 0.15, hi: 0.40, minTimeMs: 60000, tpAbs: 0.96,
              volLo: 30, volHi: 90, center: 0.27, halfW: 0.10,
              wVol: 1.0, wCorr: 1.0, wSess: 0.6, minScore: 0.45, edgeMax: 0.14,
              maxPerWindow: 1, kellyFrac: 0.12, maxFrac: 0.06 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const side  = np.up <= np.dn ? 'UP' : 'DOWN';
    const price = Math.min(np.up, np.dn);
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
    // Фактор 1: волатильность предыдущего окна (0..1)
    const vol      = (ctx.prevMove != null) ? ctx.prevMove : 0;
    const volScore = Math.max(0, Math.min(1, (vol - p.volLo) / (p.volHi - p.volLo)));
    // Фактор 2: центральность цены в коридоре (пик у center, 0 на краях ±halfW)
    const corrScore = Math.max(0, 1 - Math.abs(price - p.center) / p.halfW);
    // Фактор 3: US-сессия (14–23 UTC лучше)
    const hr        = new Date().getUTCHours();
    const sessScore = (hr >= 14 && hr <= 23) ? 1 : 0.5;
    // Штраф за слишком дешёвый андердог (капкан)
    const deepPen   = price < 0.20 ? 0.5 : 1;
    const score = (p.wVol*volScore + p.wCorr*corrScore + p.wSess*sessScore)
                / (p.wVol + p.wCorr + p.wSess) * deepPen;
    if (score < p.minScore) return null;                       // гейт качества
    const ourProb = _clampProb(price + p.edgeMax * score, price);  // размер ∝ score (через Kelly)
    return { side, polyPrice: price, ourProb, edge: ourProb - price,
             info: `udgScore ${side} @${(price*100).toFixed(0)}¢ s=${score.toFixed(2)}` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// ── UDG-SKIP3 — Underdog Hold + Skip-3 фильтр ─────────────────────────────────
// По результатам бэктеста (Jun 1-9, 2026, 5min BTC Up/Down):
//   Skip-3 выиграл по всем параметрам среди Skip-1..6:
//   WR 39.2% (+5.8pp к базе), EV +12.2%/сделку, PF 1.20, итог +$1460 за 8 дней.
//
// Логика фильтра:
// • Смотрим на лог ДЕМО-аккаунта стратегии underdogHold (всегда включён, всегда актуален).
// • Считаем сколько последних сделок подряд были проигрышем.
// • Если таких ≥ skipAfter (=3) — пропускаем вход, ждём первой победы в том же логе.
// • Вход и выход идентичны underdogHold (15–35¢, TP при 96¢, держим до SETTLE).
const STRAT_UDG_SKIP3 = {
  id: 'udgSkip3',
  name: 'UDG-Skip-3 (Hold + Skip-фильтр)',
  desc: 'Дог 20–40¢ ТОЛЬКО после 3 лузов underdogHold подряд. Коридор подобран на РЕАЛЬНЫХ данных Polymarket (важнее demo-логов): 20-40 даёт +$157/6дн EV+0.72 4/6 дней+ против 10-35 +$8 EV+0.04. Глубокие доги <20¢ на этом рынке мертвы. 3 луза — оптимум (2 рано, 4-5 поздно). ЧЕСТНО: эдж на реальных данных скромный, нестабилен 4/6 дней.',
  defaults: {
    lo: 0.20, hi: 0.40,
    minTimeMs: 60000,
    tpAbs: 0.96,
    skipAfter: 3,
    maxPerWindow: 1,
    kellyFrac: 0.10,
    maxFrac: 0.05,
  },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    if (dogPrice < p.lo || dogPrice > p.hi || dogPrice < MIN_ENTRY_PRICE) return null;

    // ── Skip-фильтр: читаем лог демо-аккаунта underdogHold ──────────────────
    // Логика: входим ТОЛЬКО если после последнего нашего входа накопилось
    // skipAfter новых лузов подряд в логе underdogHold.
    // Как только мы входим — запоминаем текущую длину лога как «точку сброса».
    // Следующая серия считается только с этой точки, старые лузы не учитываются.
    const ref = STRATEGIES['underdogHold'];
    if (!ref || !ref.demo || ref.demo.log.length < p.skipAfter) return null; // мало истории — ждём
    const log = ref.demo.log;

    // Точка сброса: индекс в логе, начиная с которого считаем новую серию.
    // Хранится на объекте стратегии udgSkip3.
    const selfStrat = STRATEGIES['udgSkip3'];
    // Если точки сброса нет — начинаем счёт с начала лога.
    const resetIdx = (selfStrat && selfStrat._skip3ResetIdx != null)
      ? selfStrat._skip3ResetIdx
      : 0;

    // Считаем лузы подряд начиная с конца, но не раньше resetIdx
    let losses = 0;
    for (let i = log.length - 1; i >= resetIdx; i--) {
      if (!log[i].won) losses++;
      else break;
    }
    if (losses < p.skipAfter) return null; // серия ещё не набралась — ждём

    // НЕ сбрасываем _skip3ResetIdx здесь: shouldEnter вызывается дважды при demo-delay
    // (1й раз — фиксируем pendingEntry, 2й — верифицируем перед входом).
    // Сброс происходит в stratOpen() — только когда вход реально состоялся.

    const ourProb = _clampProb(dogPrice + 0.10, dogPrice);
    return {
      side: dogSide, polyPrice: dogPrice, ourProb,
      edge: ourProb - dogPrice,
      info: `udgSkip3 ${dogSide} @${(dogPrice * 100).toFixed(0)}¢`,
    };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null; // держим до SETTLE
  },
};

// ── UDG-SKIP3-B — диапазон 0.10-0.30, лучший Profit Factor (1.47) ────────────
// Бэктест Jun 1-9 2026, 135 сделок, WR 36.3%, ROI на стейк +26.7%, PF 1.47
// Более широкий нижний порог: берём всех андердогов от 10¢, TP 96¢.
const STRAT_UDG_SKIP3_B = {
  id: 'udgSkip3B',
  name: 'UDG-Skip-3-B (0.10–0.30, PF 1.47)',
  desc: 'Underdog Hold 10–30¢ + Skip-3 фильтр. Лучший Profit Factor (1.47) по бэктесту Jun 2026.',
  defaults: {
    lo: 0.10, hi: 0.30,
    minTimeMs: 60000,
    tpAbs: 0.96,
    skipAfter: 3,
    maxPerWindow: 1,
    kellyFrac: 0.10,
    maxFrac: 0.05,
  },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    if (dogPrice < p.lo || dogPrice > p.hi || dogPrice < MIN_ENTRY_PRICE) return null;

    const ref = STRATEGIES['underdogHold'];
    if (!ref || !ref.demo || ref.demo.log.length < p.skipAfter) return null;
    const log = ref.demo.log;

    const selfStrat = STRATEGIES['udgSkip3B'];
    const resetIdx = (selfStrat && selfStrat._skip3ResetIdx != null)
      ? selfStrat._skip3ResetIdx
      : 0;

    let losses = 0;
    for (let i = log.length - 1; i >= resetIdx; i--) {
      if (!log[i].won) losses++;
      else break;
    }
    if (losses < p.skipAfter) return null;

    // Сброс _skip3ResetIdx — в stratOpen(), не здесь (см. комментарий в udgSkip3).

    const ourProb = _clampProb(dogPrice + 0.10, dogPrice);
    return {
      side: dogSide, polyPrice: dogPrice, ourProb,
      edge: ourProb - dogPrice,
      info: `udgSkip3B ${dogSide} @${(dogPrice * 100).toFixed(0)}¢`,
    };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// ── UDG-SKIP3-C — диапазон 0.20-0.30, топ-3 ROI + минимальная просадка ───────
// Бэктест Jun 1-9 2026, 132 сделки, WR 36.4%, ROI на стейк +26.1%, PF 1.38
// Узкий диапазон: только «середина рынка», меньше экстремальных ставок.
const STRAT_UDG_SKIP3_C = {
  id: 'udgSkip3C',
  name: 'UDG-Skip-3-C (0.20–0.30, ROI +26%)',
  desc: 'Underdog Hold 20–30¢ + Skip-3 фильтр. Топ-3 по ROI, минимальная просадка среди лидеров.',
  defaults: {
    lo: 0.20, hi: 0.30,
    minTimeMs: 60000,
    tpAbs: 0.96,
    skipAfter: 3,
    maxPerWindow: 1,
    kellyFrac: 0.10,
    maxFrac: 0.05,
  },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    if (dogPrice < p.lo || dogPrice > p.hi || dogPrice < MIN_ENTRY_PRICE) return null;

    const ref = STRATEGIES['underdogHold'];
    if (!ref || !ref.demo || ref.demo.log.length < p.skipAfter) return null;
    const log = ref.demo.log;

    const selfStrat = STRATEGIES['udgSkip3C'];
    const resetIdx = (selfStrat && selfStrat._skip3ResetIdx != null)
      ? selfStrat._skip3ResetIdx
      : 0;

    let losses = 0;
    for (let i = log.length - 1; i >= resetIdx; i--) {
      if (!log[i].won) losses++;
      else break;
    }
    if (losses < p.skipAfter) return null;

    // Сброс _skip3ResetIdx — в stratOpen(), не здесь (см. комментарий в udgSkip3).

    const ourProb = _clampProb(dogPrice + 0.10, dogPrice);
    return {
      side: dogSide, polyPrice: dogPrice, ourProb,
      edge: ourProb - dogPrice,
      info: `udgSkip3C ${dogSide} @${(dogPrice * 100).toFixed(0)}¢`,
    };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};


// ── UDG-SKIP3-D — диапазон 0.22-0.30 (топ-1 по ROI, WR 36.9%, PF 1.40) ──────
// Бэктест Jun 1-9 2026, 130 сделок, WR 36.9%, ROI +27.2%, PF 1.40, MaxDD -$971
// Лучший результат среди всех диапазонов по соотношению ROI/Drawdown.
const STRAT_UDG_SKIP3_D = {
  id: 'udgSkip3D',
  name: 'UDG-Skip-3-D (0.22–0.30, топ ROI)',
  desc: 'Underdog Hold 22–30¢ + Skip-3 фильтр. Лучший диапазон: ROI +27.2%, PF 1.40, MaxDD -$971.',
  defaults: {
    lo: 0.22, hi: 0.30,
    minTimeMs: 60000,
    tpAbs: 0.96,
    skipAfter: 3,
    maxPerWindow: 1,
    kellyFrac: 0.10,
    maxFrac: 0.05,
  },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    if (dogPrice < p.lo || dogPrice > p.hi || dogPrice < MIN_ENTRY_PRICE) return null;

    const ref = STRATEGIES['underdogHold'];
    if (!ref || !ref.demo || ref.demo.log.length < p.skipAfter) return null;
    const log = ref.demo.log;

    const selfStrat = STRATEGIES['udgSkip3D'];
    const resetIdx = (selfStrat && selfStrat._skip3ResetIdx != null)
      ? selfStrat._skip3ResetIdx
      : 0;

    let losses = 0;
    for (let i = log.length - 1; i >= resetIdx; i--) {
      if (!log[i].won) losses++;
      else break;
    }
    if (losses < p.skipAfter) return null;

    // Сброс _skip3ResetIdx — в stratOpen(), не здесь (см. комментарий в udgSkip3).

    const ourProb = _clampProb(dogPrice + 0.10, dogPrice);
    return {
      side: dogSide, polyPrice: dogPrice, ourProb,
      edge: ourProb - dogPrice,
      info: `udgSkip3D ${dogSide} @${(dogPrice * 100).toFixed(0)}¢`,
    };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// ── UDG-SKIP3-E — диапазон 0.18-0.32 (WR 37%, ROI +20.8%, PF 1.32) ──────────
// Бэктест Jun 1-9 2026, 127 сделок, WR 37%, ROI +20.8%, PF 1.32, MaxDD -$892
// Компромисс: самый высокий WR среди Skip-диапазонов, умеренная просадка.
const STRAT_UDG_SKIP3_E = {
  id: 'udgSkip3E',
  name: 'UDG-Skip-3-E (0.18–0.32, WR 37%)',
  desc: 'Underdog Hold 18–32¢ + Skip-3 фильтр. Лучший Win Rate 37%, PF 1.32, MaxDD -$892.',
  defaults: {
    lo: 0.18, hi: 0.32,
    minTimeMs: 60000,
    tpAbs: 0.96,
    skipAfter: 3,
    maxPerWindow: 1,
    kellyFrac: 0.10,
    maxFrac: 0.05,
  },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    if (dogPrice < p.lo || dogPrice > p.hi || dogPrice < MIN_ENTRY_PRICE) return null;

    const ref = STRATEGIES['underdogHold'];
    if (!ref || !ref.demo || ref.demo.log.length < p.skipAfter) return null;
    const log = ref.demo.log;

    const selfStrat = STRATEGIES['udgSkip3E'];
    const resetIdx = (selfStrat && selfStrat._skip3ResetIdx != null)
      ? selfStrat._skip3ResetIdx
      : 0;

    let losses = 0;
    for (let i = log.length - 1; i >= resetIdx; i--) {
      if (!log[i].won) losses++;
      else break;
    }
    if (losses < p.skipAfter) return null;

    // Сброс _skip3ResetIdx — в stratOpen(), не здесь (см. комментарий в udgSkip3).

    const ourProb = _clampProb(dogPrice + 0.10, dogPrice);
    return {
      side: dogSide, polyPrice: dogPrice, ourProb,
      edge: ourProb - dogPrice,
      info: `udgSkip3E ${dogSide} @${(dogPrice * 100).toFixed(0)}¢`,
    };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    return null;
  },
};

// ═══════════════════════════════════════════════════════════════════════════
// ML-ЛОГ — обучающий журнал. Пишет в ml_log.jsonl три типа записей:
//   entry   — полный слепок рынка на каждом demo-входе (все фичи);
//   exit    — исход сделки (связан с entry по id);
//   virtual — КОНТРФАКТЫ: входы, заблокированные гейтами FLOMD, с их
//             виртуальным исходом по резолву окна. Это данные, которых нет в
//             обычных логах: что было бы со сделками, которые мы НЕ открыли —
//             по ним видно, сколько реально экономит каждый гейт.
// Самообучение здесь сознательно «мягкое»: бот копит доказательства и строит
// выводы (/api/ml/report + ежедневный TG-дайджест), но НЕ крутит пороги сам —
// на малых данных авто-тюнинг переподгоняется под шум за считанные дни.
// Файл ml_log.jsonl приноси на перекалибровку — по нему пороги пересчитываются
// на реальном форвард-объёме.
// ═══════════════════════════════════════════════════════════════════════════
const ML_LOG_FILE = path.join(__dirname, 'ml_log.jsonl');
let mlPendingVirtual = [];
const _mlBlockedSeen = new Set();
let _mlSeq = 0, _mlCvdSlug = null, _mlCvdAt = 0, _mlLastDigestDay = null;

function mlAppend(rec) {
  try { fs.appendFile(ML_LOG_FILE, JSON.stringify(rec) + '\n', () => {}); } catch (_) {}
}
function _mlFlow10s() {
  const cutoff = Date.now() - 10000;
  let buy = 0, tot = 0;
  for (let i = ticks.length - 1; i >= 0; i--) {
    const tk = ticks[i];
    if (tk.time < cutoff) break;
    tot += tk.qty || 0; if (tk.side === 'BUY') buy += tk.qty || 0;
  }
  return tot > 0 ? +(buy / tot).toFixed(3) : null;
}
function _mlRV60() {
  const r = ticks.filter(tk => tk.time >= Date.now() - 60000);
  if (r.length < 10) return null;
  const bySec = new Map();
  for (const tk of r) bySec.set(Math.floor(tk.time / 1000), tk.price);
  const arr = [...bySec.values()];
  if (arr.length < 10) return null;
  let s1 = 0, s2 = 0, n = 0;
  for (let i = 1; i < arr.length; i++) {
    const ret = Math.log(arr[i] / arr[i - 1]) * 10000;
    s1 += ret; s2 += ret * ret; n++;
  }
  return n ? +Math.sqrt(Math.max(0, s2 / n - (s1 / n) ** 2)).toFixed(3) : null;
}
function _mlCvdWin(ctx) {
  if (_mlCvdSlug !== ctx.win.slug) { _mlCvdSlug = ctx.win.slug; _mlCvdAt = cvd; }
  return +(cvd - _mlCvdAt).toFixed(3);
}
function mlSnapshot(ctx) {
  const wh = poly.winHist || [];
  const gsum = n => wh.length >= n ? +wh.slice(-n).reduce((a, x) => a + (x.move || 0), 0).toFixed(1) : null;
  let stk = 0;
  if (wh.length) for (let i = wh.length - 1; i >= 0; i--) { if (wh[i].winner === wh[wh.length - 1].winner) stk++; else break; }
  const qu = poly.market ? (clobQuotes[poly.market.tokenIdUp]   || {}) : {};
  const qd = poly.market ? (clobQuotes[poly.market.tokenIdDown] || {}) : {};
  return {
    t: Date.now(), slug: ctx.win.slug, hr: new Date().getUTCHours(),
    msToEnd: ctx.msToEnd,
    deltaUSD: (ctx.curBTC != null && ctx.openingBTC != null) ? +(ctx.curBTC - ctx.openingBTC).toFixed(1) : null,
    up: ctx.polyUp, dn: ctx.polyDn,
    upAskSz: qu.askSz ?? null, dnAskSz: qd.askSz ?? null,
    upBidSz: qu.bidSz ?? null, dnBidSz: qd.bidSz ?? null,
    prevMove: wh.length ? +(wh[wh.length - 1].move || 0).toFixed(1) : null,
    grind3: gsum(3), grind6: gsum(6),
    outcomeStreak: wh.length ? stk : null,
    flow10s: _mlFlow10s(), rv60: _mlRV60(), cvdWin: _mlCvdWin(ctx),
  };
}
function mlEntry(s, ctx, entry, o) {
  const id = (++_mlSeq) + '-' + Date.now();
  o._mlId = id;
  mlAppend({ type: 'entry', id, strat: s.def.id, side: entry.side,
             sigPrice: entry.polyPrice, fill: o.polyEntryPrice, ...mlSnapshot(ctx) });
}
function mlExit(s, o, pnl, won, reason, dirty) {
  mlAppend({ type: 'exit', id: o._mlId || null, strat: s.def.id, t: Date.now(),
             slug: o.marketSlug, side: o.side, fill: o.polyEntryPrice,
             pnl: +pnl.toFixed(3), won: won ? 1 : 0, reason, dirty: dirty ? 1 : 0 });
}
function mlBlocked(stratId, gate, ctx, side, price) {
  const key = ctx.win.slug + '|' + stratId + '|' + gate;
  if (_mlBlockedSeen.has(key)) return;
  _mlBlockedSeen.add(key);
  if (_mlBlockedSeen.size > 4000) {
    const it = _mlBlockedSeen.values();
    for (let i = 0; i < 2000; i++) _mlBlockedSeen.delete(it.next().value);
  }
  mlPendingVirtual.push({ type: 'virtual', strat: stratId, gate, side, price,
                          endTs: ctx.win.endTs, ...mlSnapshot(ctx) });
}
// Резолвер контрфактов: окно закрылось → проставляем виртуальный исход
setInterval(() => {
  if (!mlPendingVirtual.length) return;
  const now = Date.now(); const keep = [];
  for (const v of mlPendingVirtual) {
    const wnr = winnerBySlug[v.slug];
    if (wnr) {
      const won = v.side === wnr;
      const fill = Math.min(0.99, v.price + 0.01);            // ~ask-филл
      v.won = won ? 1 : 0;
      v.virtPnl = +(won ? 10 * (1 / fill - 1) : -10).toFixed(2); // на $10 ставку
      mlAppend(v);
    } else if (now < v.endTs + 180000) keep.push(v);
  }
  mlPendingVirtual = keep;
}, 5000);

function mlReadAll(sinceMs) {
  try {
    if (!fs.existsSync(ML_LOG_FILE)) return [];
    const out = [];
    for (const line of fs.readFileSync(ML_LOG_FILE, 'utf8').split('\n')) {
      if (!line) continue;
      try { const r = JSON.parse(line); if (!sinceMs || r.t >= sinceMs) out.push(r); } catch (_) {}
    }
    return out;
  } catch (_) { return []; }
}
function _mlBucket(v, edges) {
  if (v == null || !isFinite(v)) return null;
  for (let i = 0; i < edges.length - 1; i++) if (v >= edges[i] && v < edges[i + 1]) return edges[i] + '..' + edges[i + 1];
  return null;
}
function mlBuildReport(days) {
  const since = Date.now() - days * 86400000;
  const recs = mlReadAll(since);
  const entries = {}; const out = { days, generatedAt: new Date().toISOString(), strategies: {}, gates: {}, buckets: {}, flags: [] };
  for (const r of recs) if (r.type === 'entry') entries[r.id] = r;
  const agg = (o, k, pnl, won) => {
    const a = o[k] || (o[k] = { n: 0, pnl: 0, wins: 0 });
    a.n++; a.pnl = +(a.pnl + pnl).toFixed(2); a.wins += won ? 1 : 0;
  };
  const bDelta = {}, bHour = {}, bPrice = {}, bGrindDir = {};
  for (const r of recs) {
    if (r.type === 'exit' && !r.dirty) {
      agg(out.strategies, r.strat, r.pnl, r.won);
      const e = entries[r.id];
      if (e) {
        agg(bHour, 'h' + e.hr, r.pnl, r.won);
        if (e.deltaUSD != null) agg(bDelta, _mlBucket(Math.abs(e.deltaUSD), [0, 30, 60, 100, 9999]) || 'na', r.pnl, r.won);
        agg(bPrice, _mlBucket(r.fill, [0, 0.2, 0.3, 0.4, 0.6, 1.01]) || 'na', r.pnl, r.won);
        if (e.grind3 != null) {
          const withGrind = (r.side === 'UP') === (e.grind3 > 0);
          agg(bGrindDir, Math.abs(e.grind3) < 20 ? 'flat' : (withGrind ? 'with' : 'against'), r.pnl, r.won);
        }
      }
    }
    if (r.type === 'virtual' && r.virtPnl != null) agg(out.gates, r.gate, r.virtPnl, r.won);
  }
  for (const o of [out.strategies, out.gates, bDelta, bHour, bPrice, bGrindDir])
    for (const k in o) { o[k].ev = +(o[k].pnl / o[k].n).toFixed(2); o[k].wr = +(o[k].wins / o[k].n * 100).toFixed(1); }
  out.buckets = { absDelta: bDelta, hourUTC: bHour, fillPrice: bPrice, grindDirection: bGrindDir };
  // «сэкономлено гейтом» = −(виртуальный PnL заблокированного), если он минусовой
  for (const gname in out.gates) out.gates[gname].savedUSD = +(-out.gates[gname].pnl).toFixed(2);
  for (const [zone, o] of Object.entries(out.buckets))
    for (const [k, a] of Object.entries(o))
      if (a.n >= 30 && a.ev <= -1) out.flags.push(`${zone}:${k} — EV ${a.ev}$/сделку на n=${a.n} — присмотреться`);
  return out;
}
// Ежедневный TG-дайджест в 06:00 UTC (09:00 МСК)
setInterval(() => {
  const d = new Date();
  if (d.getUTCHours() !== 6) return;
  const day = d.toISOString().slice(0, 10);
  if (_mlLastDigestDay === day) return;
  _mlLastDigestDay = day;
  try {
    const r = mlBuildReport(1);
    const sl = Object.entries(r.strategies).map(([k, a]) => `• ${_tgEsc(k)}: ${a.n} сдел., EV ${a.ev >= 0 ? '+' : ''}$${a.ev}, WR ${a.wr}%`).join('\n') || '• сделок не было';
    const gl = Object.entries(r.gates).map(([k, a]) => `• ${_tgEsc(k)}: блокир. ${a.n}, сэкономлено ${a.savedUSD >= 0 ? '+' : ''}$${a.savedUSD}`).join('\n') || '• блокировок не было';
    const fl = r.flags.length ? '\n⚠️ ' + r.flags.map(_tgEsc).join('\n⚠️ ') : '';
    sendTg(`📊 <b>ML-дайджест за сутки</b>\n\n<b>Стратегии (demo):</b>\n${sl}\n\n<b>Гейты FLOMD (контрфакты):</b>\n${gl}${fl}`);
  } catch (_) {}
}, 60000);

// ── LAG FAVORITE («отстающий фаворит») ────────────────────────────────────────
// АУДИТ (повторная проверка всего пайплайна): первоначальная σ-версия опиралась
// на записанную delta_sigma из логов коллектора, формулу которой бот не может
// воспроизвести вживую точно (реконструкция совпадает лишь на ~70%) — при живой
// формуле эдж разваливался. Поэтому зашита ЧИСТАЯ Δ-версия без сигмы — все её
// входы бот вычисляет из того, что у него есть: цена BTC и книга Polymarket.
//
// Логика: BTC ушёл от открытия окна на ≥$90, а ЛИДИРУЮЩАЯ сторона всё ещё
// стоит 50–70¢ — книга отстаёт от спота. Берём лидера, держим до SETTLE.
// Бектест (вход по ASK +0.8с, chase 15%, SETTLE по книге), подбор IS 1–7 июня,
// проверка OOS 8–11: IS n=55 ROI +32.3%/сделку PF 2.48 maxDD $33 |
// OOS n=30 ROI +20.0% PF 1.86 maxDD $20. Соседние пороги тоже в плюсе на обоих
// периодах: Δ≥$75 (+18.4/+6.0), Δ≥$120 (+50/+26), коридор 55–75 (+17.4/+12.3).
// ~8 сделок/день; в совсем тихие дни может не торговать вообще — это нормально.
//
// Вторая ступень lagFav75 (Δ≥$75): IS +18.4% PF 1.66 | OOS +6.0% PF 1.21, ~15
// сделок/день — слабее на сделку, но быстрее набирает статистику. ВНИМАНИЕ: её
// входы — НАДмножество входов lagFav (каждый сигнал Δ≥90 сначала проходит 75),
// в demo это два независимых счёта для сравнения, на REAL включать только ОДНУ.
const STRAT_LAG_FAV = {
  id: 'lagFav', name: 'Lag Favorite (отстающий фаворит)',
  desc: 'BTC ушёл ≥$90 от открытия, а лидер ещё 50–70¢ — книга отстаёт. Берём лидера, держим до SETTLE. IS +32%/сделку PF 2.5 | OOS +20% PF 1.9.',
  defaults: { minDeltaUSD: 90, lo: 0.55, hi: 0.72,
              elFromSec: 30, elToSec: 240, minTimeMs: 45000,
              maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    if (ctx.curBTC == null || ctx.openingBTC == null) return null;
    const winLenSec = (typeof POLY_WINDOW_SEC === 'number' ? POLY_WINDOW_SEC : 300);
    const elapsed   = winLenSec - ctx.msToEnd / 1000;
    if (elapsed < p.elFromSec || elapsed > p.elToSec) return null;

    const deltaUSD = ctx.curBTC - ctx.openingBTC;
    if (Math.abs(deltaUSD) < p.minDeltaUSD) return null;

    const dir = deltaUSD > 0 ? 'UP' : 'DOWN';
    const np  = _normPoly(ctx); if (!np) return null;
    const price = dir === 'UP' ? np.up : np.dn;
    if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;

    const ourProb = _clampProb(Math.min(0.72, price + 0.12), price);
    return { side: dir, polyPrice: price, ourProb, edge: ourProb - price,
             info: `lagFav ${dir} Δ$${deltaUSD.toFixed(0)} @${(price * 100).toFixed(0)}¢` };
  },
  shouldExit() { return null; },   // hold до SETTLE — по бектесту лучший выход
};

const STRAT_LAG_FAV_75 = {
  id: 'lagFav75', name: 'Lag Favorite 75 (активная ступень)',
  desc: 'То же, но порог Δ≥$75: больше сделок, ниже EV. IS +18.4% PF 1.66 | OOS +6.0% PF 1.21. На REAL — только одну из двух ступеней.',
  defaults: { minDeltaUSD: 75, lo: 0.50, hi: 0.70,
              elFromSec: 30, elToSec: 240, minTimeMs: 45000,
              maxPerWindow: 1, kellyFrac: 0.08, maxFrac: 0.04 },
  shouldEnter(ctx, p) { return STRAT_LAG_FAV.shouldEnter(ctx, p); },
  shouldExit() { return null; },
};

// ── FLOMD TACTIC (v3) ─────────────────────────────────────────────────────────
// Дог-стратегия с полностью автоматическим управлением режимом. Все пороги
// найдены на посекундных данных 1–11 июня: подбор на IS (1–7), проверка на OOS
// (8–11); вся сетка соседних порогов (54 комбинации) в плюсе на ОБОИХ периодах.
//
// ВХОД: дешёвая сторона 25–35¢ (НЕ 15–35: дог ниже 25¢ токсичен — WR 7–22%,
//   EV −1.4…−6.7$/сделку на обоих периодах; возврат с 20¢ почти не случается).
//   Выход: hold до SETTLE + TP@96¢ (lock-выход перед закрытием помогает только
//   НЕфильтрованному потоку; после гейтов он режет победителей — отвергнут).
//
// ГЕЙТЫ (порядок от дешёвых к дорогим):
//   1) NIGHT 21–23 UTC (00–02 МСК): час 21 UTC = −5.0$/сделку, 22 UTC = −2.5.
//      Часы 20 и 23 ~нейтральны — разблокированы (в v1 блок был шире, 20–24).
//   2) CAP |Δ| ТЕКУЩЕГО окна ≥$60: EV гниёт с ростом движения (−4.3 у $75–100).
//   3) TREND-ПАУЗА: |сумма ПОДПИСАННЫХ движений последних 3 окон| в [$40..$300) —
//      однонаправленная перемолка, доги ложатся сериями. Возврат АВТОМАТИЧЕСКИЙ:
//      сумма < $40 (устаканилось) или ≥ $300 (перелёт → снапбэк, доги в плюсе).
//   4) МАШИНА по demo-логу underdogHold: 8 лузов подряд → halt; 3 вина подряд →
//      resume. («1 win» включается слишком рано, vol-триггеры не фильтруют.)
//
// Проверено и ОТВЕРГНУТО (чтобы не возвращаться): абсорбция CVD-против-движения
// (IS +0.9, OOS не подтвердилась), сторона дога UP/DOWN (симметрично), фаза окна
// при входе (нестабильна между периодами), lock-выход (см. выше).
//
// Итог на 11 днях ($10/сделку, ask-филлы + 0.8с): IS +$391 (n=84), OOS +$247
// (n=162) против −$793 у голого underdogHold 15–35.
// Гейт чистый (пересчитывается из лога underdogHold на каждом тике) — ничего не
// «застревает» между рестартами и при demo-delay.
function _flomdRegimeActive(p) {
  const ref = STRATEGIES['underdogHold'];
  if (!ref || !ref.demo || !ref.demo.log.length) return true;   // нет истории — работаем
  let active = true, ls = 0, ws = 0;
  for (const t of ref.demo.log) {
    if (t.dirty) continue;
    if (active) {
      ls = t.won ? 0 : ls + 1;
      if (ls >= p.skipAfter) { active = false; ws = 0; ls = 0; }
    } else {
      ws = t.won ? ws + 1 : 0;
      if (ws >= p.resumeWins) { active = true; ls = 0; ws = 0; }
    }
  }
  return active;
}
const STRAT_FLOMD = {
  id: 'flomd', name: 'FLOMD TACTIC',
  desc: 'Дог 25–35¢ (ниже 25¢ — токсично) с авто-режимом: стоп после 8 лузов underdogHold, возврат после 3 винов, ночной блок 21–23 UTC, ГЛАВНЫЙ ФИЛЬТР — вход только при малом движении BTC (|Δ|<$20 = рынок пилит у нуля, возврат к 50/50 реален; большое Δ = тренд, дог дохнет), пауза при перемолке, дог ПО направлению потока, SL 5¢, TP выкл. Фильтр |Δ|<$20 на РЕАЛЬНЫХ данных 1–13 июня: +$217 8/13 дней против −$865 5/13 без фильтра; чинит даже трендовую неделю (8-13 июня −$1160 → −$53).',
  // Свип 1¢ (train/test): SL-плато 3-6¢, центр 5¢. TP ВЫКЛЮЧЕН: с SL=5¢
  // «без TP» лучше TP96 на КАЖДОМ SL плато (+$40-60, оба периода) — продажа
  // победителя на 96¢ по bid−fee жертвует ~4-5¢/шэр против $1.00 резолва,
  // а защиту от разворота уже даёт SL. tpAbs можно вернуть из UI (напр. 0.96).
  // maxEntryMoveUSD=17: ТРИГГЕР РАЗВОРОТА (симметричный |Δ|, свип 1-50). Пик Δ<17:
  // +$291 EV+0.49 10/13 дней. Направленность (откуп Δ<0 vs рост Δ>0) ПРОВЕРЕНА и
  // НЕ зашита: эффект «откуп лучше» держался только 1-7 июня (EV +5.25 на 42 сделках),
  // на 8-13 перевернулся (откуп +0.14 < рост +0.27) — артефакт периода, не сигнал.
  defaults: { lo: 0.25, hi: 0.35, minTimeMs: 60000, tpAbs: 0, maxBtcAgeMs: 3000,
              skipAfter: 8, resumeWins: 3, blockFromUTC: 21, blockToUTC: 23,
              maxEntryMoveUSD: 17, trendPauseLoUSD: 40, trendPauseHiUSD: 300, trendPauseWindows: 3,
              skipAgainstGrind: 1, grindDirMinUSD: 20,
              stopLossPrice: 0.05,
              maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    // Сначала проверяем КАНДИДАТА (дог в коридоре) — если его нет, гейты молчат;
    // если есть, но гейт блокирует — пишем контрфакт в ML-лог (mlBlocked), чтобы
    // потом видеть, сколько каждый гейт сэкономил/недозаработал на самом деле.
    const np = _normPoly(ctx); if (!np) return null;
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    if (dogPrice < p.lo || dogPrice > p.hi || dogPrice < MIN_ENTRY_PRICE) return null;
    const blockedBy = (gate) => { try { mlBlocked('flomd', gate, ctx, dogSide, dogPrice); } catch (_) {} return null; };
    // ночной блок (UTC, поддержан переход через полночь)
    const h = new Date().getUTCHours();
    const f = p.blockFromUTC % 24, t = p.blockToUTC % 24;
    const night = (f === t) ? false : (f < t ? (h >= f && h < t) : (h >= f || h < t));
    if (night) return blockedBy('night');
    // ── Фильтр свежести цены: не входить на устаревшей цене Chainlink ─────────
    // Страховка от сбоев сбора (10-11 июня цена висела минутами → дельта тухла).
    if (p.maxBtcAgeMs && ctx.btcAgeMs != null && ctx.btcAgeMs > p.maxBtcAgeMs) return blockedBy('staleBtc');
    // ── Анти-тренд гейт 1: ТЕКУЩЕЕ окно уже уехало слишком далеко (|Δ|, симметрично)
    if (ctx.curBTC != null && ctx.openingBTC != null
        && Math.abs(ctx.curBTC - ctx.openingBTC) >= p.maxEntryMoveUSD) return blockedBy('entryMoveCap');
    // ── Анти-тренд гейт 2: однонаправленная перемолка соседних окон ───────────
    // Пауза в полосе [lo..hi); авто-возврат при <lo (штиль) или ≥hi (перелёт).
    const wh = poly.winHist || [];
    let grindSum = null;
    if (wh.length >= p.trendPauseWindows) {
      grindSum = 0;
      for (let i = wh.length - p.trendPauseWindows; i < wh.length; i++) grindSum += (wh[i].move || 0);
      const grind = Math.abs(grindSum);
      if (grind >= p.trendPauseLoUSD && grind < p.trendPauseHiUSD) return blockedBy('trendPause');
    }
    // ── Гейт 3 (v4): дог ПРОТИВ направления перемолки ─────────────────────────
    // Берём дога только ПО направлению макро-потока последних окон (ловля ножа
    // против потока: IS EV +1.7 vs +5.3, OOS −1.2 vs +2.0).
    if (p.skipAgainstGrind && grindSum != null && Math.abs(grindSum) >= (p.grindDirMinUSD || 20)) {
      const dogUp = dogSide === 'UP';
      if ((dogUp && grindSum < 0) || (!dogUp && grindSum > 0)) return blockedBy('againstGrind');
    }
    // авто-режим по логу underdogHold
    if (!_flomdRegimeActive(p)) return blockedBy('machine');
    const ourProb = _clampProb(dogPrice + 0.10, dogPrice);
    return { side: dogSide, polyPrice: dogPrice, ourProb, edge: ourProb - dogPrice,
             info: `FLOMD ${dogSide} @${(dogPrice * 100).toFixed(0)}¢` };
  },
  shouldExit(ctx, pos, p) {
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.tpAbs && mid >= p.tpAbs) return { reason: 'TP', exitPrice: mid };
    // СТОП-ЛОСС (добавлен по реальным данным 12 июня): если дог упал ниже
    // stopLossPrice — позиция мертва, режем не дожидаясь SETTLE. Бектест с
    // комиссией: +$498 vs +$370 у hold, OOS удвоился ($63→$139). Это
    // автоматизация ручного «режь покойника».
    if (mid != null && p.stopLossPrice && mid <= p.stopLossPrice) return { reason: 'SL', exitPrice: mid };
    return null;
  },
};

// ═══════════════════════════════════════════════════════════════════════════
// РЕЖИМ-СЛЕДЯЩИЕ СТРАТЕГИИ (FLOMD-семейство для моментум-стратегий).
// ─────────────────────────────────────────────────────────────────────────────
// Глубокий анализ 47k demo-сделок за 1–13 июня (все 13 дней, train 1–8 / test
// 9–13) подтвердил гипотезу ИНЕРЦИИ: если стратегия последние N сделок суммарно
// в плюсе — её EV следующих сделок ВЫШЕ (режим продолжается). У всех семи
// отобранных горячий EV > холодного без исключений. Робастность (плюс на train
// И на test): momScratch, momConfirm, longHold, momHi, momScratchHi, longHoldX,
// timeSession. Из дублей (longHold↔longHoldX corr 0.63; momScratchHi корр с
// longHold 0.58) оставлены наиболее независимые.
//
// Все 7 параллельно на полном периоде: +$7199, плюс 11/12 дней, корреляции
// «горячих режимов» низкие (0.0–0.3) — включаются в РАЗНОЕ время, дополняя друг
// друга в разных рыночных режимах. Здесь подключены 5 наименее коррелированных.
//
// ВХОД: базовый сигнал стратегии + гейт «горячести» (Σ PnL последних gateWindow
//   ДЕМО-сделок опоры > gateMinPnL). СТОП (авто): Σ ≤ порога → пауза до
//   восстановления. Порог 0 — оптимум по бектесту (как только последние N в
//   минус → выключаемся). Опора = одноимённая demo-стратегия (держать в DEMO).
//
// ОТВЕРГНУТО (проверено на ВСЕХ 13 днях, не только train): underdog self-сигнал
// (на train +$2230, на test ПЕРЕВЕРНУЛСЯ −$410); momentum-hold (минус на обоих).
// Берём только то, что робастно out-of-sample.
function _demoHotGate(refId, gateWindow, gateMinPnL) {
  const ref = STRATEGIES[refId];
  if (!ref || !ref.demo || !ref.demo.log) return false;
  const log = ref.demo.log.filter(t => !t.dirty);
  if (log.length < gateWindow) return false;
  let sum = 0;
  for (let i = log.length - gateWindow; i < log.length; i++) sum += (log[i].pnl || 0);
  return sum > gateMinPnL;
}
// ДНЕВНОЙ walk-forward гейт: торгуем сегодня, только если ВЧЕРАШНИЙ день опоры был
// прибыльным (Σ PnL вчера > 0). Для медленных «дневных» режимов (underdogHold):
// его внутридневной self-сигнал переворачивается на тесте, а дневной — держится
// (на test 9-13 июня: −$208 против −$300 always-on, режет плохие дни до нуля).
// dayWin — сколько прошлых КАЛЕНДАРНЫХ дней суммировать (1 = только вчера).
function _demoDayGate(refId, dayWin) {
  const ref = STRATEGIES[refId];
  if (!ref || !ref.demo || !ref.demo.log) return false;
  const log = ref.demo.log.filter(t => !t.dirty && t.closeTime);
  if (!log.length) return false;
  const DAY = 86400000;
  const todayStart = Math.floor(Date.now() / DAY) * DAY;
  const from = todayStart - dayWin * DAY;
  let sum = 0, seen = 0;
  for (const t of log) {
    if (t.closeTime >= from && t.closeTime < todayStart) { sum += (t.pnl || 0); seen++; }
  }
  if (seen < 5) return true;   // мало истории за вчера — не блокируем
  return sum > 0;
}
// Фабрика: оборачивает базовую стратегию режим-гейтом по её demo-сенсору.
// Универсальный «горячий» гейт с тремя типами сигнала по demo-логу опоры:
//   'sum'   — сумма PnL последних N demo-сделок > thr
//   'wr'    — число ВИНОВ среди последних N demo-сделок > thr (винрейт-сигнал;
//             на тесте оказался устойчивее суммы для скальп-стратегий)
//   'accel' — «ускорение»: Σ последних 5 минус Σ предыдущих 5 > thr (тренд
//             результата улучшается). Лучший для momConfirm/timeSession.
// Все три подобраны перебором с проверкой на TEST (9-13 июня) и по дням (anti-overfit).
function _demoSignalGate(refId, sigType, N, thr) {
  const ref = STRATEGIES[refId];
  if (!ref || !ref.demo || !ref.demo.log) return false;
  const log = ref.demo.log.filter(t => !t.dirty);
  const need = sigType === 'accel' ? 10 : N;
  if (log.length < need) return false;
  const pnl = i => (log[log.length - i] ? (log[log.length - i].pnl || 0) : 0); // i=1 последняя
  if (sigType === 'sum') {
    let s = 0; for (let i = 1; i <= N; i++) s += pnl(i);
    return s > thr;
  }
  if (sigType === 'wr') {
    let wins = 0; for (let i = 1; i <= N; i++) if (pnl(i) > 0) wins++;
    return wins > thr;
  }
  if (sigType === 'accel') {
    let recent = 0, prev = 0;
    for (let i = 1; i <= 5; i++) recent += pnl(i);
    for (let i = 6; i <= 10; i++) prev += pnl(i);
    return (recent - prev) > thr;
  }
  return false;
}
// КОМБО-условие: проверяет «горячесть» ДРУГОЙ опоры (sum последних 8 demo > 0)
// и сравнивает с желаемым состоянием. Открытие: режим стратегии лучше
// предсказывается СОСТОЯНИЕМ ДРУГИХ стратегий (зеркальные/согласованные режимы),
// чем собственным. Напр.: momConfirm работает когда momentum ХОЛОДНЫЙ;
// longHold — когда momScratch холодный; momScratch усиливается когда longHold горячий.
// ВРЕМЕННОЙ гейт: сумма PnL demo-сделок опоры за последние N МИНУТ > порога.
// Отличие от _demoSignalGate (последние N сделок): учитывает ПЛОТНОСТЬ сделок —
// в активный период окно охватит больше сделок, в тихий меньше. Проверено: для
// momConfirm/longHold/momScratchHi временное окно чуть устойчивее на test, чем
// счётное. Для momScratch/momentum — счётное лучше (оставлены на нём).
function _demoTimeGate(refId, windowMin, thr) {
  const ref = STRATEGIES[refId];
  if (!ref || !ref.demo || !ref.demo.log) return false;
  const cutoff = Date.now() - windowMin * 60000;
  const log = ref.demo.log.filter(t => !t.dirty && t.closeTime && t.closeTime >= cutoff);
  if (log.length < 3) return false;          // мало сделок в окне — молчим
  let sum = 0;
  for (const t of log) sum += (t.pnl || 0);
  return sum > thr;
}
function _comboOk(combo) {
  if (!combo || !combo.length) return true;
  for (const c of combo) {
    const hot = _demoSignalGate(c.ref, 'sum', c.win || 8, 0);  // горячая ли опора
    if (hot !== c.wantHot) return false;
  }
  return true;
}
function makeRegimeStrat(base, opts) {
  return {
    id: opts.id, name: opts.name, desc: opts.desc,
    defaults: { ...base.defaults, gateRefId: opts.gateRefId,
                gateSigType: opts.gateSigType || 'sum', gateWindow: opts.gateWindow || 0,
                gateThr: opts.gateThr != null ? opts.gateThr : 0,
                dayGateWin: opts.dayGateWin || 0,
                timeGateMin: opts.timeGateMin || 0, timeGateThr: opts.timeGateThr || 0,
                kellyFrac: opts.kellyFrac != null ? opts.kellyFrac : 0.08,
                maxFrac: opts.maxFrac != null ? opts.maxFrac : 0.04 },
    _combo: opts.combo || null,
    shouldEnter(ctx, p) {
      // режим-гейт: сигнальный (sum/wr/accel), временной (N минут), дневной (вчера>0), комбо
      if (p.gateWindow && !_demoSignalGate(p.gateRefId, p.gateSigType, p.gateWindow, p.gateThr)) return null;
      if (p.timeGateMin && !_demoTimeGate(p.gateRefId, p.timeGateMin, p.timeGateThr || 0)) return null;
      if (p.dayGateWin && !_demoDayGate(p.gateRefId, p.dayGateWin)) return null;
      if (this._combo && !_comboOk(this._combo)) return null;
      return base.shouldEnter(ctx, p);
    },
    shouldExit(ctx, pos, p) { return base.shouldExit(ctx, pos, p); },
  };
}

const STRAT_MOM_FLOMD_SCRATCH = makeRegimeStrat(STRAT_MOM_SCRATCH, {
  id: 'momFlomdScratch', name: 'MOMENTUM FLOMD SCRATCH',
  desc: 'momScratch только когда ≥2 вина в последних 5 demo-сделках momScratch. test EV+3.9, TEST 5/5 дней+.',
  gateRefId: 'momScratch', gateSigType: 'wr', gateWindow: 5, gateThr: 1 });

const STRAT_MOM_FLOMD_CONFIRM = makeRegimeStrat(STRAT_MOM_CONFIRM, {
  id: 'momFlomdConfirm', name: 'MOMENTUM FLOMD CONFIRM',
  desc: 'momConfirm когда «ускорение» demo momConfirm > 20 (тренд результата улучшается). test EV+3.2.',
  gateRefId: 'momConfirm', gateSigType: 'accel', gateWindow: 10, gateThr: 20 });

const STRAT_MOM_FLOMD_HI = makeRegimeStrat(STRAT_MOM_HI, {
  id: 'momFlomdHi', name: 'MOMENTUM FLOMD HI',
  desc: 'momHi когда Σ5 demo momHi > 5. test EV+3.4.',
  gateRefId: 'momHi', gateSigType: 'sum', gateWindow: 5, gateThr: 5 });

const STRAT_LONG_FLOMD = makeRegimeStrat(STRAT_LONG_HOLD, {
  id: 'longFlomd', name: 'LONGSHOT FLOMD',
  desc: 'longHold когда Σ5 demo longHold > 0. test EV+2.7.',
  gateRefId: 'longHold', gateSigType: 'sum', gateWindow: 5, gateThr: 0 });

const STRAT_SESSION_FLOMD = makeRegimeStrat(STRAT_TIME_SESSION, {
  id: 'sessionFlomd', name: 'SESSION FLOMD',
  desc: 'timeSession когда «ускорение» demo timeSession > 10. test EV+15.6 (мало сделок, высокая выборочность).',
  gateRefId: 'timeSession', gateSigType: 'sum', gateWindow: 10, gateThr: 20 });

// ── КОМБО-СТРАТЕГИИ (режим по СОСТОЯНИЮ ДРУГИХ стратегий) ──────────────────────
// Глубже self-сигнала: входим по согласованности НЕСКОЛЬКИХ demo-опор.
// Проверено train/test + по дням (анти-overfit, топ-день <50% прибыли).
const STRAT_COMBO_CONFIRM = makeRegimeStrat(STRAT_MOM_CONFIRM, {
  id: 'comboConfirm', name: 'COMBO CONFIRM (momConfirm × momentum-холодный)',
  desc: 'momConfirm входит когда momentum ХОЛОДНЫЙ (зеркальные режимы). Сам momConfirm база −$195 на тесте → комбо +$462. 8/11 дней+.',
  gateRefId: 'momConfirm', gateSigType: 'accel', gateWindow: 10, gateThr: 20,
  combo: [{ ref: 'momentum', wantHot: false }] });

const STRAT_COMBO_LONG = makeRegimeStrat(STRAT_LONG_HOLD, {
  id: 'comboLong', name: 'COMBO LONG (longHold × momScratch-холодный)',
  desc: 'longHold входит когда momScratch ХОЛОДНЫЙ. test +$332, TEST 3/3 дня+, топ-день 33%.',
  gateRefId: 'longHold', gateSigType: 'sum', gateWindow: 5, gateThr: 0,
  combo: [{ ref: 'momScratch', wantHot: false }] });

const STRAT_COMBO_SCRATCH = makeRegimeStrat(STRAT_MOM_SCRATCH, {
  id: 'comboScratch', name: 'COMBO SCRATCH (momScratch × longHold-горячий)',
  desc: 'momScratch входит когда И сам горячий, И longHold горячий (согласованные режимы). test +$797, TEST 4/5 дней+.',
  gateRefId: 'momScratch', gateSigType: 'wr', gateWindow: 5, gateThr: 1,
  combo: [{ ref: 'longHold', wantHot: true }] });

// НОВЫЕ (добавлены при глубоком переборе — раньше считались безнадёжными):
const STRAT_MOM_FLOMD_PURE = makeRegimeStrat(STRAT_MOMENTUM, {
  id: 'momFlomdPure', name: 'MOMENTUM FLOMD PURE',
  desc: 'Чистый momentum (hold) когда Σ15 demo momentum > 5. Сам momentum убыточен (−$537), но в горячем режиме: test EV+4.3 $1444! Окно 15 — ключ (на 8 не ловится).',
  gateRefId: 'momentum', gateSigType: 'sum', gateWindow: 15, gateThr: 0 });  // порог 0: 8/12 дней (стабильнее >5)

const STRAT_MOM_FLOMD_SCRATCH_HI = makeRegimeStrat(STRAT_MOM_SCRATCH_HI, {
  id: 'momFlomdScratchHi', name: 'MOMENTUM FLOMD SCRATCH HI',
  desc: 'momScratchHi когда Σ8 demo momScratchHi > 20 (высокий порог = только явно горячий режим). test EV+5.6.',
  gateRefId: 'momScratchHi', gateSigType: 'sum', gateWindow: 8, gateThr: 20 });

const STRAT_UNDERDOG_FLOMD = makeRegimeStrat(STRAT_UNDERDOG_HOLD, {
  id: 'underdogFlomd', name: 'UNDERDOG FLOMD (TRADE ON/OFF)',
  desc: 'underdogHold с авто TRADE ON/OFF (наблюдение из эфира: «прёт → бери, выдохся → стоп»). TRADE OFF = 5 лузов underdogHold подряд (0 винов из 5). TRADE ON = появился ≥1 вин из последних 5. Вся выборка 13 дней: +$3305 (≈ как ≥1из3), но maxDD $360 vs $503 и худший день −$134 vs −$262 — выбрано ради «главное не терять». Проверено: PnL-за-время и стрики 2-5 хуже; ≥1из5 — оптимум риск/доход.',
  gateRefId: 'underdogHold', gateSigType: 'wr', gateWindow: 5, gateThr: 0 });

// ── UNDERDOG DIP (ЭКСПЕРИМЕНТ: откуп после малого падения) ─────────────────────
// ГИПОТЕЗА на тест (НЕ подтверждена на всей выборке): дог отыгрывает лучше, когда
// BTC немного припал ПРОТИВ него ($3-20) — выкуп просадки → отскок. На реальных
// данных 1-13 июня в СУММЕ выглядела сильно (+$377 EV+1.39 maxDD$76), НО при
// раздельной проверке эффект держался только 1-7 июня (EV+5.25 на 42 сделках) и
// ПЕРЕВЕРНУЛСЯ на 8-13 (откуп +0.14 < рост +0.27). Вероятно шум/артефакт периода.
// Поэтому вынесена ОТДЕЛЬНО для форвард-теста — НЕ включать на реал, пока свежие
// данные не подтвердят, что направленность реальна. Симметричные версии (FLOMD,
// UNDERDOG DELTA) остаются на |Δ|<17.
const STRAT_UNDERDOG_DIP = {
  id: 'underdogDip', name: 'UNDERDOG DIP (эксперимент, откуп)',
  desc: 'ЭКСПЕРИМЕНТ для форвард-теста: дог 15-35¢ когда BTC припал против дога на $3-20 (ставка на отскок). На полной выборке +$377, но направленность держалась только 1-7 июня и перевернулась 8-13 — возможно шум. НЕ для реала до подтверждения на свежих данных.',
  defaults: { lo: 0.15, hi: 0.35, minTimeMs: 60000, tpAbs: 0.96,
              btcDipMin: 3, btcDipMax: 20,
              maxPerWindow: 1, kellyFrac: 0.08, maxFrac: 0.04 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    if (dogPrice < p.lo || dogPrice > p.hi || dogPrice < MIN_ENTRY_PRICE) return null;
    if (ctx.curBTC != null && ctx.openingBTC != null) {
      const delta = ctx.curBTC - ctx.openingBTC;
      const dipAgainstDog = dogSide === 'UP' ? -delta : delta;  // BTC ушёл ПРОТИВ дога
      if (dipAgainstDog < p.btcDipMin || dipAgainstDog > p.btcDipMax) return null;
    }
    const ourProb = _clampProb(dogPrice + 0.10, dogPrice);
    return { side: dogSide, polyPrice: dogPrice, ourProb, edge: ourProb - dogPrice,
             info: `UDG-DIP ${dogSide} @${(dogPrice*100).toFixed(0)}¢ dip$${p.btcDipMin}-${p.btcDipMax}` };
  },
  shouldExit(ctx, pos, p) {
    const cur = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (cur != null && p.tpAbs && cur >= p.tpAbs) return { reason: 'TP', exitPrice: cur };
    return null;
  },
};

// ── UNDERDOG DELTA (дог при штиле BTC) ────────────────────────────────────────
// ОТКРЫТИЕ на полных реальных данных Polymarket 1–13 июня: дельта-фильтр —
// универсальный ключ для дешёвых догов. underdogHold САМ ПО СЕБЕ убыточен
// (−$927, 5/13 дней), НО при МАЛОМ движении BTC (|Δ|<$15-20) выходит в плюс:
//   |Δ|<$15: +$208, 9/13 дней+, EV +0.39
//   |Δ|<$20: +$227, 8/13 дней+, EV +0.31 (больше сделок)
// Логика (зеркало FLOMD FAVE): малое движение = BTC болтается у нуля = возврат к
// 50/50 реален = дешёвый дог отыгрывает. Большое движение = тренд = дог дохнет.
// Это та же идея, что спасла FLOMD-дога (|Δ|<$20), но как ОТДЕЛЬНАЯ стратегия на
// коридоре underdogHold 15-35 (шире, чем FLOMD 25-35 — больше дешёвых догов).
// ВАЖНО: это НЕ датчик underdogHold (тот без фильтра кормит FLOMD/skip3/underdogFlomd).
// Это самостоятельная рабочая стратегия. Держим до резолва (TP 96¢), SL не нужен
// (при штиле дог редко обнуляется). Зеркало: для ФАВОРИТА нужна БОЛЬШАЯ дельта
// (см. FLOMD INVERSE Δ≥30 / FAVE) — один признак, два направления.
const STRAT_UNDERDOG_DELTA = {
  id: 'underdogDelta', name: 'UNDERDOG DELTA (дог при штиле)',
  desc: 'Дешёвый дог 15–35¢ ТОЛЬКО когда BTC мало двигался (|Δ|<$17, обе стороны). Реальные данные 1–13 июня: +$287, 9/13 дней+, EV +0.48 — против −$927 у underdogHold без фильтра. Направленность (откуп vs рост) проверена и отброшена как шум (перевернулась во 2-м периоде). Держим до резолва.',
  defaults: { lo: 0.15, hi: 0.35, minTimeMs: 60000, tpAbs: 0.96, btcMoveMax: 17, maxBtcAgeMs: 3000,
              maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    if (dogPrice < p.lo || dogPrice > p.hi || dogPrice < MIN_ENTRY_PRICE) return null;
    // ФИЛЬТР СВЕЖЕСТИ: дельта-стратегии не входят на устаревшей цене Chainlink.
    // Защита не от оракула (он обычно свежий ~0.5с), а от сбоев сбора данных:
    // 10-11 июня цена "висела" минутами → дельта замораживалась. ≤3с страхует.
    if (p.maxBtcAgeMs && ctx.btcAgeMs != null && ctx.btcAgeMs > p.maxBtcAgeMs) return null;
    // ДЕЛЬТА-ФИЛЬТР (симметричный): дог только при малом движении BTC (рынок пилит → возврат)
    if (p.btcMoveMax && ctx.curBTC != null && ctx.openingBTC != null) {
      if (Math.abs(ctx.curBTC - ctx.openingBTC) >= p.btcMoveMax) return null;
    }
    const ourProb = _clampProb(dogPrice + 0.10, dogPrice);
    return { side: dogSide, polyPrice: dogPrice, ourProb, edge: ourProb - dogPrice,
             info: `UDG-Δ ${dogSide} @${(dogPrice*100).toFixed(0)}¢ |Δ|<$${p.btcMoveMax}` };
  },
  shouldExit(ctx, pos, p) {
    const cur = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (cur != null && p.tpAbs && cur >= p.tpAbs) return { reason: 'TP', exitPrice: cur };
    return null;
  },
};

// ═══════════════════════════════════════════════════════════════════════════
// UNDERDOG DELTA — АНАЛОГИ С АВТО-СТОПОМ ПО DEMO-ЛОГУ underdogHold ────────────
// ─────────────────────────────────────────────────────────────────────────────
// Вход/выход = базовый UNDERDOG DELTA (дешёвый дог 15–35¢ при штиле BTC |Δ|<$17,
// держим до резолва, фикс на 96¢), НО с авто-гейтом, который читает demo-лог
// опоры underdogHold и стопает/возобновляет стратегию.
//
// ВАЖНО (требование «изначально дождаться результатов»): гейт стартует ЗАКРЫТЫМ —
// стратегия НЕ входит, пока underdogHold не выдаст нужный результат:
//   • стрик-версии  — нужно resumeWins винов подряд (по умолчанию 2),
//   • pnl-версии    — нужна неотрицательная Σ PnL в окне (и хотя бы 1 сделка).
// Опору underdogHold держим в DEMO постоянно (это датчик, на REAL не нужен).

// Стрик-гейт с гистерезисом: стоп после skipAfter лузов подряд, возврат после
// resumeWins винов подряд. Старт ЗАКРЫТ (active=false) — ждём resumeWins подряд.
// Лог проигрывается целиком, поэтому состояние всегда сходится к текущему.
function _udgDeltaStreakActive(skipAfter, resumeWins) {
  const ref = STRATEGIES['underdogHold'];
  if (!ref || !ref.demo || !ref.demo.log.length) return false;   // нет истории — ЖДЁМ
  let active = false, ls = 0, ws = 0;
  for (const t of ref.demo.log) {
    if (t.dirty) continue;                                        // sim/feed-записи не считаем
    if (active) {
      ls = t.won ? 0 : ls + 1;
      if (ls >= skipAfter) { active = false; ws = 0; ls = 0; }
    } else {
      ws = t.won ? ws + 1 : 0;
      if (ws >= resumeWins) { active = true; ls = 0; ws = 0; }
    }
  }
  return active;
}

// PnL-оконный гейт: торгуем, только если Σ PnL demo-сделок underdogHold за
// последние windowMin минут НЕ отрицательна. Стоп при Σ<0, возврат при Σ≥0.
// Нет закрытых сделок в окне → ЖДЁМ (старт закрыт — «изначально дождаться»).
function _udgDeltaPnlWindowOk(windowMin) {
  const ref = STRATEGIES['underdogHold'];
  if (!ref || !ref.demo || !ref.demo.log) return false;
  const cutoff = Date.now() - windowMin * 60000;
  let sum = 0, seen = 0;
  for (const t of ref.demo.log) {
    if (t.dirty || !t.closeTime || t.closeTime < cutoff) continue;
    sum += (t.pnl || 0); seen++;
  }
  if (seen === 0) return false;       // ещё нет результатов в окне — ждём
  return sum >= 0;                    // Σ PnL не отрицательна → можно торговать
}

// Фабрика: UNDERDOG DELTA + авто-гейт по underdogHold (стрик ИЛИ pnl-окно).
function makeUdgDeltaGated(opts) {
  return {
    id: opts.id, name: opts.name, desc: opts.desc,
    defaults: { ...STRAT_UNDERDOG_DELTA.defaults,
                udgStreakSkip:   opts.streakSkip   || 0,
                udgStreakResume: opts.streakResume || 0,
                udgPnlWindowMin: opts.pnlWindowMin || 0 },
    shouldEnter(ctx, p) {
      if (p.udgStreakSkip && !_udgDeltaStreakActive(p.udgStreakSkip, p.udgStreakResume || 2)) return null;
      if (p.udgPnlWindowMin && !_udgDeltaPnlWindowOk(p.udgPnlWindowMin)) return null;
      return STRAT_UNDERDOG_DELTA.shouldEnter(ctx, p);
    },
    shouldExit(ctx, pos, p) { return STRAT_UNDERDOG_DELTA.shouldExit(ctx, pos, p); },
  };
}

// 9 аналогов: 4 стрик-стопа (3/5/4/6 лузов → возврат после 2 винов) + 5 pnl-окон.
const UDG_DELTA_GATED = [
  makeUdgDeltaGated({ id: 'udgDeltaS3', name: 'UDG DELTA STOP-3 (3луз/2вин)',
    desc: 'UNDERDOG DELTA + авто-стоп: пауза после 3 лузов underdogHold подряд, возврат после 2 винов подряд. Старт закрыт — ждём 2 вина.',
    streakSkip: 3, streakResume: 2 }),
  makeUdgDeltaGated({ id: 'udgDeltaS5', name: 'UDG DELTA STOP-5 (5луз/2вин)',
    desc: 'UNDERDOG DELTA + авто-стоп: пауза после 5 лузов underdogHold подряд, возврат после 2 винов подряд. Старт закрыт.',
    streakSkip: 5, streakResume: 2 }),
  makeUdgDeltaGated({ id: 'udgDeltaS4', name: 'UDG DELTA STOP-4 (4луз/2вин)',
    desc: 'UNDERDOG DELTA + авто-стоп: пауза после 4 лузов underdogHold подряд, возврат после 2 винов подряд. Старт закрыт.',
    streakSkip: 4, streakResume: 2 }),
  makeUdgDeltaGated({ id: 'udgDeltaS6', name: 'UDG DELTA STOP-6 (6луз/2вин)',
    desc: 'UNDERDOG DELTA + авто-стоп: пауза после 6 лузов underdogHold подряд, возврат после 2 винов подряд. Старт закрыт.',
    streakSkip: 6, streakResume: 2 }),
  makeUdgDeltaGated({ id: 'udgDeltaPnl60', name: 'UDG DELTA PNL-1ч',
    desc: 'UNDERDOG DELTA + авто-стоп: если Σ PnL underdogHold за последний час отрицательна — пауза, пока не станет ≥0. Старт закрыт — ждём результатов.',
    pnlWindowMin: 60 }),
  makeUdgDeltaGated({ id: 'udgDeltaPnl45', name: 'UDG DELTA PNL-45м',
    desc: 'UNDERDOG DELTA + авто-стоп: если Σ PnL underdogHold за последние 45 минут отрицательна — пауза, пока не станет ≥0.',
    pnlWindowMin: 45 }),
  makeUdgDeltaGated({ id: 'udgDeltaPnl35', name: 'UDG DELTA PNL-35м',
    desc: 'UNDERDOG DELTA + авто-стоп: если Σ PnL underdogHold за последние 35 минут отрицательна — пауза, пока не станет ≥0, потом продолжаем.',
    pnlWindowMin: 35 }),
  makeUdgDeltaGated({ id: 'udgDeltaPnl120', name: 'UDG DELTA PNL-2ч',
    desc: 'UNDERDOG DELTA + авто-стоп: если Σ PnL underdogHold за последние 2 часа отрицательна — пауза, пока не станет ≥0.',
    pnlWindowMin: 120 }),
  makeUdgDeltaGated({ id: 'udgDeltaPnl150', name: 'UDG DELTA PNL-2ч30м',
    desc: 'UNDERDOG DELTA + авто-стоп: если Σ PnL underdogHold за последние 2ч30м отрицательна — пауза, пока не станет ≥0.',
    pnlWindowMin: 150 }),
];

// ── UNDERDOG DELTA — МАТРИЦА КОРИДОР × TP, абсолютный SL 8¢ ────────────────────
// Тот же штиль-вход (|Δ|<$17, фильтр свежести), но: коридоры 22–35 / 22–40 /
// 22–32 / 22–30¢ и НЕ держим до резолва. Выход:
//   • TP — ПРОЦЕНТНЫЙ рост цены дога от входа (38…88%),
//   • SL — АБСОЛЮТНОЕ падение цены дога на 8¢ от входа (slAbsCents=0.08),
//   • плюс страховочный потолок 96¢.
// 4 коридора × 7 TP = 28 вариантов для A/B-сбора данных по соотношению риск/доход.
function _udgDeltaAbsSlPctTpExit(ctx, pos, p) {
  const cur = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
  if (cur == null) return null;
  // Абсолютный стоп-лосс: цена дога упала на slAbsCents от цены входа.
  if (p.slAbsCents && cur <= pos.polyEntryPrice - p.slAbsCents) return { reason: 'SL', exitPrice: cur };
  // Процентный тейк-профит от цены входа.
  if (p.tpPct) {
    const mv = (cur - pos.polyEntryPrice) / pos.polyEntryPrice;
    if (mv >= p.tpPct) return { reason: 'TP', exitPrice: cur };
  }
  // Страховочный абсолютный потолок (бинарный токен не дороже 100¢).
  if (p.tpAbs && cur >= p.tpAbs) return { reason: 'TP', exitPrice: cur };
  return null;
}

function makeUdgDeltaTpSl(loC, hiC, tpPct) {
  const loN = Math.round(loC * 100), hiN = Math.round(hiC * 100), tpN = Math.round(tpPct * 100);
  return {
    id: `udgDelta${loN}${hiN}t${tpN}`,
    name: `UDG Δ ${loN}-${hiN} TP${tpN} SL8¢`,
    desc: `UNDERDOG DELTA (штиль |Δ|<$17) в коридоре ${loN}–${hiN}¢, TP ${tpN}% роста от входа, абсолютный SL 8¢. A/B-сбор данных по риск/доходу.`,
    defaults: { ...STRAT_UNDERDOG_DELTA.defaults, lo: loC, hi: hiC,
                tpPct, slAbsCents: 0.08, tpAbs: 0.96 },
    shouldEnter(ctx, p) { return STRAT_UNDERDOG_DELTA.shouldEnter(ctx, p); },
    shouldExit(ctx, pos, p) { return _udgDeltaAbsSlPctTpExit(ctx, pos, p); },
  };
}

const UDG_DELTA_CORRIDORS = [[0.22, 0.35], [0.22, 0.40], [0.22, 0.32], [0.22, 0.30]];
const UDG_DELTA_TPS       = [0.38, 0.44, 0.50, 0.58, 0.68, 0.77, 0.88];
const UDG_DELTA_TPSL      = [];
for (const [lo, hi] of UDG_DELTA_CORRIDORS)
  for (const tp of UDG_DELTA_TPS)
    UDG_DELTA_TPSL.push(makeUdgDeltaTpSl(lo, hi, tp));

// ── FLOMD FAVE (недооценённый глубокий фаворит) ───────────────────────────────
// САМОЕ ФУНДАМЕНТАЛЬНОЕ открытие сессии (реальные посекундные данные Polymarket
// 8–13 июня): сторона, КУДА движется BTC в момент входа, выигрывает окно в ~98%
// случаев — рынок BTC на 5-минутках почти чисто ТРЕНДОВЫЙ, развороты к концу
// окна крайне редки. Это объясняет, почему все дог-стратегии (ставка на возврат)
// системно убыточны.
//
// Книга Polymarket откалибрована почти идеально (edge ±2pp везде), КРОМЕ одной
// устойчивой щели: ГЛУБОКИЙ фаворит (75–96¢) в поздней фазе окна (150–280с)
// книгой НЕдооценён — реальный WR 85–93% против break-even ~80%. Edge +4…6pp.
//   Реальные данные: +$304 за 6 дней, 5/6 дней+, EV +0.23/сделку (WR 85%).
//   СТРЕСС-ТЕСТ: EV держится +0.23 даже при задержке 5с и слиппедже 15% — это
//   признак НАСТОЯЩЕГО эджа (книга недооценивает), а не артефакта исполнения.
//   В отличие от FLOMD INVERSE (фаворит 60–72¢, edge тоньше), здесь щель шире и
//   подтверждена и на train, и на test.
// Это «противоположность underdogHold»: вместо дешёвого underdog берём дорогого,
// почти решённого фаворита под конец окна. Держим до резолва (он уже близок).
const STRAT_FLOMD_FAVE = {
  id: 'flomdFave', name: 'FLOMD FAVE (глубокий фаворит)',
  desc: 'Глубокий фаворит 75–96¢ в поздней фазе окна (150–280с) — книга его недооценивает (WR 85% vs break-even 80%). Реальные данные: +$304/6дн, EV держится при задержке 5с. Лучший honest edge из реальных данных.',
  defaults: { lo: 0.75, hi: 0.96, elFromSec: 150, elToSec: 280, minTimeMs: 15000,
              maxPerWindow: 1, kellyFrac: 0.10, maxFrac: 0.05 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const winLenSec = (typeof POLY_WINDOW_SEC === 'number' ? POLY_WINDOW_SEC : 300);
    const elapsed = winLenSec - ctx.msToEnd / 1000;
    if (elapsed < p.elFromSec || elapsed > p.elToSec) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const favSide  = np.up >= np.dn ? 'UP' : 'DOWN';
    const favPrice = Math.max(np.up, np.dn);
    if (favPrice < p.lo || favPrice > p.hi) return null;
    if (favPrice > 0.96) return null;                  // выше 96¢ — нет смысла (мало навара)
    const ourProb = _clampProb(Math.min(0.97, favPrice + 0.05), favPrice);
    return { side: favSide, polyPrice: favPrice, ourProb, edge: ourProb - favPrice,
             info: `FLOMD-FAVE ${favSide} @${(favPrice * 100).toFixed(0)}¢ el${elapsed.toFixed(0)}s` };
  },
  shouldExit() { return null; },   // hold до резолва — он уже близок
};

// ── FLOMD INVERSE (фаворит вместо дога) ───────────────────────────────────────
// Открытие на РЕАЛЬНЫХ посекундных данных Polymarket 8–13 июня (тот период, где
// дог-FLOMD страдал): в окнах, где дог стоит 25–35¢ (а фаворит 60–72¢), выигрывает
// ФАВОРИТ в ~67–70% случаев. Тот же сетап, что у FLOMD, но ставка на ПРОТИВО-
// положную (дорогую) сторону.
//   • Дог hold (текущий FLOMD): на этих окнах −$960 за 6 дней, 2/6 дней+.
//   • Фаворит hold: +$159…183, 4/6 дней+, train +$34 / test +$148 (устойчиво OOS).
// ЧЕСТНО: плюс СКРОМНЫЙ (EV +0.14 на $10) — фаворит дорогой, комиссия и задержка
// съедают много. SL фавориту ВРЕДИТ (−$103) — просевшие фавориты возвращаются,
// держим до резолва. CVD/OBI-фильтры ПРОВЕРЕНЫ и отвергнуты (мираж на train,
// разворот на test). Это не золотая жила, а структурно верная сторона ставки.
// Включать ОТДЕЛЬНО от FLOMD (это его зеркало — обе одновременно бессмысленно:
// в одном окне взяли бы обе стороны).
const STRAT_FLOMD_INVERSE = {
  id: 'flomdInverse', name: 'FLOMD INVERSE (умный фаворит)',
  desc: 'Фаворит 60–72¢ + фильтр: вход ТОЛЬКО когда BTC уже двинулся ≥$30 в его сторону (тренд подтверждён, не шум). Реальные данные 8–13 июня: фильтр поднял EV +0.15→+0.53, WR 67→72%, maxDD $75→$0, 4/5 дней+. Держим до резолва (SL вредит). Движение ≥$50 пересушивает (мало сделок).',
  defaults: { lo: 0.60, hi: 0.72, minTimeMs: 60000, elFromSec: 30, btcMoveMin: 30,
              maxPerWindow: 1, kellyFrac: 0.08, maxFrac: 0.04 },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const winLenSec = (typeof POLY_WINDOW_SEC === 'number' ? POLY_WINDOW_SEC : 300);
    const elapsed = winLenSec - ctx.msToEnd / 1000;
    if (elapsed < p.elFromSec) return null;
    const np = _normPoly(ctx); if (!np) return null;
    // ФАВОРИТ = дорогая сторона
    const favSide  = np.up >= np.dn ? 'UP' : 'DOWN';
    const favPrice = Math.max(np.up, np.dn);
    if (favPrice < p.lo || favPrice > p.hi || favPrice > 0.90) return null;
    // УМНЫЙ ФИЛЬТР: BTC должен реально двинуться в сторону фаворита (тренд подтверждён)
    if (p.btcMoveMin && ctx.curBTC != null && ctx.openingBTC != null) {
      const delta = ctx.curBTC - ctx.openingBTC;
      const moveForFav = favSide === 'UP' ? delta : -delta;
      if (moveForFav < p.btcMoveMin) return null;
    }
    const ourProb = _clampProb(Math.min(0.95, favPrice + 0.05), favPrice);
    return { side: favSide, polyPrice: favPrice, ourProb, edge: ourProb - favPrice,
             info: `FLOMD-INV ${favSide} @${(favPrice * 100).toFixed(0)}¢ Δ≥$${p.btcMoveMin}` };
  },
  shouldExit() { return null; },   // hold до резолва — SL фавориту вредит
};

// ── FAVMOM (фаворит-моментум) ─────────────────────────────────────────────────
// НОВАЯ стратегия (бектест на данных 1–12 июня с комиссией). Идея ПРОТИВОПОЛОЖНА
// lagFav: не ждём отставания книги, а едем НА продолжении тренда. BTC рванул от
// открытия (Δ≥порог), книга УЖЕ оценила лидера дорого (72–88¢) — но движение
// сильное и до конца окна обычно не разворачивается. Берём дорогого лидера,
// держим до SETTLE. WR ~85%, торгует часто (не редкий сетап как lagFav).
// favMomA Δ90 72-88: n=447, +$122, 8/11 дней+, WR 85%.
// favMomB Δ120 75-90: n=214, +$69, 9/11 дней+, WR 88% (реже, но надёжнее).
function _favMomEntry(ctx, p, tag) {
  if (ctx.msToEnd < (p.minTimeMs || 45000)) return null;
  if (ctx.curBTC == null || ctx.openingBTC == null) return null;
  const winLenSec = (typeof POLY_WINDOW_SEC === 'number' ? POLY_WINDOW_SEC : 300);
  const elapsed   = winLenSec - ctx.msToEnd / 1000;
  if (elapsed < p.elFromSec || elapsed > p.elToSec) return null;
  const deltaUSD = ctx.curBTC - ctx.openingBTC;
  if (Math.abs(deltaUSD) < p.minDeltaUSD) return null;
  const dir = deltaUSD > 0 ? 'UP' : 'DOWN';
  const np = _normPoly(ctx); if (!np) return null;
  const price = dir === 'UP' ? np.up : np.dn;
  if (price < p.lo || price > p.hi || price < MIN_ENTRY_PRICE) return null;
  if (price > 0.90) return null;   // не платим > 90¢ за лидера (плохой R/R)
  const ourProb = _clampProb(Math.min(0.95, price + 0.06), price);
  return { side: dir, polyPrice: price, ourProb, edge: ourProb - price,
           info: `${tag} ${dir} Δ$${deltaUSD.toFixed(0)} @${(price * 100).toFixed(0)}¢` };
}
const STRAT_FAVMOM_A = {
  id: 'favMomA', name: 'Fav Momentum A (продолжение тренда)',
  desc: 'BTC рванул Δ≥$90, лидер уже 72–88¢ — едем на продолжении до SETTLE. WR 85%, 8/11 дней+, +$122.',
  defaults: { minDeltaUSD: 90, lo: 0.72, hi: 0.88, elFromSec: 20, elToSec: 200,
              minTimeMs: 45000, maxPerWindow: 1, kellyFrac: 0.08, maxFrac: 0.04 },
  shouldEnter(ctx, p) { return _favMomEntry(ctx, p, 'favMomA'); },
  shouldExit() { return null; },
};
const STRAT_FAVMOM_B = {
  id: 'favMomB', name: 'Fav Momentum B (сильный тренд, надёжнее)',
  desc: 'Δ≥$120, лидер 75–90¢. Реже, но WR 88%, 9/11 дней+, +$69.',
  defaults: { minDeltaUSD: 120, lo: 0.75, hi: 0.90, elFromSec: 20, elToSec: 200,
              minTimeMs: 45000, maxPerWindow: 1, kellyFrac: 0.08, maxFrac: 0.04 },
  shouldEnter(ctx, p) { return _favMomEntry(ctx, p, 'favMomB'); },
  shouldExit() { return null; },
};

// ── АКТИВНЫЙ НАБОР (вычищен от мусора) ────────────────────────────────────────
// Убраны по итогам бектеста на реальных данных и анализа demo/real-логов:
//   momentum/momScratch/momHi/momConfirm — модель predictPoly минусит даже в demo;
//   udgA/B/C/D/E, udgBest, udgFav, udgStreak, udgScore — A/B-тест коридоров
//   завершён: при реалистичном исполнении (ask + 0.8с) эдж знакопеременный;
//   udgFlip/udgFlipFav — к тому же не работали с demo-delay (мутация state
//   в shouldEnter); udgSkip3/B/C/E — дубли, оставлен лучший D.
// Ядро: underdogHold (опорный лог для skip/брейкера/FLOMD), udgSkip3D, udgVol,
// новые lagFav и FLOMD TACTIC, 2 ручных слота.
// ФИНАЛЬНЫЙ НАБОР ДЛЯ ДЕМО-ТЕСТА (по верифицированному бектесту с комиссией):
//   underdogHold — ОПОРА: кормит логом машину skip и FLOMD, на REAL не включать;
//   udgSkip3 10-35 — лучший skip (+$214/11дн);
//   lagFav Δ90 (+$220, maxDD $35) и lagFav75 Δ75 — две ступени, на REAL одна;
//   FLOMD TACTIC v3 — топ набора (+$558/11дн);
//   удалены как слабые: udgSkip3D 22-30 (+$53, OOS −1.5%), udgVol (~$0).
// ── ИТОГОВЫЙ НАБОР ────────────────────────────────────────────────────────────
// Параллельность: каждая стратегия смотрит на свой acct.open — входят независимо.
// Защиты от суммарного риска: MAX_TOTAL_EXPOSURE_FRAC (50% баланса, Guard F).
// favMomB убрана: 47% окон пересекается с favMomA → дублёр, не независимый сигнал.
// lagFav и favMomA пересекаются в 18% окон, но с РАЗНЫХ СТОРОН (lagFav 55-72¢,
// favMomA 72-88¢) — это разные ставки на разные исходы, ок.
// underdogHold — ТОЛЬКО demo (датчик для FLOMD и skip3), на REAL не включать.
// ── ИТОГОВЫЙ НАБОР ────────────────────────────────────────────────────────────
// СЕНСОРЫ (держать в DEMO — кормят гейты, на REAL не нужны):
//   underdogHold → FLOMD/skip3; momScratch/momConfirm/momHi/longHold/timeSession
//   → одноимённые РЕЖИМ-стратегии ниже.
// РАБОЧИЕ (можно REAL): lagFav, favMomA, FLOMD, udgSkip3 + 5 режим-следящих.
// Каждая стратегия смотрит свой acct.open (входят независимо); суммарный риск
// ограничен MAX_TOTAL_EXPOSURE_FRAC (Guard F, 50% баланса).
// ═══════════════════════════════════════════════════════════════════════════
// REGIME SWITCH — единая авто-переключающая стратегия (ДОГ ↔ MOMENTUM).
// ─────────────────────────────────────────────────────────────────────────────
// Идея (из анализа 47k demo-сделок): underdog и momentum АНТИкоррелированы
// (−0.58 по дням). underdog зарабатывает в ЧОПЕ (рынок пилит у нуля, реальны
// развороты к 50/50), momentum — в ТРЕНДЕ (BTC идёт в одну сторону, дог дохнет).
// Эта стратегия меряет режим рынка по истории окон и сама выбирает сторону:
//   • ЧОП  (efficiency ratio низкий) → берём дешёвую сторону (DOG-плечо)
//   • ТРЕНД (efficiency ratio высокий) → берём momentum (MOM-плечо)
//   • середина → разрешаем спор недавним реализованным эджем плеча, иначе пропуск
// Переключение по САМОМУ BTC (не по своему PnL) — мгновенное, не опаздывает на
// сломе режима, в отличие от трейлинг-PnL переключателя (тот залипает).
// Доп-защита: пер-плечевой предохранитель по своему demo-логу (стоп плеча после
// серии лузов, возврат после серии винов) — автоматически банит «протухшее» плечо.

// Efficiency ratio за последние N окон: |Σ движение| / Σ|движение|. 0 = чоп, 1 = тренд.
function _regimeState(p) {
  const wh = poly.winHist || [];
  if (wh.length < Math.max(p.regimeMinWindows, 1)) return { ready: false, er: null, vol: 0, net: 0 };
  const slice = wh.slice(-p.regimeWindows);
  let net = 0, gross = 0;
  for (const w of slice) { const m = w.move || 0; net += m; gross += Math.abs(m); }
  return { ready: true, er: gross > 0 ? Math.abs(net) / gross : 0, vol: gross, net };
}
// Разрешено ли плечо: машина по СВОЕМУ demo-логу, считаем только сделки этого плеча
// (по тегу [DOG]/[MOM] в entryInfo). Стоп после breakerLosses лузов подряд,
// возврат после breakerWins винов подряд. Чистый пересчёт на каждом тике.
function _legAllowed(self, legTag, p) {
  if (!self || !self.demo || !self.demo.log.length) return true;
  let active = true, ls = 0, ws = 0;
  for (const t of self.demo.log) {
    if (t.dirty) continue;
    if ((t.entryInfo || '').indexOf(legTag) === -1) continue;
    if (active) { ls = t.won ? 0 : ls + 1; if (ls >= p.breakerLosses) { active = false; ws = 0; ls = 0; } }
    else        { ws = t.won ? ws + 1 : 0; if (ws >= p.breakerWins)   { active = true;  ls = 0; ws = 0; } }
  }
  return active;
}
// Недавний реализованный счёт плеча (для разрешения «середины»): среднее по
// последним tieK сделкам плеча (pnl если есть, иначе ±1 по исходу).
function _legScore(self, legTag, K) {
  if (!self || !self.demo) return 0;
  const log = self.demo.log.filter(t => !t.dirty && (t.entryInfo || '').indexOf(legTag) !== -1).slice(-K);
  if (!log.length) return 0;
  let s = 0;
  for (const t of log) s += (typeof t.pnl === 'number' ? t.pnl : (t.won ? 1 : -1));
  return s / log.length;
}

const STRAT_REGIME_SWITCH = {
  id: 'regimeSwitch', name: 'Regime Switch (Dog ↔ Momentum)',
  desc: 'Сам меряет режим рынка по истории окон (efficiency ratio тренд/чоп) и переключает сторону: дог в чопе, momentum в тренде, пропуск в неясной середине. Пер-плечевой предохранитель по demo-логу банит протухшее плечо. Переключение по поведению BTC, а не по своему PnL — не опаздывает на сломе режима.',
  defaults: {
    minTimeMs: 60000,
    // — детектор режима —
    regimeWindows: 6,      // окон в efficiency ratio
    regimeMinWindows: 5,   // минимум истории, иначе bootstrap = дог
    chopMaxER: 0.40,       // ER ≤ это → ЧОП → дог
    trendMinER: 0.60,      // ER ≥ это → ТРЕНД → momentum
    minVolUSD: 8,          // Σ|движение| ниже → мёртвый рынок, пропуск
    // — DOG-плечо (коридор из анализа: 0.40–0.50 = лучший EV; <0.35 токсично) —
    lo: 0.40, hi: 0.50,
    dogEntryMoveCapUSD: 20, // текущее окно уехало ≥ → тренд внутри окна, дог не берём
    dogTpAbs: 0.96, dogStopPrice: 0.05,
    // — MOM-плечо (как momentum) —
    minConf: 35, minEdge: 0.03, tpPct: 0.50, slPct: 0.30, flipConf: 50, advMovePct: 0.25,
    // — предохранитель / разрешение середины / фоллбэк —
    breakerLosses: 8, breakerWins: 3, tieK: 20, allowFallback: 1,
    // — сайзинг —
    kellyFrac: 0.15, maxFrac: 0.07, maxPerWindow: 1,
  },
  shouldEnter(ctx, p) {
    if (ctx.msToEnd < p.minTimeMs) return null;
    const np = _normPoly(ctx); if (!np) return null;
    const self = STRATEGIES['regimeSwitch'];
    const rs = _regimeState(p);
    if (rs.ready && rs.vol < p.minVolUSD) return null;   // мёртвый рынок

    // кандидаты обоих плеч
    const dogSide  = np.up <= np.dn ? 'UP' : 'DOWN';
    const dogPrice = Math.min(np.up, np.dn);
    const dogOk    = dogPrice >= p.lo && dogPrice <= p.hi && dogPrice >= MIN_ENTRY_PRICE;
    const momE     = _momentumEntry(ctx, p, INVERT_SIGNAL);

    // выбор режима
    let want;
    if (!rs.ready)                 want = 'DOG';                       // bootstrap до набора истории
    else if (rs.er >= p.trendMinER) want = 'MOM';
    else if (rs.er <= p.chopMaxER)  want = 'DOG';
    else want = _legScore(self, '[MOM]', p.tieK) > _legScore(self, '[DOG]', p.tieK) ? 'MOM' : 'DOG';

    const erTag = rs.ready ? rs.er.toFixed(2) : 'na';
    const tryDog = () => {
      if (!dogOk) return null;
      if (!_legAllowed(self, '[DOG]', p)) return null;
      // анти-тренд гейт: дог берём только если текущее окно НЕ уехало (дог живёт в пиле)
      if (ctx.curBTC != null && ctx.openingBTC != null &&
          Math.abs(ctx.curBTC - ctx.openingBTC) >= p.dogEntryMoveCapUSD) return null;
      const ourProb = _clampProb(dogPrice + 0.10, dogPrice);
      return { side: dogSide, polyPrice: dogPrice, ourProb, edge: ourProb - dogPrice,
               info: `RS DOG @${(dogPrice * 100).toFixed(0)}¢ ER=${erTag} [DOG]` };
    };
    const tryMom = () => {
      if (!momE) return null;
      if (!_legAllowed(self, '[MOM]', p)) return null;
      return { side: momE.side, polyPrice: momE.polyPrice, ourProb: momE.ourProb, edge: momE.edge,
               info: `RS MOM ${momE.info} ER=${erTag} [MOM]` };
    };

    let entry = want === 'MOM' ? tryMom() : tryDog();
    if (!entry && p.allowFallback) entry = want === 'MOM' ? tryDog() : tryMom();
    return entry;
  },
  shouldExit(ctx, pos, p) {
    const isMom = (pos.entryInfo || '').indexOf('[MOM]') !== -1;
    if (isMom) {
      const ex = _tpSlExit(ctx, pos, { ...p, tpPct: p.tpPct, slPct: p.slPct }) || _advExit(ctx, pos, p);
      if (ex) return ex;
      let effDir = ctx.sigP.dir;
      if (INVERT_SIGNAL && effDir !== 'WAIT') effDir = effDir === 'UP' ? 'DOWN' : 'UP';
      if (effDir !== 'WAIT' && effDir !== pos.side && ctx.sigP.conf > p.flipConf) {
        const curMid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
        return { reason: 'FLIP', exitPrice: curMid };
      }
      return null;
    }
    // DOG-плечо: абсолютный TP + жёсткий стоп (по данным FLOMD стоп помогает)
    const mid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (mid != null && p.dogTpAbs    && mid >= p.dogTpAbs)    return { reason: 'TP', exitPrice: mid };
    if (mid != null && p.dogStopPrice && mid <= p.dogStopPrice) return { reason: 'SL', exitPrice: mid };
    return null;
  },
};


const STRAT_DEFINITIONS = [
  // — сенсоры (DEMO only) —
  STRAT_UNDERDOG_HOLD,
  STRAT_MOM_SCRATCH,
  STRAT_MOM_CONFIRM,
  STRAT_MOM_HI,
  STRAT_LONG_HOLD,
  STRAT_TIME_SESSION,
  STRAT_MOMENTUM,
  STRAT_MOM_SCRATCH_HI,
  STRAT_REGIME_SWITCH,   // ← авто-переключатель дог↔momentum
  // — рабочие: книга < спота / книга > спота / дог —
  STRAT_LAG_FAV,
  STRAT_FAVMOM_A,
  STRAT_FLOMD,
  STRAT_FLOMD_INVERSE,
  STRAT_FLOMD_FAVE,
  STRAT_UNDERDOG_DELTA,
  ...UDG_DELTA_GATED,    // ← 9 аналогов с авто-стопом по underdogHold (стрики + pnl-окна)
  ...UDG_DELTA_TPSL,     // ← 28 вариантов: коридор × TP, абсолютный SL 8¢
  STRAT_UNDERDOG_DIP,
  STRAT_UDG_SKIP3,
  // — режим-следящие (FLOMD-семейство для моментума) —
  STRAT_MOM_FLOMD_SCRATCH,
  STRAT_MOM_FLOMD_CONFIRM,
  STRAT_MOM_FLOMD_HI,
  STRAT_SESSION_FLOMD,
  STRAT_MOM_FLOMD_PURE,
  STRAT_MOM_FLOMD_SCRATCH_HI,
  STRAT_UNDERDOG_FLOMD,
  ...MANUAL_STRATS,
];

// ─── UNDERDOG HOLD LOSS-STREAK CIRCUIT BREAKER ───────────────────────────────
// Если underdogHold набирает UNDERDOG_HOLD_LOSS_LIMIT поражений подряд (в demo-логе)
// — у всех стратегий из UNDERDOG_LOSS_DEPENDENT_IDS отключается только РЕАЛЬНАЯ
// торговля (realEnabled → false). Demo продолжает работать — статистика копится.
// В Telegram уходит уведомление. Флаг underdogHoldAutoBlocked снимается только
// вручную: пользователь выключает и снова включает real на дашборде.
const UNDERDOG_HOLD_LOSS_LIMIT = 8;
// FLOMD сюда НЕ входит — у него собственный авто-режим (стоп/возврат внутри
// shouldEnter). Остальные skip-зависимые стопаются по-старому, включение вручную.
const UNDERDOG_LOSS_DEPENDENT_IDS = [
  'udgSkip3',
];

// ─── REAL-TRADING RISK CONTROLS ──────────────────────────────────────────────
// These guards exist to prevent the bot from spamming trades on dead markets
// where one side has already won and the loser-token trades at 1-5¢. On those
// extreme prices our edge calculation looks huge (model says "still 50/50",
// market knows the answer is 99/1), but ADVERSE/SL triggers instantly because
// any micro-move is a huge % of a 2¢ token. Result: 6 burned trades in 11 s.
const REAL_MIN_PRICE         = 0.10;     // Skip if either side < 10¢ — market has decided
const REAL_MAX_PRICE         = 0.90;     // Skip if our entry side > 90¢ — bad RR even when right
const REAL_MIN_MS_TO_END     = 45_000;   // Need ≥45s left in window — else no time to play out
const REAL_COOLDOWN_MS       = 20_000;   // Wait ≥20s after any real close before opening again
let REAL_DAILY_LOSS_CAP      = parseFloat(process.env.REAL_DAILY_LOSS_CAP || '3');  // USD; -$3 default
                                                                                    // (УСТАРЕЛО — заменено мин. балансом ниже, см. REAL_MIN_BALANCE)
// ── МИН. БАЛАНС (реал) ────────────────────────────────────────────────────────
// Вместо «лимита потерь за день» — простой пол по балансу: ниже этой суммы (USDC
// в кошельке) НЕ открываем реальных сделок. Проверяется так, что новая сделка не
// уводит свободный баланс ниже пола. По умолчанию $20, крутится с дашборда.
let REAL_MIN_BALANCE         = Math.max(0, parseFloat(process.env.REAL_MIN_BALANCE || '20') || 20);
let _realFloorNotified       = false;    // чтобы не спамить в TG при каждом тике у пола
// FIX: предел СУММАРНОЙ открытой real-экспозиции (доля от баланса кошелька).
// Каждая стратегия сайзится от полного баланса — без этого лимита при N
// включённых стратегиях совокупный риск умножался на N.
const MAX_TOTAL_EXPOSURE_FRAC = Math.max(0.05, Math.min(1.0,
  parseFloat(process.env.MAX_TOTAL_EXPOSURE_FRAC || '0.5') || 0.5));

// ── АБСОЛЮТНЫЙ TAKE-PROFIT ─────────────────────────────────────────────────────
// Бинарный токен не может стоить дороже 100¢, поэтому ПРОЦЕНТНЫЙ TP при высоком
// входе недостижим (вход 75¢ × 1.5 = 112¢ — невозможно), и позиция зависает до
// SETTLE. Этот абсолютный потолок фиксирует прибыль при ЛЮБОМ входе, как только
// цена дошла до уровня: выше апсайд мизерный (≤5¢), а риск разворота огромный.
//   TP_ABS_PRICE=0.95 → фиксировать на 95¢ (по умолчанию). Можно 0.90–0.97.
let TP_ABS_PRICE = Math.max(0.50, Math.min(0.99,
  parseFloat(process.env.TP_ABS_PRICE || '0.95') || 0.95));

// Минимальная цена входа: не заходим, если наша сторона дешевле этого порога.
// Дешёвые токены на резком рывке вживую не заливаются (цена уже ушла), а demo
// рисует фантомный филл по 1–20¢ с нереальными +1000%. Порог режет эти окна на
// ОБЕИХ ветках (demo и real), чтобы статистика была сравнимой. Меняется с дашборда.
let MIN_ENTRY_PRICE = Math.max(0.0, Math.min(0.50,
  parseFloat(process.env.MIN_ENTRY_PRICE || '0.15') || 0.15));

// ── MARKETABLE ENTRY (вход по рынку) ──────────────────────────────────────────
// Раньше BUY ставился лимиткой ровно по цене входа. Если ask был выше — ордер
// висел в стакане как status=live и НЕ исполнялся, но бот считал позицию
// открытой (фантомная позиция). Теперь BUY идёт маркетабельной лимиткой GTC по
// "потолку" = entry + BUY_SLIPPAGE (округлённому вверх до целого цента). Ордер
// берёт ликвидность до потолка как тейкер; если за пару секунд не залился —
// отменяется и откатывается. Позиция открывается только при реальном исполнении.
//   BUY_SLIPPAGE=0.05  → допустимое проскальзывание вверх (по умолчанию 5¢).
//                        Подними (0.07–0.10), если часто "вход не состоялся".
const BUY_SLIPPAGE = Math.max(0, Math.min(0.20,
  parseFloat(process.env.BUY_SLIPPAGE || '0.05') || 0.05));

// Активные параметры: база (def.defaults) или кастом (с дашборда), если включён.
// Движок всегда читает s.params — здесь просто пересобираем его при изменениях.
function applyParams(s) {
  s.params = (s.def.manual || s.customEnabled) ? { ...s.def.defaults, ...s.customParams } : { ...s.def.defaults };
}

// Инверсия сигнала: торгуем ПРОТИВ модели (UP↔DOWN). Переключается с дашборда
// (/api/invert/toggle) и сохраняется в state. По умолчанию ВЫКЛ (обычный режим).
let INVERT_SIGNAL = ['true', '1', 'yes', 'on']
  .includes((process.env.INVERT_SIGNAL || 'false').toLowerCase().trim());

// ── РЕАЛИСТИЧНОСТЬ DEMO ───────────────────────────────────────────────────────
// Проблема: при резком рывке цены real не может залиться (нет ликвидности / цена
// уже ушла), а demo мгновенно «входит» по идеальной цене и ловит фантомную
// прибыль. Лечим двумя вещами:
//  1) DEMO_ENTRY_DELAY_MS — demo не входит мгновенно по сигналу, а ждёт N секунд
//     и заливается уже по ЦЕНЕ ПОСЛЕ задержки (как реальная задержка ордера).
//  2) DEMO_MAX_CHASE — если за время задержки цена входа убежала вверх больше чем
//     на этот %, считаем что «залиться нельзя» (вагон уехал) и пропускаем сделку.
let DEMO_ENTRY_DELAY_MS = Math.max(0, Math.min(30000,
  Math.round((parseFloat(process.env.DEMO_ENTRY_DELAY_SEC || '2') || 2) * 1000)));
let DEMO_MAX_CHASE = Math.max(0.01, Math.min(2.0,
  (parseFloat(process.env.DEMO_MAX_CHASE_PCT || '15') || 15) / 100));
// Реальный спред в demo: вход по ask, выход по bid (как реал). По умолчанию ВЫКЛ —
// тогда demo торгует по mid (идеальная точка отсчёта). Включается тумблером.
let DEMO_REAL_SPREAD = ['true', '1', 'yes', 'on']
  .includes((process.env.DEMO_REAL_SPREAD || 'false').toLowerCase().trim());

// ── РАСПИСАНИЕ ТОРГОВЛИ ───────────────────────────────────────────────────────
// Ограничивает ОТКРЫТИЕ сделок по часам (МСК, UTC+3). Выходы работают всегда.
// from..to — часы [0..24). Если from==to → круглосуточно. Поддержан переход
// через полночь (например 22→6 = с вечера до утра).
let SCHEDULE_ENABLED = ['true', '1', 'yes', 'on']
  .includes((process.env.SCHEDULE_ENABLED || 'false').toLowerCase().trim());
let SCHEDULE_FROM = Math.max(0, Math.min(24, parseInt(process.env.SCHEDULE_FROM || '9', 10)));
let SCHEDULE_TO   = Math.max(0, Math.min(24, parseInt(process.env.SCHEDULE_TO   || '23', 10)));

// Разрешено ли СЕЙЧАС открывать сделки ПО ГЛОБАЛЬНОМУ расписанию. Выходы не трогает.
function entriesAllowedNow() {
  if (!SCHEDULE_ENABLED) return true;
  if (SCHEDULE_FROM === SCHEDULE_TO) return true; // круглосуточно
  const mskHour = (new Date().getUTCHours() + 3) % 24; // МСК = UTC+3
  return SCHEDULE_FROM < SCHEDULE_TO
    ? (mskHour >= SCHEDULE_FROM && mskHour < SCHEDULE_TO)        // дневной интервал
    : (mskHour >= SCHEDULE_FROM || mskHour < SCHEDULE_TO);       // через полночь
}

// Разрешено ли открывать сделки КОНКРЕТНОЙ стратегии. Если у стратегии включено
// своё расписание — оно имеет приоритет; иначе действует глобальное расписание.
function strategyEntriesAllowed(s) {
  if (s && s.schedEnabled) {
    const f = s.schedFrom, t = s.schedTo;
    if (f === t) return true;                          // 0/0 (или равные) = круглосуточно
    const h = (new Date().getUTCHours() + 3) % 24;     // МСК
    return f < t ? (h >= f && h < t) : (h >= f || h < t);
  }
  return entriesAllowedNow();
}

function initStrategies() {
  for (const def of STRAT_DEFINITIONS) {
    STRATEGIES[def.id] = {
      def,
      demoEnabled:  false,
      realEnabled:  false,
      schedEnabled: false,   // своё расписание выкл → действует глобальное
      schedFrom:    7,       // час МСК «от»
      schedTo:      24,      // час МСК «до» (24 = до полуночи)
      demo: { balance: 1000, peakBalance: 1000, open: null, log: [] },
      real: { balance: 1000, peakBalance: 1000, open: null, log: [] },
      params:       { ...def.defaults },
      customEnabled: false,             // false = база (def.defaults), true = кастом с дашборда
      customParams:  { ...def.defaults },// редактируемые значения для кастом-режима
      pendingReal:           false,    // true while a real BUY order is in-flight
      lastRealCloseTime:     0,        // epoch ms — for cooldown enforcement
      lastRealClosedWindow:  null,     // window slug of the last close — for per-window trade counter
      realTradesThisWindow:  0,        // how many real trades opened in the current window (max 2)
      realDailyLossDate:     null,     // 'YYYY-MM-DD' (UTC) — bookkeeping for the daily cap
      realDailyLossAmount:   0,        // running USD loss for the current UTC day
      realDailyAutoDisabled: false,    // user must re-enable real after the cap fires
      _skip3ResetIdx:          0,        // udgSkip3: index in underdogHold log from which to count new loss streak
      underdogHoldAutoBlocked: false,   // true = real auto-disabled by 8-loss streak breaker; cleared on manual real toggle-ON
    };
  }
}

function getStratContext() {
  const win    = currentPolyWindow();
  const sigP   = predictPoly();
  const curBTC = chain.currentPrice || (ticks.length ? ticks[ticks.length - 1].price : null);
  // ── Признаки из истории окон (для новых тест-стратегий udgVol / udgStreak) ──
  const H = poly.winHist;
  let outcomeStreak = 0, streakDir = null, prevMove = null, prevRange = null, vol5 = null;
  if (H.length) {
    streakDir = H[H.length - 1].winner;
    for (let i = H.length - 1; i >= 0 && H[i].winner === streakDir; i--) outcomeStreak++;
    prevMove  = Math.abs(H[H.length - 1].move);
    prevRange = H[H.length - 1].range;
    const last5 = H.slice(-5);
    vol5 = last5.reduce((a, w) => a + Math.abs(w.move), 0) / last5.length;
  }
  return {
    win,
    msToEnd:     Math.max(0, win.endTs - Date.now()),
    polyUp:      poly.prices.up,
    polyDn:      poly.prices.down,
    sigP,
    curBTC,
    btcAgeMs:    (chain.lastUpdate != null) ? (Date.now() - chain.lastUpdate) : null,  // свежесть цены Chainlink
    openingBTC:  poly.windowOpeningBTC,
    openingSource: poly.windowOpeningSource,
    outcomeStreak,        // сколько окон ПОДРЯД закрылись в одну сторону (до текущего)
    streakDir,            // направление этой серии ('UP'/'DOWN')
    prevMove,             // |движение| предыдущего окна, $
    prevRange,            // диапазон (hi-lo) предыдущего окна, $
    vol5,                 // среднее |движение| за 5 последних окон, $
  };
}

// Котировки стороны (bid/ask/mid) в текущий момент — для калибровочного лога.
function _sideQuote(side) {
  const p = poly.prices;
  return side === 'UP'
    ? { bid: p.upBid, ask: p.upAsk, mid: p.up }
    : { bid: p.dnBid, ask: p.dnAsk, mid: p.down };
}

// Записать условия входа. Исход окна допишется позже в resolveCalib().
function logCalibEntry(s, ctx, entry, acct, isReal) {
  const q = _sideQuote(entry.side);
  const mode = isReal ? 'real' : (acct === s.demo ? 'demo' : 'simreal');
  calibLog.push({
    ts:         Date.now(),
    strategy:   s.def.id,
    mode,
    side:       entry.side,
    mid:        entry.polyPrice,                                   // норм. цена (как видит стратегия)
    rawMid:     q.mid,                                             // сырой mid стороны
    bid:        q.bid,
    ask:        q.ask,
    spread:     (q.bid != null && q.ask != null) ? +(q.ask - q.bid).toFixed(4) : null,
    msToEnd:    ctx.msToEnd,
    btcMove:    (ctx.curBTC != null && ctx.openingBTC != null) ? +(ctx.curBTC - ctx.openingBTC).toFixed(2) : null,
    openingBTC: ctx.openingBTC,
    windowEnd:  ctx.win.endTs,
    slug:       poly.market ? poly.market.eventSlug : 'manual',
    outcome:    null,   // 'UP'/'DOWN'/'stale' — дописывается при закрытии окна
    ourWin:     null,   // 1 если outcome === side
  });
  if (calibLog.length > CALIB_MAX) calibLog.shift();
}

// Дописать фактический исход окна для записей, чьё окно уже закрылось.
// FIX: сначала пытаемся взять победителя ПО КНИГЕ (winnerBySlug) — это резолв
// Polymarket. Фид BTC используется только как фолбэк (помечается dirty=1).
function resolveCalib(ctx) {
  const now = Date.now();
  for (const r of calibLog) {
    if (r.outcome !== null) continue;
    if (now < r.windowEnd) continue;
    const bookWinner = winnerBySlug[r.slug];
    if (bookWinner) {
      r.outcome = bookWinner;
      r.ourWin  = (r.outcome === r.side) ? 1 : 0;
      continue;
    }
    if (now > r.windowEnd + 120000) { r.outcome = 'stale'; continue; } // не поймали закрытие
    if (ctx.curBTC == null || r.openingBTC == null) continue;
    // окно закрылось, книга не дорезолвилась — ждём ещё (до 120с), потом фолбэк
    if (now > r.windowEnd + 30000) {
      r.outcome = ctx.curBTC > r.openingBTC ? 'UP' : 'DOWN';
      r.ourWin  = (r.outcome === r.side) ? 1 : 0;
      r.dirty   = 1;
    }
  }
}

function stratOpen(s, ctx, entry, acct, isReal) {
  // ── Кулдаун: лимит входов в одно окно (борьба с churn). Работает для любого
  // аккаунта (demo и real). Порог задаётся параметром maxPerWindow; если не задан
  // — лимита нет. Счётчик на самом аккаунте, сбрасывается со сменой окна.
  const maxPW = s.params.maxPerWindow;
  if (maxPW) {
    if (acct._cdWindow !== ctx.win.slug) { acct._cdWindow = ctx.win.slug; acct._cdCount = 0; }
    if ((acct._cdCount || 0) >= maxPW) return;   // уже исчерпан лимит входов в этом окне
  }

  // ── Safety guard: never size a real trade from the default $1000 placeholder ──
  // If the USDC balance was never successfully fetched from CLOB, bail out.
  if (isReal && REAL_TRADING && realBalance === null) {
    console.warn(`[real] skipping OPEN — USDC balance not yet confirmed (still at default). Will retry next signal.`);
    return;
  }

  // For real accounts, always use the live wallet balance for sizing (not stale state value)
  const effectiveBalance = isReal && realBalance !== null ? realBalance : acct.balance;
  // Реальный спред в demo: заливаемся по ASK стороны (как реал платит за вход),
  // а не по mid. Тогда позиция сразу слегка в минусе на полспреда — реалистично.
  if (acct === s.demo && DEMO_REAL_SPREAD) {
    const q = _sideQuote(entry.side);
    if (q.ask != null) entry = { ...entry, polyPrice: q.ask };
  }
  let sizeUSDC = sizingByKelly(effectiveBalance, entry.ourProb, entry.polyPrice, s.params.kellyFrac, s.params.maxFrac);
  if (entry.fixedUSD != null && entry.fixedUSD > 0) sizeUSDC = entry.fixedUSD;   // ручные стратегии: фикс. сумма входа
  // For sim: reject tiny sizes immediately. For real: check AFTER the 5-share
  // bump below, so a $0.94 Kelly still becomes $3.03 (5 shares × 60.5¢) and passes.
  if (!isReal && sizeUSDC < 1)            return;
  if (sizeUSDC > effectiveBalance * 0.95) return;

  // Реальный ордер размещается для ЛЮБОЙ стратегии с включённым тумблером REAL
  // (isReal истинно только когда s.realEnabled И REAL_TRADING И есть кошелёк/ключи).
  const isRealOrder = isReal && !!polyWallet && !!polyApiCreds;
  const tokenId     = entry.side === 'UP' ? poly.market?.tokenIdUp : poly.market?.tokenIdDown;

  // For real orders: need tokenId
  if (isRealOrder && !tokenId) {
    console.warn('[real] missing tokenId — skipping real entry');
    return;
  }

  // ── REAL-TRADING RISK CONTROLS ─────────────────────────────────────────────
  // Each guard below applies ONLY to real orders — demo keeps trading
  // unhindered so we still collect statistics.
  if (isRealOrder) {
    // [Guard F — FIX] Общий лимит экспозиции: каждая real-стратегия сайзится от
    // ПОЛНОГО баланса кошелька, поэтому при нескольких включённых стратегиях
    // суммарный риск умножался. Теперь сумма открытых real-позиций + новая
    // не может превысить MAX_TOTAL_EXPOSURE_FRAC от баланса.
    let totalOpenReal = 0;
    for (const id2 in STRATEGIES) {
      const op = STRATEGIES[id2].real && STRATEGIES[id2].real.open;
      if (op && op.isReal) totalOpenReal += op.sizeUSDC || 0;
    }
    const expCap = (realBalance !== null ? realBalance : effectiveBalance) * MAX_TOTAL_EXPOSURE_FRAC;
    if (totalOpenReal + sizeUSDC > expCap) {
      console.log(`[real] SKIP — total exposure $${(totalOpenReal + sizeUSDC).toFixed(2)} would exceed cap $${expCap.toFixed(2)}`);
      return;
    }

    // Reset daily-loss bucket if we've rolled into a new UTC day (kept for
    // backward-compat bookkeeping; the active risk control is the balance floor).
    const utcToday = new Date().toISOString().slice(0, 10);
    if (s.realDailyLossDate !== utcToday) {
      s.realDailyLossDate     = utcToday;
      s.realDailyLossAmount   = 0;
      s.realDailyAutoDisabled = false;
    }

    // [Guard E] МИН. БАЛАНС: не открываем реальную сделку, если свободный USDC
    // после неё опустится ниже пола REAL_MIN_BALANCE (или уже ниже него). Это
    // заменило прежний «дневной лимит потерь» — теперь просто не уходим под пол.
    if (realBalance !== null && (realBalance - sizeUSDC) < REAL_MIN_BALANCE) {
      console.log(`[real] SKIP — баланс $${realBalance.toFixed(2)} − $${sizeUSDC.toFixed(2)} < пол $${REAL_MIN_BALANCE.toFixed(2)}`);
      if (!_realFloorNotified) {
        _realFloorNotified = true;
        sendTg(
          `🛑 <b>Мин. баланс достигнут</b>\n` +
          `Баланс: <b>$${realBalance.toFixed(2)}</b>, пол: <b>$${REAL_MIN_BALANCE.toFixed(2)}</b>\n` +
          `Новые реальные сделки приостановлены, чтобы не уйти ниже пола.\n` +
          `Demo продолжает работать. Подними баланс или опусти пол на дашборде.`
        );
      }
      return;
    }
    // Баланс выше пола — снимаем флажок, чтобы при следующем заходе под пол снова уведомить.
    if (realBalance !== null && realBalance >= REAL_MIN_BALANCE) _realFloorNotified = false;

    // [Guard A] Skip extreme prices. When one side trades ≤ 10¢, the market
    // has effectively decided the outcome. Our model still says "50/50" so
    // edge looks gigantic (+50pp), but it's mathematical artifact — the
    // market knows something our predictor doesn't (e.g. window almost over,
    // BTC already 100¢ in the other direction). On 2¢ tokens any micro-move
    // is a huge % swing, so ADVERSE/SL triggers within 1 second and we
    // spam-trade ourselves to zero. This single guard would have blocked
    // all 6 burned trades from window 1779977100.
    const oppositePrice = entry.side === 'UP' ? ctx.polyDn : ctx.polyUp;
    if (entry.polyPrice < REAL_MIN_PRICE || entry.polyPrice > REAL_MAX_PRICE
        || oppositePrice < REAL_MIN_PRICE || oppositePrice > REAL_MAX_PRICE) {
      console.log(`[real] SKIP extreme price — ${entry.side}=${(entry.polyPrice*100).toFixed(1)}¢ / opp=${(oppositePrice*100).toFixed(1)}¢ (market already decided)`);
      return;
    }

    // [Guard D] Need enough time left in the window. Less than 45s and SL/TP
    // won't get a chance to work out — the position will just expire.
    if (ctx.msToEnd < REAL_MIN_MS_TO_END) {
      console.log(`[real] SKIP — only ${Math.round(ctx.msToEnd/1000)}s left in window, need ≥${REAL_MIN_MS_TO_END/1000}s`);
      return;
    }

    // [Guard C] Cooldown after any real close. Even across windows, give a
    // 20-second buffer so a stuck SELL or a wallet-balance sync can complete
    // before we touch another trade.
    const sinceClose = Date.now() - (s.lastRealCloseTime || 0);
    if (sinceClose < REAL_COOLDOWN_MS) {
      console.log(`[real] SKIP — cooldown, ${Math.round((REAL_COOLDOWN_MS - sinceClose)/1000)}s remaining`);
      return;
    }

    // [Guard B] Max 2 real trades per 5-minute window.
    // Reset the counter when a new window starts.
    const curSlug = ctx.win.slug;
    if (s.lastRealClosedWindow !== curSlug) {
      // New window — reset counter
      s.lastRealClosedWindow = curSlug;
      s.realTradesThisWindow = 0;
    }
    const MAX_TRADES_PER_WINDOW = 2;
    if (s.realTradesThisWindow >= MAX_TRADES_PER_WINDOW) {
      console.log(`[real] SKIP — already ${s.realTradesThisWindow} trades this window (max ${MAX_TRADES_PER_WINDOW})`);
      return;
    }
  }

  // ── Real-order sizing: enforce Polymarket 5-share minimum ──────────────────
  // If Kelly says $1.30 but at price 0.36 that's only 3.6 shares < 5, bump the
  // trade up to 5 shares so we can SELL it later (every SELL needs ≥5 shares).
  // This may push the trade above maxFrac but it's required for the position
  // to be exitable. Skip if even 5 shares would blow >95% of balance.
  let plannedShares = null;
  if (isRealOrder) {
    const kellyShares = sizeUSDC / entry.polyPrice;
    // Целое число акций: Polymarket market-ордера требуют ограниченной точности
    // сумм (maker amount ≤ 2 знака). Дробные акции (5.07) ломали вход с ошибкой
    // "invalid amounts". Округляем ВВЕРХ до целого, минимум 5.
    plannedShares = Math.max(POLYMARKET_MIN_SHARES, Math.ceil(kellyShares));
    const requiredUSDC = plannedShares * entry.polyPrice;
    // Apply the < $1 guard AFTER bump (edge case: very low price + tiny balance)
    if (requiredUSDC < 1) return;
    if (requiredUSDC > effectiveBalance * 0.95) {
      console.warn(`[real] skipping OPEN — 5-share minimum ($${requiredUSDC.toFixed(2)}) exceeds 95% of balance ($${effectiveBalance.toFixed(2)}). Pop up balance to trade at this price.`);
      sendTg(
        `⚠️ <b>Сделка пропущена</b>\n` +
        `5 shares × ${(entry.polyPrice * 100).toFixed(1)}¢ = $${requiredUSDC.toFixed(2)} — больше 95% твоего баланса $${effectiveBalance.toFixed(2)}.\n` +
        `Пополни кошелёк или подожди более выгодной цены.`
      );
      return;
    }
    // Bumped: use the corrected size for both sim accounting and the real order
    sizeUSDC = requiredUSDC;
  }

  const openingBTC = ctx.openingBTC || ctx.curBTC;
  acct.open = {
    side:               entry.side,
    entryTime:          Date.now(),
    btcAtEntry:         openingBTC,
    btcAtEntryCoinbase: ctx.curBTC,
    polyEntryPrice:     entry.polyPrice,
    sizeUSDC,
    edge:               entry.edge,
    expiryTime:         ctx.win.endTs,
    marketSlug:         poly.market ? poly.market.eventSlug : 'manual',
    ourProb:            entry.ourProb,
    openingSource:      ctx.openingSource,
    entryInfo:          entry.info,
    // Real-trading fields
    tokenId:            tokenId || null,
    isReal:             isRealOrder,
    realOrderId:        null,
    realOrderStatus:    isRealOrder ? 'pending' : 'sim',
    plannedShares:      plannedShares,  // ← exactly what we'll try to BUY (for SELL later)
    actualShares:       null,           // ← filled after BUY response confirms
  };
  acct.balance    -= sizeUSDC;
  if (acct === s.demo) { try { mlEntry(s, ctx, entry, acct.open); } catch (_) {} }  // ML-ЛОГ
  if (s.params.maxPerWindow) acct._cdCount = (acct._cdCount || 0) + 1;
  if (isRealOrder) {
    s.pendingReal = true;
    s.realTradesThisWindow = (s.realTradesThisWindow || 0) + 1;
  }
  // ── Skip-фильтр: сбрасываем точку отсчёта лузов только здесь, при реальном входе.
  // Нельзя делать это в shouldEnter: demo-delay вызывает shouldEnter дважды
  // (1й раз — фиксирует pendingEntry, 2й — верифицирует сигнал перед входом).
  // Если сбрасывать в shouldEnter, 2й вызов видит resetIdx уже сдвинутым → сигнал
  // исчезает → вход никогда не происходит. Все 5 UDG-SKIP-стратегий используют
  // поле _skip3ResetIdx на своём объекте стратегии.
  if (s._skip3ResetIdx != null) {
    const ref = STRATEGIES['underdogHold'];
    if (ref && ref.demo) {
      s._skip3ResetIdx = ref.demo.log.length;
      console.log(`[${s.def.id}] skip-reset → _skip3ResetIdx=${s._skip3ResetIdx}`);
    }
  }

  logCalibEntry(s, ctx, entry, acct, isReal);
  saveState();
  console.log(`[${s.def.id}] ${isRealOrder ? 'REAL' : 'SIM'} OPEN ${entry.side} @ ${entry.polyPrice.toFixed(3)} size=$${sizeUSDC.toFixed(2)} (balance=$${effectiveBalance.toFixed(2)}) | ${entry.info}`);

  // ── Place real BUY order on Polymarket CLOB (async, Momentum only) ──────────
  if (isRealOrder) {
    // Маркетабельная лимитка (GTC) по потолку = entry + slippage, ОКРУГЛЁННОМУ
    // вверх до целого цента. Лимитка берёт всю ликвидность до потолка как тейкер
    // (как рыночный ордер), но, в отличие от FAK, не умирает мгновенно, если ask
    // чуть выше — стоит пару секунд и может поймать продавца. Если за окно
    // проверки не залилась — отменяем и откатываем (фантома не оставляем).
    // GTC-лимитки не подпадают под жёсткое "max 2 decimals" для market-ордеров.
    //
    // ceiling округляем ВВЕРХ до цента, чтобы цена была валидным тиком Polymarket
    // (1¢) и не оказалась ниже рынка из-за получентовой entry-цены.
    const ceiling = Math.max(0.02, Math.min(0.99,
      Math.ceil((entry.polyPrice + BUY_SLIPPAGE) * 100) / 100));
    // plannedShares уже целое. size = shares * ceiling → placeClobOrder получит
    // ровно plannedShares акций, а maker amount = целые_акции × цент = чистая
    // сумма с 2 знаками. Заплатим по факту ≤ ceiling за штуку.
    const buySize  = plannedShares * ceiling;
    const BUY_VERIFY_MS = 2_500; // сколько ждём заполнения перед откатом

    // Считается ли BUY исполнившимся по ответу/статусу ордера.
    const filledByStatus = (st, sizeMatched) => {
      if (String(st || '').toLowerCase() === 'matched') return true;
      const m = parseFloat(sizeMatched ?? 'NaN');
      return !isNaN(m) && m >= plannedShares * 0.99;
    };

    // Откат фантомной позиции: вернуть баланс, снять счётчик окна, очистить open.
    const rollback = (whyTg) => {
      s.pendingReal = false;
      if (acct.open) {
        acct.balance += acct.open.sizeUSDC;
        acct.open     = null;
      }
      s.realTradesThisWindow = Math.max(0, (s.realTradesThisWindow || 1) - 1);
      saveState();
      if (whyTg) sendTg(whyTg);
    };

    const confirmOpen = (orderId, actualShares) => {
      if (!acct.open) return;
      acct.open.realOrderId     = orderId;
      acct.open.realOrderStatus = 'matched';
      acct.open.actualShares    = actualShares;
      saveState();
      sendTgButtons(
        `🔵 <b>ОТКРЫТА</b> — ${entry.side}\n` +
        `Стратегия: <i>${_tgEsc(s.def.id)}</i>\n` +
        `Цена входа: <b>≤ ${(ceiling * 100).toFixed(0)}¢</b> (по рынку)\n` +
        `Размер: <b>${actualShares} shares = $${sizeUSDC.toFixed(2)}</b> (${(sizeUSDC / effectiveBalance * 100).toFixed(1)}% от баланса)\n` +
        `Edge: ${(entry.edge * 100).toFixed(1)}pp\n` +
        `Баланс: $${effectiveBalance.toFixed(2)}`,
        [
          [{ text: `⚡ ПРОДАТЬ ${_tgEsc(s.def.id)} по рынку`, callback_data: `panic:${s.def.id}` }],
          [{ text: '📊 Статус позиций', callback_data: 'status' }],
        ]
      );
    };

    placeClobOrder({ tokenId, side: 'BUY', size: buySize, price: ceiling, orderType: 'GTC' })
      .then(async result => {
        s.pendingReal = false;
        console.log(`[real] BUY placed orderId=${result.orderID} status=${result.status} ceiling=${ceiling} shares=${plannedShares}`);
        if (!acct.open) { await cancelClobOrder(result.orderID); return; }

        // Сразу залилось как тейкер?
        if (filledByStatus(result.status, result.raw?.size_matched ?? result.raw?.sizeMatched)) {
          confirmOpen(result.orderID, result.actualShares);
          return;
        }

        // Повисло — даём короткое окно и перепроверяем статус.
        await new Promise(r => setTimeout(r, BUY_VERIFY_MS));
        if (!acct.open) { await cancelClobOrder(result.orderID); return; }
        const st = await getClobOrderStatus(result.orderID);
        if (filledByStatus(st?.status, st?.size_matched)) {
          console.log(`[real] BUY filled on verify orderId=${result.orderID}`);
          confirmOpen(result.orderID, result.actualShares);
          return;
        }

        // Так и не залилось за окно проверки. Пытаемся отменить — НО отмена
        // может прийти ровно в момент заполнения (гонка). Поэтому после отмены
        // ПЕРЕпроверяем реальное заполнение и откатываемся ТОЛЬКО при нуле.
        // Иначе оставим без присмотра реальную позицию, которая сгорит в SETTLE.
        const cancelResp = await cancelClobOrder(result.orderID);
        const finalSt    = await getClobOrderStatus(result.orderID);
        const matched    = parseFloat(finalSt?.size_matched ?? finalSt?.sizeMatched ?? '0') || 0;
        const cantCancel = !!(cancelResp && cancelResp.not_canceled &&
                              Object.keys(cancelResp.not_canceled).length > 0);
        const raceFilled = matched > 0
          || String(finalSt?.status || '').toLowerCase() === 'matched'
          || cantCancel; // не смогли отменить → ордер уже исполнен

        if (raceFilled) {
          const filledShares = matched > 0 ? matched : plannedShares;
          if (acct.open) {
            acct.open.realOrderId     = result.orderID;
            acct.open.realOrderStatus = 'matched';
            acct.open.actualShares    = filledShares;
            saveState();
          }
          console.warn(`[real] BUY filled during cancel race — KEEP position, shares=${filledShares}`);
          sendTg(
            `⚠️ <b>Вход всё-таки прошёл</b> — ${entry.side}\n` +
            `Ордер залился в момент отмены (${filledShares} shares). НЕ бросаю позицию — ` +
            `веду её, выход по TP/SL/panic-sell, чтобы не сгорела в ноль.`
          );
          return;
        }

        // Подтверждённо НЕ залилось → чистый откат (без фантома).
        console.warn(`[real] BUY not filled (status=${finalSt?.status || result.status}) — rolled back, NO position`);
        rollback(
          `🚫 <b>Вход не состоялся</b> — ${entry.side}\n` +
          `Нет ликвидности ≤ ${(ceiling * 100).toFixed(0)}¢ за ${BUY_VERIFY_MS / 1000}с — ордер отменён.\n` +
          `Позицию НЕ открыл, реальных акций нет. Жду следующий сигнал.`
        );
      })
      .catch(err => {
        console.error('[real] BUY order FAILED:', err.message);
        rollback(`❌ <b>BUY order failed</b>\n<code>${_tgEsc(err.message)}</code>\nПозиция откатилась.`);
        console.warn('[real] position rolled back due to order failure');
      });
  }
}

function stratClose(s, ctx, reason, exitPolyPrice, acct, isReal) {
  const o      = acct.open;
  // For real orders: use the actual shares we BOUGHT (post-Polymarket-minimum
  // adjustment), not a recomputed estimate. Falls back gracefully for sim.
  const shares = o.actualShares || o.plannedShares || (o.sizeUSDC / o.polyEntryPrice);
  let proceeds, won;
  let settleViaFeed = false;

  if (reason === 'SETTLE') {
    // НАСТОЯЩИЙ резолв: на закрытии выигравшая сторона книги стоит ~1.0 (следует за
    // Chainlink). Берём ЕЁ, а не наш BTC-фид — фид расходится с Chainlink и на тонких
    // окнах давал фантомные «победы». Фолбэк на фид только если рынок ещё не решился
    // (помечаем dirty, такие записи отфильтровываются при анализе статистики).
    const winner = marketResolvedWinner(ctx);
    if (winner !== null) {
      won = (o.side === winner);
    } else {
      const openRef = (ctx.openingBTC != null) ? ctx.openingBTC : o.btcAtEntry;
      won = o.side === 'UP' ? ctx.curBTC > openRef : ctx.curBTC < openRef;
      settleViaFeed = true;
    }
    proceeds      = won ? shares * 1.0 : 0;
    exitPolyPrice = won ? 1.0 : 0.0;
  } else {
    proceeds = shares * exitPolyPrice;
    won      = proceeds > o.sizeUSDC;
  }

  const pnl   = proceeds - o.sizeUSDC;
  const entry = { ...o, closeTime: Date.now(), reason, proceeds, pnl, won, btcAtClose: ctx.curBTC, polyExitPrice: exitPolyPrice, strategy: s.def.id, dirty: (wsStatus === 'sim' || settleViaFeed) ? 1 : 0 };
  acct.balance    += proceeds;
  acct.peakBalance = Math.max(acct.peakBalance, acct.balance);
  acct.log.push(entry);
  if (acct === s.demo) { try { mlExit(s, o, pnl, won, reason, entry.dirty === 1); } catch (_) {} }  // ML-ЛОГ
  if (acct.log.length > 500) acct.log.shift();
  acct.open = null;
  saveState();
  console.log(`[${s.def.id}] ${o.isReal ? 'REAL' : 'SIM'} CLOSE ${o.side} reason=${reason} pnl=${pnl >= 0 ? '+' : ''}$${pnl.toFixed(2)} shares=${shares}`);

  // ── UnderDogHold loss-streak circuit breaker ───────────────────────────────
  // После каждого закрытия демо-сделки underdogHold проверяем серию поражений.
  // Если набралось UNDERDOG_HOLD_LOSS_LIMIT подряд — выключаем REAL у зависимых
  // стратегий и шлём TG. Demo не трогаем — статистика продолжает копиться.
  if (s.def.id === 'underdogHold' && !o.isReal) {
    const log = s.demo.log;
    let streak = 0;
    for (let i = log.length - 1; i >= 0; i--) {
      if (log[i].dirty) continue;   // dirty-записи не считаем
      if (!log[i].won) streak++;
      else break;
    }
    if (streak >= UNDERDOG_HOLD_LOSS_LIMIT) {
      const blocked = [];
      for (const depId of UNDERDOG_LOSS_DEPENDENT_IDS) {
        const dep = STRATEGIES[depId];
        if (!dep) continue;
        if (dep.realEnabled && !dep.underdogHoldAutoBlocked) {
          dep.realEnabled             = false;
          dep.underdogHoldAutoBlocked = true;
          blocked.push(depId);
          console.warn(`[udg-breaker] ${depId} real AUTO-DISABLED — underdogHold ${streak} losses in a row`);
        }
      }
      if (blocked.length > 0) {
        saveState();
        sendTg(
          `🚨 <b>UnderDogHold: ${streak} поражений подряд</b>\n` +
          `Лимит сработал (≥${UNDERDOG_HOLD_LOSS_LIMIT}). Реальная торговля выключена у:\n` +
          blocked.map(id => `• <code>${_tgEsc(id)}</code>`).join('\n') + '\n\n' +
          `Demo продолжает работать. Разберись вручную и включи real обратно на дашборде.`
        );
      }
    }
  }

  // ── Update real-trade tracking for the next-entry guards ──────────────────
  if (o.isReal) {
    s.lastRealCloseTime    = Date.now();
    s.lastRealClosedWindow = o.marketSlug || ctx.win.slug;
    // Прежний «дневной лимит потерь» отключён — риск-контроль теперь это пол по
    // балансу (REAL_MIN_BALANCE), проверяемый перед каждым открытием. Дневной
    // счётчик ниже остаётся только для совместимости/статистики, ничего не стопает.
    const utcToday = new Date().toISOString().slice(0, 10);
    if (s.realDailyLossDate !== utcToday) {
      s.realDailyLossDate   = utcToday;
      s.realDailyLossAmount = 0;
    }
    if (pnl < 0) s.realDailyLossAmount += Math.abs(pnl);
  }

  // ── Telegram alert on real position close (PRELIMINARY — real PnL confirmed after SELL settles) ──
  if (o.isReal) {
    const emoji   = pnl >= 0 ? '✅' : '🔻';
    const sign    = pnl >= 0 ? '+' : '';
    const pctMove = ((proceeds / o.sizeUSDC - 1) * 100).toFixed(1);
    const reasonLabel = reason === 'MANUAL' ? 'Ручной выход (кнопка)' : reason;
    sendTg(
      `${emoji} <b>ЗАКРЫТА</b> — ${o.side}\n` +
      `Стратегия: <i>${_tgEsc(s.def.id)}</i>\n` +
      `Причина: <b>${_tgEsc(reasonLabel)}</b>\n` +
      `P&amp;L (расчёт): <b>${sign}$${pnl.toFixed(2)}</b> (${pctMove}%)\n` +
      `Размер: ${shares} shares = $${o.sizeUSDC.toFixed(2)}\n` +
      `Баланс (модель): $${acct.balance.toFixed(2)}`
    );
  }

  // ── Place real SELL order (or wait for on-chain settlement) ─────────────────
  if (o.isReal) {
    // After any real close, sync acct.balance to actual on-chain balance.
    // This catches all the cases where the model diverges from reality:
    //   - SELL failed (shares stuck) → balance won't grow → acct corrects down
    //   - SELL filled at better price → balance higher than expected → corrects up
    //   - SETTLE redeemed → Polymarket auto-converts winning shares to USDC
    const syncBalanceAfter = (delayMs, label) => setTimeout(async () => {
      const b = await fetchRealBalance();
      if (b !== null) {
        realBalance = b;
        // FIX: раньше тут всегда обновлялся STRATEGIES.momentum, даже если
        // закрылась другая стратегия. Обновляем ИМЕННО эту стратегию (s).
        if (s && s.real && !s.real.open) {
          const before = s.real.balance;
          const drift  = b - before;
          s.real.balance = b;
          s.real.peakBalance = Math.max(s.real.peakBalance, b);
          saveState();
          console.log(`[real] balance sync (${label}): $${before.toFixed(2)} → $${b.toFixed(2)} (drift=${drift >= 0 ? '+' : ''}$${drift.toFixed(2)})`);
          // If there's meaningful drift from model, tell the user.
          if (Math.abs(drift) >= 0.05) {
            sendTg(
              `🔄 <b>Баланс сверен</b>\n` +
              `Модель: $${before.toFixed(2)}\n` +
              `Реально на CLOB: <b>$${b.toFixed(2)}</b>\n` +
              `Расхождение: ${drift >= 0 ? '+' : ''}$${drift.toFixed(2)}`
            );
          }
        }
      }
    }, delayMs);

    if (reason === 'SETTLE') {
      // Polymarket auto-redeems winning tokens ~1 min after window close.
      syncBalanceAfter(90_000, 'post-settle');
    } else if (o.tokenId && o.realOrderId && exitPolyPrice > 0.01) {
      // Early exit (TP / SL / FLIP / ADVERSE): sell shares back on CLOB.
      //
      // Price ladder — 3 attempts, each more aggressive than the last.
      // If none fill, we do NOT dump at a floor price (that would be worse than
      // holding to SETTLE). Instead we cancel any hanging order and wait for the
      // window to expire so Polymarket settles at 0 or 1.
      //
      //   attempt 1 → 97%  of exitPolyPrice  (just below market, fills instantly on normal books)
      //   attempt 2 → 90%  (after 4s — more aggressive)
      //   attempt 3 → 80%  (after 4s — very aggressive, ~best bid on thin books)
      //   if all 3 miss  → cancel last order, wait for on-chain SETTLE
      const SELL_LADDER        = [0.97, 0.90, 0.80];
      const SELL_RETRY_DELAY_MS = 2_000;

      // ── PANIC SELL (рыночный сброс) ──────────────────────────────────────
      // Если лесенка лимитных ордеров не залилась, НЕ держим позицию до SETTLE
      // (для SL это почти гарантированный 0). Вместо этого делаем рыночный
      // выход: ордер FAK (Fill-And-Kill) по "полу" цены. FAK не висит в стакане,
      // а мгновенно сметает все доступные биды сверху вниз по их ценам и убивает
      // остаток. Так мы гарантированно выходим в ту ликвидность, что есть сейчас.
      //   PANIC_SELL=false      → отключить, вернуться к старому "держать до SETTLE"
      //   PANIC_SELL_FLOOR=0.05 → не продавать дешевле 5¢ (по умолчанию 0.01 = любой бид)
      const PANIC_SELL = !['false', '0', 'no', 'off']
        .includes((process.env.PANIC_SELL || 'true').toLowerCase().trim());
      const PANIC_SELL_FLOOR = Math.max(0.01, Math.min(0.99,
        parseFloat(process.env.PANIC_SELL_FLOOR || '0.01') || 0.01));

      // SELL_LADDER_FIRST — пробовать ли лесенку лимиток ПЕРЕД рыночным сбросом.
      //   false (по умолчанию) → сразу паник-селл по рынку (FAK), без задержек.
      //                          FAK всё равно берёт лучшие биды первыми, так что
      //                          в цене не теряем, зато выходим мгновенно и точно.
      //   true                 → старое поведение: 3 лимитки (97→90→80%), и только
      //                          если все промахнулись — паник-селл.
      const SELL_LADDER_FIRST = ['true', '1', 'yes', 'on']
        .includes((process.env.SELL_LADDER_FIRST || 'false').toLowerCase().trim());

      // Рыночный сброс всей позиции через FAK по floor-цене.
      // Возвращает true, если ордер ушёл на матчинг (даже частичный),
      // false — если биржа отвергла ордер (тогда падаем в SETTLE как раньше).
      const panicSell = async () => {
        try {
          const result = await placeClobOrder({
            tokenId:   o.tokenId,
            side:      'SELL',
            size:      shares,
            price:     PANIC_SELL_FLOOR,
            orderType: 'FAK',
          });
          console.log(
            `[real] PANIC SELL (FAK @ ${PANIC_SELL_FLOOR}) orderId=${result.orderID} ` +
            `status=${result.status} shares=${result.actualShares} reason=${reason}`
          );
          sendTg(
            `🆘 <b>PANIC SELL — рыночный сброс</b>\n` +
            `Лимитные попытки не залились — продаю по рынку (FAK).\n` +
            `Беру лучшие биды, принимаю любую цену ≥ ${(PANIC_SELL_FLOOR * 100).toFixed(0)}¢.\n` +
            `Статус: <b>${_tgEsc(result.status || 'placed')}</b> | ${result.actualShares} shares`
          );
          // Дать матчингу/ончейну осесть, затем сверить реальный баланс.
          syncBalanceAfter(8_000, 'post-PANIC-SELL');
          return true;
        } catch (err) {
          console.error(`[real] PANIC SELL failed (${reason}):`, err.message);
          sendTg(
            `❌ <b>PANIC SELL не прошёл</b>: ${_tgEsc(err.message)}\n` +
            `Стакан пустой или ордер отвергнут — остаётся ждать SETTLE.`
          );
          return false;
        }
      };

      const trySellWithRetry = async () => {
        let lastOrderId = null;

        // ── Прямой выход по рынку (по умолчанию) ──────────────────────────
        // Не тратим время на лесенку: сразу сбрасываем позицию рыночным FAK.
        // FAK забирает лучшие биды первыми, поэтому цена не хуже лесенки,
        // зато выход мгновенный и без риска "повисеть в стакане".
        if (!SELL_LADDER_FIRST) {
          if (PANIC_SELL) {
            console.warn(`[real] straight-to-market exit (FAK), reason=${reason}`);
            const dumped = await panicSell();
            if (dumped) return;
            // FAK не нашёл ликвидности → падаем в SETTLE ниже.
          }
          console.warn(`[real] no market liquidity / panic disabled — holding for SETTLE`);
          sendTg(
            `⏳ <b>Выход по рынку не удался</b> (${_tgEsc(reason)})\n` +
            `${PANIC_SELL ? 'Стакан пустой — ' : 'Panic sell выключен — '}` +
            `жду SETTLE (~${Math.max(0, Math.round((o.expiryTime - Date.now()) / 1000))}с).\n` +
            `Финальный P&amp;L будет после закрытия окна.`
          );
          syncBalanceAfter(Math.max(60_000, o.expiryTime + 90_000 - Date.now()), 'post-SETTLE-fallback');
          return;
        }

        // ── Лесенка лимиток (SELL_LADDER_FIRST=true) ──────────────────────
        for (let attempt = 0; attempt < SELL_LADDER.length; attempt++) {
          const sellPrice = Math.max(0.01, parseFloat((exitPolyPrice * SELL_LADDER[attempt]).toFixed(4)));

          try {
            const result = await placeClobOrder({ tokenId: o.tokenId, side: 'SELL', size: shares, price: sellPrice });
            lastOrderId = result.orderID;
            console.log(`[real] SELL placed (attempt ${attempt + 1}/${SELL_LADDER.length}) orderId=${result.orderID} reason=${reason} price=${sellPrice} shares=${result.actualShares}`);

            if (result.status === 'matched') {
              // Filled immediately — done
              syncBalanceAfter(5_000, `post-SELL-attempt${attempt + 1}`);
              return;
            }

            // Order placed but unmatched — wait and check
            await new Promise(r => setTimeout(r, SELL_RETRY_DELAY_MS));
            const orderStatus   = await getClobOrderStatus(result.orderID);
            const isFullyFilled = orderStatus?.status === 'MATCHED'
              || parseFloat(orderStatus?.size_matched || '0') >= shares * 0.99;

            if (isFullyFilled) {
              console.log(`[real] SELL filled on delay (attempt ${attempt + 1}) price=${sellPrice}`);
              syncBalanceAfter(5_000, `post-SELL-attempt${attempt + 1}`);
              return;
            }

            // Not filled — cancel and try next step
            await cancelClobOrder(result.orderID);
            lastOrderId = null;

            if (attempt < SELL_LADDER.length - 1) {
              const nextPct = (SELL_LADDER[attempt + 1] * 100).toFixed(0);
              console.warn(`[real] SELL unmatched @ ${(sellPrice*100).toFixed(1)}¢ — trying ${nextPct}% (attempt ${attempt + 2})`);
              sendTg(`⚠️ <b>SELL не заполнен</b> @ ${(sellPrice*100).toFixed(1)}¢ — пробую ${nextPct}% (попытка ${attempt + 2}/${SELL_LADDER.length})`);
            }
          } catch (err) {
            console.error(`[real] SELL attempt ${attempt + 1} API error (${reason}):`, err.message);
            lastOrderId = null;
            if (attempt < SELL_LADDER.length - 1) {
              await new Promise(r => setTimeout(r, SELL_RETRY_DELAY_MS));
            }
          }
        }

        // ── Лесенка не залилась ──────────────────────────────────────────
        // Раньше тут бот просто держал позицию до SETTLE. Для SL это означало
        // почти гарантированный 0 (рынок ушёл против нас). Теперь сначала
        // пытаемся выйти по рынку (FAK), и только если стакан совсем пуст —
        // падаем в ожидание SETTLE.
        console.warn(`[real] SELL: all ${SELL_LADDER.length} ladder attempts missed`);

        if (PANIC_SELL) {
          console.warn('[real] firing PANIC market sell (FAK)…');
          const dumped = await panicSell();
          if (dumped) return; // вышли по рынку — дальше не ждём SETTLE
        }

        // PANIC_SELL выключен ИЛИ стакан пуст / ордер отвергнут → последний
        // рубеж: ждём ончейн-SETTLE по истечении окна.
        console.warn(`[real] holding for on-chain SETTLE (panic ${PANIC_SELL ? 'failed' : 'disabled'})`);
        sendTg(
          `⏳ <b>Выход по рынку не удался</b> (${_tgEsc(reason)})\n` +
          `${PANIC_SELL ? 'Стакан пустой — ' : 'Panic sell выключен — '}` +
          `жду SETTLE (~${Math.max(0, Math.round((o.expiryTime - Date.now()) / 1000))}с).\n` +
          `Финальный P&amp;L будет после закрытия окна.`
        );
        syncBalanceAfter(Math.max(60_000, o.expiryTime + 90_000 - Date.now()), 'post-SETTLE-fallback');
      };

      trySellWithRetry();
    } else if (o.tokenId && !o.realOrderId) {
      // BUY order was placed but hasn't confirmed yet — wait then cancel
      console.warn('[real] closing before BUY order confirmed — will cancel once orderId is known');
      const waitAndCancel = async () => {
        for (let i = 0; i < 10; i++) {
          await new Promise(r => setTimeout(r, 1000));
          if (o.realOrderId) { await cancelClobOrder(o.realOrderId); return; }
        }
        console.warn('[real] BUY orderId never arrived — could not cancel');
      };
      waitAndCancel().catch(e => console.error('[real] waitAndCancel error:', e.message));
      syncBalanceAfter(15_000, 'post-cancel');
    }
  }
}

function processAccount(s, ctx, acct, isReal) {
  if (acct.open) {
    // FIX (settle-race): пока позиция открыта и poly.market ещё принадлежит ЕЁ
    // окну — запоминаем последние цены этого рынка. На SETTLE используем их,
    // а не «снапшот после expiry», который мог уже принадлежать НОВОМУ рынку.
    if (poly.market && poly.market.eventSlug === acct.open.marketSlug
        && ctx.polyUp != null && ctx.polyDn != null && Date.now() < acct.open.expiryTime + 4000) {
      acct.open._lastOwnUp = ctx.polyUp;
      acct.open._lastOwnDn = ctx.polyDn;
    }
    // Реальный вход ещё не подтверждён (BUY висит / идёт проверка заполнения)?
    // НЕ трогаем позицию логикой выхода — иначе можем отменить собственную
    // покупку до того, как она зальётся (так была упущена сделка @13.5¢).
    // В этот момент позицией управляет verify-логика в stratOpen: она либо
    // подтвердит заполнение (status→matched), либо откатит вход.
    if (isReal && acct.open.isReal && acct.open.realOrderStatus === 'pending') {
      return;
    }
    if (Date.now() >= acct.open.expiryTime) {
      // ── SETTLE: закрываем позицию немедленно, не блокируя вход в новое окно ──
      // Проблема старого подхода: ждали до 60с пока рынок «дорезолвится», но за это
      // время новое окно уже шло и ctx.polyUp/polyDn уже принадлежали НОВОМУ рынку
      // → фантомные победы/поражения. Плюс стратегия не могла открыть новую сделку.
      //
      // Новый подход:
      // 1. При первом попадании в блок (сразу после expiryTime) — снимаем snapshot
      //    цен этого момента и сохраняем в acct.open. Это последние котировки
      //    старого рынка (ещё не переключились на новый).
      // 2. Пробуем определить победителя по snapshot.
      // 3. Если snapshot нечёткий — даём 5 секунд (не 60!) на дорезолв.
      // 4. По истечении 5 секунд — всегда закрываем (с фолбэком на BTC-фид).
      //    Это освобождает позицию и позволяет войти в новое окно.
      const SETTLE_FAST_WAIT_MS = 5000; // максимум 5 сек ожидания, не 60

      // Снимаем snapshot цен в момент первого попадания в блок.
      // FIX: приоритет — последним ценам СВОЕГО рынка (_lastOwnUp/_lastOwnDn),
      // сохранённым пока poly.market ещё принадлежал окну позиции. Старый
      // снапшот мог взять цены уже НОВОГО рынка (fetchPolyMarket крутится каждые 1.5с).
      if (!acct.open._settleSnapshotUp) {
        if (acct.open._lastOwnUp != null) {
          acct.open._settleSnapshotUp = acct.open._lastOwnUp;
          acct.open._settleSnapshotDn = acct.open._lastOwnDn;
          acct.open._settleDetectedAt = Date.now();
        } else if (ctx.polyUp != null && poly.market && poly.market.eventSlug === acct.open.marketSlug) {
          acct.open._settleSnapshotUp = ctx.polyUp;
          acct.open._settleSnapshotDn = ctx.polyDn;
          acct.open._settleDetectedAt = Date.now();
        }
      }

      // Пробуем определить победителя: сначала по snapshot, потом по текущим ценам
      const snapshotCtx = (acct.open._settleSnapshotUp != null)
        ? { ...ctx, polyUp: acct.open._settleSnapshotUp, polyDn: acct.open._settleSnapshotDn }
        : ctx;
      const decisive = marketResolvedWinner(snapshotCtx) !== null
                    || marketResolvedWinner(ctx) !== null;

      const waitedMs = Date.now() - (acct.open._settleDetectedAt || acct.open.expiryTime);
      if (!decisive && waitedMs < SETTLE_FAST_WAIT_MS) return; // даём 5 сек — не 60

      // Закрываем с лучшим из доступных контекстов
      const closeCtx = (decisive && marketResolvedWinner(snapshotCtx) !== null) ? snapshotCtx : ctx;
      stratClose(s, closeCtx, 'SETTLE', null, acct, isReal); return;
    }
    const exit = s.def.shouldExit(ctx, acct.open, s.params);
    if (exit && exit.exitPrice !== null) {
      let xp = exit.exitPrice;
      // Реальный спред в demo: продаём в BID стороны (как реал получает при выходе).
      if (acct === s.demo && DEMO_REAL_SPREAD && exit.reason !== 'SETTLE') {
        const q = _sideQuote(acct.open.side);
        if (q.bid != null) xp = q.bid;
      }
      stratClose(s, ctx, exit.reason, xp, acct, isReal);
    }
  } else {
    if (ctx.polyUp === null) return;
    if (!strategyEntriesAllowed(s)) { acct.pendingEntry = null; return; } // расписание (своё или глобальное): вне окна не открываем

    // DEMO: реалистичный вход с задержкой и отсечкой «улетевшей» цены.
    if (acct === s.demo && DEMO_ENTRY_DELAY_MS > 0) {
      const now   = Date.now();
      // FIX: намерение, зафиксированное в прошлом окне, не должно исполняться
      // в новом (чужие цены / чужой рынок). Сбрасываем при смене slug.
      if (acct.pendingEntry && acct.pendingEntry.slug !== ctx.win.slug) acct.pendingEntry = null;
      const entry = s.def.shouldEnter(ctx, s.params);
      if (!acct.pendingEntry) {
        // фиксируем намерение войти и ждём задержку (заливаемся позже, по факту-цене)
        if (entry) acct.pendingEntry = { side: entry.side, signalPrice: entry.polyPrice, fireAt: now + DEMO_ENTRY_DELAY_MS, slug: ctx.win.slug };
        return;
      }
      if (now < acct.pendingEntry.fireAt) return;       // ещё ждём
      const sig = acct.pendingEntry;
      acct.pendingEntry = null;                          // намерение израсходовано
      if (!entry || entry.side !== sig.side) return;     // сигнал пропал/сменился за задержку → не входим
      const chase = (entry.polyPrice - sig.signalPrice) / sig.signalPrice;
      if (chase > DEMO_MAX_CHASE) {                       // цена убежала вверх → «нет ликвидности», пропускаем
        console.log(`[demo] SKIP — цена убежала +${(chase*100).toFixed(0)}% за задержку (вагон уехал)`);
        return;
      }
      stratOpen(s, ctx, entry, acct, false);             // заливаемся по ТЕКУЩЕЙ (после задержки) цене
      return;
    }

    const entry = s.def.shouldEnter(ctx, s.params);
    if (entry) stratOpen(s, ctx, entry, acct, isReal);
  }
}

function processStrategies() {
  const ctx = getStratContext();
  resolveCalib(ctx);
  // Трекаем экстремумы BTC текущего окна (для range/волатильность-фильтров новых стратегий)
  if (ctx.curBTC != null) {
    poly.winHi = (poly.winHi == null) ? ctx.curBTC : Math.max(poly.winHi, ctx.curBTC);
    poly.winLo = (poly.winLo == null) ? ctx.curBTC : Math.min(poly.winLo, ctx.curBTC);
  }
  for (const id in STRATEGIES) {
    const s = STRATEGIES[id];
    if (ticks.length < 60) continue;

    // ИЗОЛЯЦИЯ: ошибка в одной стратегии/аккаунте НЕ должна срывать обработку
    // остальных (раньше throw в любой shouldEnter/shouldExit/stratOpen прерывал
    // ВЕСЬ тик — все стратегии ПОСЛЕ сбойной переставали торговать и в demo, и в real).
    // Demo account — always simulation, never real orders
    if (s.demoEnabled) {
      try { processAccount(s, ctx, s.demo, false); }
      catch (e) { console.error(`[tick] ${id} demo error:`, e && e.message); }
    }

    // Real account — places CLOB orders if wallet is configured; otherwise sim
    if (s.realEnabled && !s.pendingReal) {
      // FIX: в SIM-режиме реальные ордера ЗАПРЕЩЕНЫ — данные BTC симулированные.
      const canReal = REAL_TRADING && !!polyWallet && !!polyApiCreds && !isSim;
      try { processAccount(s, ctx, s.real, canReal); }
      catch (e) { console.error(`[tick] ${id} real error:`, e && e.message); }
    }
  }
}

// ─── COINBASE WEBSOCKET ──────────────────────────────────────────────────────
let ws_ = null;
let simInterval = null, simRetry = null;   // хэндлы цикла симуляции и таймера авто-переподключения

function connectCoinbase() {
  wsStatus = 'connecting';
  try {
    ws_ = new WebSocket('wss://advanced-trade-ws.coinbase.com');
    const timeout = setTimeout(() => { if (wsStatus !== 'live') { try { ws_.terminate(); } catch (_) {} if (!isSim) startSim(); } }, 10000);

    ws_.on('open', () => {
      const sub = {
        type: 'subscribe',
        product_ids: ['BTC-USD'],
        channel: 'market_trades',
      };
      ws_.send(JSON.stringify(sub));
      ws_.send(JSON.stringify({ ...sub, channel: 'ticker' }));
      ws_.send(JSON.stringify({ ...sub, channel: 'level2' }));
    });

    ws_.on('message', raw => {
      let d;
      try { d = JSON.parse(raw); } catch (_) { return; }
      if (!wsStatus.startsWith('live') && d.channel) {
        wsStatus = 'live';
        clearTimeout(timeout);
        exitSim();                       // вернулись из SIM в реальные цены
        console.log('[coinbase] ws connected');
      }
      if (d.channel === 'market_trades' && d.events) {
        d.events.forEach(ev => (ev.trades || []).forEach(tr => pushTick(parseFloat(tr.price), parseFloat(tr.size), tr.side)));
      }
      if (d.channel === 'ticker' && d.events) {
        d.events.forEach(ev => (ev.tickers || []).forEach(tk => {
          if (tk.best_bid) bestBid = parseFloat(tk.best_bid);
          if (tk.best_ask) bestAsk = parseFloat(tk.best_ask);
        }));
      }
      if ((d.channel === 'l2_data' || d.channel === 'level2') && d.events) {
        d.events.forEach(ev => {
          if (ev.type === 'snapshot') { book.bids.clear(); book.asks.clear(); }
          (ev.updates || []).forEach(u => {
            const side  = u.side === 'bid' ? 'bid' : 'ask';
            const price = parseFloat(u.price_level), size = parseFloat(u.new_quantity);
            if (!isNaN(price) && !isNaN(size)) updateBookLevel(side, price, size);
          });
        });
      }
    });

    ws_.on('error', () => { if (wsStatus !== 'live' && !isSim) startSim(); });
    ws_.on('close', () => {
      if (wsStatus === 'live') {
        wsStatus = 'reconnecting';
        console.log('[coinbase] disconnected — reconnecting in 3s');
        setTimeout(connectCoinbase, 3000);
      }
    });
  } catch (e) { if (!isSim) startSim(); }
}

// ─── SIMULATION MODE ─────────────────────────────────────────────────────────
function exitSim() {
  if (!isSim) return;
  isSim = false;
  if (simInterval) { clearInterval(simInterval); simInterval = null; }
  if (simRetry)    { clearInterval(simRetry);    simRetry = null; }
  console.log('[sim] stopped — back to live Coinbase');
}

function startSim() {
  if (isSim) return;
  isSim    = true;
  wsStatus = 'sim';
  // FIX: в SIM-режиме обнуляем Chainlink-цену, чтобы getStratContext брал цену
  // из sim-тиков, а не из устаревшего (или, как раньше, ПОДМЕНЁННОГО фейком)
  // chain.currentPrice. Реальная торговля в SIM полностью запрещена (см. canReal).
  chain.currentPrice = null;
  chain.available    = false;
  console.log('[sim] started (ws blocked/failed) — будет пробовать вернуться в live каждые 30с');
  // Авто-восстановление: пока в SIM, периодически пробуем переподключиться к Coinbase.
  // Как только WS оживёт, message-handler вызовет exitSim() и SIM остановится.
  if (!simRetry) simRetry = setInterval(() => { if (isSim) { console.log('[sim] retry coinbase…'); connectCoinbase(); } }, 30000);
  let price = 107650;
  sessionStart = price;
  bestBid = price - 0.5; bestAsk = price + 0.5;
  let trend = 0, trendLife = 0, regime = 'ranging';

  const seedBook = () => {
    book.bids.clear(); book.asks.clear();
    for (let i = 0; i < 20; i++) {
      book.bids.set(+(price - i * 0.5 - 0.3).toFixed(2), +(Math.random() * 1.5 + 0.1).toFixed(4));
      book.asks.set(+(price + i * 0.5 + 0.3).toFixed(2), +(Math.random() * 1.5 + 0.1).toFixed(4));
    }
  };
  seedBook();

  simInterval = setInterval(() => {
    if (Math.random() < 0.005) regime = ['trending', 'ranging', 'volatile'][Math.floor(Math.random() * 3)];
    if (Math.random() < 0.015) { trend = (Math.random() - 0.46) * 2; trendLife = Math.random() * 50 + 10; }
    trendLife > 0 ? trendLife-- : (trend *= 0.97);
    const noise = regime === 'volatile' ? 20 : regime === 'trending' ? 5 : 9;
    price += trend * (regime === 'trending' ? 1.4 : 0.6) * 0.9 + (Math.random() - 0.5) * noise + (107650 - price) * 0.00012;
    price  = Math.max(95000, Math.min(120000, price));
    bestBid = price - (0.3 + Math.random() * 0.8);
    bestAsk = price + (0.3 + Math.random() * 0.8);
    seedBook();
    const buyBias = 0.48 + trend * 0.09 + (Math.random() - 0.5) * 0.22;
    const n = Math.floor(Math.random() * 5) + 1;
    for (let i = 0; i < n; i++) pushTick(price + (Math.random() - 0.5) * noise * 0.25, Math.random() * 0.35 + 0.005, Math.random() > buyBias ? 'BUY' : 'SELL');
    // FIX: раньше тут sim ПЕРЕЗАПИСЫВАЛ chain.currentPrice фейковой ценой —
    // при живом REAL_TRADING это позволяло ставить реальные ордера по выдуманному
    // BTC. Теперь sim живёт только в ticks/book; chain не трогаем.
  }, 120);
}

// ─── STATE SNAPSHOT FOR DASHBOARD ────────────────────────────────────────────
function accountSummary(acct) {
  const log  = acct.log;
  const wins = log.filter(t => t.won).length;
  const pnl  = log.reduce((a, t) => a + t.pnl, 0);
  const dd   = (() => {
    let peak = 1000, cur = 1000, d = 0;
    for (const t of log) { cur += t.pnl; peak = Math.max(peak, cur); d = Math.min(d, (cur - peak) / peak); }
    return d;
  })();
  return {
    balance:    acct.balance,
    pnl,
    trades:     log.length,
    wins,
    dd,
    open:       acct.open,
    lastTrades: log.slice(-5).reverse(),
  };
}

function buildSnapshot() {
  const sigS   = predictScalp();
  const sigP   = predictPoly();
  const sigM   = computeMainSignal();
  const curBTC = chain.currentPrice || (ticks.length ? ticks[ticks.length - 1].price : null);
  const win    = currentPolyWindow();

  // Per-strategy summary
  const strats = {};
  for (const id in STRATEGIES) {
    const s = STRATEGIES[id];
    strats[id] = {
      name:        s.def.name,
      desc:        s.def.desc,
      manual:      !!s.def.manual,
      demoEnabled: s.demoEnabled,
      realEnabled: s.realEnabled,
      schedEnabled: s.schedEnabled, schedFrom: s.schedFrom, schedTo: s.schedTo,
      demo:        accountSummary(s.demo),
      real:        accountSummary(s.real),
      pendingReal: s.pendingReal,
      customEnabled: s.customEnabled,
      customParams:  s.customParams,
      params:        s.params,
    };
  }

  return {
    ts:        Date.now(),
    ws:        wsStatus,
    isSim,
    btc:       curBTC,
    bestBid, bestAsk,
    poly: {
      status:   poly.status,
      lastErr:  poly.lastErr,
      up:       poly.prices.up,
      down:     poly.prices.down,
      priceTs:  poly.prices.ts,
      opening:  poly.windowOpeningBTC,
      openingSrc: poly.windowOpeningSource,
      market:   poly.market ? { slug: poly.market.eventSlug, windowEnd: poly.market.windowEnd } : null,
    },
    chain: {
      price:    chain.currentPrice,
      lastUpdate: chain.lastUpdate,
      available: chain.available,
    },
    win: { endTs: win.endTs, msLeft: Math.max(0, win.endTs - Date.now()) },
    signals: { scalp: sigS, poly: sigP, main: sigM },
    strats,
    realTrading: {
      enabled:  REAL_TRADING,
      ready:    !!(polyWallet && polyApiCreds),
      wallet:   polyWallet?.address ?? null,
      balance:  realBalance,
    },
    copy: copySnapshot(),
    config: {
      invertSignal: INVERT_SIGNAL, tpAbsPrice: TP_ABS_PRICE, minEntryPrice: MIN_ENTRY_PRICE,
      dailyLossCap: REAL_DAILY_LOSS_CAP, minBalance: REAL_MIN_BALANCE,
      demoDelaySec: DEMO_ENTRY_DELAY_MS / 1000, demoMaxChasePct: DEMO_MAX_CHASE * 100,
      schedEnabled: SCHEDULE_ENABLED, schedFrom: SCHEDULE_FROM, schedTo: SCHEDULE_TO,
      entriesAllowedNow: entriesAllowedNow(),
      demoRealSpread: DEMO_REAL_SPREAD,
      calibTotal: calibLog.length,
      calibResolved: calibLog.filter(r => r.outcome === 'UP' || r.outcome === 'DOWN').length,
    },
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// КОПИТРЕЙДИНГ POLYMARKET — движок ────────────────────────────────────────────
// ─────────────────────────────────────────────────────────────────────────────
// До 5 кошельков. Опрашиваем публичный Data API (история сделок). Сделки ПОСЛЕ
// добавления кошелька копируются в copy-счёт фиксированным размером copyUSD на
// вход. SELL источника закрывает нашу копию по их цене (реализуем PnL). Открытые
// позиции маркуем по midpoint CLOB и авто-закрываем при резолве (mid→1 / →0).
// Реальный режим — те же расчёты; реальные ордера только при COPY_REAL_LIVE.
// Полностью отделён от BTC-стратегий: свой реестр, свой цикл, свой раздел на UI.

function _copyId()      { return 'cw_' + Math.random().toString(36).slice(2, 9); }
function _copyAccount() { return { balance: COPY_START_BALANCE, positions: {}, log: [] }; }

function _copyMakeWallet({ address, label, copyUSD }) {
  const addr = String(address || '').trim().toLowerCase();
  return {
    id: _copyId(), address: addr,
    label: (label || '').trim() || (addr.slice(0, 6) + '…' + addr.slice(-4)),
    copyUSD: Math.max(1, Number(copyUSD) || 20),
    demoEnabled: true, realEnabled: false,
    demo: _copyAccount(), real: _copyAccount(),
    feed: [], seen: new Set(),
    startTs: Date.now(), createdAt: Date.now(),
    lastPollTs: 0, lastErr: null,
  };
}

function _copyParseFill(t) {
  const side   = String(t.side || '').toUpperCase();
  const price  = Number(t.price);
  const shares = Number(t.size);
  const token  = t.asset || t.tokenId || t.token_id;
  if (!token || !(price > 0) || !(shares > 0) || (side !== 'BUY' && side !== 'SELL')) return null;
  return {
    side, price, shares, tokenId: String(token),
    market:  t.title || t.market || t.eventSlug || 'Polymarket',
    slug:    t.slug || t.eventSlug || '',
    outcome: t.outcome || (t.outcomeIndex != null ? `#${t.outcomeIndex}` : ''),
    ts:      (Number(t.timestamp) || Math.floor(Date.now() / 1000)) * 1000,
    usd:     price * shares,
  };
}

// Единый ключ дедупликации — общий для опроса (Data API) и турбо (ончейн),
// чтобы один и тот же филл не применился дважды из двух источников.
function _copyFillKey(fill, txHash) {
  return (txHash || ('t' + fill.ts)) + ':' + fill.tokenId + ':' + fill.side + ':' + (Math.round(fill.shares * 10) / 10);
}

// Применяет филл к кошельку: дедуп → лента → demo/real счета. Возвращает true, если применён.
async function _copyRouteFill(wallet, fill, txHash, src) {
  if (!fill) return false;
  const key = _copyFillKey(fill, txHash);
  if (wallet.seen.has(key)) return false;
  wallet.seen.add(key);
  if (fill.ts < wallet.startTs - 5000) return false;             // копируем только сделки ПОСЛЕ добавления
  wallet.feed.unshift({ side: fill.side, price: fill.price, shares: fill.shares,
    usd: fill.usd, market: fill.market, outcome: fill.outcome, ts: fill.ts, src: src || 'poll' });
  if (wallet.feed.length > 30) wallet.feed.pop();
  if (wallet.demoEnabled) await _copyApplyFill(wallet, wallet.demo, fill, false);
  if (wallet.realEnabled) await _copyApplyFill(wallet, wallet.real, fill, true);
  _copyDirty = true;
  return true;
}

// Реальный ордер копитрейда — только при мастер-флаге COPY_REAL_LIVE и кошельке/ключах.
async function _copyTryRealOrder(wallet, side, fill, usd) {
  if (!COPY_REAL_LIVE) return;                                  // мастер-предохранитель (paper по умолчанию)
  if (!REAL_TRADING || !polyClob || !polyApiCreds || isSim) return;
  if (side === 'BUY' && realBalance !== null && (realBalance - (usd || 0)) < REAL_MIN_BALANCE) {
    console.log(`[copy] real BUY skip — ниже пола баланса $${REAL_MIN_BALANCE}`); return;
  }
  try {
    const price = Math.min(0.99, Math.max(0.01, side === 'BUY' ? fill.price + 0.02 : fill.price - 0.02));
    await placeClobOrder({ tokenId: fill.tokenId, side,
      size: side === 'BUY' ? usd : fill.shares, price, orderType: 'GTC' });
    console.log(`[copy] REAL ${side} placed (${wallet.label}) token=${fill.tokenId.slice(0, 10)}…`);
  } catch (e) { console.error(`[copy] real ${side} error:`, e && e.message); }
}

// Зеркалируем один филл в счёт (demo или real).
async function _copyApplyFill(wallet, acct, fill, isReal) {
  const copyUSD = Math.max(1, wallet.copyUSD || 20);
  if (fill.side === 'BUY') {
    if (acct.balance < copyUSD) return;                          // нет средств на копию
    const addShares = copyUSD / fill.price;
    const pos = acct.positions[fill.tokenId];
    if (pos) {
      if ((pos.adds || 1) >= 4) return;                          // не усредняем бесконечно
      pos.shares += addShares; pos.costUSD += copyUSD;
      pos.avgPrice = pos.costUSD / pos.shares; pos.adds = (pos.adds || 1) + 1; pos.lastPrice = fill.price;
    } else {
      acct.positions[fill.tokenId] = {
        tokenId: fill.tokenId, market: fill.market, slug: fill.slug, outcome: fill.outcome,
        shares: addShares, avgPrice: fill.price, costUSD: copyUSD,
        openTime: fill.ts, lastPrice: fill.price, adds: 1,
      };
    }
    acct.balance -= copyUSD;
    if (isReal) await _copyTryRealOrder(wallet, 'BUY', fill, copyUSD);
  } else {                                                       // SELL → закрываем копию по их цене
    const pos = acct.positions[fill.tokenId];
    if (!pos) return;
    const proceeds = pos.shares * fill.price;
    const pnl = proceeds - pos.costUSD;
    acct.balance += proceeds;
    acct.log.push({ tokenId: fill.tokenId, market: pos.market, outcome: pos.outcome,
      entryPrice: pos.avgPrice, exitPrice: fill.price, shares: pos.shares, sizeUSD: pos.costUSD,
      pnl, won: pnl > 0, openTime: pos.openTime, closeTime: fill.ts, reason: 'COPY-SELL' });
    if (acct.log.length > 500) acct.log = acct.log.slice(-500);
    const shares = pos.shares;
    delete acct.positions[fill.tokenId];
    if (isReal) await _copyTryRealOrder(wallet, 'SELL', { ...fill, shares }, null);
  }
}

// Маркируем открытые позиции по midpoint CLOB и авто-закрываем при резолве.
async function _copyMarkAndResolve(wallet, acct, isReal) {
  for (const tk of Object.keys(acct.positions).slice(0, 8)) {
    const pos = acct.positions[tk];
    if (!pos) continue;
    let mid = null;
    try { mid = await fetchPolyMidpoint(tk); } catch (_) {}
    if (mid == null || !isFinite(mid)) continue;
    pos.lastPrice = mid;
    const resolved = mid >= 0.97 ? 1 : (mid <= 0.03 ? 0 : null);
    if (resolved != null && (Date.now() - pos.openTime) > 60000) {
      const proceeds = pos.shares * resolved;
      const pnl = proceeds - pos.costUSD;
      acct.balance += proceeds;
      acct.log.push({ tokenId: tk, market: pos.market, outcome: pos.outcome,
        entryPrice: pos.avgPrice, exitPrice: resolved, shares: pos.shares, sizeUSD: pos.costUSD,
        pnl, won: pnl > 0, openTime: pos.openTime, closeTime: Date.now(), reason: 'RESOLVE' });
      if (acct.log.length > 500) acct.log = acct.log.slice(-500);
      delete acct.positions[tk];
    }
  }
}

async function _copyPollWallet(wallet) {
  if (wallet._backoffUntil && Date.now() < wallet._backoffUntil) return;   // под rate-limit/ошибкой — ждём
  let trades = [];
  try {
    const res = await fetch(`${POLY_DATA}/trades?user=${wallet.address}&limit=${COPY_FETCH_LIMIT}`, { signal: AbortSignal.timeout(7000) });
    if (res.status === 429) { wallet._backoffUntil = Date.now() + COPY_BACKOFF_429; wallet.lastErr = 'rate-limit (429) — пауза'; wallet.lastPollTs = Date.now(); return; }
    if (!res.ok) throw new Error('HTTP ' + res.status);
    const j = await res.json();
    trades = Array.isArray(j) ? j : (j.data || j.trades || []);
    wallet.lastErr = null; wallet._backoffUntil = 0;
  } catch (e) {
    wallet.lastErr = e.message || String(e);
    wallet._backoffUntil = Date.now() + COPY_BACKOFF_ERR;                  // не долбим API при сетевых сбоях
    wallet.lastPollTs = Date.now(); return;
  }

  const parsed = [];
  for (const t of trades) {
    const fill = _copyParseFill(t);
    if (!fill) continue;
    parsed.push({ fill, txHash: (t.transactionHash || t.transaction_hash || '') });
  }
  parsed.sort((a, b) => a.fill.ts - b.fill.ts);                            // старые → новые
  for (const { fill, txHash } of parsed) {
    await _copyRouteFill(wallet, fill, txHash, 'poll');
  }
  if (wallet.seen.size > 6000) wallet.seen = new Set([...wallet.seen].slice(-3000));

  // Маркировка открытых позиций по midpoint — дорого, поэтому реже, чем опрос сделок.
  if (Date.now() - (wallet._lastMarkTs || 0) >= COPY_MARK_MS) {
    wallet._lastMarkTs = Date.now();
    const before = (wallet.demo.log.length + wallet.real.log.length);
    if (wallet.demoEnabled) await _copyMarkAndResolve(wallet, wallet.demo, false);
    if (wallet.realEnabled) await _copyMarkAndResolve(wallet, wallet.real, true);
    if ((wallet.demo.log.length + wallet.real.log.length) !== before) _copyDirty = true;
  }
  wallet.lastPollTs = Date.now();
}

async function copyPollAll() {
  if (_copyPollBusy || !COPY_WALLETS.length) return;
  _copyPollBusy = true;
  try {
    // Параллельно: один медленный кошелёк не задерживает остальные.
    await Promise.allSettled(COPY_WALLETS.map(w =>
      _copyPollWallet(w).catch(e => { console.error('[copy] poll', w.label, e && e.message); })));
    if (_copyDirty && Date.now() - _copyLastSave >= COPY_SAVE_MS) {
      saveState(); _copyLastSave = Date.now(); _copyDirty = false;
    }
  } finally { _copyPollBusy = false; }
}

// Адаптивный цикл: когда ТУРБО (ончейн-WS) подключён — опрос редкий (только сверка),
// иначе быстрый. Самопланируется, чтобы менять темп на лету.
function _copyScheduleLoop() {
  const delay = (_turbo.connected ? COPY_POLL_RECON_MS : COPY_POLL_MS);
  setTimeout(async () => { try { await copyPollAll(); } catch (_) {} _copyScheduleLoop(); }, delay);
}
_copyScheduleLoop();

// ═══════════════════════════════════════════════════════════════════════════
// ТУРБО-РЕЖИМ: ончейн-вотчер OrderFilled (push, без задержки Data API) ─────────
// ─────────────────────────────────────────────────────────────────────────────
// Слушаем событие OrderFilled контрактов биржи Polymarket на Polygon через WSS-RPC.
// Фильтр по topic: maker ∈ {наши адреса} ИЛИ taker ∈ {наши адреса} — RPC шлёт только
// нужные логи. Падает безопасно: при отвале WS работает обычный опрос (фолбэк).
const _ORDER_FILLED_ABI = ['event OrderFilled(bytes32 indexed orderHash, address indexed maker, address indexed taker, uint256 makerAssetId, uint256 takerAssetId, uint256 makerAmountFilled, uint256 takerAmountFilled, uint256 fee)'];
const _ifaceOF   = new ethers.Interface(_ORDER_FILLED_ABI);
const _OF_TOPIC  = ethers.id('OrderFilled(bytes32,address,address,uint256,uint256,uint256,uint256,uint256)');

// Декод одного лога OrderFilled в наш fill для конкретного кошелька (или null).
function _copyDecodeOnchain(parsed, walletAddr) {
  const maker = parsed.args.maker.toLowerCase();
  const taker = parsed.args.taker.toLowerCase();
  const w = walletAddr.toLowerCase();
  const isMaker = maker === w, isTaker = taker === w;
  if (!isMaker && !isTaker) return null;
  const mId = parsed.args.makerAssetId, tId = parsed.args.takerAssetId;       // BigInt
  const mAmt = Number(parsed.args.makerAmountFilled) / 1e6;
  const tAmt = Number(parsed.args.takerAmountFilled) / 1e6;
  let side, tokenId, shares, price;
  if (isMaker) {
    if (mId === 0n)      { side = 'BUY';  tokenId = tId.toString(); shares = tAmt; price = tAmt > 0 ? mAmt / tAmt : 0; }
    else if (tId === 0n) { side = 'SELL'; tokenId = mId.toString(); shares = mAmt; price = mAmt > 0 ? tAmt / mAmt : 0; }
    else return null;
  } else {
    if (tId === 0n)      { side = 'BUY';  tokenId = mId.toString(); shares = mAmt; price = mAmt > 0 ? tAmt / mAmt : 0; }
    else if (mId === 0n) { side = 'SELL'; tokenId = tId.toString(); shares = tAmt; price = tAmt > 0 ? mAmt / tAmt : 0; }
    else return null;
  }
  if (!(price > 0) || !(shares > 0) || price > 1) return null;
  return { side, price, shares, tokenId, market: '⚡ on-chain', slug: '', outcome: '', ts: Date.now(), usd: price * shares };
}

async function _copyOnChainLog(log) {
  try {
    _turbo.lastEventTs = Date.now();
    const parsed = _ifaceOF.parseLog(log);
    if (!parsed) return;
    const txHash = log.transactionHash + ':' + log.index;       // лог-уникальный ключ
    for (const w of COPY_WALLETS) {
      const fill = _copyDecodeOnchain(parsed, w.address);
      if (!fill) continue;
      const applied = await _copyRouteFill(w, fill, txHash, 'onchain');
      if (applied) console.log(`[copy] ⚡ ончейн ${fill.side} ${w.label} ${(fill.price*100).toFixed(0)}¢ ×${fill.shares.toFixed(1)}`);
    }
  } catch (e) { /* нерелевантный лог — игнор */ }
}

function _copyTurboUnsub() {
  if (!_turbo.provider) return;
  for (const f of _turbo.listeners) { try { _turbo.provider.off(f, _copyOnChainLog); } catch (_) {} }
  _turbo.listeners = [];
}

// (Пере)подписка под текущий набор адресов. Два фильтра: maker-set и taker-set.
function copyTurboResubscribe() {
  if (!_turbo.provider || !_turbo.connected) return;
  _copyTurboUnsub();
  if (!COPY_WALLETS.length) return;
  const padded = COPY_WALLETS.map(w => ethers.zeroPadValue(w.address, 32));
  const fMaker = { address: COPY_EXCHANGES, topics: [_OF_TOPIC, null, padded] };        // maker ∈ set
  const fTaker = { address: COPY_EXCHANGES, topics: [_OF_TOPIC, null, null, padded] };  // taker ∈ set
  try {
    _turbo.provider.on(fMaker, _copyOnChainLog);
    _turbo.provider.on(fTaker, _copyOnChainLog);
    _turbo.listeners = [fMaker, fTaker];
    console.log(`[copy] ⚡ турбо подписан на ${COPY_WALLETS.length} кошельков (${COPY_EXCHANGES.length} контракта)`);
  } catch (e) { console.error('[copy] turbo subscribe error:', e && e.message); }
}

async function copyTurboStart() {
  if (!COPY_WSS_URL) { console.log('[copy] ТУРБО выключен (нет POLYGON_WSS) — работает опрос Data API'); return; }
  if (_turbo.started) return;
  _turbo.started = true;
  const connect = () => {
    try {
      const provider = new ethers.WebSocketProvider(COPY_WSS_URL, 137, { staticNetwork: ethers.Network.from(137) });
      _turbo.provider = provider;
      provider.on('error', (e) => { console.error('[copy] turbo WS error:', e && e.message); });
      // ждём готовности сети и подписываемся
      provider.getBlockNumber().then(bn => {
        _turbo.connected = true; _turbo.reconnectMs = 3000;
        console.log(`[copy] ⚡ ТУРБО подключён к Polygon (block ${bn})`);
        copyTurboResubscribe();
      }).catch(err => { console.error('[copy] turbo connect failed:', err && err.message); _turbo.connected = false; });
    } catch (e) { console.error('[copy] turbo init error:', e && e.message); _turbo.connected = false; }
  };
  connect();
  // Хартбит + авто-реконнект: если WS отвалился — переподключаемся, опрос тем временем подстраховывает.
  setInterval(async () => {
    if (!_turbo.provider) { connect(); return; }
    try {
      await Promise.race([
        _turbo.provider.getBlockNumber(),
        new Promise((_, rej) => setTimeout(() => rej(new Error('hb timeout')), 8000)),
      ]);
      _turbo.connected = true;
    } catch (e) {
      console.warn('[copy] turbo heartbeat fail → reconnect:', e && e.message);
      _turbo.connected = false;
      try { _copyTurboUnsub(); await _turbo.provider.destroy(); } catch (_) {}
      _turbo.provider = null;
      setTimeout(connect, _turbo.reconnectMs);
      _turbo.reconnectMs = Math.min(30000, _turbo.reconnectMs * 1.7);
    }
  }, 15000);
}
copyTurboStart();

console.log(`[copy] poll=${COPY_POLL_MS}ms recon=${COPY_POLL_RECON_MS}ms limit=${COPY_FETCH_LIMIT} maxWallets=${COPY_MAX_WALLETS} real-live=${COPY_REAL_LIVE} turbo=${COPY_WSS_URL ? 'on' : 'off'}`);


function _copyAccountSummary(acct) {
  const log  = acct.log;
  const wins = log.filter(t => t.won).length;
  const realized = log.reduce((a, t) => a + t.pnl, 0);
  const open = Object.values(acct.positions).map(p => ({
    market: p.market, outcome: p.outcome, shares: p.shares, avgPrice: p.avgPrice,
    lastPrice: p.lastPrice, costUSD: p.costUSD,
    uPnl: (p.lastPrice != null ? p.shares * p.lastPrice - p.costUSD : 0), openTime: p.openTime,
  }));
  const uPnl = open.reduce((a, p) => a + p.uPnl, 0);
  return {
    balance: acct.balance, realizedPnl: realized, unrealizedPnl: uPnl,
    trades: log.length, wins, winRate: log.length ? wins / log.length : 0,
    openCount: open.length, open: open.slice(0, 8), lastTrades: log.slice(-6).reverse(),
  };
}

function copySnapshot() {
  return {
    live: COPY_REAL_LIVE, maxWallets: COPY_MAX_WALLETS,
    turbo: { enabled: !!COPY_WSS_URL, connected: !!_turbo.connected, pollMs: _turbo.connected ? COPY_POLL_RECON_MS : COPY_POLL_MS },
    wallets: COPY_WALLETS.map(w => ({
      id: w.id, address: w.address, label: w.label, copyUSD: w.copyUSD,
      demoEnabled: w.demoEnabled, realEnabled: w.realEnabled,
      lastPollTs: w.lastPollTs, lastErr: w.lastErr, createdAt: w.createdAt,
      demo: _copyAccountSummary(w.demo), real: _copyAccountSummary(w.real),
      feed: w.feed.slice(0, 12),
    })),
  };
}

// ─── EXPRESS APP ─────────────────────────────────────────────────────────────
const app = express();
app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

// SSE endpoint — push live updates every second
app.get('/events', (req, res) => {
  res.set({ 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-cache', 'Connection': 'keep-alive' });
  res.flushHeaders();
  sseClients.add(res);
  res.write(`data: ${JSON.stringify(buildSnapshot())}\n\n`);
  req.on('close', () => sseClients.delete(res));
});

// API: get state
app.get('/api/state', (_, res) => res.json(buildSnapshot()));

// ── НАСТРОЙКИ СТРАТЕГИИ (редактируются с дашборда, применяются на лету) ───────
// Список редактируемых параметров стратегии.
const PARAM_KEYS = ['minConf','minEdge','minTimeMs','tpPct','slPct','flipConf','advMovePct','kellyFrac','maxFrac'];

// Установить кастомные параметры. ВАЖНО: значения коэрсятся через Number(), так
// что строки из инпутов ("0.25") тоже принимаются — это и была причина, по
// которой в тестовом боте «сохранение ничего не делало» (там был typeof===number).
app.post('/api/strategy/:id/params', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  const b = req.body || {};
  const applied = {};
  for (const k of PARAM_KEYS) {
    if (b[k] === undefined || b[k] === null || b[k] === '') continue;
    const v = Number(b[k]);
    if (Number.isFinite(v)) { s.customParams[k] = v; applied[k] = v; }
  }
  applyParams(s);
  // tpAbsPrice — глобальный потолок TP (не per-strategy), принимаем здесь же
  if (b.tpAbsPrice !== undefined && b.tpAbsPrice !== null && b.tpAbsPrice !== '') {
    const t = Number(b.tpAbsPrice);
    if (Number.isFinite(t)) { TP_ABS_PRICE = Math.max(0.50, Math.min(0.99, t)); applied.tpAbsPrice = TP_ABS_PRICE; }
  }
  if (b.minEntryPrice !== undefined && b.minEntryPrice !== null && b.minEntryPrice !== '') {
    const t = Number(b.minEntryPrice);
    if (Number.isFinite(t)) { MIN_ENTRY_PRICE = Math.max(0.0, Math.min(0.50, t)); applied.minEntryPrice = MIN_ENTRY_PRICE; }
  }
  if (b.dailyLossCap !== undefined && b.dailyLossCap !== null && b.dailyLossCap !== '') {
    const t = Number(b.dailyLossCap);
    if (Number.isFinite(t)) { REAL_DAILY_LOSS_CAP = Math.max(0.1, Math.min(10000, t)); applied.dailyLossCap = REAL_DAILY_LOSS_CAP; }
  }
  if (b.minBalance !== undefined && b.minBalance !== null && b.minBalance !== '') {
    const t = Number(b.minBalance);
    if (Number.isFinite(t)) { REAL_MIN_BALANCE = Math.max(0, Math.min(1000000, t)); applied.minBalance = REAL_MIN_BALANCE; _realFloorNotified = false; }
  }
  if (b.demoDelaySec !== undefined && b.demoDelaySec !== null && b.demoDelaySec !== '') {
    const t = Number(b.demoDelaySec);
    if (Number.isFinite(t)) { DEMO_ENTRY_DELAY_MS = Math.max(0, Math.min(30000, Math.round(t * 1000))); applied.demoDelaySec = DEMO_ENTRY_DELAY_MS / 1000; }
  }
  if (b.demoMaxChasePct !== undefined && b.demoMaxChasePct !== null && b.demoMaxChasePct !== '') {
    const t = Number(b.demoMaxChasePct);
    if (Number.isFinite(t)) { DEMO_MAX_CHASE = Math.max(0.01, Math.min(2.0, t / 100)); applied.demoMaxChasePct = DEMO_MAX_CHASE * 100; }
  }
  saveState();
  console.log(`[params] ${req.params.id} updated`, applied);
  res.json({ ok: true, customEnabled: s.customEnabled, customParams: s.customParams, params: s.params, tpAbsPrice: TP_ABS_PRICE, minEntryPrice: MIN_ENTRY_PRICE, dailyLossCap: REAL_DAILY_LOSS_CAP, minBalance: REAL_MIN_BALANCE, demoDelaySec: DEMO_ENTRY_DELAY_MS/1000, demoMaxChasePct: DEMO_MAX_CHASE*100 });
});

// Включить/выключить кастом-режим (база ↔ кастом).
app.post('/api/strategy/:id/custom/toggle', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  s.customEnabled = typeof (req.body || {}).enabled === 'boolean' ? req.body.enabled : !s.customEnabled;
  applyParams(s);
  saveState();
  console.log(`[params] ${req.params.id} custom → ${s.customEnabled ? 'ON' : 'OFF'}`);
  res.json({ ok: true, customEnabled: s.customEnabled, params: s.params });
});

// Настроить РУЧНУЮ параметрическую стратегию (manual1..8): строка dir, булевы
// тумблеры (tpOn/slOn/active) и числовые поля.
app.post('/api/strategy/:id/manual', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s || !s.def.manual) return res.status(404).json({ error: 'not a manual strategy' });
  const b = req.body || {};
  const cp = s.customParams;
  if (b.dir === 'UP' || b.dir === 'DOWN' || b.dir === 'BOTH') cp.dir = b.dir;
  for (const k of ['entryFromSec','entryToSec','btcDeltaMin','btcDeltaMax','shareMin','shareMax','betUSD','tpPct','slPct','maxPerWindow']) {
    if (b[k] === undefined || b[k] === null || b[k] === '') continue;
    const v = Number(b[k]); if (Number.isFinite(v)) cp[k] = v;
  }
  for (const k of ['tpOn','slOn','active']) { if (b[k] !== undefined) cp[k] = b[k] ? 1 : 0; }
  s.customEnabled = true;
  applyParams(s);
  saveState();
  res.json({ ok: true, params: s.params });
});

// Сбросить кастомные параметры к базовым.
app.post('/api/strategy/:id/params/reset', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  s.customParams = { ...s.def.defaults };
  applyParams(s);
  saveState();
  console.log(`[params] ${req.params.id} reset to defaults`);
  res.json({ ok: true, customEnabled: s.customEnabled, customParams: s.customParams, params: s.params });
});

// ── КОПИТРЕЙДИНГ POLYMARKET — API ────────────────────────────────────────────
function _copyFind(id) { return COPY_WALLETS.find(w => w.id === id); }
const _ADDR_RE = /^0x[a-fA-F0-9]{40}$/;

// Добавить кошелёк на копитрейдинг.
app.post('/api/copy/add', (req, res) => {
  const b = req.body || {};
  const address = String(b.address || '').trim();
  if (!_ADDR_RE.test(address)) return res.status(400).json({ error: 'Некорректный адрес кошелька (нужен 0x… 42 символа)' });
  if (COPY_WALLETS.length >= COPY_MAX_WALLETS) return res.status(400).json({ error: `Максимум ${COPY_MAX_WALLETS} кошельков` });
  if (COPY_WALLETS.some(w => w.address === address.toLowerCase())) return res.status(400).json({ error: 'Этот кошелёк уже добавлен' });
  const w = _copyMakeWallet({ address, label: b.label, copyUSD: b.copyUSD });
  COPY_WALLETS.push(w);
  saveState();
  copyPollAll();   // первый опрос (зафиксирует базовую историю как «уже видели»)
  copyTurboResubscribe();   // обновить ончейн-подписку под новый адрес
  console.log(`[copy] добавлен кошелёк ${w.label} (${w.address})`);
  res.json({ ok: true, copy: copySnapshot() });
});

// Удалить кошелёк.
app.post('/api/copy/:id/remove', (req, res) => {
  const i = COPY_WALLETS.findIndex(w => w.id === req.params.id);
  if (i === -1) return res.status(404).json({ error: 'not found' });
  const [w] = COPY_WALLETS.splice(i, 1);
  saveState();
  copyTurboResubscribe();   // обновить ончейн-подписку
  console.log(`[copy] удалён кошелёк ${w.label}`);
  res.json({ ok: true, copy: copySnapshot() });
});

// Тумблер demo/real для кошелька.
app.post('/api/copy/:id/toggle', (req, res) => {
  const w = _copyFind(req.params.id);
  if (!w) return res.status(404).json({ error: 'not found' });
  const acct = (req.body || {}).account === 'real' ? 'real' : 'demo';
  if (acct === 'demo') w.demoEnabled = typeof req.body.enabled === 'boolean' ? req.body.enabled : !w.demoEnabled;
  else                 w.realEnabled = typeof req.body.enabled === 'boolean' ? req.body.enabled : !w.realEnabled;
  saveState();
  res.json({ ok: true, copy: copySnapshot() });
});

// Изменить размер копии ($ на вход).
app.post('/api/copy/:id/size', (req, res) => {
  const w = _copyFind(req.params.id);
  if (!w) return res.status(404).json({ error: 'not found' });
  const v = Number((req.body || {}).copyUSD);
  if (!isFinite(v) || v < 1) return res.status(400).json({ error: 'copyUSD ≥ 1' });
  w.copyUSD = Math.min(100000, v);
  saveState();
  res.json({ ok: true, copy: copySnapshot() });
});

// Сброс copy-счёта (demo или real): баланс, позиции и лог.
app.post('/api/copy/:id/reset', (req, res) => {
  const w = _copyFind(req.params.id);
  if (!w) return res.status(404).json({ error: 'not found' });
  const acct = (req.body || {}).account === 'real' ? 'real' : 'demo';
  w[acct] = _copyAccount();
  w.startTs = Date.now();          // заново копируем только будущие сделки
  if (acct === 'demo') { w.feed = []; w.seen = new Set(); }
  saveState();
  res.json({ ok: true, copy: copySnapshot() });
});


// Переключить инверсию сигнала (база ↔ наоборот). Глобально для всех стратегий.
app.post('/api/invert/toggle', (req, res) => {
  INVERT_SIGNAL = typeof (req.body || {}).enabled === 'boolean' ? req.body.enabled : !INVERT_SIGNAL;
  saveState();
  console.warn(`[config] INVERT_SIGNAL → ${INVERT_SIGNAL ? 'ON (торгуем ПРОТИВ сигнала)' : 'OFF (обычный режим)'}`);
  res.json({ ok: true, invertSignal: INVERT_SIGNAL });
});

// API: тумблер «реальный спред в demo» (вход по ask, выход по bid).
app.post('/api/demo-spread/toggle', (req, res) => {
  DEMO_REAL_SPREAD = typeof (req.body || {}).enabled === 'boolean' ? req.body.enabled : !DEMO_REAL_SPREAD;
  saveState();
  console.warn(`[config] DEMO_REAL_SPREAD → ${DEMO_REAL_SPREAD ? 'ON (demo платит спред)' : 'OFF (demo по mid)'}`);
  res.json({ ok: true, demoRealSpread: DEMO_REAL_SPREAD });
});

// API: ИНДИВИДУАЛЬНОЕ расписание стратегии (часы МСК). Приоритет над глобальным.
// enabled=false → стратегия следует глобальному расписанию. from===to → круглосуточно.
app.post('/api/strategy/:id/schedule', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  const b = req.body || {};
  if (typeof b.enabled === 'boolean') s.schedEnabled = b.enabled;
  if (b.from !== undefined && b.from !== '') { const v = Math.max(0, Math.min(24, Math.floor(Number(b.from)))); if (Number.isFinite(v)) s.schedFrom = v; }
  if (b.to   !== undefined && b.to   !== '') { const v = Math.max(0, Math.min(24, Math.floor(Number(b.to))));   if (Number.isFinite(v)) s.schedTo   = v; }
  applyParams(s); saveState();
  console.log(`[schedule] ${req.params.id} своё=${s.schedEnabled} ${s.schedFrom}->${s.schedTo} МСК · открытие сейчас: ${strategyEntriesAllowed(s)}`);
  res.json({ ok: true, schedEnabled: s.schedEnabled, schedFrom: s.schedFrom, schedTo: s.schedTo, allowedNow: strategyEntriesAllowed(s) });
});

// API: расписание торговли (часы МСК; выходы всегда работают).
app.post('/api/schedule', (req, res) => {
  const b = req.body || {};
  if (typeof b.enabled === 'boolean') SCHEDULE_ENABLED = b.enabled;
  if (b.from !== undefined && b.from !== null && b.from !== '' && isFinite(Number(b.from)))
    SCHEDULE_FROM = Math.max(0, Math.min(24, parseInt(b.from, 10)));
  if (b.to !== undefined && b.to !== null && b.to !== '' && isFinite(Number(b.to)))
    SCHEDULE_TO = Math.max(0, Math.min(24, parseInt(b.to, 10)));
  saveState();
  console.log(`[schedule] enabled=${SCHEDULE_ENABLED} ${SCHEDULE_FROM}→${SCHEDULE_TO} МСК · открытие сейчас: ${entriesAllowedNow()}`);
  res.json({ ok: true, schedEnabled: SCHEDULE_ENABLED, schedFrom: SCHEDULE_FROM, schedTo: SCHEDULE_TO, entriesAllowedNow: entriesAllowedNow() });
});

// API: переключить расписание (быстрый тумблер)
app.post('/api/schedule/toggle', (req, res) => {
  SCHEDULE_ENABLED = typeof (req.body || {}).enabled === 'boolean' ? req.body.enabled : !SCHEDULE_ENABLED;
  saveState();
  res.json({ ok: true, schedEnabled: SCHEDULE_ENABLED, entriesAllowedNow: entriesAllowedNow() });
});


// Дёргает ту же рыночную логику (straight-to-market FAK), что и авто-выход.
app.post('/api/strategy/:id/panic', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  const acct = s.real;
  if (!acct.open || !acct.open.isReal) return res.status(400).json({ error: 'нет открытой реальной позиции' });
  if (acct.open.realOrderStatus === 'pending')
    return res.status(409).json({ error: 'вход ещё не подтверждён — подожди заполнения' });

  const ctx     = getStratContext();
  const curMid  = acct.open.side === 'UP' ? ctx.polyUp : ctx.polyDn;
  const exitRef = (curMid && curMid > 0.01) ? curMid : 0.02; // референс для расчёта; продаём по рынку
  const side    = acct.open.side;
  console.warn(`[manual] PANIC SELL по кнопке: ${req.params.id} ${side} @~${(exitRef*100).toFixed(0)}¢`);
  try {
    stratClose(s, ctx, 'MANUAL', exitRef, acct, true); // reason MANUAL → рыночный сброс
    res.json({ ok: true, side, message: 'Рыночный выход запущен (MANUAL)' });
  } catch (e) {
    console.error('[manual] panic sell error:', e.message);
    res.status(500).json({ error: e.message });
  }
});

// API: toggle strategy demo account (backward-compat shortcut)
app.post('/api/strategy/:id/toggle', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  s.demoEnabled = !s.demoEnabled;
  saveState();
  console.log(`[strategy] ${req.params.id} demo → ${s.demoEnabled ? 'ON' : 'OFF'}`);
  res.json({ id: req.params.id, demoEnabled: s.demoEnabled });
});

// API: toggle DEMO account
app.post('/api/strategy/:id/demo/toggle', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  s.demoEnabled = !s.demoEnabled;
  saveState();
  console.log(`[strategy] ${req.params.id} demo → ${s.demoEnabled ? 'ON' : 'OFF'}`);
  res.json({ id: req.params.id, demoEnabled: s.demoEnabled });
});

// API: toggle REAL account
app.post('/api/strategy/:id/real/toggle', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  s.realEnabled = !s.realEnabled;
  // Если пользователь вручную включает real — снимаем блокировку стрик-брейкера.
  // Выключение вручную блокировку не ставит (это действие самого пользователя).
  if (s.realEnabled && s.underdogHoldAutoBlocked) {
    s.underdogHoldAutoBlocked = false;
    console.log(`[udg-breaker] ${req.params.id} manually re-enabled — auto-block cleared`);
  }
  saveState();
  console.log(`[strategy] ${req.params.id} real → ${s.realEnabled ? 'ON' : 'OFF'}`);
  res.json({ id: req.params.id, realEnabled: s.realEnabled });
});

// API: reset DEMO account (backward-compat shortcut)
app.post('/api/strategy/:id/reset', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  s.demo.balance     = 1000;
  s.demo.peakBalance = 1000;
  s.demo.open        = null;
  s.demo.log         = [];
  saveState();
  res.json({ ok: true });
});

// API: reset DEMO account
app.post('/api/strategy/:id/demo/reset', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  s.demo.balance     = 1000;
  s.demo.peakBalance = 1000;
  s.demo.open        = null;
  s.demo.log         = [];
  saveState();
  res.json({ ok: true });
});

// API: reset REAL account
app.post('/api/strategy/:id/real/reset', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  s.real.balance     = 1000;
  s.real.peakBalance = 1000;
  s.real.open        = null;
  s.real.log         = [];
  saveState();
  res.json({ ok: true });
});

// API: export CSV
app.get('/api/export/csv', (_, res) => {
  const rows = [['mode','strategy','time_open','time_close','side','market','poly_entry','poly_exit','btc_open','btc_close','size','pnl','edge','reason','won','entry_info','real_order_id','dirty']];
  for (const id in STRATEGIES) {
    for (const [mode, acct] of [['demo', STRATEGIES[id].demo], ['real', STRATEGIES[id].real]]) {
      for (const t of acct.log) {
        rows.push([
          mode,
          t.strategy,
          new Date(t.entryTime).toISOString(),
          new Date(t.closeTime).toISOString(),
          t.side, t.marketSlug || '',
          t.polyEntryPrice.toFixed(4),
          (t.polyExitPrice ?? (t.won ? 1 : 0)).toFixed(4),
          (t.btcAtEntry || 0).toFixed(2), (t.btcAtClose || 0).toFixed(2),
          t.sizeUSDC.toFixed(4), t.pnl.toFixed(4),
          (t.edge * 100).toFixed(2),
          t.reason, t.won ? 1 : 0,
          (t.entryInfo || '').replace(/,/g, ';'),
          t.realOrderId || '',
          t.dirty ? 1 : 0,
        ]);
      }
    }
  }
  res.set({ 'Content-Type': 'text/csv', 'Content-Disposition': `attachment; filename="bot_log_${Date.now()}.csv"` });
  res.send(rows.map(r => r.join(',')).join('\n'));
});

// API: экспорт КАЛИБРОВОЧНОГО лога (цена/спред входа + фактический исход окна).
// На реальных данных по нему считаем, в каком диапазоне цены входа есть эдж.
app.get('/api/export/calib.csv', (_, res) => {
  const cols = ['ts','strategy','mode','side','mid','rawMid','bid','ask','spread','msToEnd','btcMove','openingBTC','windowEnd','slug','outcome','ourWin'];
  const rows = [cols];
  for (const r of calibLog) {
    rows.push([
      new Date(r.ts).toISOString(), r.strategy, r.mode, r.side,
      r.mid != null ? r.mid.toFixed(4) : '', r.rawMid != null ? Number(r.rawMid).toFixed(4) : '',
      r.bid != null ? Number(r.bid).toFixed(4) : '', r.ask != null ? Number(r.ask).toFixed(4) : '',
      r.spread != null ? r.spread.toFixed(4) : '',
      r.msToEnd ?? '', r.btcMove ?? '', r.openingBTC != null ? Number(r.openingBTC).toFixed(2) : '',
      r.windowEnd ? new Date(r.windowEnd).toISOString() : '', r.slug || '',
      r.outcome ?? '', r.ourWin ?? '',
    ]);
  }
  res.set({ 'Content-Type': 'text/csv', 'Content-Disposition': `attachment; filename="calib_${Date.now()}.csv"` });
  res.send(rows.map(r => r.join(',')).join('\n'));
});

// ─── REAL TRADING API ENDPOINTS ───────────────────────────────────────────────

// GET /api/real/status — wallet address, readiness, live USDC balance
app.get('/api/ml/report', (req, res) => {
  try { res.json(mlBuildReport(Math.max(0.1, parseFloat(req.query.days || '3')))); }
  catch (e) { res.status(500).json({ error: String(e) }); }
});
app.get('/api/ml/export', (_, res) => {
  if (!fs.existsSync(ML_LOG_FILE)) return res.status(404).json({ error: 'нет лога' });
  res.download(ML_LOG_FILE);
});

app.get('/api/real/status', async (_, res) => {
  const balance = polyWallet && polyApiCreds ? await fetchRealBalance() : null;
  if (balance !== null) realBalance = balance;
  res.json({
    enabled:     REAL_TRADING,
    ready:       !!(polyWallet && polyApiCreds),
    wallet:      polyWallet?.address ?? null,
    balance,
    strategies:  Object.keys(STRATEGIES).filter(id => id === 'momentum').map(id => ({
      id,
      realEnabled: STRATEGIES[id].realEnabled,
      open:        STRATEGIES[id].real.open,
    })),
  });
});

// POST /api/real/cancel — cancel the open real order for Momentum (emergency stop)
app.post('/api/real/cancel', async (_, res) => {
  const mom = STRATEGIES.momentum;
  if (!mom || !mom.real.open?.realOrderId) return res.json({ ok: false, reason: 'no open real order' });
  await cancelClobOrder(mom.real.open.realOrderId);
  res.json({ ok: true, cancelledOrderId: mom.real.open.realOrderId });
});

// GET /api/tg/test — send a test message to verify Telegram integration
app.get('/api/tg/test', async (_, res) => {
  if (!TG_ON) {
    return res.json({
      ok: false,
      reason: 'Telegram disabled. Set TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID env vars on Railway.',
    });
  }
  const sent = await sendTg(
    `🧪 <b>Тестовое сообщение</b>\n` +
    `Время: ${new Date().toISOString()}\n` +
    `Кошелёк: <code>${_tgEsc(polyWallet?.address || 'not initialized')}</code>\n` +
    `Баланс: ${realBalance !== null ? `$${realBalance.toFixed(2)}` : 'n/a'}`
  );
  res.json({ ok: sent });
});

// GET /api/real/reinit — re-run wallet initialization (без перезапуска контейнера).
// Полезно после смены env vars в Railway. Заменил собой старый /redetect, т.к.
// V2 SDK сам управляет правильной комбинацией auth — нечего "детектить".
app.get('/api/real/reinit', async (_, res) => {
  try {
    polyClob = null;
    polyApiCreds = null;
    realBalance = null;
    await initPolyWallet();
    res.json({
      ok:           !!polyClob,
      wallet:       polyWallet ? polyWallet.address : null,
      activeApiKey: polyApiCreds?.key || null,
      balance:      realBalance,
    });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

// Backward-compat alias for the old /redetect path
app.get('/api/real/redetect', (req, res) => res.redirect(307, '/api/real/reinit'));

// POST /api/real/close-now — immediately close real position at current mid price
app.post('/api/real/close-now', async (_, res) => {
  const mom = STRATEGIES.momentum;
  if (!mom || !mom.real.open) return res.status(400).json({ error: 'no open position' });
  const ctx      = getStratContext();
  const midPrice = mom.real.open.side === 'UP' ? ctx.polyUp : ctx.polyDn;
  if (!midPrice)  return res.status(400).json({ error: 'no poly price available' });
  stratClose(mom, ctx, 'MANUAL', midPrice, mom.real, true);
  res.json({ ok: true, exitPrice: midPrice });
});

// GET /api/real/diagnose — comprehensive diagnostic of the V2 auth stack.
// Open this in your browser after deploy to see what's actually happening.
app.get('/api/real/diagnose', async (_, res) => {
  const report = {
    timestamp:    new Date().toISOString(),
    sdkVersion:   'CLOB V2 (@polymarket/clob-client-v2)',
    env: {
      REAL_TRADING:    REAL_TRADING,
      POLY_PRIVATE_KEY: POLY_PK ? `set (${POLY_PK.length} chars)` : 'NOT SET',
      POLY_FUNDER:     POLY_FUNDER || 'not set',
      POLY_API_KEY:    process.env.POLY_API_KEY ? `${process.env.POLY_API_KEY.slice(0,8)}...` : 'not set (will derive)',
      POLY_API_SECRET: process.env.POLY_API_SECRET ? `set (${process.env.POLY_API_SECRET.length} chars)` : 'not set',
      POLY_PASSPHRASE: process.env.POLY_PASSPHRASE ? `set (${process.env.POLY_PASSPHRASE.length} chars)` : 'not set',
      SIGNATURE_TYPE:  SIG_TYPE,
      TELEGRAM:        TG_ON ? `enabled (chat ${TG_CHAT.slice(0,4)}…)` : 'disabled (set TELEGRAM_BOT_TOKEN + TELEGRAM_CHAT_ID)',
    },
    wallet:           polyWallet ? polyWallet.address : null,
    walletReady:      !!(polyWallet && polyClob),
    activeApiKey:     polyApiCreds ? polyApiCreds.key : null,
    tests: {},
  };

  // ─── PUBLIC ENDPOINTS (no auth — proves reachability / no geo-block) ────────
  try {
    const t0   = Date.now();
    const r    = await fetch(`${POLY_CLOB}/markets?limit=1`, { method: 'GET', signal: AbortSignal.timeout(8000) });
    const ms   = Date.now() - t0;
    let parsed = null;
    try { parsed = await r.json(); } catch {}
    report.tests.publicClob = {
      status:  r.status,
      ok:      r.ok,
      ms,
      hasData: !!(parsed && (parsed.data || parsed.length || parsed.markets)),
      verdict: r.ok ? '✅ Публичный CLOB доступен → не геоблок' : `❌ CLOB ${r.status} — возможен геоблок`,
    };
  } catch (e) {
    report.tests.publicClob = { error: e.message, verdict: '❌ network error' };
  }

  // ─── ON-CHAIN BALANCES (independent of CLOB auth) ───────────────────────────
  if (polyWallet) {
    try {
      const provider     = getRpcProvider(POLYGON_RPCS[0]);
      const USDC_NATIVE  = '0x3c499c542cEF5E3811e1192ce70d8cC03d5c3359';
      const USDC_BRIDGED = '0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174';
      const erc20Abi     = ['function balanceOf(address) view returns (uint256)'];
      const cBridged     = new ethers.Contract(USDC_BRIDGED, erc20Abi, provider);
      const cNative      = new ethers.Contract(USDC_NATIVE,  erc20Abi, provider);
      const checks       = {};
      const eoa          = polyWallet.address;
      checks.EOA = { addr: eoa };
      try { checks.EOA.usdc_bridged = Number(await cBridged.balanceOf(eoa)) / 1e6; } catch {}
      try { checks.EOA.usdc_native  = Number(await cNative .balanceOf(eoa)) / 1e6; } catch {}
      try { checks.EOA.matic        = Number(await provider.getBalance(eoa)) / 1e18; } catch {}
      try { checks.EOA.code         = (await provider.getCode(eoa)) === '0x' ? 'EOA (no code)' : 'contract'; } catch {}
      if (POLY_FUNDER) {
        checks.FUNDER = { addr: POLY_FUNDER };
        try { checks.FUNDER.usdc_bridged = Number(await cBridged.balanceOf(POLY_FUNDER)) / 1e6; } catch {}
        try { checks.FUNDER.usdc_native  = Number(await cNative .balanceOf(POLY_FUNDER)) / 1e6; } catch {}
        try {
          const code = await provider.getCode(POLY_FUNDER);
          checks.FUNDER.code = code === '0x'
            ? '⚠ NO CONTRACT — этот адрес не задеплоен. Это НЕ proxy.'
            : `contract (${code.length} bytes) ✓`;
        } catch {}
      }
      report.tests.onChain = checks;
    } catch (e) {
      report.tests.onChain = { error: e.message };
    }
  }

  // ─── GAMMA PROFILE (returns user's real trading proxy by EOA) ───────────────
  if (polyWallet) {
    try {
      const url = `https://gamma-api.polymarket.com/profile?address=${polyWallet.address}`;
      const r   = await fetch(url, { method: 'GET', signal: AbortSignal.timeout(8000) });
      const txt = await r.text();
      let p; try { p = JSON.parse(txt); } catch { p = txt.slice(0,300); }
      report.tests.gammaProfile = {
        status:   r.status,
        response: p,
        hint:     r.ok && p?.proxyWallet
          ? `🎯 Настоящий торговый proxy: ${p.proxyWallet}. Если POLY_FUNDER ≠ этот адрес — замени.`
          : (r.ok ? 'gamma вернул профиль' : `EOA не зарегистрирован в Polymarket (${r.status})`),
      };
    } catch (e) {
      report.tests.gammaProfile = { error: e.message };
    }
  }

  // ─── V2 SDK SMOKE TEST (real L2 auth round-trip) ────────────────────────────
  if (polyClob) {
    try {
      const t0 = Date.now();
      const r  = await polyClob.getBalanceAllowance({ asset_type: 'COLLATERAL' });
      report.tests.v2BalanceAllowance = {
        ms:      Date.now() - t0,
        ok:      true,
        balance: r?.balance ? `$${(parseFloat(r.balance)/1e6).toFixed(4)}` : 'n/a',
        raw:     r,
        verdict: '✅ V2 L2 auth работает',
      };
    } catch (e) {
      report.tests.v2BalanceAllowance = {
        ok:      false,
        error:   e.message,
        status:  e instanceof ApiError ? e.status : undefined,
        data:    e instanceof ApiError ? e.data   : undefined,
        verdict: '❌ V2 L2 auth fails',
        hint:    (e.message?.includes('401') || e.status === 401)
          ? 'Аккаунт не активирован для CLOB. Проверь: 1) залогинен ли этим кошельком в polymarket.com 2) принят ли ToS 3) SIGNATURE_TYPE правильный (0=EOA,1=Magic,2=Phantom+Safe,3=smart)'
          : 'возможно нужен updateBalanceAllowance (V2 sync)',
      };
      try {
        await polyClob.updateBalanceAllowance({ asset_type: 'COLLATERAL' });
        const r2 = await polyClob.getBalanceAllowance({ asset_type: 'COLLATERAL' });
        report.tests.v2BalanceAllowance.afterUpdate = {
          balance: r2?.balance ? `$${(parseFloat(r2.balance)/1e6).toFixed(4)}` : 'n/a',
          verdict: '✅ заработало после updateBalanceAllowance',
        };
      } catch (e2) {
        report.tests.v2BalanceAllowance.afterUpdate = {
          error:  e2.message,
          status: e2 instanceof ApiError ? e2.status : undefined,
        };
      }
    }
    try {
      const orders = await polyClob.getOpenOrders({}, true);
      report.tests.v2OpenOrders = { ok: true, count: orders?.data?.length || 0 };
    } catch (e) {
      report.tests.v2OpenOrders = { ok: false, error: e.message, status: e instanceof ApiError ? e.status : undefined };
    }
  } else {
    report.tests.v2BalanceAllowance = { skipped: 'polyClob not initialized — see logs for init error' };
  }

  // ─── L1 AUTH PROBE (independent attempt to derive a fresh key) ──────────────
  if (polyWallet && POLY_PK) {
    try {
      const pkNorm      = POLY_PK.startsWith('0x') ? POLY_PK : '0x' + POLY_PK;
      const viemWallet  = _buildViemWallet(pkNorm);
      const sigType     = _resolveSigType();
      const funderAddr  = POLY_FUNDER || polyWallet.address;
      const probeClient = _buildBootClient(viemWallet, sigType, funderAddr);
      const t0 = Date.now();
      const creds = await probeClient.createOrDeriveApiKey();
      report.tests.v2L1Auth = {
        ms:         Date.now() - t0,
        ok:         true,
        apiKey:     creds.key.slice(0, 8) + '...',
        matchesEnv: !!process.env.POLY_API_KEY && creds.key === process.env.POLY_API_KEY,
        verdict:    '✅ L1 EIP-712 подпись принята Polymarket → wallet валидный',
      };
    } catch (e) {
      report.tests.v2L1Auth = {
        ok:      false,
        error:   e.message,
        status:  e instanceof ApiError ? e.status : undefined,
        verdict: '❌ L1 auth fails — wallet/sigType/funder неверен',
      };
    }
  }

  res.json(report);
});

// ─── BOOT ────────────────────────────────────────────────────────────────────
initStrategies();
loadState();
connectCoinbase();
// Real trading: init wallet AFTER strategies are loaded
initPolyWalletWithRetry().catch(e => console.error('[real] boot error:', e.message));

// Book snapshot for OFI every 500ms
setInterval(() => {
  if (book.bids.size && book.asks.size) {
    bookHistory.push(bookSnapshotDepth(10));
    if (bookHistory.length > 600) bookHistory.shift();
  }
}, 500);

// Polymarket every 2s
setInterval(() => { if (poly.autoFetch) fetchPolyMarket().catch(e => console.error('[poly]', e.message)); }, 1500);
// Chainlink every 4s
setInterval(() => { if (chain.enabled && !isSim) refreshChainlinkPrice().catch(() => {}); }, 1500);
// Strategy engine every 1s
setInterval(() => { try { processStrategies(); } catch (e) { console.error('[strategies]', e.message); } }, 1000);
// SSE broadcast every 1s
setInterval(() => { if (sseClients.size > 0) broadcast(buildSnapshot()); }, 1000);
// Auto-save every 60s
setInterval(saveState, 60000);

// ─── NO-TRADES ALERT ─────────────────────────────────────────────────────────
// If real trading is enabled but no real trade has opened for 60 minutes,
// send a Telegram alert so we know the bot is alive but not firing.
// Checks every 5 minutes; only alerts once per silence period (resets after a trade).
const NO_TRADE_ALERT_MS  = 60 * 60 * 1000;  // 60 minutes
const NO_TRADE_CHECK_MS  =  5 * 60 * 1000;  // check every 5 minutes
let   _lastNoTradeAlertSent = 0;             // epoch ms of last alert sent

setInterval(() => {
  if (!TG_ON) return;
  const mom = STRATEGIES.momentum;
  if (!mom || !mom.realEnabled) return;

  // Find the most recent real trade open time across all strategies
  let lastTradeTime = 0;
  for (const id in STRATEGIES) {
    const s = STRATEGIES[id];
    // Check open position
    if (s.real.open?.entryTime) lastTradeTime = Math.max(lastTradeTime, s.real.open.entryTime);
    // Check last closed trade
    const lastLog = s.real.log[s.real.log.length - 1];
    if (lastLog?.entryTime) lastTradeTime = Math.max(lastTradeTime, lastLog.entryTime);
  }

  const silenceMs = Date.now() - (lastTradeTime || 0);
  if (silenceMs < NO_TRADE_ALERT_MS) {
    // Within the hour — reset alert flag so it can fire again next silence
    _lastNoTradeAlertSent = 0;
    return;
  }

  // Been silent for ≥60 min. Alert once per silence period.
  if (_lastNoTradeAlertSent > lastTradeTime) return; // already alerted for this silence

  _lastNoTradeAlertSent = Date.now();
  const silenceMin = Math.round(silenceMs / 60000);
  const reason = !ticks.length || ticks.length < 60
    ? 'мало тиков с Coinbase'
    : poly.status !== 'live'
      ? `Polymarket статус: ${poly.status}`
      : 'сигнал WAIT (рынок боковой)';

  sendTg(
    `🔕 <b>Нет сделок уже ${silenceMin} мин</b>\n` +
    `Стратегия включена, бот работает.\n` +
    `Вероятная причина: <i>${_tgEsc(reason)}</i>\n` +
    `BTC: $${ticks.length ? ticks[ticks.length-1].price.toFixed(0) : '?'} | ` +
    `UP: ${poly.prices.up !== null ? (poly.prices.up*100).toFixed(0)+'¢' : '?'} | ` +
    `DOWN: ${poly.prices.down !== null ? (poly.prices.down*100).toFixed(0)+'¢' : '?'}`
  );
  console.log(`[alert] no trades for ${silenceMin}min — TG sent`);
}, NO_TRADE_CHECK_MS);

// ─── TELEGRAM BOT: INCOMING UPDATES (команды и кнопки) ───────────────────────
//
// Регистрирует webhook: POST /tg/webhook  (путь задаётся в env TG_WEBHOOK_PATH,
// по умолчанию «/tg/webhook»). После деплоя один раз вызови:
//   GET /api/tg/register-webhook
// — и Telegram начнёт присылать обновления сюда.
//
// Поддерживаемые команды:
//   /panic              — паник-сел всех открытых реальных позиций
//   /panic <stratId>    — паник-сел конкретной стратегии
//   /status             — сводка по открытым реальным позициям
//
// Кнопки (inline keyboard) отправляются автоматически при открытии реальной
// позиции — кнопка «⚡ ПРОДАТЬ» прямо в уведомлении.

/** Отправить сообщение с inline-клавиатурой (reply_markup). */
async function sendTgButtons(text, buttons) {
  if (!TG_ON) return false;
  try {
    const r = await fetch(`https://api.telegram.org/bot${TG_TOKEN}/sendMessage`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        chat_id:                  TG_CHAT,
        text,
        parse_mode:               'HTML',
        disable_web_page_preview: true,
        reply_markup:             { inline_keyboard: buttons },
      }),
      signal: AbortSignal.timeout(5000),
    });
    return r.ok;
  } catch (e) {
    console.warn('[tg] sendButtons error:', e.message);
    return false;
  }
}

/** Ответить на callback_query (убирает «часики» на кнопке). */
async function answerCallback(callbackId, text = '') {
  if (!TG_ON) return;
  try {
    await fetch(`https://api.telegram.org/bot${TG_TOKEN}/answerCallbackQuery`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ callback_query_id: callbackId, text }),
      signal: AbortSignal.timeout(5000),
    });
  } catch (e) {
    console.warn('[tg] answerCallback error:', e.message);
  }
}

/** Собрать сводку открытых реальных позиций. */
function buildStatusText() {
  const ctx = getStratContext();
  const open = Object.entries(STRATEGIES)
    .filter(([, s]) => s.real.open?.isReal)
    .map(([id, s]) => {
      const pos = s.real.open;
      const curMid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
      const pnl = curMid && pos.entryPrice
        ? ((curMid - pos.entryPrice) * (pos.actualShares || pos.plannedShares || 0)).toFixed(2)
        : '?';
      return `• <b>${_tgEsc(id)}</b> ${pos.side} @ ${(pos.entryPrice * 100).toFixed(0)}¢ | сейчас ~${curMid ? (curMid*100).toFixed(0)+'¢' : '?'} | PnL ~$${pnl}`;
    });
  if (!open.length) return '📭 <b>Нет открытых реальных позиций</b>';
  return `📊 <b>Открытые позиции (${open.length}):</b>\n` + open.join('\n');
}

/** Паник-сел одной или всех стратегий. Возвращает { sold[], errors[] }. */
function executePanic(stratId = null) {
  const ctx  = getStratContext();
  const sold = [];
  const errs = [];
  const targets = stratId
    ? (STRATEGIES[stratId] ? [[stratId, STRATEGIES[stratId]]] : [])
    : Object.entries(STRATEGIES);

  for (const [id, s] of targets) {
    const acct = s.real;
    if (!acct.open?.isReal) continue;
    if (acct.open.realOrderStatus === 'pending') { errs.push(`${id}: вход не подтверждён`); continue; }
    try {
      const curMid   = acct.open.side === 'UP' ? ctx.polyUp : ctx.polyDn;
      const exitRef  = (curMid && curMid > 0.01) ? curMid : 0.02;
      const side     = acct.open.side;
      console.warn(`[tg-panic] PANIC SELL ${id} ${side} @~${(exitRef*100).toFixed(0)}¢`);
      stratClose(s, ctx, 'MANUAL', exitRef, acct, true);
      sold.push(`${id} (${side})`);
    } catch (e) {
      errs.push(`${id}: ${e.message}`);
    }
  }
  return { sold, errs };
}

/** Обработчик входящего update от Telegram. */
function handleTgUpdate(update) {
  // ── Inline-кнопка нажата ────────────────────────────────────────────────
  if (update.callback_query) {
    const cb   = update.callback_query;
    const data = cb.data || '';
    answerCallback(cb.id, '⚡ Выполняю...');

    if (data === 'panic_all') {
      const { sold, errs } = executePanic(null);
      const msg = sold.length
        ? `⚡ <b>ПАНИК-СЕЛ выполнен</b>\nПродано: ${sold.map(_tgEsc).join(', ')}` +
          (errs.length ? `\n⚠️ Ошибки: ${errs.map(_tgEsc).join('; ')}` : '')
        : `❌ Нечего продавать` + (errs.length ? `\n${errs.map(_tgEsc).join('; ')}` : '');
      sendTg(msg);
    } else if (data.startsWith('panic:')) {
      const id = data.slice(6);
      const { sold, errs } = executePanic(id);
      const msg = sold.length
        ? `⚡ <b>ПРОДАНО:</b> ${sold.map(_tgEsc).join(', ')}`
        : `❌ Не продано${errs.length ? ': ' + errs.map(_tgEsc).join('; ') : ' — нет открытой позиции'}`;
      sendTg(msg);
    } else if (data === 'status') {
      sendTg(buildStatusText());
    }
    return;
  }

  // ── Текстовая команда ────────────────────────────────────────────────────
  const msg  = update.message;
  if (!msg?.text) return;

  // Проверяем что сообщение из нашего чата (безопасность)
  if (String(msg.chat?.id) !== String(TG_CHAT)) {
    console.warn(`[tg] ignoring message from unknown chat ${msg.chat?.id}`);
    return;
  }

  const text = (msg.text || '').trim();

  if (text === '/status' || text.startsWith('/status ')) {
    sendTg(buildStatusText());
    return;
  }

  if (text === '/panic' || text.startsWith('/panic ')) {
    const parts  = text.split(/\s+/);
    const stratId = parts[1] || null;

    if (stratId && !STRATEGIES[stratId]) {
      sendTg(`❌ Стратегия <code>${_tgEsc(stratId)}</code> не найдена`);
      return;
    }

    const { sold, errs } = executePanic(stratId);
    let reply;
    if (sold.length) {
      reply = `⚡ <b>ПАНИК-СЕЛ выполнен</b>\nПродано: ${sold.map(_tgEsc).join(', ')}`;
      if (errs.length) reply += `\n⚠️ Ошибки: ${errs.map(_tgEsc).join('; ')}`;
    } else if (errs.length) {
      reply = `⚠️ Ошибки при продаже:\n${errs.map(_tgEsc).join('\n')}`;
    } else {
      reply = `📭 Нет открытых реальных позиций${stratId ? ` для <code>${_tgEsc(stratId)}</code>` : ''}`;
    }
    sendTg(reply);
    return;
  }

  // /help
  if (text === '/help' || text === '/start') {
    sendTg(
      `🤖 <b>BOTblet команды:</b>\n\n` +
      `/status — открытые позиции\n` +
      `/panic — продать всё по рынку\n` +
      `/panic <i>stratId</i> — продать конкретную стратегию\n\n` +
      `Или нажми кнопку <b>⚡ ПРОДАТЬ</b> прямо в уведомлении об открытии позиции.`
    );
  }
}

// Webhook endpoint — Telegram шлёт сюда POST при каждом update
const TG_WEBHOOK_PATH = (process.env.TG_WEBHOOK_PATH || '/tg/webhook').trim();
app.post(TG_WEBHOOK_PATH, (req, res) => {
  res.sendStatus(200); // сначала ответить 200, потом обработать
  try { handleTgUpdate(req.body); } catch (e) { console.error('[tg] update error:', e.message); }
});

// GET /api/tg/register-webhook — один раз вызвать после деплоя чтобы зарегистрировать
app.get('/api/tg/register-webhook', async (req, res) => {
  if (!TG_ON) return res.json({ ok: false, reason: 'Telegram disabled' });

  // Определяем публичный URL: из env RAILWAY_PUBLIC_DOMAIN или из заголовка Host
  const domain = process.env.RAILWAY_PUBLIC_DOMAIN
    || process.env.PUBLIC_DOMAIN
    || req.headers['x-forwarded-host']
    || req.headers.host
    || '';
  if (!domain) return res.json({ ok: false, reason: 'Не удалось определить домен. Задай env PUBLIC_DOMAIN.' });

  const webhookUrl = `https://${domain}${TG_WEBHOOK_PATH}`;
  try {
    const r = await fetch(`https://api.telegram.org/bot${TG_TOKEN}/setWebhook`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ url: webhookUrl, allowed_updates: ['message', 'callback_query'] }),
      signal: AbortSignal.timeout(8000),
    });
    const data = await r.json();
    console.log('[tg] setWebhook:', data);
    res.json({ ok: data.ok, webhookUrl, result: data });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

app.listen(PORT, () => {
  console.log(`[server] running on port ${PORT}`);
  console.log(`[server] HMAC sig encoding: URL-safe base64 (+→-, /→_) ✓ POLYMARKET_FIX_APPLIED`);
});
