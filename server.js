'use strict';

// ─── DEPS ───────────────────────────────────────────────────────────────────
const express  = require('express');
const { WebSocket } = require('ws');
// Node 18+ has built-in fetch — no import needed
const { ethers } = require('ethers');
const crypto   = require('crypto');   // built-in, for HMAC-SHA256
const fs       = require('fs');
const path     = require('path');

// ─── CONFIG ─────────────────────────────────────────────────────────────────
const PORT             = process.env.PORT || 3000;
const STATE_FILE       = path.join(__dirname, 'state.json');
const POLY_GAMMA       = 'https://gamma-api.polymarket.com';
const POLY_CLOB        = 'https://clob.polymarket.com';
const POLY_INTERVAL    = 'btc-updown-5m';
const POLY_WINDOW_SEC  = 300;
const CHAINLINK_ADDR   = '0xc907E116054Ad103354f2D350FD2514433D57F6f'; // BTC/USD Polygon
const POLYGON_RPCS     = [
  'https://polygon-bor-rpc.publicnode.com',
  'https://polygon.llamarpc.com',
  'https://rpc.ankr.com/polygon',
  'https://1rpc.io/matic',
];
const CHAINLINK_ABI    = ['function latestAnswer() view returns (int256)'];

// ─── REAL TRADING CONFIG ──────────────────────────────────────────────────────
// To enable: set REAL_TRADING=true and POLY_PRIVATE_KEY=0x... in Railway env vars
// Optionally set POLY_API_KEY + POLY_API_SECRET + POLY_PASSPHRASE to skip key derivation
const REAL_TRADING  = process.env.REAL_TRADING === 'true';
const POLY_PK       = process.env.POLY_PRIVATE_KEY || '';
const POLY_FUNDER   = process.env.POLY_FUNDER_ADDRESS || '';
// Polymarket CTF Exchange contract on Polygon mainnet (settles all prediction markets)
const CTF_EXCHANGE  = '0x4bFb41d5B3570DeFd03C39a9A4D8dE6Bd8B8982E';
const POLY_CHAIN_ID = 137;

// ─── STATE ───────────────────────────────────────────────────────────────────
let ticks        = [];   // { time, price, qty, isBuyerMaker }
let cvd          = 0;
let cvdSeries    = [];   // { t, v }
let book         = { bids: new Map(), asks: new Map() };
let bookHistory  = [];   // snapshots for OFI
let bestBid      = null;
let bestAsk      = null;
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
};
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
        enabled: s.enabled,
        balance: s.balance,
        peakBalance: s.peakBalance,
        open: s.open,
        log: s.log.slice(-500),
        params: s.params,
      };
    }
    fs.writeFileSync(STATE_FILE, JSON.stringify(out, null, 2));
  } catch (e) { console.error('[state] save error:', e.message); }
}

function loadState() {
  try {
    if (!fs.existsSync(STATE_FILE)) return;
    const stored = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
    for (const id in stored) {
      if (STRATEGIES[id]) {
        STRATEGIES[id].enabled    = stored[id].enabled ?? false;
        STRATEGIES[id].balance    = stored[id].balance ?? 1000;
        STRATEGIES[id].peakBalance = stored[id].peakBalance ?? 1000;
        STRATEGIES[id].open       = stored[id].open ?? null;
        STRATEGIES[id].log        = stored[id].log ?? [];
        STRATEGIES[id].params     = { ...STRATEGIES[id].params, ...(stored[id].params ?? {}) };
      }
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
    poly.prices = { up, down: dn, ts: Date.now() };
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

let polyWallet   = null;   // ethers.Wallet derived from POLY_PRIVATE_KEY
let polyApiCreds = null;   // { key, secret, passphrase, address }
let realBalance  = null;   // latest USDC balance fetched from CLOB

/** EIP-712 domain for CTF Exchange order signing */
const ORDER_DOMAIN = {
  name:              'Polymarket CTF Exchange',
  version:           '1',
  chainId:           POLY_CHAIN_ID,
  verifyingContract: CTF_EXCHANGE,
};

/** EIP-712 types — must match the CTF Exchange contract exactly */
const ORDER_TYPES = {
  Order: [
    { name: 'salt',          type: 'uint256' },
    { name: 'maker',         type: 'address' },
    { name: 'signer',        type: 'address' },
    { name: 'taker',         type: 'address' },
    { name: 'tokenId',       type: 'uint256' },
    { name: 'makerAmount',   type: 'uint256' },
    { name: 'takerAmount',   type: 'uint256' },
    { name: 'expiration',    type: 'uint256' },
    { name: 'nonce',         type: 'uint256' },
    { name: 'feeRateBps',    type: 'uint256' },
    { name: 'side',          type: 'uint8'   },
    { name: 'signatureType', type: 'uint8'   },
  ],
};

/**
 * EIP-712 domain and types for Polymarket CLOB L1 authentication.
 * Must match the official clob-client exactly.
 */
const CLOB_AUTH_DOMAIN = {
  name:    'ClobAuthDomain',
  version: '1',
  chainId: POLY_CHAIN_ID,   // 137
};

const CLOB_AUTH_TYPES = {
  ClobAuth: [
    { name: 'address',   type: 'address' },
    { name: 'timestamp', type: 'string'  },
    { name: 'nonce',     type: 'uint256' },  // must be uint256 per official Polymarket docs
    { name: 'message',   type: 'string'  },
  ],
};

/**
 * L1 auth headers (EIP-712 signTypedData on ClobAuthDomain).
 * Required for: creating / fetching API keys via /auth/api-key.
 *
 * For Gnosis Safe / proxy wallets (POLY_FUNDER set):
 *   - POLY_ADDRESS = funder (Safe/proxy) address
 *   - EIP-712 address value = signing EOA address
 *   - Signature = from EOA
 * For plain EOA:
 *   - POLY_ADDRESS = EOA address (same as signer)
 */
async function l1Headers(method, reqPath, body = '') {
  const ts          = String(Math.floor(Date.now() / 1000));
  const nonce       = 0;
  const polyAddress = POLY_FUNDER || polyWallet.address;  // Safe/funder or EOA

  const sig = await polyWallet.signTypedData(
    CLOB_AUTH_DOMAIN,
    CLOB_AUTH_TYPES,
    {
      address:   polyWallet.address,  // always the EOA signing key
      timestamp: ts,
      nonce,
      message:   'This message attests that I control the given wallet',
    }
  );
  return {
    'Content-Type':   'application/json',
    'POLY_ADDRESS':   polyAddress,   // funder for Safe, EOA otherwise
    'POLY_SIGNATURE': sig,
    'POLY_TIMESTAMP': ts,
    'POLY_NONCE':     String(nonce),
  };
}

/**
 * L2 auth headers (HMAC-SHA256).
 * Required for: placing orders, cancelling, querying balance, etc.
 */
function l2Headers(method, reqPath, body = '') {
  const ts        = String(Math.floor(Date.now() / 1000));
  const msg       = ts + method + reqPath + (body || '');
  // Polymarket отдаёт secret в URL-safe base64 (символы - и _).
  // Buffer.from(..., 'base64') их не понимает → неверный HMAC → 401 на всех запросах.
  const secret64  = polyApiCreds.secret.replace(/-/g, '+').replace(/_/g, '/');
  const secretBuf = Buffer.from(secret64, 'base64');
  const sig       = crypto.createHmac('sha256', secretBuf).update(msg).digest('base64');
  return {
    'Content-Type':    'application/json',
    'POLY_ADDRESS':    polyWallet.address,  // всегда EOA-подписант
    'POLY_SIGNATURE':  sig,
    'POLY_TIMESTAMP':  ts,
    'POLY_NONCE':      '0',
    'POLY_API_KEY':    polyApiCreds.key,
    'POLY_PASSPHRASE': polyApiCreds.passphrase,
  };
}

/**
 * Fetch or create an API key pair for the current wallet.
 * If POLY_API_KEY / POLY_API_SECRET / POLY_PASSPHRASE are set in env,
 * they are used directly (skip on-chain derivation).
 */
async function getOrCreateApiKey() {
  if (process.env.POLY_API_KEY && process.env.POLY_API_SECRET && process.env.POLY_PASSPHRASE) {
    console.log('[real] using pre-configured API credentials from env');
    return {
      key:        process.env.POLY_API_KEY,
      secret:     process.env.POLY_API_SECRET,
      passphrase: process.env.POLY_PASSPHRASE,
      address:    polyWallet.address,
    };
  }

  // Try fetching existing keys first (GET)
  try {
    console.log('[real] GET /auth/api-key ...');
    const hdrs = await l1Headers('GET', '/auth/api-key');
    console.log('[real] L1 headers built, POLY_ADDRESS=', hdrs['POLY_ADDRESS']);
    const r    = await fetch(`${POLY_CLOB}/auth/api-key`, { method: 'GET', headers: hdrs, signal: AbortSignal.timeout(10000) });
    console.log('[real] GET /auth/api-key HTTP', r.status);
    if (r.ok) {
      const body = await r.json();
      const keys = Array.isArray(body) ? body : (body.apiKeys || [body]);
      console.log('[real] existing keys found:', keys.length);
      if (keys.length > 0 && keys[0].key) return { ...keys[0], address: POLY_FUNDER || polyWallet.address };
    } else {
      const txt = await r.text().catch(() => '');
      console.warn('[real] GET /auth/api-key failed:', r.status, txt.slice(0, 200));
    }
  } catch (e) {
    console.warn('[real] GET /auth/api-key exception:', e.message);
  }

  // Create a fresh key pair (POST)
  console.log('[real] POST /auth/api-key (creating new key)...');
  try {
    const hdrs = await l1Headers('POST', '/auth/api-key');
    const r2   = await fetch(`${POLY_CLOB}/auth/api-key`, { method: 'POST', headers: hdrs, signal: AbortSignal.timeout(10000) });
    const txt2 = await r2.text();
    console.log('[real] POST /auth/api-key HTTP', r2.status, txt2.slice(0, 300));
    if (!r2.ok) throw new Error(`create api-key failed: HTTP ${r2.status} — ${txt2}`);
    const creds = JSON.parse(txt2);
    return { ...creds, address: POLY_FUNDER || polyWallet.address };
  } catch (e) {
    console.error('[real] POST /auth/api-key exception:', e.message);
    throw e;
  }
}

/**
 * Build and EIP-712 sign a Polymarket CTF order.
 *
 * @param {string}       tokenId   clobTokenId for the outcome
 * @param {'BUY'|'SELL'} side
 * @param {number}       size      BUY → USDC to spend; SELL → shares to sell
 * @param {number}       price     price per share (0–1), e.g. 0.55
 */
async function buildSignedOrder(tokenId, side, size, price) {
  const isBuy = side === 'BUY';
  const MICRO = 1_000_000; // USDC and conditional tokens both use 6 decimal places

  // BUY:  maker gives USDC (makerAmount),  taker gives shares (takerAmount)
  // SELL: maker gives shares (makerAmount), taker gives USDC  (takerAmount)
  const makerAmount = isBuy
    ? BigInt(Math.round(size * MICRO))               // USDC to spend
    : BigInt(Math.round(size * MICRO));               // shares to sell
  const takerAmount = isBuy
    ? BigInt(Math.round((size / price) * MICRO))     // shares to receive
    : BigInt(Math.round((size * price) * MICRO));    // USDC to receive

  const salt = BigInt(Math.floor(Math.random() * Number.MAX_SAFE_INTEGER));

  const orderStruct = {
    salt,
    maker:         POLY_FUNDER || polyWallet.address,  // сейф, где лежат деньги
    signer:        polyWallet.address,                 // EOA, которым подписываем
    taker:         '0x0000000000000000000000000000000000000000',
    tokenId:       BigInt(tokenId),
    makerAmount,
    takerAmount,
    expiration:    0n,
    nonce:         0n,
    feeRateBps:    0n,
    side:          isBuy ? 0 : 1,
    signatureType: POLY_FUNDER ? 2 : 0,  // 2 = Gnosis Safe (when funder set), 0 = plain EOA
  };

  const signature = await polyWallet.signTypedData(ORDER_DOMAIN, ORDER_TYPES, orderStruct);

  return {
    salt:          salt.toString(),
    maker:         (POLY_FUNDER || polyWallet.address),  // та же замена
    signer:        polyWallet.address,
    taker:         '0x0000000000000000000000000000000000000000',
    tokenId:       tokenId.toString(),
    makerAmount:   makerAmount.toString(),
    takerAmount:   takerAmount.toString(),
    expiration:    '0',
    nonce:         '0',
    feeRateBps:    '0',
    side,
    signatureType: POLY_FUNDER ? 2 : 0,
    signature,
  };
}

/**
 * Place an order on the Polymarket CLOB.
 * @param {{ tokenId, side, size, price, orderType? }} opts
 * @returns {{ orderID, status, ... }}
 */
async function placeClobOrder({ tokenId, side, size, price, orderType = 'GTC' }) {
  if (!polyWallet || !polyApiCreds) throw new Error('wallet not initialised');
  if (!tokenId)                     throw new Error('tokenId is required');

  const signedOrder = await buildSignedOrder(tokenId, side, size, price);
  const body        = JSON.stringify({ order: signedOrder, owner: polyWallet.address, orderType });
  const hdrs        = l2Headers('POST', '/order', body);

  const res  = await fetch(`${POLY_CLOB}/order`, {
    method: 'POST', headers: hdrs, body,
    signal: AbortSignal.timeout(12000),
  });
  const data = await res.json().catch(() => ({}));

  if (!res.ok || data.error || data.errorCode) {
    throw new Error(data.errorMsg || data.error || data.errorCode || `HTTP ${res.status}`);
  }
  return data;  // { orderID, status, transactionsHashes?, ... }
}

/** Cancel an open order by ID. Safe to call even if already filled. */
async function cancelClobOrder(orderId) {
  if (!polyWallet || !polyApiCreds || !orderId) return;
  try {
    const body = JSON.stringify({ orderID: orderId });
    const hdrs = l2Headers('DELETE', '/order', body);
    const res  = await fetch(`${POLY_CLOB}/order`, {
      method: 'DELETE', headers: hdrs, body,
      signal: AbortSignal.timeout(8000),
    });
    console.log(`[real] cancel orderId=${orderId} HTTP ${res.status}`);
  } catch (e) { console.error('[real] cancel error:', e.message); }
}

/** Fetch real USDC balance from the CLOB API. */
async function fetchRealBalance() {
  if (!polyWallet || !polyApiCreds) return null;
  try {
    const reqPath = '/balance-allowance?asset_type=USDC';
    const hdrs    = l2Headers('GET', reqPath);
    const res     = await fetch(`${POLY_CLOB}${reqPath}`, {
      method: 'GET', headers: hdrs,
      signal: AbortSignal.timeout(8000),
    });
    if (!res.ok) {
      const txt = await res.text().catch(() => '');
      console.warn(`[real] balance-allowance HTTP ${res.status}: ${txt.slice(0, 200)}`);
      return null;
    }
    const d = await res.json();
    const b = parseFloat(d.balance ?? d.USDC ?? d.usdc ?? 0);
    return isNaN(b) ? null : b;
  } catch (e) {
    console.warn('[real] fetchRealBalance error:', e.message);
    return null;
  }
}

/** Get the status of a specific order. */
async function getClobOrderStatus(orderId) {
  if (!polyWallet || !polyApiCreds || !orderId) return null;
  try {
    const reqPath = `/order/${orderId}`;
    const hdrs    = l2Headers('GET', reqPath);
    const res     = await fetch(`${POLY_CLOB}${reqPath}`, {
      method: 'GET', headers: hdrs,
      signal: AbortSignal.timeout(8000),
    });
    if (!res.ok) return null;
    return res.json();
  } catch (_) { return null; }
}

/**
 * Boot: initialise wallet, derive API creds, sync real USDC balance.
 * Must be called AFTER initStrategies() and loadState().
 */
async function initPolyWallet() {
  // Диагностика — лог всегда, независимо от условий
  console.log(`[real] initPolyWallet called. REAL_TRADING=${REAL_TRADING}, POLY_PK_set=${!!POLY_PK}, POLY_FUNDER=${POLY_FUNDER || '(none)'}`);
  if (!REAL_TRADING) {
    console.log('[real] REAL_TRADING disabled — Momentum runs in simulation');
    return;
  }
  if (!POLY_PK) {
    console.warn('[real] REAL_TRADING=true but POLY_PRIVATE_KEY is not set — falling back to sim');
    return;
  }
  try {
    polyWallet   = new ethers.Wallet(POLY_PK);
    console.log(`[real] wallet address : ${polyWallet.address}`);
    if (POLY_FUNDER) console.log(`[real] funder address : ${POLY_FUNDER}`);
    polyApiCreds = await getOrCreateApiKey();
    console.log(`[real] API key        : ${polyApiCreds.key}`);
    realBalance  = await fetchRealBalance();
    if (realBalance !== null) {
      console.log(`[real] USDC balance   : $${realBalance.toFixed(2)}`);
      // Sync Momentum strategy's balance with the actual wallet balance
      const mom = STRATEGIES.momentum;
      if (mom && realBalance > 0) {
        mom.balance     = realBalance;
        mom.peakBalance = Math.max(mom.peakBalance || 0, realBalance);
        saveState();
      }
    } else {
      console.warn('[real] could not fetch USDC balance — check API creds');
    }
  } catch (e) {
    console.error('[real] init failed:', e.message);
    polyWallet   = null;   // stay in sim if anything goes wrong
    polyApiCreds = null;
  }
}

// Periodically refresh real balance (every 30 s) and keep Momentum in sync
setInterval(async () => {
  if (!REAL_TRADING || !polyWallet || !polyApiCreds) return;
  const b = await fetchRealBalance();
  if (b !== null) {
    realBalance = b;
    const mom = STRATEGIES.momentum;
    // Only overwrite balance when no position is open
    if (mom && !mom.open && !mom.pendingReal) {
      mom.balance = b;
    }
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
    const polyPrice = ctx.sigP.dir === 'UP' ? ctx.polyUp : ctx.polyDn;
    const ourProb   = ctx.sigP.dir === 'UP' ? ctx.sigP.prob : (1 - ctx.sigP.prob);
    const edge      = ourProb - polyPrice;
    if (edge < p.minEdge) return null;
    return { side: ctx.sigP.dir, polyPrice, ourProb, edge, info: `conf=${ctx.sigP.conf.toFixed(0)}% edge=+${(edge * 100).toFixed(1)}pp` };
  },
  shouldExit(ctx, pos, p) {
    const curMid = pos.side === 'UP' ? ctx.polyUp : ctx.polyDn;
    if (curMid !== null) {
      const mv = (curMid - pos.polyEntryPrice) / pos.polyEntryPrice;
      if (mv >= p.tpPct) return { reason: 'TP', exitPrice: curMid };
      if (mv <= -p.slPct) return { reason: 'SL', exitPrice: curMid };
    }
    if (ctx.sigP.dir !== 'WAIT' && ctx.sigP.dir !== pos.side && ctx.sigP.conf > p.flipConf)
      return { reason: 'FLIP', exitPrice: curMid };
    if (ctx.curBTC && pos.btcAtEntry && ctx.msToEnd > 90000) {
      const mvBTC = ((ctx.curBTC - pos.btcAtEntry) / pos.btcAtEntry) * 100;
      if (pos.side === 'UP'   && mvBTC < -p.advMovePct) return { reason: 'ADVERSE', exitPrice: curMid };
      if (pos.side === 'DOWN' && mvBTC > p.advMovePct)  return { reason: 'ADVERSE', exitPrice: curMid };
    }
    return null;
  },
};

const STRAT_DEFINITIONS = [STRAT_MOMENTUM];

function initStrategies() {
  for (const def of STRAT_DEFINITIONS) {
    STRATEGIES[def.id] = {
      def,
      enabled:      false,
      balance:      1000,
      peakBalance:  1000,
      open:         null,
      log:          [],
      params:       { ...def.defaults },
      pendingReal:  false,   // true while a real BUY order is in-flight
    };
  }
}

function getStratContext() {
  const win    = currentPolyWindow();
  const sigP   = predictPoly();
  const curBTC = chain.currentPrice || (ticks.length ? ticks[ticks.length - 1].price : null);
  return {
    win,
    msToEnd:     Math.max(0, win.endTs - Date.now()),
    polyUp:      poly.prices.up,
    polyDn:      poly.prices.down,
    sigP,
    curBTC,
    openingBTC:  poly.windowOpeningBTC,
    openingSource: poly.windowOpeningSource,
  };
}

function stratOpen(s, ctx, entry) {
  const sizeUSDC = sizingByKelly(s.balance, entry.ourProb, entry.polyPrice, s.params.kellyFrac, s.params.maxFrac);
  if (sizeUSDC < 1)                return;
  if (sizeUSDC > s.balance * 0.95) return;

  const isRealOrder = REAL_TRADING && s.def.id === 'momentum' && !!polyWallet && !!polyApiCreds;
  const tokenId     = entry.side === 'UP' ? poly.market?.tokenIdUp : poly.market?.tokenIdDown;

  // For real orders: block re-entry while async BUY is in-flight
  if (isRealOrder && !tokenId) {
    console.warn('[real] missing tokenId — skipping real entry');
    return;
  }

  const openingBTC = ctx.openingBTC || ctx.curBTC;
  s.open = {
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
  };
  s.balance    -= sizeUSDC;
  s.pendingReal = isRealOrder;   // prevent double-entry while order is in-flight
  saveState();
  console.log(`[${s.def.id}] ${isRealOrder ? 'REAL' : 'SIM'} OPEN ${entry.side} @ ${entry.polyPrice.toFixed(3)} size=$${sizeUSDC.toFixed(2)} | ${entry.info}`);

  // ── Place real BUY order on Polymarket CLOB (async, Momentum only) ──────────
  if (isRealOrder) {
    placeClobOrder({ tokenId, side: 'BUY', size: sizeUSDC, price: entry.polyPrice })
      .then(result => {
        s.pendingReal = false;
        if (s.open) {
          s.open.realOrderId     = result.orderID;
          s.open.realOrderStatus = result.status || 'placed';
          saveState();
          console.log(`[real] BUY placed orderId=${result.orderID} status=${result.status}`);
        }
      })
      .catch(err => {
        console.error('[real] BUY order FAILED:', err.message);
        // Rollback: refund balance and clear the position
        if (s.open) {
          s.balance    += s.open.sizeUSDC;
          s.open        = null;
          s.pendingReal = false;
          saveState();
          console.warn('[real] position rolled back due to order failure');
        }
      });
  }
}

function stratClose(s, ctx, reason, exitPolyPrice) {
  const o      = s.open;
  const shares = o.sizeUSDC / o.polyEntryPrice;
  let proceeds, won;

  if (reason === 'SETTLE') {
    const settleBTC = ctx.curBTC;
    won           = o.side === 'UP' ? settleBTC > o.btcAtEntry : settleBTC < o.btcAtEntry;
    proceeds      = won ? shares * 1.0 : 0;
    exitPolyPrice = won ? 1.0 : 0.0;
  } else {
    proceeds = shares * exitPolyPrice;
    won      = proceeds > o.sizeUSDC;
  }

  const pnl   = proceeds - o.sizeUSDC;
  const entry = { ...o, closeTime: Date.now(), reason, proceeds, pnl, won, btcAtClose: ctx.curBTC, polyExitPrice: exitPolyPrice, strategy: s.def.id };
  s.balance    += proceeds;
  s.peakBalance = Math.max(s.peakBalance, s.balance);
  s.log.push(entry);
  if (s.log.length > 500) s.log.shift();
  s.open = null;
  saveState();
  console.log(`[${s.def.id}] ${o.isReal ? 'REAL' : 'SIM'} CLOSE ${o.side} reason=${reason} pnl=${pnl >= 0 ? '+' : ''}$${pnl.toFixed(2)}`);

  // ── Place real SELL order (or wait for on-chain settlement) ─────────────────
  if (o.isReal) {
    if (reason === 'SETTLE') {
      // Polymarket auto-redeems winning tokens ~1 min after window close.
      // We just sync the real balance after the grace period.
      setTimeout(async () => {
        const b = await fetchRealBalance();
        if (b !== null) {
          realBalance = b;
          const mom = STRATEGIES.momentum;
          if (mom && !mom.open) {
            mom.balance = b;
            saveState();
            console.log(`[real] post-settle balance: $${b.toFixed(2)}`);
          }
        }
      }, 90_000); // 90 s after window close
    } else if (o.tokenId && o.realOrderId && exitPolyPrice > 0.01) {
      // Early exit (TP / SL / FLIP / ADVERSE): sell shares back on CLOB.
      // Discount 0.5 % to increase fill probability.
      const sellPrice = Math.max(0.01, parseFloat((exitPolyPrice * 0.995).toFixed(4)));
      placeClobOrder({ tokenId: o.tokenId, side: 'SELL', size: shares, price: sellPrice })
        .then(result => {
          console.log(`[real] SELL placed orderId=${result.orderID} reason=${reason} price=${sellPrice}`);
          // Refresh balance after sell fills (optimistic 10 s delay)
          setTimeout(async () => {
            const b = await fetchRealBalance();
            if (b !== null) {
              realBalance = b;
              const mom = STRATEGIES.momentum;
              if (mom && !mom.open) { mom.balance = b; saveState(); }
            }
          }, 10_000);
        })
        .catch(err => {
          console.error(`[real] SELL order FAILED (${reason}):`, err.message);
          // Position will auto-settle at expiry — no further action needed.
        });
    } else if (o.tokenId && !o.realOrderId) {
      // BUY order was still pending when we decided to close — cancel it.
      console.warn('[real] closing before BUY order confirmed — attempting cancel');
      if (o.realOrderId) cancelClobOrder(o.realOrderId);
    }
  }
}

function processStrategies() {
  const ctx = getStratContext();
  for (const id in STRATEGIES) {
    const s = STRATEGIES[id];
    if (!s.enabled)           continue;
    if (ticks.length < 60)    continue;
    if (s.pendingReal)        continue;   // real BUY in-flight, skip tick

    if (s.open) {
      if (Date.now() >= s.open.expiryTime) {
        stratClose(s, ctx, 'SETTLE', null); continue;
      }
      const exit = s.def.shouldExit(ctx, s.open, s.params);
      if (exit && exit.exitPrice !== null) stratClose(s, ctx, exit.reason, exit.exitPrice);
    } else {
      if (ctx.polyUp === null) continue;
      const entry = s.def.shouldEnter(ctx, s.params);
      if (entry) stratOpen(s, ctx, entry);
    }
  }
}

// ─── COINBASE WEBSOCKET ──────────────────────────────────────────────────────
let ws_ = null;

function connectCoinbase() {
  wsStatus = 'connecting';
  try {
    ws_ = new WebSocket('wss://advanced-trade-ws.coinbase.com');
    const timeout = setTimeout(() => { if (wsStatus !== 'live') { ws_.terminate(); startSim(); } }, 10000);

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

    ws_.on('error', () => { if (wsStatus !== 'live') startSim(); });
    ws_.on('close', () => {
      if (wsStatus === 'live') {
        wsStatus = 'reconnecting';
        console.log('[coinbase] disconnected — reconnecting in 3s');
        setTimeout(connectCoinbase, 3000);
      }
    });
  } catch (e) { startSim(); }
}

// ─── SIMULATION MODE ─────────────────────────────────────────────────────────
function startSim() {
  if (isSim) return;
  isSim    = true;
  wsStatus = 'sim';
  console.log('[sim] started (ws blocked/failed)');
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

  setInterval(() => {
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
    if (chain.enabled) { chain.currentPrice = price + (Math.random() - 0.5) * 1; chain.lastUpdate = Date.now(); chain.available = true; }
  }, 120);
}

// ─── STATE SNAPSHOT FOR DASHBOARD ────────────────────────────────────────────
function buildSnapshot() {
  const sigS   = predictScalp();
  const sigP   = predictPoly();
  const sigM   = computeMainSignal();
  const curBTC = chain.currentPrice || (ticks.length ? ticks[ticks.length - 1].price : null);
  const win    = currentPolyWindow();

  // Per-strategy summary
  const strats = {};
  for (const id in STRATEGIES) {
    const s   = STRATEGIES[id];
    const log = s.log;
    const wins = log.filter(t => t.won).length;
    const pnl  = log.reduce((a, t) => a + t.pnl, 0);
    const dd   = (() => { let peak = 1000, cur = 1000, d = 0; for (const t of log) { cur += t.pnl; peak = Math.max(peak, cur); d = Math.min(d, (cur - peak) / peak); } return d; })();
    strats[id] = {
      name:     s.def.name,
      enabled:  s.enabled,
      balance:  s.balance,
      pnl,
      trades:   log.length,
      wins,
      dd,
      open:     s.open,
      pendingReal: s.pendingReal,
      lastTrades: log.slice(-5).reverse(),
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

// API: toggle strategy
app.post('/api/strategy/:id/toggle', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  s.enabled = !s.enabled;
  saveState();
  console.log(`[strategy] ${req.params.id} → ${s.enabled ? 'ON' : 'OFF'}`);
  res.json({ id: req.params.id, enabled: s.enabled });
});

// API: reset strategy
app.post('/api/strategy/:id/reset', (req, res) => {
  const s = STRATEGIES[req.params.id];
  if (!s) return res.status(404).json({ error: 'not found' });
  s.balance    = 1000;
  s.peakBalance = 1000;
  s.open       = null;
  s.log        = [];
  saveState();
  res.json({ ok: true });
});

// API: export CSV
app.get('/api/export/csv', (_, res) => {
  const rows = [['strategy','time_open','time_close','side','market','poly_entry','poly_exit','btc_open','btc_close','size','pnl','edge','reason','won','entry_info','real_order_id']];
  for (const id in STRATEGIES) {
    for (const t of STRATEGIES[id].log) {
      rows.push([
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
      ]);
    }
  }
  res.set({ 'Content-Type': 'text/csv', 'Content-Disposition': `attachment; filename="bot_log_${Date.now()}.csv"` });
  res.send(rows.map(r => r.join(',')).join('\n'));
});

// ─── REAL TRADING API ENDPOINTS ───────────────────────────────────────────────

// GET /api/real/status — wallet address, readiness, live USDC balance
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
      realEnabled: REAL_TRADING && id === 'momentum',
      open:        STRATEGIES[id].open,
    })),
  });
});

// POST /api/real/cancel — cancel the open real order for Momentum (emergency stop)
app.post('/api/real/cancel', async (_, res) => {
  const mom = STRATEGIES.momentum;
  if (!mom || !mom.open?.realOrderId) return res.json({ ok: false, reason: 'no open real order' });
  await cancelClobOrder(mom.open.realOrderId);
  res.json({ ok: true, cancelledOrderId: mom.open.realOrderId });
});

// POST /api/real/close-now — immediately close real position at current mid price
app.post('/api/real/close-now', async (_, res) => {
  const mom = STRATEGIES.momentum;
  if (!mom || !mom.open) return res.status(400).json({ error: 'no open position' });
  const ctx      = getStratContext();
  const midPrice = mom.open.side === 'UP' ? ctx.polyUp : ctx.polyDn;
  if (!midPrice)  return res.status(400).json({ error: 'no poly price available' });
  stratClose(mom, ctx, 'MANUAL', midPrice);
  res.json({ ok: true, exitPrice: midPrice });
});

// ─── BOOT ────────────────────────────────────────────────────────────────────
initStrategies();
loadState();
connectCoinbase();
// Real trading: init wallet AFTER strategies are loaded
initPolyWallet().catch(e => console.error('[real] boot error:', e.message));

// Book snapshot for OFI every 500ms
setInterval(() => {
  if (book.bids.size && book.asks.size) {
    bookHistory.push(bookSnapshotDepth(10));
    if (bookHistory.length > 600) bookHistory.shift();
  }
}, 500);

// Polymarket every 2s
setInterval(() => { if (poly.autoFetch) fetchPolyMarket().catch(e => console.error('[poly]', e.message)); }, 2000);
// Chainlink every 4s
setInterval(() => { if (chain.enabled && !isSim) refreshChainlinkPrice().catch(() => {}); }, 4000);
// Strategy engine every 1s
setInterval(() => { try { processStrategies(); } catch (e) { console.error('[strategies]', e.message); } }, 1000);
// SSE broadcast every 1s
setInterval(() => { if (sseClients.size > 0) broadcast(buildSnapshot()); }, 1000);
// Auto-save every 60s
setInterval(saveState, 60000);

app.listen(PORT, () => console.log(`[server] running on port ${PORT}`));
