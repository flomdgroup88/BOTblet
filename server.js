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
        demoEnabled: s.demoEnabled,
        realEnabled: s.realEnabled,
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
      const s = STRATEGIES[id];
      if (!s) continue;
      const st = stored[id];
      if (st.demo !== undefined) {
        // New dual-account format
        s.demoEnabled      = st.demoEnabled      ?? false;
        s.realEnabled      = st.realEnabled      ?? false;
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
 * - tokenId: string (Polymarket conditional token ID)
 * - side:    'BUY' | 'SELL'
 * - size:    number (in shares for limit / in USDC for market)
 * - price:   number (0.01..0.99)
 * - orderType: 'GTC' (default) | 'FOK' | 'FAK' | 'GTD'
 */
async function placeClobOrder({ tokenId, side, size, price, orderType = 'GTC' }) {
  if (!polyClob)          throw new Error('CLOB client not initialised — wallet/creds missing');
  if (!tokenId)           throw new Error('tokenId is required');

  const userOrder = {
    tokenID: tokenId,
    price:   price,
    side:    _mapSide(side),
    size:    size,
  };

  try {
    const resp = await polyClob.createAndPostOrder(userOrder, {}, _mapOrderType(orderType));
    if (resp && (resp.error || resp.errorMsg)) {
      throw new Error(resp.errorMsg || resp.error);
    }
    // V2 response shape: { success, errorMsg, orderID, transactionsHashes, status, takingAmount, makingAmount }
    return {
      orderID:            resp.orderID,
      status:             resp.status,
      success:            resp.success,
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

/** Cancel an open order by ID. Safe to call even if already filled. */
async function cancelClobOrder(orderId) {
  if (!polyClob || !orderId) return;
  try {
    const resp = await polyClob.cancelOrder({ orderID: orderId });
    console.log(`[real] cancel orderId=${orderId} →`, JSON.stringify(resp).slice(0, 200));
  } catch (e) {
    console.error('[real] cancel error:', e.message);
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
    } else {
      console.warn('[real] ⚠️  L2 auth or balance fetch failed — see prior logs');
      console.warn('[real] If this persists: check that POLY_PRIVATE_KEY matches the wallet you used to log into Polymarket UI');
      console.warn('[real] and that SIGNATURE_TYPE matches your account type (0=EOA, 1=Magic/email, 2=Phantom+Safe, 3=smart wallet)');
    }
  } catch (e) {
    console.error('[real] init failed:', e.message);
    if (e.stack) console.error(e.stack.split('\n').slice(0, 5).join('\n'));
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
      demoEnabled:  false,
      realEnabled:  false,
      demo: { balance: 1000, peakBalance: 1000, open: null, log: [] },
      real: { balance: 1000, peakBalance: 1000, open: null, log: [] },
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

function stratOpen(s, ctx, entry, acct, isReal) {
  // ── Safety guard: never size a real trade from the default $1000 placeholder ──
  // If the USDC balance was never successfully fetched from CLOB, bail out.
  if (isReal && REAL_TRADING && realBalance === null) {
    console.warn(`[real] skipping OPEN — USDC balance not yet confirmed (still at default). Will retry next signal.`);
    return;
  }

  // For real accounts, always use the live wallet balance for sizing (not stale state value)
  const effectiveBalance = isReal && realBalance !== null ? realBalance : acct.balance;
  const sizeUSDC = sizingByKelly(effectiveBalance, entry.ourProb, entry.polyPrice, s.params.kellyFrac, s.params.maxFrac);
  if (sizeUSDC < 1)                       return;
  if (sizeUSDC > effectiveBalance * 0.95) return;

  const isRealOrder = isReal && s.def.id === 'momentum' && !!polyWallet && !!polyApiCreds;
  const tokenId     = entry.side === 'UP' ? poly.market?.tokenIdUp : poly.market?.tokenIdDown;

  // For real orders: need tokenId
  if (isRealOrder && !tokenId) {
    console.warn('[real] missing tokenId — skipping real entry');
    return;
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
  };
  acct.balance    -= sizeUSDC;
  if (isRealOrder) s.pendingReal = true;
  saveState();
  console.log(`[${s.def.id}] ${isRealOrder ? 'REAL' : 'SIM'} OPEN ${entry.side} @ ${entry.polyPrice.toFixed(3)} size=$${sizeUSDC.toFixed(2)} (balance=$${effectiveBalance.toFixed(2)}) | ${entry.info}`);

  // ── Place real BUY order on Polymarket CLOB (async, Momentum only) ──────────
  if (isRealOrder) {
    placeClobOrder({ tokenId, side: 'BUY', size: sizeUSDC, price: entry.polyPrice })
      .then(result => {
        s.pendingReal = false;
        if (acct.open) {
          acct.open.realOrderId     = result.orderID;
          acct.open.realOrderStatus = result.status || 'placed';
          saveState();
          console.log(`[real] BUY placed orderId=${result.orderID} status=${result.status}`);
        }
      })
      .catch(err => {
        console.error('[real] BUY order FAILED:', err.message);
        // Rollback: refund balance and clear the position
        if (acct.open) {
          acct.balance    += acct.open.sizeUSDC;
          acct.open        = null;
          s.pendingReal    = false;
          saveState();
          console.warn('[real] position rolled back due to order failure');
        }
      });
  }
}

function stratClose(s, ctx, reason, exitPolyPrice, acct, isReal) {
  const o      = acct.open;
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
  acct.balance    += proceeds;
  acct.peakBalance = Math.max(acct.peakBalance, acct.balance);
  acct.log.push(entry);
  if (acct.log.length > 500) acct.log.shift();
  acct.open = null;
  saveState();
  console.log(`[${s.def.id}] ${o.isReal ? 'REAL' : 'SIM'} CLOSE ${o.side} reason=${reason} pnl=${pnl >= 0 ? '+' : ''}$${pnl.toFixed(2)}`);

  // ── Place real SELL order (or wait for on-chain settlement) ─────────────────
  if (o.isReal) {
    if (reason === 'SETTLE') {
      // Polymarket auto-redeems winning tokens ~1 min after window close.
      setTimeout(async () => {
        const b = await fetchRealBalance();
        if (b !== null) {
          realBalance = b;
          const mom = STRATEGIES.momentum;
          if (mom && !mom.real.open) {
            mom.real.balance = b;
            saveState();
            console.log(`[real] post-settle balance: $${b.toFixed(2)}`);
          }
        }
      }, 90_000); // 90 s after window close
    } else if (o.tokenId && o.realOrderId && exitPolyPrice > 0.01) {
      // Early exit (TP / SL / FLIP / ADVERSE): sell shares back on CLOB.
      const sellPrice = Math.max(0.01, parseFloat((exitPolyPrice * 0.995).toFixed(4)));
      placeClobOrder({ tokenId: o.tokenId, side: 'SELL', size: shares, price: sellPrice })
        .then(result => {
          console.log(`[real] SELL placed orderId=${result.orderID} reason=${reason} price=${sellPrice}`);
          setTimeout(async () => {
            const b = await fetchRealBalance();
            if (b !== null) {
              realBalance = b;
              const mom = STRATEGIES.momentum;
              if (mom && !mom.real.open) { mom.real.balance = b; saveState(); }
            }
          }, 10_000);
        })
        .catch(err => {
          console.error(`[real] SELL order FAILED (${reason}):`, err.message);
        });
    } else if (o.tokenId && !o.realOrderId) {
      // BUY order was placed but hasn't confirmed yet — attempt cancel by querying open orders
      console.warn('[real] closing before BUY order confirmed — will cancel once orderId is known');
      // Poll for orderId for up to 10s then cancel
      const waitAndCancel = async () => {
        for (let i = 0; i < 10; i++) {
          await new Promise(r => setTimeout(r, 1000));
          if (o.realOrderId) { await cancelClobOrder(o.realOrderId); return; }
        }
        console.warn('[real] BUY orderId never arrived — could not cancel');
      };
      waitAndCancel().catch(e => console.error('[real] waitAndCancel error:', e.message));
    }
  }
}

function processAccount(s, ctx, acct, isReal) {
  if (acct.open) {
    if (Date.now() >= acct.open.expiryTime) {
      stratClose(s, ctx, 'SETTLE', null, acct, isReal); return;
    }
    const exit = s.def.shouldExit(ctx, acct.open, s.params);
    if (exit && exit.exitPrice !== null) stratClose(s, ctx, exit.reason, exit.exitPrice, acct, isReal);
  } else {
    if (ctx.polyUp === null) return;
    const entry = s.def.shouldEnter(ctx, s.params);
    if (entry) stratOpen(s, ctx, entry, acct, isReal);
  }
}

function processStrategies() {
  const ctx = getStratContext();
  for (const id in STRATEGIES) {
    const s = STRATEGIES[id];
    if (ticks.length < 60) continue;

    // Demo account — always simulation, never real orders
    if (s.demoEnabled) {
      processAccount(s, ctx, s.demo, false);
    }

    // Real account — places CLOB orders if wallet is configured; otherwise sim
    if (s.realEnabled && !s.pendingReal) {
      const canReal = REAL_TRADING && !!polyWallet && !!polyApiCreds;
      processAccount(s, ctx, s.real, canReal);
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
      demoEnabled: s.demoEnabled,
      realEnabled: s.realEnabled,
      demo:        accountSummary(s.demo),
      real:        accountSummary(s.real),
      pendingReal: s.pendingReal,
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
  const rows = [['mode','strategy','time_open','time_close','side','market','poly_entry','poly_exit','btc_open','btc_close','size','pnl','edge','reason','won','entry_info','real_order_id']];
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
        ]);
      }
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
setInterval(() => { if (poly.autoFetch) fetchPolyMarket().catch(e => console.error('[poly]', e.message)); }, 2000);
// Chainlink every 4s
setInterval(() => { if (chain.enabled && !isSim) refreshChainlinkPrice().catch(() => {}); }, 4000);
// Strategy engine every 1s
setInterval(() => { try { processStrategies(); } catch (e) { console.error('[strategies]', e.message); } }, 1000);
// SSE broadcast every 1s
setInterval(() => { if (sseClients.size > 0) broadcast(buildSnapshot()); }, 1000);
// Auto-save every 60s
setInterval(saveState, 60000);

app.listen(PORT, () => {
  console.log(`[server] running on port ${PORT}`);
  console.log(`[server] HMAC sig encoding: URL-safe base64 (+→-, /→_) ✓ POLYMARKET_FIX_APPLIED`);
});
