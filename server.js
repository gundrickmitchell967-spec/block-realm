'use strict';
// Block Realm multiplayer server.
// Serves the game page and a WebSocket at /ws. The server keeps two worlds. Each has its own block edits,
// players, cow and time of day, and players in one world never see players in the other:
//   OUR WORLD    - locked with a password (OUR_WORLD_PASSWORD, default 8645). Saved in WORLD_FILE (world.json).
//   PUBLIC WORLD - anybody can join. Saved in PUBLIC_WORLD_FILE (world-public.json).
// Terrain is generated in each browser from the same seed, so the server only stores changes.

const http = require('http');
const https = require('https');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');
const crypto = require('crypto');

const PORT = Number(process.env.PORT) || 8080;
const HOST = process.env.HOST || '0.0.0.0';
const MAX_PLAYERS = Number(process.env.MAX_PLAYERS) || 16;     // across both worlds
const PAGE = path.join(__dirname, 'public', 'index.html');
const CH = 64;                  // world height in blocks
const REACH = 12;               // a block change must be this close to the player's last reported position
const MAX_BLOCK_ID = 999;       // highest block id a player may place (see BLOCKS in index.html: MAX_ID there must match)
const COLORS = ['#e6594b', '#4b9be6', '#58c25a', '#e6c44b', '#b35ae6', '#4be6d6', '#e6894b', '#e64b9b'];
const DAY_LEN = 480;            // seconds for one full day (the same as in index.html)
const PLOT_RATE = 20, PLOT_MIN = 3, PLOT_MAX = 32;   // a plot costs this much cash per block; its sides are between these lengths
const HACK_MS = (Number(process.env.HACK_SECONDS) || 30) * 1000;   // how long a decoded door stays open
const SHOP_PRICES = { hacktool: { name: 'Hacker Tool', price: 10000 } };   // the shop's items and prices (the client shows the same prices)
const VOICE_RELAY_RANGE = 48;   // voice connections can only be set up between players this close (see VOICE_RANGE in index.html)

// the two worlds. OUR WORLD keeps the world that was already saved in world.json; its password is checked here
const WORLDS = {
  our: {
    key: 'our', name: 'OUR WORLD',
    file: process.env.WORLD_FILE || path.join(__dirname, 'world.json'),
    password: process.env.OUR_WORLD_PASSWORD || '8645',
  },
  public: {
    key: 'public', name: 'PUBLIC WORLD',
    file: process.env.PUBLIC_WORLD_FILE || path.join(__dirname, 'world-public.json'),
    password: null,
  },
};

// admin codes are checked here, on the server, so nobody can gain admin powers by reading the page.
// set ADMIN_CODE_DESIGNER and ADMIN_CODE_CREATOR in the environment to change them
const ADMIN_CODES = [
  { role: 'designer', code: process.env.ADMIN_CODE_DESIGNER || '5468' },   // GAME DESIGNER: invisibility, wall hacks
  { role: 'creator',  code: process.env.ADMIN_CODE_CREATOR  || '0702' },   // GAME CREATOR: all of the above, plus player commands
];
const authTries = new Map();     // client address -> { n: wrong tries so far, until: time the lock ends }
const pwTries = new Map();       // client address -> the same, for world passwords
const doorTries = new Map();     // client address -> the same, for typing a door's password
function codeDigest(s) { return crypto.createHash('sha256').update(String(s)).digest(); }

// ---- who placed each block, and doors with passwords ----
// a player's id (sent by their browser) is kept only as a hash, so the saved world holds no raw ids. A browser that sends
// no usable id still plays, but its blocks cannot be claimed again after it reconnects.
function pidFor(s) {
  if (typeof s === 'string' && /^[A-Za-z0-9_-]{16,64}$/.test(s)) return codeDigest('pid:' + s).toString('hex');
  return crypto.randomBytes(16).toString('hex');
}
// the game creator's BREAK ANY BLOCK switch: while it is on, the creator may break any block and open any locked door
function canBypass(p) { return p.role === 'creator' && p.bypass === true; }
function isDoorBlock(id) { return id >= 12 && id <= 15; }
// two halves of one door that open or shut into each other (lower 12/13, upper 14/15)
function sameDoorHalf(a, b) { return isDoorBlock(a) && isDoorBlock(b) && (a <= 13) === (b <= 13); }
// the keys of the two blocks of a door, given its lower block [x,y,z]
function lockKeys(lo) { return [lo.join(','), [lo[0], lo[1] + 1, lo[2]].join(',')]; }
// the lower block [x,y,z] of the door that (x,y,z) is part of, if a player placed that door; otherwise null
function doorPair(w, x, y, z) {
  const id = w.edits.get(x + ',' + y + ',' + z);
  const lo = (id === 14 || id === 15) ? [x, y - 1, z] : (id === 12 || id === 13) ? [x, y, z] : null;
  if (!lo) return null;
  const below = w.edits.get(lo.join(',')), above = w.edits.get(lockKeys(lo)[1]);
  return (below === 12 || below === 13) && (above === 14 || above === 15) ? lo : null;
}
function passDigest(salt, pass) { return crypto.createHash('sha256').update(salt + ':' + pass).digest('hex'); }
function cleanPass(s) { return typeof s === 'string' ? s.replace(/[\u0000-\u001f]/g, '').trim().slice(0, 16) : ''; }
// may this player open the lock: its owner, someone who typed the password, or the creator with BREAK ANY BLOCK on
function lockOpenFor(p, lock) { return lock.owner === p.pid || lock.allowed.has(p.pid) || canBypass(p) || Date.now() < (lock.openUntil || 0); }
// what a player's wallet looks like: their cash and hacker tools
function walletMsg(w, q) { return { type: 'wallet', cash: w.coins.get(q.pid) || 0, tools: w.tools.get(q.pid) || 0 }; }
// what one player is told about a door's lock: whether it is locked, whether it is theirs, and whether they may open it
function lockMsg(w, q, lo, lock) {
  const left = lock && lock.openUntil > Date.now() && lock.decodedBy === q.pid ? lock.openUntil - Date.now() : 0;
  return { type: 'lock', x: lo[0], y: lo[1], z: lo[2], locked: !!lock, mine: w.owners.get(lo.join(',')) === q.pid, ok: !!lock && lockOpenFor(q, lock), openFor: left };
}
function announceLock(w, lo, lock) {
  for (const q of players.values()) if (q.world === w && q.joined) sendTo(q, lockMsg(w, q, lo, lock));
}
// a door's password is removed, or the door is broken: the lock is gone for everyone
function dropLock(w, key) {
  const L = w.locks.get(key);
  if (!L) return;
  for (const k of L.keys) w.locks.delete(k);
  announceLock(w, L.lower, null);
}
// when a decoded door's time is up: it shuts again, and locks for everyone. It waits while someone stands in the doorway
function shutDecodedDoor(w, lo, lock) {
  const lk = lo.join(','), uk = [lo[0], lo[1] + 1, lo[2]].join(',');
  if (w.locks.get(lk) !== lock) return;                       // the door was broken, or its lock changed, meanwhile
  const inDoorway = [...players.values()].some(q => q.world === w && q.joined &&
    Math.abs(q.x - (lo[0] + 0.5)) < 0.9 && Math.abs(q.z - (lo[2] + 0.5)) < 0.9 && q.y < lo[1] + 2 && q.y + 1.8 > lo[1]);
  if (inDoorway) return setTimeout(() => shutDecodedDoor(w, lo, lock), 500);
  let changed = false;
  if (w.edits.get(lk) === 13) { w.edits.set(lk, 12); changed = true; broadcast(w, { type: 'edit', x: lo[0], y: lo[1], z: lo[2], id: 12, by: 0 }); }
  if (w.edits.get(uk) === 15) { w.edits.set(uk, 14); changed = true; broadcast(w, { type: 'edit', x: lo[0], y: lo[1] + 1, z: lo[2], id: 14, by: 0 }); }
  if (changed) scheduleSave(w);
  announceLock(w, lo, lock);
}
// the plot a block position is in, if any (plots never overlap)
function plotAt(w, x, z) { return w.plots.find(pl => x >= pl.x0 && x <= pl.x1 && z >= pl.z0 && z <= pl.z1) || null; }
function plotsOverlap(a, b) { return a.x0 <= b.x1 && b.x0 <= a.x1 && a.z0 <= b.z1 && b.z0 <= a.z1; }
function plotsMsg(w, q) { return { type: 'plots', list: w.plots.map(pl => ({ x0: pl.x0, z0: pl.z0, x1: pl.x1, z1: pl.z1, mine: pl.owner === q.pid, name: pl.name || 'PLOT', who: pl.ownerName || 'SOMEONE', refund: pl.owner === q.pid ? Math.floor((pl.price || 0) / 2) : 0, sale: pl.sale || 0 })) }; }
const MERGED_MAX = 64;                       // the longest side a merged plot may have
function canMerge(a, b) {
  return (a.x0 === b.x0 && a.x1 === b.x1 && (a.z1 + 1 === b.z0 || b.z1 + 1 === a.z0)) ||
         (a.z0 === b.z0 && a.z1 === b.z1 && (a.x1 + 1 === b.x0 || b.x1 + 1 === a.x0));
}
const sameRect = (o, r) => o.x0 === r[0] && o.z0 === r[1] && o.x1 === r[2] && o.z1 === r[3];
let nextOfferId = 1;
function cleanPlotName(v) { return typeof v === 'string' ? v.replace(/[\x00-\x1f<>]/g, '').trim().slice(0, 24) : ''; }
function offersMsg(w, q) {
  const out = o => ({ id: o.id, fromName: o.fromName, toName: o.toName, name: o.name, size: o.size, price: o.price });
  const all = [...w.offers.values()];
  return { type: 'offers', incoming: all.filter(o => o.toPid === q.pid).map(out), outgoing: all.filter(o => o.fromPid === q.pid).map(out) };
}
function announceOffers(w) { for (const q of players.values()) if (q.world === w && q.joined) sendTo(q, offersMsg(w, q)); }
function announcePlots(w) { for (const q of players.values()) if (q.world === w && q.joined) sendTo(q, plotsMsg(w, q)); }
// a transaction goes in the world's log (the latest 300 are kept)
function logTxn(w, e) {
  w.log.push(Object.assign({ t: Date.now() }, e));
  if (w.log.length > 300) w.log.splice(0, w.log.length - 300);
  scheduleSave(w);
}
// ---- the shop's job, the bounties, and the slot machine ----
// the shop's jobs: a shift pays each job's cash a minute, and the most a shift can pay is perMin * shiftMin. The client has the same list (JOBS in index.html).
const JOBS = [
  { name: 'Shop sweeper',      perMin: 12, shiftMin: 15, desc: 'Sweep the shop floor for the shopkeeper.' },
  { name: 'Stock clerk',       perMin: 14, shiftMin: 15, desc: 'Count and shelve the stock behind the counter.' },
  { name: 'Delivery runner',   perMin: 16, shiftMin: 12, desc: 'Run parcels between the shops and the plots.' },
  { name: "Surveyor's helper", perMin: 18, shiftMin: 10, desc: 'Hold the measuring pole for the Land Surveyor.' },
  { name: "Builder's mate",    perMin: 24, shiftMin: 10, desc: 'Carry and place blocks for the builders.' },
  { name: 'Site foreman',      perMin: 30, shiftMin: 10, desc: 'Keep the building site moving.' },
  { name: 'Master builder',    perMin: 40, shiftMin: 8,  desc: 'Build the finest work in town.' },
];
const JOB_EVERY = 60000, JOB_BREAK = 5 * 60000;   // a shift pays once a minute; then a 5 minute break
// passive income: an investment pays while you are away. At most INVEST_MAX_HOURS of it waits to be collected.
const INVESTMENTS = [
  { name: 'Lemonade stand',   cost: 1000, perHour: 10, desc: 'A stand on the shop street. It sells lemonade while you are away.' },
  { name: 'Vending machines', cost: 5000, perHour: 60, desc: 'Machines in the shop lobbies. They fill up and pay out while you are away.' },
];
const INVEST_MAX_HOURS = 12;
// rewards: a daily sign-in (day 1 pays 50, each day in a row adds 15, up to day 7 at 140; a missed day starts again)
// and playtime (every 10 minutes of play banks 20 cash, up to 3 waiting; only time spent moving around counts)
const DAILY_BASE = 50, DAILY_STEP = 15, DAILY_CAP_DAY = 7;
const PLAY_BLOCK = (Number(process.env.PLAY_BLOCK_SECONDS) || 600) * 1000;   // 10 minutes of play per reward (the variable is for testing)
const PLAY_REWARD = 20, PLAY_BANK_MAX = 3, PLAY_ACTIVE = 60000;
const SMACK_FREEZE = 15;                                        // seconds a bountied player stands still after a smack
const CLAIM_MS = 10 * 60000;                                    // a claim waits this long for the claimer to take it to the shop
const SLOT_SYMBOLS = ['SEVEN', 'BAR', 'BELL', 'CHERRY', 'LEMON', 'PLUM'];
const SLOT_MAX_BET = 50000;                                    // the most a player may put on one spin or one wheel turn
// the wheel: 30 segments, each with a multiplier (0 = the bet is lost). Its odds pay back about 93 cash for every 100 bet.
const WHEEL_MULTS = [0,2,0,1,0,0,3,0,1,0,2,0,0,5,0,1,0,2,0,0,10,0,1,0,0,0,0,0,0,0];
// what a spin pays, as a multiple of the stake: 0 = the stake is lost, 1 = the stake comes back
function slotPay(r) {
  if (r[0] === r[1] && r[1] === r[2]) return r[0] === 0 ? 60 : 8;
  return (r[0] === r[1] || r[1] === r[2] || r[0] === r[2]) ? 1 : 0;
}
function shiftMsg(p) { return { type: 'shift', on: !!p.shift, job: p.shift ? p.shift.job : -1, paid: p.shift ? p.shift.paid : 0, endsAt: p.shift ? p.shift.start + JOBS[p.shift.job].shiftMin * 60000 : 0, breakUntil: p.shiftBreakUntil || 0 }; }
function endShift(p, text) {
  const paid = p.shift.paid;
  p.shift = null; p.shiftBreakUntil = Date.now() + JOB_BREAK;
  sendTo(p, shiftMsg(p));
  sendTo(p, { type: 'notice', text: text + '. YOU EARNED ' + paid });
}
function sendBounties(w) {
  const list = [...w.bounties.values()].map(b => ({ name: b.name, amount: b.amount }));
  for (const q of players.values()) if (q.world === w && q.joined) {
    const c = w.claims.get(q.pid);
    sendTo(q, { type: 'bounties', list, claim: c && c.until > Date.now() ? c.amount : 0 });
  }
}
// every few seconds: a player on a shift is paid each minute; a shift ends when its time is up or it has paid enough
function jobTick() {
  const now = Date.now();
  for (const p of players.values()) {
    if (!p.joined || !p.shift) continue;
    const w = p.world, s = p.shift, job = JOBS[s.job];
    if (now - s.lastPay >= JOB_EVERY) {
      s.lastPay = now;
      // the work rule: moving around earns half of each minute's pay, building or breaking blocks the other half. Standing still earns nothing.
      const moved = now - (p.movedAt || 0) < 60000, worked = now - (p.workedAt || 0) < 60000;
      const pay = Math.round(job.perMin * ((moved ? 0.5 : 0) + (worked ? 0.5 : 0)));
      if (pay > 0) {
        s.paid += pay;
        w.coins.set(p.pid, (w.coins.get(p.pid) || 0) + pay);
        logTxn(w, { kind: 'job', amount: pay, to: p.pid, toName: p.name });
      } else sendTo(p, { type: 'notice', text: 'NO WORK THIS MINUTE: MOVE AROUND AND BUILD OR BREAK BLOCKS' });
      sendTo(p, walletMsg(w, p));
      sendTo(p, shiftMsg(p));
    }
    if (p.shift && (s.paid >= job.perMin * job.shiftMin || now - s.start >= job.shiftMin * 60000)) endShift(p, 'YOUR SHIFT IS OVER');
  }
}
setInterval(jobTick, 10000);
// playtime: a player who has moved in the last minute gets 10 minutes of playtime for every 10 minutes they play
function rewardTick() {
  const now = Date.now();
  for (const p of players.values()) {
    if (!p.joined || !p.pid || !p.world || now - (p.movedAt || 0) > PLAY_ACTIVE) continue;
    const r = rewardsOf(p.world, p.pid);
    r.play += 10000;
    if (r.play >= PLAY_BLOCK) { r.play -= PLAY_BLOCK; if (r.banked < PLAY_BANK_MAX) r.banked++; }
  }
}
setInterval(rewardTick, 10000);
function rewardsOf(w, pid) {
  let r = w.rewards.get(pid);
  if (!r) { r = { day: '', streak: 0, play: 0, banked: 0, invest: {} }; w.rewards.set(pid, r); }
  r.invest = r.invest || {};
  return r;
}
function dayKey(t) { return new Date(t).toISOString().slice(0, 10); }
function dailyPay(streak) { return DAILY_BASE + DAILY_STEP * (Math.min(Math.max(streak, 1), DAILY_CAP_DAY) - 1); }
// what an investment has earned and not yet been collected
function stakePending(r, k, now) {
  const hours = Math.min(INVEST_MAX_HOURS, (now - r.invest[k]) / 3600000);
  return Math.floor(hours * INVESTMENTS[k].perHour);
}
function rewardState(w, p) {
  const now = Date.now(), r = rewardsOf(w, p.pid);
  const claimed = r.day === dayKey(now);
  const streak = claimed || r.day === dayKey(now - 86400000) ? r.streak : 0;   // a streak survives until a day is missed
  const next = claimed ? streak : streak + 1;                                    // the day the next sign-in would be
  return {
    type: 'rewardstate',
    daily: { claimed, streak, day: ((next - 1) % DAILY_CAP_DAY) + 1, pay: dailyPay(next) },
    play: { banked: r.banked, pay: r.banked * PLAY_REWARD, nextIn: Math.ceil((PLAY_BLOCK - r.play) / 60000), max: PLAY_BANK_MAX },
    stakes: INVESTMENTS.map((it, k) => ({ k, name: it.name, desc: it.desc, cost: it.cost, perHour: it.perHour,
      owned: r.invest[k] !== undefined, pending: r.invest[k] !== undefined ? stakePending(r, k, Date.now()) : 0 })),
  };
}
// the transactions a player is part of, newest first, worded from that player's side
function cashLogFor(w, p) {
  const out = [];
  for (const e of w.log) {
    let dir = null, text = null;
    if (e.kind === 'trade') {
      if (e.from === p.pid) { dir = '-'; text = 'Sent ' + e.amount + ' to ' + e.toName; }
      else if (e.to === p.pid) { dir = '+'; text = e.fromName + ' sent you ' + e.amount; }
    } else if (e.kind === 'give' && e.to === p.pid) { dir = '+'; text = 'The game creator gave you ' + e.amount; }
    else if (e.kind === 'take' && e.from === p.pid) { dir = '-'; text = 'The game creator took ' + e.amount; }
    else if (e.kind === 'buy' && e.from === p.pid) { dir = '-'; text = 'Bought ' + e.what + ' for ' + e.amount; }
    else if (e.kind === 'plot' && e.from === p.pid) { dir = '-'; text = 'Bought a plot of ' + e.what + ' for ' + e.amount; }
    else if (e.kind === 'plotsale' && e.to === p.pid) { dir = '+'; text = 'Sold a plot of ' + e.what + ' for ' + e.amount; }
    else if (e.kind === 'job' && e.to === p.pid) { dir = '+'; text = 'Wages from your shift'; }
    else if (e.kind === 'bountyset' && e.from === p.pid) { dir = '-'; text = 'Put a bounty on ' + e.what; }
    else if (e.kind === 'bountypaid' && e.to === p.pid) { dir = '+'; text = 'Claimed the bounty on ' + e.what; }
    else if (e.kind === 'slots' && e.from === p.pid) {
      if (e.won > e.amount) { dir = '+'; text = 'Won ' + (e.won - e.amount) + ' at the slots'; }
      else if (e.won < e.amount) { dir = '-'; text = 'Lost ' + (e.amount - e.won) + ' at the slots'; }
    }
    else if (e.kind === 'wheel' && e.from === p.pid) {
      if (e.won > e.amount) { dir = '+'; text = 'Won ' + (e.won - e.amount) + ' at the wheel'; }
      else if (e.won < e.amount) { dir = '-'; text = 'Lost ' + (e.amount - e.won) + ' at the wheel'; }
    }
    else if (e.kind === 'daily' && e.to === p.pid) { dir = '+'; text = 'Daily sign-in reward'; }
    else if (e.kind === 'playtime' && e.to === p.pid) { dir = '+'; text = 'Playtime reward'; }
    else if (e.kind === 'invest' && e.from === p.pid) { dir = '-'; text = 'Bought ' + e.what; }
    else if (e.kind === 'stake' && e.to === p.pid) { dir = '+'; text = 'Investment income'; }
    if (dir) out.push({ t: e.t, dir, text, amount: e.amount });
  }
  return out.slice(-40).reverse();
}
// the locks a player sees when they join
function lockList(w, p) {
  const out = [], seen = new Set();
  for (const L of w.locks.values()) {
    if (seen.has(L)) continue;
    seen.add(L);
    out.push({ x: L.lower[0], y: L.lower[1], z: L.lower[2], ok: lockOpenFor(p, L) });
  }
  return out;
}
// the server will not allow a change: the block goes back to how it was, and the player is told why
function fixBlock(p, w, key, msg) {
  const [x, y, z] = key.split(',').map(Number);
  sendTo(p, { type: 'fix', x, y, z, id: w.edits.get(key) || 0, own: w.owners.get(key) === p.pid, msg });
}
function roleForCode(code) {
  const d = codeDigest(code);
  let role = null;
  for (const a of ADMIN_CODES) if (crypto.timingSafeEqual(d, codeDigest(a.code))) role = a.role;
  return role;
}

// each world's state: its block edits ("x,y,z" -> block id, 0 is air, so a broken block is stored as 0),
// its cow (the last position the host sent, for players who join later), and its clock
for (const w of Object.values(WORLDS)) {
  w.passDigest = w.password ? codeDigest(w.password) : null;
  w.edits = new Map();
  w.owners = new Map();    // "x,y,z" -> hashed id of the player who placed the block there (land has no owner)
  w.locks = new Map();     // "x,y,z" of each half of a door with a password -> the lock (both halves share one lock)
  w.coins = new Map();     // hashed player id -> cash (the game creator gives it, players trade it and buy with it)
  w.tools = new Map();     // hashed player id -> hacker tools they own (each one can be used once)
  w.mail = new Map();      // lowercase name -> the messages waiting for that player: [{ from, text, at }]
  w.bounties = new Map();  // target's id -> { amount, name }: cash paid out to whoever smacks them
  w.claims = new Map();
  w.rewards = new Map();   // player's id -> { day, streak, play, banked }: the daily sign-in and the playtime rewards    // claimer's id -> { amount, target, until }: a bounty smacked, to be claimed at the shop
  w.plots = [];            // plots of land: { x0, z0, x1, z1 (inclusive), owner (hashed id), ownerName, name, price }
  w.offers = new Map();    // offers to buy a plot, kept while the server runs: id -> offer
  w.log = [];              // the latest cash transactions in this world
  w.mob = null;
  w.clock = { t: DAY_LEN * 0.3, at: Date.now() };    // the world time is w.clock.t at the moment w.clock.at; it then runs on in real time
  w.saveTimer = null;
  w.loaded = false;                                 // only a world that loaded cleanly is ever saved, so a bad file is never overwritten
  try {
    const data = JSON.parse(fs.readFileSync(w.file, 'utf8'));
    const list = Array.isArray(data) ? data : data.edits;          // older saves were just the list of edits
    for (const [pid, n] of (Array.isArray(data) ? [] : (data.coins || []))) w.coins.set(pid, n);
    for (const [pid, n] of (Array.isArray(data) ? [] : (data.tools || []))) w.tools.set(pid, n);
    if (!Array.isArray(data)) { w.plots = data.plots || []; w.log = data.log || []; for (const [to, list] of (data.mail || [])) w.mail.set(to, list); for (const [k, v] of (data.bounties || [])) w.bounties.set(k, v); for (const [k, v] of (data.claims || [])) w.claims.set(k, v); for (const [k, v] of (data.rewards || [])) w.rewards.set(k, v); }
    for (const [k, v, o] of list) { if (v === 260 || v === 261) continue; w.edits.set(k, v); if (o !== undefined) w.owners.set(k, o); }   // the removed camera and screen blocks
    for (const L of Array.isArray(data) ? [] : (data.locks || [])) {
      const lo = L.lower.split(',').map(Number);
      const lock = { lower: lo, owner: L.owner, salt: L.salt, digest: L.digest, allowed: new Set(L.allowed || []), keys: lockKeys(lo) };
      for (const k of lock.keys) w.locks.set(k, lock);
    }
    w.loaded = true;
    console.log(`${w.name}: loaded ${w.edits.size} block edits from ${w.file}`);
  } catch (e) {
    if (e.code === 'ENOENT') w.loaded = true;       // a new world starts empty
    else console.error(`${w.name}: could not read ${w.file}, it will not be saved over: ${e.message}`);
  }
}

function worldTime(w) { return w.clock.t + (Date.now() - w.clock.at) / 1000; }
function setWorldTime(w, t) { w.clock = { t, at: Date.now() }; }
function saveWorld(w) {
  w.saveTimer = null;
  if (!w.loaded) return;
  const edits = [...w.edits].map(([k, v]) => (w.owners.has(k) ? [k, v, w.owners.get(k)] : [k, v]));
  const locks = [...new Set(w.locks.values())].map(L => ({ lower: L.lower.join(','), owner: L.owner, salt: L.salt, digest: L.digest, allowed: [...L.allowed] }));
  const tmp = w.file + '.tmp';
  try {
    fs.writeFileSync(tmp, JSON.stringify({ edits, locks, coins: [...w.coins], tools: [...w.tools], plots: w.plots, log: w.log, mail: [...w.mail], bounties: [...w.bounties], claims: [...w.claims], rewards: [...w.rewards] }));
    fs.renameSync(tmp, w.file);
  } catch (e) {
    console.error(`${w.name}: could not save the world:`, e.message);
  }
}
function scheduleSave(w) {
  if (!w.saveTimer) w.saveTimer = setTimeout(() => saveWorld(w), 2000);
}
function flushAndExit() {
  for (const w of Object.values(WORLDS)) { if (w.saveTimer) clearTimeout(w.saveTimer); saveWorld(w); }
  process.exit(0);
}
process.on('SIGINT', flushAndExit);
process.on('SIGTERM', flushAndExit);
process.on('SIGHUP', flushAndExit);

// HTTPS: browsers only allow the microphone on secure (https) pages. Give the server a certificate
// with TLS_CERT and TLS_KEY (paths to the PEM files), or put it behind a host that provides https.
const TLS_CERT = process.env.TLS_CERT, TLS_KEY = process.env.TLS_KEY;
const useTls = !!(TLS_CERT && TLS_KEY);
// media the game loads, such as the TV's video: only files inside public/media are served
const MEDIA_TYPES = { '.mp4': 'video/mp4', '.webm': 'video/webm', '.m4a': 'audio/mp4', '.mp3': 'audio/mpeg' };
const requestHandler = (req, res) => {
  const url = req.url.split('?')[0];
  if (url === '/favicon.ico') { res.writeHead(204); return res.end(); }
  if (url.startsWith('/media/')) {
    let rel = '';
    try { rel = decodeURIComponent(url).slice(1); } catch (e) { rel = ''; }
    const type = MEDIA_TYPES[path.extname(rel).toLowerCase()];
    if (!type || !rel.startsWith('media/') || rel.includes('..')) { res.writeHead(404, { 'Content-Type': 'text/plain' }); return res.end('not found'); }
    const file = path.join(__dirname, 'public', rel);
    return fs.stat(file, (err, st) => {
      if (err || !st.isFile()) { res.writeHead(404, { 'Content-Type': 'text/plain' }); return res.end('not found'); }
      const size = st.size, head = { 'Content-Type': type, 'Accept-Ranges': 'bytes', 'Cache-Control': 'max-age=3600', 'Access-Control-Allow-Origin': '*' };   // any game page may show these videos
      // a range request (the video jumps to a moment): only that part of the file is sent
      const r = /^bytes=(\d*)-(\d*)$/.exec(req.headers.range || '');
      if (r && (r[1] !== '' || r[2] !== '')) {
        let start, end;
        if (r[1] === '') { start = Math.max(0, size - Number(r[2])); end = size - 1; }
        else { start = Number(r[1]); end = r[2] !== '' ? Math.min(Number(r[2]), size - 1) : size - 1; }
        if (start > end || start >= size) { res.writeHead(416, { 'Content-Range': 'bytes */' + size }); return res.end(); }
        res.writeHead(206, { ...head, 'Content-Length': end - start + 1, 'Content-Range': `bytes ${start}-${end}/${size}` });
        return fs.createReadStream(file, { start, end }).pipe(res);
      }
      res.writeHead(200, { ...head, 'Content-Length': size });
      fs.createReadStream(file).pipe(res);
    });
  }
  if (url === '/upload') {
    // a shared video: the game sends the file here with a ticket from the server (see handleUpload)
    res.setHeader('Access-Control-Allow-Origin', '*');
    if (req.method === 'OPTIONS') { res.writeHead(204, { 'Access-Control-Allow-Methods': 'POST, OPTIONS', 'Access-Control-Allow-Headers': 'Content-Type' }); return res.end(); }
    if (req.method !== 'POST') { res.writeHead(405, { 'Content-Type': 'text/plain' }); return res.end('use POST'); }
    return handleUpload(req, res, new URL(req.url, 'http://localhost').searchParams.get('token') || '');
  }
  if (url === '/' || url === '/index.html') {
    fs.readFile(PAGE, (err, data) => {
      if (err) { res.writeHead(500, { 'Content-Type': 'text/plain' }); return res.end('game page missing'); }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
      res.end(data);
    });
    return;
  }
  res.writeHead(404, { 'Content-Type': 'text/plain' });
  res.end('not found');
};
const server = useTls
  ? https.createServer({ cert: fs.readFileSync(TLS_CERT), key: fs.readFileSync(TLS_KEY) }, requestHandler)
  : http.createServer(requestHandler);

const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 16 * 1024 });
let nextId = 1;
const players = new Map();   // id -> { ws, world, name, color, x, y, z, yaw, pitch, tokens, lastTick, joined, sleeping, hidden, role }

function sendTo(p, msg) { if (p.ws.readyState === 1) p.ws.send(JSON.stringify(msg)); }
// the TVs of a world: each TV shows a video, and they can all be on at once. "t" is the video's position in seconds at server time "at", unless it is paused
const TV_ACTIONS = ['start', 'pause', 'play', 'off', 'source', 'volume'];
const TV_DEFAULT_SRC = 'media/tv.mp4';   // the video a TV shows when nothing else was chosen (next to the game page)
const TV_VOLUME_STEPS = 5;               // the volume goes from 0 to 5, a step at a time
const UPLOAD_MAX = 150 * 1024 * 1024;    // the largest video a player can share with the world
const UPLOAD_KEEP = 8;                   // a world keeps this many shared videos; the oldest are removed
const UPLOAD_TYPES = { 'video/mp4': '.mp4', 'video/webm': '.webm' };
const uploadTokens = new Map();          // a ticket for one upload: token -> { w (the world), until }
function tvPos(t, now) { return t.paused ? t.t : t.t + (now - t.at) / 1000; }
// the videos a TV can show in a world: the default, then the ones shared there
function tvSources(w) { return [TV_DEFAULT_SRC, ...(w.uploads || [])]; }
// every TV that is on in the world: where it is, its video, its volume, and where that video has got to
function tvList(w, now = Date.now()) {
  const out = [];
  if (!w.tvs) return out;
  for (const t of w.tvs.values()) if (t.on) out.push({ x: t.x, y: t.y, z: t.z, src: t.src, vol: t.vol, paused: t.paused, pos: Math.max(0, tvPos(t, now)) });
  return out;
}
// a video a player shares: it is saved on the server, and listed for the world (the oldest are removed)
function handleUpload(req, res, token) {
  const json = (code, body) => { res.writeHead(code, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' }); res.end(JSON.stringify(body)); };
  const ticket = uploadTokens.get(token);
  uploadTokens.delete(token);                       // a ticket is good for one upload
  if (!ticket || ticket.until < Date.now()) return json(403, { error: 'the upload was not allowed, try again' });
  const ext = UPLOAD_TYPES[String(req.headers['content-type'] || '').split(';')[0].trim()];
  if (!ext) return json(415, { error: 'use an MP4 or WebM video' });
  if (Number(req.headers['content-length'] || 0) > UPLOAD_MAX) return json(413, { error: 'that video is too big' });
  const name = crypto.randomBytes(8).toString('hex') + ext;
  const dir = path.join(__dirname, 'public', 'media', 'uploads');
  fs.mkdirSync(dir, { recursive: true });
  const file = path.join(dir, name);
  const out = fs.createWriteStream(file);
  let size = 0, failed = false;
  const fail = (code, msg) => {
    if (failed) return;
    failed = true;
    req.unpipe(out); req.resume();                  // the rest of the upload is thrown away
    out.destroy(); fs.unlink(file, () => {});
    json(code, { error: msg });
  };
  req.on('data', (chunk) => { size += chunk.length; if (size > UPLOAD_MAX) fail(413, 'that video is too big'); });
  req.pipe(out);
  out.on('error', () => fail(500, 'the video could not be saved'));
  out.on('finish', () => {
    if (failed) return;
    const p = '/media/uploads/' + name;
    ticket.w.uploads = [...(ticket.w.uploads || []), p];
    while (ticket.w.uploads.length > UPLOAD_KEEP) {
      const old = ticket.w.uploads.shift();
      // a TV still showing the removed video is switched off, so nobody is left with a missing file
      if (ticket.w.tvs) for (const t of ticket.w.tvs.values()) if (t.src === old) { t.src = TV_DEFAULT_SRC; t.on = false; }
      fs.unlink(path.join(__dirname, 'public', old), () => {});
    }
    json(200, { path: p });
  });
}
// a message to everyone in one world (optionally not to one player)
function broadcast(w, msg, exceptId) {
  const s = JSON.stringify(msg);
  for (const [id, p] of players) if (p.world === w && id !== exceptId && p.ws.readyState === 1) p.ws.send(s);
}
function lowestJoinedId(w) { let low = Infinity; for (const [oid, o] of players) if (o.world === w && o.joined && oid < low) low = oid; return low; }
function cleanName(s) {
  return String(s || '').replace(/[^\w \-.]/g, '').trim().slice(0, 16) || 'Builder';
}
function isNum(v) { return typeof v === 'number' && Number.isFinite(v); }
function isInt(v) { return Number.isInteger(v); }
// the night passes only when every joined player in the world is in a bed at the same time
function checkMorning(w) {
  const joined = [...players.values()].filter(q => q.world === w && q.joined);
  if (joined.length && joined.every(q => q.sleeping)) {
    for (const q of joined) q.sleeping = false;
    // the night passes: the world's clock jumps to the next morning
    const now = worldTime(w), base = Math.floor(now / DAY_LEN) * DAY_LEN;
    let t = base + DAY_LEN * 0.27; if (t <= now) t += DAY_LEN;
    setWorldTime(w, t);
    broadcast(w, { type: 'morning', time: t });
  }
}
// simple rate limit: each player has a bucket of 60 messages, refilled at 40 per second
function allow(p) {
  const now = Date.now();
  p.tokens = Math.min(60, p.tokens + (now - p.lastTick) / 1000 * 40);
  p.lastTick = now;
  if (p.tokens < 1) return false;
  p.tokens -= 1;
  return true;
}
function clientAddress(ws) { return (ws._socket && ws._socket.remoteAddress) || 'unknown'; }
function deny(p, msg) { sendTo(p, { type: 'denied', msg }); try { p.ws.close(); } catch (e) {} }

// joining: the player picks a world; OUR WORLD needs its password, and wrong guesses are slowed down per address
function hello(p, id, m) {
  const w = typeof m.world === 'string' && Object.hasOwn(WORLDS, m.world) ? WORLDS[m.world] : null;
  if (!w) return deny(p, 'Choose a world to join.');
  if (w.passDigest) {
    const ip = clientAddress(p.ws), now = Date.now();
    const t = pwTries.get(ip) || { n: 0, until: 0 };
    if (t.until > now) return deny(p, 'Too many tries. Wait a minute and try again.');
    const given = typeof m.password === 'string' ? m.password.slice(0, 32) : '';
    if (!crypto.timingSafeEqual(codeDigest(given), w.passDigest)) {
      t.n += 1;
      if (t.n >= 5) { t.until = now + 60000; t.n = 0; }
      pwTries.set(ip, t);
      return deny(p, 'That password is not right.');
    }
    pwTries.delete(ip);
  }
  p.world = w; p.joined = true; p.pid = pidFor(m.pid);
  p.name = cleanName(m.name);
  const list = [];
  for (const [oid, o] of players) if (oid !== id && o.joined && o.world === w) list.push({ id: oid, name: o.name, color: o.color, x: o.x, y: o.y, z: o.z, yaw: o.yaw, sleeping: o.sleeping, hidden: o.hidden, role: o.role });
  const all = [];
  // each block also says who it belongs to for this player: 1 = yours, 0 = another player's, null = nobody's (land or older saves)
  for (const [k, v] of w.edits) { const [x, y, z] = k.split(',').map(Number); const o = w.owners.get(k); all.push([x, y, z, v, o === undefined ? null : (o === p.pid ? 1 : 0)]); }
  sendTo(p, { type: 'welcome', id, world: w.key, worldName: w.name, edits: all, players: list, time: worldTime(w), mob: w.mob, tvs: tvList(w), sources: tvSources(w), locks: lockList(w, p), coins: w.coins.get(p.pid) || 0, tools: w.tools.get(p.pid) || 0, plots: plotsMsg(w, p).list });
  // mail that was waiting for this player's name is handed over once, after they have joined, and removed from the mailbox
  const waiting = w.mail.get((p.name || '').toLowerCase());
  if (waiting) { w.mail.delete((p.name || '').toLowerCase()); scheduleSave(w); sendTo(p, { type: 'mail', list: waiting }); }
  sendBounties(w);
  broadcast(w, { type: 'join', id, name: p.name, color: p.color, x: p.x, y: p.y, z: p.z, yaw: p.yaw, role: p.role }, id);
  broadcast(w, { type: 'system', text: p.name + ' joined' }, id);
}

wss.on('connection', (ws) => {
  if (players.size >= MAX_PLAYERS) { ws.close(1013, 'server full'); return; }
  const id = nextId++;
  const p = { ws, world: null, name: 'Builder' + id, color: COLORS[id % COLORS.length], x: 8.5, y: 40, z: 8.5, yaw: 0, pitch: 0,
              tokens: 60, lastTick: Date.now(), joined: false, sleeping: false, hidden: false, role: null, pid: null, bypass: false };
  players.set(id, p);

  ws.on('message', (raw) => {
    if (!allow(p)) return;
    let m;
    try { m = JSON.parse(raw); } catch (e) { return; }
    if (!m || typeof m !== 'object') return;

    if (m.type === 'hello' && !p.joined) return hello(p, id, m);
    if (!p.joined) return;
    const w = p.world;

    if (m.type === 'chat') {
      // chat goes to everyone in the world, including the sender; text is cleaned and limited to 120 characters
      const text = typeof m.text === 'string' ? m.text.replace(/[\u0000-\u001f]/g, '').trim().slice(0, 120) : '';
      if (text) broadcast(w, { type: 'chat', name: p.name, text });
      return;
    }

    if (m.type === 'sleep') {
      p.sleeping = m.on === true;
      broadcast(w, { type: 'sleep', id, on: p.sleeping }, id);
      checkMorning(w);
      return;
    }

    if (m.type === 'auth') {
      // an admin code: the answer comes back to this player only; wrong guesses are slowed down per address
      const ip = clientAddress(ws);
      const now = Date.now();
      const t = authTries.get(ip) || { n: 0, until: 0 };
      if (t.until > now) { sendTo(p, { type: 'auth', ok: false, msg: 'Too many tries. Wait a minute and try again.' }); return; }
      const code = typeof m.code === 'string' ? m.code.trim().slice(0, 16) : '';
      const role = roleForCode(code);
      if (!role) {
        t.n += 1;
        if (t.n >= 5) { t.until = now + 60000; t.n = 0; }
        authTries.set(ip, t);
        sendTo(p, { type: 'auth', ok: false, msg: 'That code is not right.' });
        return;
      }
      authTries.delete(ip);
      p.role = role;
      sendTo(p, { type: 'auth', ok: true, role });
      broadcast(w, { type: 'role', id, role }, id);
      return;
    }

    if (m.type === 'admin') {
      // player commands: only a game creator may use them, and only on another player in the same world
      if (p.role !== 'creator') return;
      if (m.action === 'give') {
        const g = players.get(m.target), amt = Number.isInteger(m.amount) ? Math.max(-1000000, Math.min(1000000, m.amount)) : 0;
        if (!g || !g.joined || g.world !== w || !g.pid || !amt) return;
        const before = w.coins.get(g.pid) || 0;
        const now = Math.max(0, before + amt);
        w.coins.set(g.pid, now); scheduleSave(w);
        const applied = now - before;
        if (applied > 0) logTxn(w, { kind: 'give', amount: applied, to: g.pid, toName: g.name });
        else if (applied < 0) logTxn(w, { kind: 'take', amount: -applied, from: g.pid, fromName: g.name });
        sendTo(g, walletMsg(w, g));
        sendTo(g, { type: 'notice', text: amt > 0 ? 'THE GAME CREATOR GAVE YOU ' + amt + ' CASH' : 'THE GAME CREATOR TOOK ' + (-amt) + ' CASH' });
        sendTo(p, { type: 'notice', text: (amt > 0 ? 'GAVE ' + amt + ' CASH TO ' : 'TOOK ' + (-amt) + ' CASH FROM ') + g.name.toUpperCase() });
        return;
      }
      const q = players.get(m.target);
      if (!q || !q.joined || q === p || q.world !== w) return;
      if (m.action === 'tp') sendTo(p, { type: 'teleport', x: q.x, y: q.y, z: q.z, exact: true });        // you go to their exact spot
      else if (m.action === 'bring') sendTo(q, { type: 'teleport', x: p.x, y: p.y, z: p.z, exact: false }); // they come beside you
      else if (m.action === 'msg') {
        // a private message: it pops up on their screen only
        const text = typeof m.text === 'string' ? m.text.replace(/[\u0000-\u001f]/g, '').trim().slice(0, 200) : '';
        if (text) sendTo(q, { type: 'pm', from: p.name, role: p.role, text });
        return;
      }
      else if (m.action === 'jump') sendTo(q, { type: 'jump' });
      return;
    }

    if (m.type === 'uploadTicket') {
      // a player who joined may share a video: this gives a ticket for one upload, and at most one ticket every 20 seconds
      const now = Date.now();
      if (p.ticketAt && now - p.ticketAt < 5000) return sendTo(p, { type: 'uploadTicket', error: 'wait a few seconds before sharing another video' });
      p.ticketAt = now;
      const token = crypto.randomBytes(16).toString('hex');
      uploadTokens.set(token, { w, until: now + 120000 });
      return sendTo(p, { type: 'uploadTicket', token });
    }
    if (m.type === 'tv') {
      // the TVs are shared by the whole world: whoever starts, pauses, plays, changes or ends a TV sets it for everyone, if they are close to it
      if (!isInt(m.x) || !isInt(m.y) || !isInt(m.z) || !TV_ACTIONS.includes(m.action)) return;
      const dx = m.x + 0.5 - p.x, dy = m.y + 0.5 - p.y, dz = m.z + 0.5 - p.z;
      if (dx * dx + dy * dy + dz * dz > REACH * REACH) return;
      if (!w.tvs) w.tvs = new Map();
      const key = m.x + ',' + m.y + ',' + m.z, now = Date.now(), dir = m.dir === -1 ? -1 : 1;
      let tv = w.tvs.get(key);
      if (m.action === 'start') {
        if (!tv) { tv = { x: m.x, y: m.y, z: m.z, src: TV_DEFAULT_SRC, vol: TV_VOLUME_STEPS }; w.tvs.set(key, tv); }
        if (typeof m.src === 'string' && tvSources(w).includes(m.src)) tv.src = m.src;   // a video shared in this world, or the default
        Object.assign(tv, { on: true, paused: false, t: 0, at: now });
      } else {
        if (!tv) return;                                          // nothing is known about that TV
        if (m.action === 'off') tv.on = false;
        else if (m.action === 'pause') { if (!tv.on || tv.paused) return; tv.t = tvPos(tv, now); tv.at = now; tv.paused = true; }
        else if (m.action === 'play') { if (!tv.on || !tv.paused) return; tv.paused = false; tv.at = now; }
        else if (m.action === 'source') {
          const list = tvSources(w), i = list.indexOf(tv.src);
          tv.src = list[((i < 0 ? 0 : i) + dir + list.length) % list.length];
          if (tv.on) Object.assign(tv, { paused: false, t: 0, at: now });
        }
        else if (m.action === 'volume') tv.vol = Math.max(0, Math.min(TV_VOLUME_STEPS, tv.vol + dir));
      }
      broadcast(w, { type: 'tv', list: tvList(w, now), sources: tvSources(w) });   // everyone in the world, the player who sent it too
      return;
    }
    if (m.type === 'mob') {
      // the cow: only the lowest-numbered connected player in the world moves it, and everyone else is sent its position
      if (id !== lowestJoinedId(w)) return;
      if (!isNum(m.x) || !isNum(m.y) || !isNum(m.z) || !isNum(m.yaw)) return;
      w.mob = { x: m.x, y: m.y, z: m.z, yaw: m.yaw };
      broadcast(w, { type: 'mob', x: m.x, y: m.y, z: m.z, yaw: m.yaw }, id);
      return;
    }

    if (m.type === 'vanish') {
      // invisibility: only admins may use it. While hidden, this player's position is not relayed to anyone
      if (m.on === true && !p.role) return;
      p.hidden = m.on === true;
      broadcast(w, { type: 'vanish', id, on: p.hidden, x: p.x, y: p.y, z: p.z, yaw: p.yaw, pitch: p.pitch }, id);
      return;
    }

    if (m.type === 'rtc') {
      // voice chat: passes connection set-up (offers, answers, ice candidates) between two players in the same world who are close together
      const q = players.get(m.to);
      if (!q || !q.joined || q === p || q.world !== w || q.hidden || p.hidden || q.ws.readyState !== 1) return;
      if (!m.data || typeof m.data !== 'object' || !(m.data.sdp || m.data.ice)) return;
      const dx = q.x - p.x, dy = q.y - p.y, dz = q.z - p.z;
      if (dx*dx + dy*dy + dz*dz > VOICE_RELAY_RANGE * VOICE_RELAY_RANGE) return;
      sendTo(q, { type: 'rtc', from: id, data: m.data });
      return;
    }
    if (m.type === 'move') {
      if (!isNum(m.x) || !isNum(m.y) || !isNum(m.z) || !isNum(m.yaw) || !isNum(m.pitch)) return;
      p.x = Math.max(-1e6, Math.min(1e6, m.x));
      p.y = Math.max(-10, Math.min(200, m.y));
      p.z = Math.max(-1e6, Math.min(1e6, m.z));
      p.yaw = m.yaw; p.pitch = m.pitch; p.movedAt = Date.now(); p.sit = !!m.sit;
      if (!p.hidden) broadcast(w, { type: 'move', id, x: p.x, y: p.y, z: p.z, yaw: p.yaw, pitch: p.pitch, sit: p.sit }, id);
      return;
    }

    if (m.type === 'doorinfo') {
      // the Q key or the DOOR button: is this door placed by a player, locked, and may this player open it
      if (!isInt(m.x) || !isInt(m.y) || !isInt(m.z)) return;
      const lo = doorPair(w, m.x, m.y, m.z), lk = lo ? lo.join(',') : null;
      const owner = lk ? w.owners.get(lk) : undefined, lock = lk ? w.locks.get(lk) : null;
      return sendTo(p, { type: 'doorinfo', x: m.x, y: m.y, z: m.z, placed: owner !== undefined,
        mine: owner !== undefined && owner === p.pid, locked: !!lock, ok: !!lock && lockOpenFor(p, lock) });
    }
    if (m.type === 'doorlock') {
      // the player who placed a door sets, changes or removes its password (a new password means everyone must type it again)
      const fail = msg => sendTo(p, { type: 'doorresult', ok: false, msg });
      if (!isInt(m.x) || !isInt(m.y) || !isInt(m.z)) return;
      const lo = doorPair(w, m.x, m.y, m.z);
      if (!lo) return fail('ONLY A DOOR A PLAYER PLACED CAN HAVE A PASSWORD');
      const [a, b] = lockKeys(lo);
      if (w.owners.get(a) !== p.pid) return fail('ONLY THE PLAYER WHO PLACED THIS DOOR CAN SET ITS PASSWORD');
      const dx = lo[0] + 0.5 - p.x, dy = lo[1] + 1 - p.y, dz = lo[2] + 0.5 - p.z;
      if (dx * dx + dy * dy + dz * dz > REACH * REACH) return fail('STAND CLOSER TO THE DOOR');
      if (m.action === 'clear') {
        if (!w.locks.has(a)) return fail('THIS DOOR HAS NO PASSWORD');
        dropLock(w, a);
        scheduleSave(w);
        return sendTo(p, { type: 'doorresult', ok: true, msg: 'PASSWORD REMOVED' });
      }
      if (m.action !== 'set') return;
      const pass = cleanPass(m.pass);
      if (!pass) return fail('TYPE A PASSWORD FIRST');
      const salt = crypto.randomBytes(12).toString('hex');
      const lock = { lower: lo, owner: p.pid, salt, digest: passDigest(salt, pass), allowed: new Set(), keys: [a, b] };
      w.locks.set(a, lock); w.locks.set(b, lock);
      scheduleSave(w);
      announceLock(w, lo, lock);
      return sendTo(p, { type: 'doorresult', ok: true, msg: 'PASSWORD SET. ONLY PLAYERS WHO TYPE IT CAN OPEN THIS DOOR' });
    }
    if (m.type === 'unlock') {
      // someone types a door's password: once it is right, that player may open the door (wrong guesses are slowed down per address)
      const fail = msg => sendTo(p, { type: 'doorresult', ok: false, msg });
      if (!isInt(m.x) || !isInt(m.y) || !isInt(m.z)) return;
      const lo = doorPair(w, m.x, m.y, m.z), lock = lo ? w.locks.get(lo.join(',')) : null;
      if (!lock) return fail('THAT DOOR HAS NO PASSWORD');
      const dx = lo[0] + 0.5 - p.x, dy = lo[1] + 1 - p.y, dz = lo[2] + 0.5 - p.z;
      if (dx * dx + dy * dy + dz * dz > REACH * REACH) return fail('STAND CLOSER TO THE DOOR');
      if (lockOpenFor(p, lock)) return sendTo(p, { type: 'doorresult', ok: true, msg: 'YOU CAN OPEN THIS DOOR' });
      const ip = clientAddress(ws), now = Date.now();
      const t = doorTries.get(ip) || { n: 0, until: 0 };
      if (t.until > now) return fail('TOO MANY TRIES. WAIT A MINUTE AND TRY AGAIN');
      const given = passDigest(lock.salt, cleanPass(m.pass));
      if (!crypto.timingSafeEqual(Buffer.from(given), Buffer.from(lock.digest))) {
        t.n += 1;
        if (t.n >= 5) { t.until = now + 60000; t.n = 0; }
        doorTries.set(ip, t);
        return fail('THAT PASSWORD IS NOT RIGHT');
      }
      doorTries.delete(ip);
      lock.allowed.add(p.pid);
      scheduleSave(w);
      sendTo(p, lockMsg(w, p, lo, lock));
      return sendTo(p, { type: 'doorresult', ok: true, msg: 'THE DOOR IS UNLOCKED FOR YOU' });
    }
    if (m.type === 'bypass') {
      // the game creator's BREAK ANY BLOCK switch (only the creator's own connection can turn it on)
      if (p.role !== 'creator') return;
      p.bypass = m.on === true;
      return sendTo(p, { type: 'bypass', on: p.bypass });
    }
    if (m.type === 'buy') {
      // the shop: a player buys an item with their cash (the item is added to the player's tools)
      const item = SHOP_PRICES[m.item];
      if (!item) return;
      const cash = w.coins.get(p.pid) || 0;
      if (cash < item.price) return sendTo(p, { type: 'notice', text: 'NOT ENOUGH CASH. YOU NEED ' + item.price });
      w.coins.set(p.pid, cash - item.price);
      w.tools.set(p.pid, (w.tools.get(p.pid) || 0) + 1);
      logTxn(w, { kind: 'buy', amount: item.price, from: p.pid, fromName: p.name, what: item.name });
      scheduleSave(w);
      sendTo(p, walletMsg(w, p));
      return sendTo(p, { type: 'notice', text: 'BOUGHT: ' + item.name.toUpperCase() });
    }
    if (m.type === 'pay') {
      // a player sends some of their cash to another player in the same world
      const fail = text => sendTo(p, { type: 'notice', text });
      const q = players.get(m.target);
      const amt = Number.isInteger(m.amount) ? m.amount : 0;
      if (!q || !q.joined || q === p || q.world !== w || !q.pid) return fail('CHOOSE A PLAYER TO SEND CASH TO');
      if (amt < 1 || amt > 1000000) return fail('TYPE AN AMOUNT OF CASH TO SEND');
      const mine = w.coins.get(p.pid) || 0;
      if (mine < amt) return fail('YOU DO NOT HAVE THAT MUCH CASH');
      w.coins.set(p.pid, mine - amt);
      w.coins.set(q.pid, (w.coins.get(q.pid) || 0) + amt);
      logTxn(w, { kind: 'trade', amount: amt, from: p.pid, fromName: p.name, to: q.pid, toName: q.name });
      scheduleSave(w);
      sendTo(p, walletMsg(w, p));
      sendTo(p, { type: 'notice', text: 'SENT ' + amt + ' CASH TO ' + q.name.toUpperCase() });
      sendTo(q, walletMsg(w, q));
      sendTo(q, { type: 'notice', text: p.name.toUpperCase() + ' SENT YOU ' + amt + ' CASH' });
      return;
    }
    if (m.type === 'hack') {
      // the hacker tool: a locked door is decoded and opens for everyone for HACK_MS, then locks again. The tool is used up.
      const fail = msg => sendTo(p, { type: 'doorresult', ok: false, msg });
      if (!isInt(m.x) || !isInt(m.y) || !isInt(m.z)) return;
      const lo = doorPair(w, m.x, m.y, m.z), lk = lo ? lo.join(',') : null;
      const lock = lk ? w.locks.get(lk) : null;
      if (!lock) return fail('THE HACKER TOOL NEEDS A DOOR WITH A PASSWORD');
      const dx = lo[0] + 0.5 - p.x, dy = lo[1] + 1 - p.y, dz = lo[2] + 0.5 - p.z;
      if (dx * dx + dy * dy + dz * dz > REACH * REACH) return fail('STAND CLOSER TO THE DOOR');
      if ((w.tools.get(p.pid) || 0) < 1) return fail('YOU HAVE NO HACKER TOOL. BUY ONE IN THE SHOP');
      if (Date.now() < (lock.openUntil || 0)) return fail('THAT DOOR IS ALREADY DECODED');
      const left = w.tools.get(p.pid) - 1;
      if (left > 0) w.tools.set(p.pid, left); else w.tools.delete(p.pid);
      lock.openUntil = Date.now() + HACK_MS;
      lock.decodedBy = p.pid;
      scheduleSave(w);
      announceLock(w, lo, lock);
      setTimeout(() => shutDecodedDoor(w, lo, lock), HACK_MS + 50);   // shuts and locks again when the time is up
      sendTo(p, walletMsg(w, p));
      return sendTo(p, { type: 'doorresult', ok: true, msg: 'DOOR DECODED: OPEN FOR ' + Math.round(HACK_MS / 1000) + ' SECONDS' });
    }
    if (m.type === 'job') {
      // the shop's job: a shift pays a little each minute, for the time it lasts
      const now = Date.now(), fail = text => sendTo(p, { type: 'notice', text });
      if (!p.pid) return fail('YOU CANNOT WORK HERE YET');
      if (m.action === 'start') {
        const job = JOBS[m.job];
        if (!Number.isInteger(m.job) || !job) return fail('CHOOSE A JOB');
        if (p.shift) return fail('YOU ARE ALREADY ON A SHIFT');
        if (p.shiftBreakUntil > now) return fail('ON A BREAK: ' + Math.ceil((p.shiftBreakUntil - now) / 60000) + ' MINUTES LEFT');
        p.shift = { start: now, lastPay: now, paid: 0, job: m.job };
        sendTo(p, shiftMsg(p));
        return fail('SHIFT STARTED AS ' + job.name.toUpperCase() + ': ' + job.perMin + ' CASH A MINUTE');
      }
      if (m.action === 'stop') {
        if (!p.shift) return fail('YOU ARE NOT ON A SHIFT');
        return endShift(p, 'YOU LEFT YOUR SHIFT');
      }
      return;
    }

    if (m.type === 'reward') {
      // the daily sign-in and the playtime rewards (the state is sent back after every change)
      const fail = text => sendTo(p, { type: 'notice', text }), now = Date.now();
      if (!p.pid) return fail('YOU CANNOT CLAIM YET');
      const r = rewardsOf(w, p.pid);
      if (m.action === 'get') return sendTo(p, rewardState(w, p));
      if (m.action === 'daily') {
        if (r.day === dayKey(now)) return fail('YOU HAVE ALREADY SIGNED IN TODAY');
        r.streak = r.day === dayKey(now - 86400000) ? r.streak + 1 : 1;
        r.day = dayKey(now);
        const pay = dailyPay(r.streak);
        w.coins.set(p.pid, (w.coins.get(p.pid) || 0) + pay);
        logTxn(w, { kind: 'daily', amount: pay, to: p.pid, toName: p.name });
        sendTo(p, walletMsg(w, p));
        sendTo(p, { type: 'notice', text: 'DAILY REWARD: ' + pay + ' CASH, DAY ' + r.streak + ' IN A ROW' });
        scheduleSave(w);
        return sendTo(p, rewardState(w, p));
      }
      if (m.action === 'play') {
        if (r.banked < 1) return fail('NO PLAYTIME REWARD YET');
        const pay = r.banked * PLAY_REWARD;
        r.banked = 0;
        w.coins.set(p.pid, (w.coins.get(p.pid) || 0) + pay);
        logTxn(w, { kind: 'playtime', amount: pay, to: p.pid, toName: p.name });
        sendTo(p, walletMsg(w, p));
        sendTo(p, { type: 'notice', text: 'PLAYTIME REWARD: ' + pay + ' CASH' });
        scheduleSave(w);
        return sendTo(p, rewardState(w, p));
      }
      if (m.action === 'invest') {
        const it = INVESTMENTS[m.k];
        if (!Number.isInteger(m.k) || !it) return fail('NOT FOR SALE');
        if (r.invest[m.k] !== undefined) return fail('YOU ALREADY OWN THIS');
        const mine = w.coins.get(p.pid) || 0;
        if (mine < it.cost) return fail('YOU DO NOT HAVE THAT MUCH CASH');
        w.coins.set(p.pid, mine - it.cost);
        r.invest[m.k] = now;
        logTxn(w, { kind: 'invest', amount: it.cost, from: p.pid, fromName: p.name, what: it.name });
        sendTo(p, walletMsg(w, p));
        sendTo(p, { type: 'notice', text: 'BOUGHT: ' + it.name.toUpperCase() + '. IT PAYS WHILE YOU ARE AWAY' });
        scheduleSave(w);
        return sendTo(p, rewardState(w, p));
      }
      if (m.action === 'collect') {
        let pay = 0;
        INVESTMENTS.forEach((it, k) => { if (r.invest[k] !== undefined) { pay += stakePending(r, k, now); r.invest[k] = now; } });
        if (pay < 1) return fail('NOTHING TO COLLECT YET');
        w.coins.set(p.pid, (w.coins.get(p.pid) || 0) + pay);
        logTxn(w, { kind: 'stake', amount: pay, to: p.pid, toName: p.name });
        sendTo(p, walletMsg(w, p));
        sendTo(p, { type: 'notice', text: 'INVESTMENT INCOME: ' + pay + ' CASH' });
        scheduleSave(w);
        return sendTo(p, rewardState(w, p));
      }
      return;
    }

    if (m.type === 'bounty') {
      // a bounty: cash is put on another player, and whoever smacks them takes it (to claim at the shop)
      const fail = text => sendTo(p, { type: 'notice', text });
      if (m.action !== 'set') return;
      const q = players.get(m.target);
      const amt = Number.isInteger(m.amount) ? m.amount : 0;
      if (!q || !q.joined || q === p || q.world !== w || !q.pid || !p.pid) return fail('CHOOSE A PLAYER TO PUT A BOUNTY ON');
      if (amt < 50 || amt > 100000) return fail('A BOUNTY IS BETWEEN 50 AND 100000 CASH');
      const mine = w.coins.get(p.pid) || 0;
      if (mine < amt) return fail('YOU DO NOT HAVE THAT MUCH CASH');
      w.coins.set(p.pid, mine - amt);
      const b = w.bounties.get(q.pid) || { amount: 0, name: q.name };
      b.amount += amt; b.name = q.name;
      w.bounties.set(q.pid, b);
      logTxn(w, { kind: 'bountyset', amount: amt, from: p.pid, fromName: p.name, what: q.name });
      sendTo(p, walletMsg(w, p));
      broadcast(w, { type: 'system', text: p.name + ' put a bounty of ' + amt + ' on ' + q.name });
      sendBounties(w);
      return fail('BOUNTY PUT ON ' + q.name.toUpperCase());
    }

    if (m.type === 'smack') {
      // smacking a player who has a bounty on them: they stand still for a while, and the smack is the claim (taken to the shop)
      if (!p.pid) return;
      const q = players.get(m.target);
      if (!q || !q.joined || q === p || q.world !== w) return;
      const dx = q.x - p.x, dy = q.y - p.y, dz = q.z - p.z;
      if (dx * dx + dy * dy + dz * dz > 4.5 * 4.5) return sendTo(p, { type: 'notice', text: 'GET CLOSER TO SMACK THEM' });
      const b = w.bounties.get(q.pid);
      if (!b) return sendTo(p, { type: 'notice', text: 'THERE IS NO BOUNTY ON THEM' });
      w.bounties.delete(q.pid);
      w.claims.set(p.pid, { amount: b.amount, target: q.name, until: Date.now() + CLAIM_MS });
      scheduleSave(w);
      sendTo(q, { type: 'freeze', seconds: SMACK_FREEZE });
      sendTo(p, { type: 'notice', text: 'YOU SMACKED ' + q.name.toUpperCase() + '. GO TO THE SHOP TO CLAIM ' + b.amount });
      broadcast(w, { type: 'system', text: p.name + ' smacked ' + q.name + ' for a bounty of ' + b.amount });
      sendBounties(w);
      return;
    }

    if (m.type === 'claim') {
      // at the shop: the bounty from a smack is paid out to the player who made it
      const c = w.claims.get(p.pid), now = Date.now();
      if (!c || c.until < now) { w.claims.delete(p.pid); return sendTo(p, { type: 'notice', text: 'NO BOUNTY TO CLAIM' }); }
      w.claims.delete(p.pid);
      w.coins.set(p.pid, (w.coins.get(p.pid) || 0) + c.amount);
      logTxn(w, { kind: 'bountypaid', amount: c.amount, to: p.pid, toName: p.name, what: c.target });
      sendTo(p, walletMsg(w, p));
      sendBounties(w);
      return sendTo(p, { type: 'notice', text: 'BOUNTY CLAIMED: ' + c.amount + ' CASH' });
    }

    if (m.type === 'wheel') {
      // the wheel: the bet is taken, the wheel stops on a random segment here, and that segment's multiplier pays out
      const fail = text => sendTo(p, { type: 'notice', text }), now = Date.now();
      const bet = Number.isInteger(m.bet) ? m.bet : 0;
      if (!p.pid) return fail('YOU CANNOT PLAY YET');
      if (bet < 1 || bet > SLOT_MAX_BET) return fail('BET BETWEEN 1 AND ' + SLOT_MAX_BET);
      if (p.spinAt && now - p.spinAt < 1500) return;      // one turn at a time
      const mine = w.coins.get(p.pid) || 0;
      if (mine < bet) return fail('YOU DO NOT HAVE THAT MUCH CASH');
      p.spinAt = now;
      const index = crypto.randomInt(WHEEL_MULTS.length);
      const mult = WHEEL_MULTS[index], win = bet * mult;
      w.coins.set(p.pid, mine - bet + win);
      logTxn(w, { kind: 'wheel', amount: bet, won: win, from: p.pid, fromName: p.name });
      sendTo(p, { type: 'wheelresult', index, mult, bet, win });
      sendTo(p, walletMsg(w, p));
      return;
    }
    if (m.type === 'slots') {
      // the slot machine: the stake is taken, the reels are turned here, and the payout is worked out here too
      const fail = text => sendTo(p, { type: 'notice', text }), now = Date.now();
      const bet = Number.isInteger(m.bet) ? m.bet : 0;
      if (!p.pid) return fail('YOU CANNOT PLAY YET');
      if (bet < 1 || bet > SLOT_MAX_BET) return fail('BET BETWEEN 1 AND ' + SLOT_MAX_BET);
      if (p.spinAt && now - p.spinAt < 1500) return;      // one spin at a time
      const mine = w.coins.get(p.pid) || 0;
      if (mine < bet) return fail('YOU DO NOT HAVE THAT MUCH CASH');
      p.spinAt = now;
      const reels = [crypto.randomInt(6), crypto.randomInt(6), crypto.randomInt(6)];
      if (slotPay(reels) === 0 && crypto.randomInt(100) < 46) reels[2] = reels[0];   // help: 46% of the losing spins come up a pair instead, so about 70% of spins win something
      const win = bet * slotPay(reels);
      w.coins.set(p.pid, mine - bet + win);
      logTxn(w, { kind: 'slots', amount: bet, won: win, from: p.pid, fromName: p.name });
      sendTo(p, { type: 'slotresult', reels: reels.map(i => SLOT_SYMBOLS[i]), bet, win });
      sendTo(p, walletMsg(w, p));
      return;
    }

    if (m.type === 'mail') {
      // a short message to a player who is not online: it waits for them, and they see it when they next join (players are matched by name)
      const to = typeof m.to === 'string' ? cleanName(m.to).toLowerCase() : '';
      const text = typeof m.text === 'string' ? m.text.replace(/[\u0000-\u001f]/g, '').trim().slice(0, 120) : '';
      if (!to || !text) return sendTo(p, { type: 'notice', text: 'WRITE A NAME AND A MESSAGE' });
      for (const q of players.values()) {
        if (q.joined && q.world === w && q.name && q.name.toLowerCase() === to) return sendTo(p, { type: 'notice', text: to.toUpperCase() + ' IS ONLINE. SAY HELLO IN CHAT' });
      }
      if (p.mailAt && Date.now() - p.mailAt < 10000) return sendTo(p, { type: 'notice', text: 'WAIT A MOMENT BEFORE SENDING ANOTHER MESSAGE' });
      const list = w.mail.get(to) || [];
      if (list.length >= 20) return sendTo(p, { type: 'notice', text: 'THAT MAILBOX IS FULL' });
      list.push({ from: p.name, text, at: Date.now() });
      w.mail.set(to, list);
      p.mailAt = Date.now();
      scheduleSave(w);
      return sendTo(p, { type: 'notice', text: 'MESSAGE SENT TO ' + to.toUpperCase() + '. IT WAITS FOR THEM' });
    }

    if (m.type === 'plotbuy') {
      // the shopkeeper sells a plot: the measured corners are checked, the price is worked out here, and the buyer owns the land
      const fail = text => sendTo(p, { type: 'notice', text });
      if (![m.x0, m.z0, m.x1, m.z1].every(Number.isInteger)) return fail('MEASURE A PLOT WITH THE LAND SURVEYOR FIRST');
      const pl = { x0: Math.min(m.x0, m.x1), x1: Math.max(m.x0, m.x1), z0: Math.min(m.z0, m.z1), z1: Math.max(m.z0, m.z1) };
      const sw = pl.x1 - pl.x0 + 1, sd = pl.z1 - pl.z0 + 1;
      if (sw < PLOT_MIN || sd < PLOT_MIN || sw > PLOT_MAX || sd > PLOT_MAX) return fail('A PLOT MUST BE ' + PLOT_MIN + ' TO ' + PLOT_MAX + ' BLOCKS ON EACH SIDE');
      if (w.plots.some(o => plotsOverlap(o, pl))) return fail('THAT LAND IS ALREADY OWNED');
      for (const [k, v] of w.edits) {
        if (v === 0) continue;
        const [x, , z] = k.split(',').map(Number);
        // only another player's blocks stop a sale: your own blocks, and old blocks nobody recorded, are fine
        const o = w.owners.get(k);
        if (o !== undefined && o !== p.pid && x >= pl.x0 && x <= pl.x1 && z >= pl.z0 && z <= pl.z1) return fail('ANOTHER PLAYER HAS BUILT ON THAT LAND');
      }
      const price = sw * sd * PLOT_RATE;
      const plotName = cleanPlotName(m.name) || 'PLOT ' + (w.plots.length + 1);
      const cash = w.coins.get(p.pid) || 0;
      if (cash < price) return fail('NOT ENOUGH CASH. THE PLOT COSTS ' + price);
      w.coins.set(p.pid, cash - price);
      w.plots.push(Object.assign(pl, { owner: p.pid, ownerName: p.name, name: plotName, price }));
      logTxn(w, { kind: 'plot', amount: price, from: p.pid, fromName: p.name, what: sw + ' x ' + sd + ' blocks' });
      scheduleSave(w);
      announcePlots(w);
      sendTo(p, walletMsg(w, p));
      return fail('YOUR PLOT IS READY: ' + sw + ' x ' + sd + ' BLOCKS. BUILD INSIDE IT');
    }
    if (m.type === 'plotsell') {
      // a player sells their own plot: every block on it is deleted and half the price comes back as cash
      const fail = text => sendTo(p, { type: 'notice', text });
      if (![m.x0, m.z0, m.x1, m.z1].every(Number.isInteger)) return fail('CHOOSE A PLOT TO SELL');
      const i = w.plots.findIndex(o => o.owner === p.pid && o.x0 === m.x0 && o.z0 === m.z0 && o.x1 === m.x1 && o.z1 === m.z1);
      if (i < 0) return fail('THAT IS NOT YOUR PLOT');
      const pl = w.plots[i];
      w.plots.splice(i, 1);
      const cleared = [];
      for (const k of [...w.edits.keys()]) {
        const [x, y, z] = k.split(',').map(Number);
        if (x < pl.x0 || x > pl.x1 || z < pl.z0 || z > pl.z1) continue;
        w.edits.delete(k); w.owners.delete(k); dropLock(w, k);
        cleared.push([x, y, z]);
      }
      const refund = Math.floor((pl.price || 0) / 2);
      w.coins.set(p.pid, (w.coins.get(p.pid) || 0) + refund);
      logTxn(w, { kind: 'plotsale', amount: refund, to: p.pid, toName: p.name, what: (pl.x1 - pl.x0 + 1) + ' x ' + (pl.z1 - pl.z0 + 1) + ' blocks' });
      scheduleSave(w);
      if (cleared.length) broadcast(w, { type: 'plotclear', blocks: cleared });
      for (const k of [...w.offers.keys()]) { const o = w.offers.get(k); if (o.x0 === pl.x0 && o.z0 === pl.z0 && o.x1 === pl.x1 && o.z1 === pl.z1) w.offers.delete(k); }
      announceOffers(w);
      announcePlots(w);
      sendTo(p, walletMsg(w, p));
      return fail('PLOT SOLD. YOU GOT ' + refund + ' CASH BACK');
    }
    if (m.type === 'plotoffer') {
      // the owner offers one of their plots to another player for a price they name
      const fail = text => sendTo(p, { type: 'notice', text });
      if (![m.x0, m.z0, m.x1, m.z1].every(Number.isInteger)) return fail('CHOOSE A PLOT TO OFFER');
      const pl = w.plots.find(o => o.owner === p.pid && o.x0 === m.x0 && o.z0 === m.z0 && o.x1 === m.x1 && o.z1 === m.z1);
      if (!pl) return fail('THAT IS NOT YOUR PLOT');
      const q = players.get(m.target);
      if (!q || !q.joined || q === p || q.world !== w || !q.pid) return fail('CHOOSE A PLAYER TO OFFER THE PLOT TO');
      const price = Number.isInteger(m.price) ? m.price : 0;
      if (price < 1 || price > 1000000) return fail('TYPE A PRICE FOR THE PLOT');
      for (const o of w.offers.values()) if (o.fromPid === p.pid && o.toPid === q.pid && o.x0 === pl.x0 && o.z0 === pl.z0 && o.x1 === pl.x1 && o.z1 === pl.z1) return fail('YOU ALREADY OFFERED THIS PLOT TO THAT PLAYER');
      const id = nextOfferId++;
      w.offers.set(id, { id, fromPid: p.pid, fromName: p.name, toPid: q.pid, toName: q.name, x0: pl.x0, z0: pl.z0, x1: pl.x1, z1: pl.z1, name: pl.name || 'PLOT', size: (pl.x1 - pl.x0 + 1) + ' x ' + (pl.z1 - pl.z0 + 1) + ' blocks', price });
      announceOffers(w);
      return fail('OFFER SENT TO ' + q.name);
    }
    if (m.type === 'plotlist' || m.type === 'plotunlist') {
      // the owner puts their plot up for sale at an asking price anyone can buy it for, or takes it off sale
      const fail = text => sendTo(p, { type: 'notice', text });
      if (![m.x0, m.z0, m.x1, m.z1].every(Number.isInteger)) return fail('CHOOSE A PLOT');
      const pl = w.plots.find(o => o.owner === p.pid && o.x0 === m.x0 && o.z0 === m.z0 && o.x1 === m.x1 && o.z1 === m.z1);
      if (!pl) return fail('THAT IS NOT YOUR PLOT');
      if (m.type === 'plotunlist') { pl.sale = 0; scheduleSave(w); announcePlots(w); return fail('PLOT TAKEN OFF SALE'); }
      const price = Number.isInteger(m.price) ? m.price : 0;
      if (price < 1 || price > 1000000) return fail('TYPE AN ASKING PRICE FROM 1 TO 1000000');
      pl.sale = price; scheduleSave(w); announcePlots(w);
      return fail('YOUR PLOT IS FOR SALE AT ' + price);
    }
    if (m.type === 'plotbuylisted') {
      // a buyer pays the asking price, and the plot (with every block on it) is theirs
      const fail = text => sendTo(p, { type: 'notice', text });
      if (![m.x0, m.z0, m.x1, m.z1].every(Number.isInteger)) return fail('CHOOSE A PLOT');
      const pl = w.plots.find(o => o.x0 === m.x0 && o.z0 === m.z0 && o.x1 === m.x1 && o.z1 === m.z1);
      if (!pl || !(pl.sale > 0)) return fail('THAT PLOT IS NOT FOR SALE');
      if (pl.owner === p.pid) return fail('YOU ALREADY OWN THIS PLOT');
      const cash = w.coins.get(p.pid) || 0, price = pl.sale, seller = pl.owner, sellerName = pl.ownerName;
      if (cash < price) return fail('NOT ENOUGH CASH. THE PLOT COSTS ' + price);
      w.coins.set(p.pid, cash - price);
      w.coins.set(seller, (w.coins.get(seller) || 0) + price);
      pl.owner = p.pid; pl.ownerName = p.name; pl.price = price; pl.sale = 0;
      for (const k of [...w.offers.keys()]) { const x = w.offers.get(k); if (x.x0 === pl.x0 && x.z0 === pl.z0 && x.x1 === pl.x1 && x.z1 === pl.z1) w.offers.delete(k); }
      const size = (pl.x1 - pl.x0 + 1) + ' x ' + (pl.z1 - pl.z0 + 1) + ' blocks';
      logTxn(w, { kind: 'plot', amount: price, from: p.pid, fromName: p.name, what: size });
      logTxn(w, { kind: 'plotsale', amount: price, to: seller, toName: sellerName, what: size });
      scheduleSave(w);
      announceOffers(w);
      announcePlots(w);
      for (const q of players.values()) if (q.world === w && q.joined && (q.pid === seller || q.pid === p.pid)) sendTo(q, walletMsg(w, q));
      for (const q of players.values()) if (q.world === w && q.joined && q.pid === seller) sendTo(q, { type: 'notice', text: p.name + ' BOUGHT YOUR PLOT FOR ' + price });
      return fail('YOU BOUGHT THE PLOT FOR ' + price);
    }
    if (m.type === 'offeraccept') {
      // the buyer accepts: they pay the price, and the plot (with every block on it) is theirs
      const fail = text => sendTo(p, { type: 'notice', text });
      const o = w.offers.get(+m.id);
      if (!o || o.toPid !== p.pid) return fail('THAT OFFER IS GONE');
      const pl = w.plots.find(x => x.owner === o.fromPid && x.x0 === o.x0 && x.z0 === o.z0 && x.x1 === o.x1 && x.z1 === o.z1);
      if (!pl) { w.offers.delete(o.id); announceOffers(w); return fail('THAT PLOT IS NO LONGER FOR SALE'); }
      const cash = w.coins.get(p.pid) || 0;
      if (cash < o.price) return fail('NOT ENOUGH CASH. THE PLOT COSTS ' + o.price);
      w.coins.set(p.pid, cash - o.price);
      w.coins.set(o.fromPid, (w.coins.get(o.fromPid) || 0) + o.price);
      pl.owner = p.pid; pl.ownerName = p.name; pl.price = o.price;
      for (const k of [...w.offers.keys()]) { const x = w.offers.get(k); if (x.x0 === o.x0 && x.z0 === o.z0 && x.x1 === o.x1 && x.z1 === o.z1) w.offers.delete(k); }
      logTxn(w, { kind: 'plot', amount: o.price, from: p.pid, fromName: p.name, what: o.size });
      logTxn(w, { kind: 'plotsale', amount: o.price, to: o.fromPid, toName: o.fromName, what: o.size });
      scheduleSave(w);
      announceOffers(w);
      announcePlots(w);
      for (const q of players.values()) if (q.world === w && q.joined && (q.pid === o.fromPid || q.pid === p.pid)) sendTo(q, walletMsg(w, q));
      for (const q of players.values()) if (q.world === w && q.joined && q.pid === o.fromPid) sendTo(q, { type: 'notice', text: p.name + ' BOUGHT YOUR PLOT FOR ' + o.price });
      return fail('YOU BOUGHT THE PLOT ' + o.name + ' FOR ' + o.price);
    }
    if (m.type === 'offerdecline') {
      // the buyer declines, or the owner takes back their offer
      const o = w.offers.get(+m.id);
      if (!o || (o.toPid !== p.pid && o.fromPid !== p.pid)) return;
      w.offers.delete(o.id);
      announceOffers(w);
      return sendTo(p, { type: 'notice', text: o.fromPid === p.pid ? 'OFFER CANCELLED' : 'OFFER DECLINED' });
    }
    if (m.type === 'plotmerge') {
      // two plots of the same owner that share a whole side become one plot; the price of both is kept
      const fail = text => sendTo(p, { type: 'notice', text });
      if (!Array.isArray(m.a) || !Array.isArray(m.b) || ![...m.a, ...m.b].every(Number.isInteger)) return fail('CHOOSE TWO PLOTS TO MERGE');
      const ia = w.plots.findIndex(o => o.owner === p.pid && sameRect(o, m.a));
      const ib = w.plots.findIndex(o => o.owner === p.pid && sameRect(o, m.b));
      if (ia < 0 || ib < 0 || ia === ib) return fail('CHOOSE TWO OF YOUR PLOTS TO MERGE');
      const A = w.plots[ia], B = w.plots[ib];
      if (!canMerge(A, B)) return fail('PLOTS MERGE ONLY WHEN THEY SHARE A WHOLE SIDE, BLOCK TO BLOCK');
      const merged = { x0: Math.min(A.x0, B.x0), x1: Math.max(A.x1, B.x1), z0: Math.min(A.z0, B.z0), z1: Math.max(A.z1, B.z1),
        owner: p.pid, ownerName: p.name, name: A.name || 'PLOT', price: (A.price || 0) + (B.price || 0), sale: 0 };
      if (merged.x1 - merged.x0 + 1 > MERGED_MAX || merged.z1 - merged.z0 + 1 > MERGED_MAX) return fail('A MERGED PLOT CAN BE AT MOST ' + MERGED_MAX + ' BLOCKS ON EACH SIDE');
      w.plots = w.plots.filter((_, i) => i !== ia && i !== ib);
      w.plots.push(merged);
      for (const k of [...w.offers.keys()]) { const o = w.offers.get(k); if (sameRect(o, m.a) || sameRect(o, m.b)) w.offers.delete(k); }
      scheduleSave(w);
      announceOffers(w);
      announcePlots(w);
      return fail('MERGED: ' + merged.name + ' IS NOW ' + (merged.x1 - merged.x0 + 1) + ' x ' + (merged.z1 - merged.z0 + 1) + ' BLOCKS');
    }
    if (m.type === 'plotsplit') {
      // cut a strip off one of your plots (a full side, so both parts stay rectangles): the strip becomes its own plot
      // with its share of the price. The blocks stay where they are.
      const fail = text => sendTo(p, { type: 'notice', text });
      if (!Array.isArray(m.plot) || !m.plot.every(Number.isInteger)) return fail('CHOOSE A PLOT TO CUT');
      const i = w.plots.findIndex(o => o.owner === p.pid && sameRect(o, m.plot));
      if (i < 0) return fail('THAT IS NOT YOUR PLOT');
      const pl = w.plots[i];
      const depth = Number.isInteger(m.depth) ? m.depth : 0;
      const W = pl.x1 - pl.x0 + 1, D = pl.z1 - pl.z0 + 1;
      let cut, rest;
      if (m.side === 'n') { cut = { x0: pl.x0, x1: pl.x1, z0: pl.z0, z1: pl.z0 + depth - 1 }; rest = { x0: pl.x0, x1: pl.x1, z0: pl.z0 + depth, z1: pl.z1 }; }
      else if (m.side === 's') { cut = { x0: pl.x0, x1: pl.x1, z0: pl.z1 - depth + 1, z1: pl.z1 }; rest = { x0: pl.x0, x1: pl.x1, z0: pl.z0, z1: pl.z1 - depth }; }
      else if (m.side === 'w') { cut = { x0: pl.x0, x1: pl.x0 + depth - 1, z0: pl.z0, z1: pl.z1 }; rest = { x0: pl.x0 + depth, x1: pl.x1, z0: pl.z0, z1: pl.z1 }; }
      else if (m.side === 'e') { cut = { x0: pl.x1 - depth + 1, x1: pl.x1, z0: pl.z0, z1: pl.z1 }; rest = { x0: pl.x0, x1: pl.x1 - depth, z0: pl.z0, z1: pl.z1 }; }
      else return fail('CHOOSE WHICH EDGE TO CUT FROM');
      if (depth < PLOT_MIN || depth >= (m.side === 'n' || m.side === 's' ? D : W)) return fail('CUT AT LEAST ' + PLOT_MIN + ' BLOCKS, AND LEAVE SOME OF THE PLOT');
      const cw = cut.x1 - cut.x0 + 1, cd = cut.z1 - cut.z0 + 1, rw = rest.x1 - rest.x0 + 1, rd = rest.z1 - rest.z0 + 1;
      if (Math.min(cw, cd) < PLOT_MIN || Math.min(rw, rd) < PLOT_MIN) return fail('BOTH PARTS MUST BE AT LEAST ' + PLOT_MIN + ' BLOCKS ON EACH SIDE');
      const total = pl.price || 0;
      const cutPrice = Math.round(total * (cw * cd) / (W * D)), restPrice = total - cutPrice;
      const cutName = cleanPlotName(m.name) || (pl.name || 'PLOT') + ' PART';
      w.plots[i] = Object.assign({}, pl, rest, { price: restPrice, sale: 0 });
      w.plots.push(Object.assign({}, pl, cut, { name: cutName, price: cutPrice, sale: 0 }));
      for (const k of [...w.offers.keys()]) { if (sameRect(w.offers.get(k), m.plot)) w.offers.delete(k); }
      scheduleSave(w);
      announceOffers(w);
      announcePlots(w);
      return fail('CUT OUT ' + cutName + ': ' + cw + ' x ' + cd + ' BLOCKS');
    }
    if (m.type === 'plotcut') {
      // cut a rectangle out of one of your plots (two corners picked with the Land Surveyor). The part becomes its own plot;
      // the land left around it becomes up to four plots of yours. Prices are split by area and the total is kept.
      const fail = text => sendTo(p, { type: 'notice', text });
      if (!Array.isArray(m.plot) || !Array.isArray(m.a) || !Array.isArray(m.b) || ![...m.plot, ...m.a, ...m.b].every(Number.isInteger)) return fail('PICK TWO POINTS INSIDE YOUR PLOT');
      const i = w.plots.findIndex(o => o.owner === p.pid && sameRect(o, m.plot));
      if (i < 0) return fail('THAT IS NOT YOUR PLOT');
      const pl = w.plots[i];
      const cut = { x0: Math.min(m.a[0], m.b[0]), x1: Math.max(m.a[0], m.b[0]), z0: Math.min(m.a[1], m.b[1]), z1: Math.max(m.a[1], m.b[1]) };
      if (cut.x0 < pl.x0 || cut.x1 > pl.x1 || cut.z0 < pl.z0 || cut.z1 > pl.z1) return fail('THE PART MUST BE INSIDE YOUR PLOT');
      const W = pl.x1 - pl.x0 + 1, D = pl.z1 - pl.z0 + 1, cw = cut.x1 - cut.x0 + 1, cd = cut.z1 - cut.z0 + 1;
      if (cw < PLOT_MIN || cd < PLOT_MIN) return fail('A PART MUST BE AT LEAST ' + PLOT_MIN + ' BLOCKS ON EACH SIDE');
      if (cw === W && cd === D) return fail('THAT IS THE WHOLE PLOT. SELL IT INSTEAD');
      const rest = [];   // the land left around the part: up to four rectangles
      if (cut.z0 > pl.z0) rest.push({ x0: pl.x0, x1: pl.x1, z0: pl.z0, z1: cut.z0 - 1 });
      if (cut.z1 < pl.z1) rest.push({ x0: pl.x0, x1: pl.x1, z0: cut.z1 + 1, z1: pl.z1 });
      if (cut.x0 > pl.x0) rest.push({ x0: pl.x0, x1: cut.x0 - 1, z0: cut.z0, z1: cut.z1 });
      if (cut.x1 < pl.x1) rest.push({ x0: cut.x1 + 1, x1: pl.x1, z0: cut.z0, z1: cut.z1 });
      if (rest.some(r => Math.min(r.x1 - r.x0 + 1, r.z1 - r.z0 + 1) < PLOT_MIN)) return fail('THE LAND LEFT AROUND THE PART MUST BE AT LEAST ' + PLOT_MIN + ' BLOCKS ON EACH SIDE. PICK A DIFFERENT PART');
      const total = pl.price || 0, area = W * D, cutArea = cw * cd, restTotal = total - Math.round(total * cutArea / area);
      const restArea = area - cutArea, cutName = cleanPlotName(m.name) || (pl.name || 'PLOT') + ' PART';
      const parts = [Object.assign({}, pl, cut, { name: cutName, price: Math.round(total * cutArea / area), sale: 0 })];
      let left = restTotal;
      rest.forEach((r, k) => {
        const a = (r.x1 - r.x0 + 1) * (r.z1 - r.z0 + 1);
        const pr = k === rest.length - 1 ? left : Math.round(restTotal * a / restArea);
        left -= pr;
        parts.push(Object.assign({}, pl, r, { name: k === 0 ? (pl.name || 'PLOT') : (pl.name || 'PLOT') + ' (' + (k + 1) + ')', price: pr, sale: 0 }));
      });
      w.plots.splice(i, 1, ...parts);
      for (const k of [...w.offers.keys()]) { if (sameRect(w.offers.get(k), m.plot)) w.offers.delete(k); }
      scheduleSave(w);
      announceOffers(w);
      announcePlots(w);
      return fail('CUT OUT ' + cutName + ': ' + cw + ' x ' + cd + ' BLOCKS. THE REST OF YOUR LAND IS STILL YOURS');
    }
    if (m.type === 'board') {
      // the leaderboard: only the players who are online in this world, with their placed blocks, plot land and cash
      const blocks = new Map(), land = new Map();
      for (const o of w.owners.values()) blocks.set(o, (blocks.get(o) || 0) + 1);
      for (const pl of w.plots) land.set(pl.owner, (land.get(pl.owner) || 0) + (pl.x1 - pl.x0 + 1) * (pl.z1 - pl.z0 + 1));
      const rows = [...players.values()].filter(q => q.world === w && q.joined && q.pid).map(q => ({
        name: q.name, me: q.pid === p.pid,
        blocks: blocks.get(q.pid) || 0, land: land.get(q.pid) || 0, cash: w.coins.get(q.pid) || 0
      }));
      return sendTo(p, { type: 'board', rows });
    }
    if (m.type === 'cashlog') return sendTo(p, { type: 'cashlog', entries: cashLogFor(w, p) });
    if (m.type === 'edit') {
      if (!isInt(m.x) || !isInt(m.y) || !isInt(m.z) || !isInt(m.id)) return;
      if (m.y < 0 || m.y >= CH || m.id < 0 || m.id > MAX_BLOCK_ID) return;   // 0 = air, 1-25 = block types (see BLOCKS in index.html)
      const dx = m.x + 0.5 - p.x, dy = m.y + 0.5 - p.y, dz = m.z + 0.5 - p.z;
      if (dx * dx + dy * dy + dz * dz > REACH * REACH) return;   // too far from where this player last was
      const key = m.x + ',' + m.y + ',' + m.z;
      const landOwner = plotAt(w, m.x, m.z);
      if (!canBypass(p)) {
        // building (and breaking) is allowed only on a plot the player has bought
        if (!landOwner) return fixBlock(p, w, key, 'BUILD ONLY ON LAND YOU HAVE BOUGHT');
        if (landOwner.owner !== p.pid) return fixBlock(p, w, key, 'THIS LAND BELONGS TO ANOTHER PLAYER');
      }
      const cur = w.edits.has(key) ? w.edits.get(key) : null;     // null: land that no player has changed
      const owner = w.owners.get(key);                            // undefined: no player placed this block
      if (owner !== undefined && owner !== p.pid && !canBypass(p)) {
        // someone else's block: it can only be opened or shut, and only by a player who may open its door
        if (m.id === 0 || !sameDoorHalf(cur, m.id)) return fixBlock(p, w, key, 'THAT BLOCK BELONGS TO ANOTHER PLAYER');
        const lock = w.locks.get(key);
        if (lock && !lockOpenFor(p, lock)) return fixBlock(p, w, key, 'THAT DOOR HAS A PASSWORD');
      }
      if (m.id === 0) { dropLock(w, key); w.owners.delete(key); }
      else {
        if (w.locks.has(key) && !isDoorBlock(m.id)) dropLock(w, key);
        if (owner === undefined && (cur === null || cur === 0)) w.owners.set(key, p.pid);   // a new block is the placer's
      }
      w.edits.set(key, m.id);
      p.workedAt = Date.now();
      scheduleSave(w);
      broadcast(w, { type: 'edit', x: m.x, y: m.y, z: m.z, id: m.id, by: id }, id);
      sendTo(p, { type: 'edit', x: m.x, y: m.y, z: m.z, id: m.id, by: id });
      return;
    }
  });

  ws.on('close', () => {
    players.delete(id);
    if (p.joined) {
      broadcast(p.world, { type: 'leave', id });
      broadcast(p.world, { type: 'system', text: p.name + ' left' });
      checkMorning(p.world);
    }
  });
  ws.on('error', () => {});
});

// everyone's clock is corrected every five seconds, in each world
setInterval(() => {
  const now = Date.now();
  for (const [token, t] of uploadTokens) if (t.until < now) uploadTokens.delete(token);
  for (const w of Object.values(WORLDS)) {
    broadcast(w, { type: 'time', time: worldTime(w) });
    broadcast(w, { type: 'tv', list: tvList(w), sources: tvSources(w) });   // the TVs are re-sent too, so the pictures stay in step (an empty list says none is on)
  }
}, 5000);

server.listen(PORT, HOST, () => {
  console.log(`Block Realm server on ${useTls ? 'https' : 'http'}://${HOST === '0.0.0.0' ? 'localhost' : HOST}:${PORT}  (game page and ws://.../ws)`);
  console.log(`worlds: ${Object.values(WORLDS).map(w => w.name + (w.passDigest ? ' (password)' : ' (public)')).join(', ')}`);
  console.log(`players up to ${MAX_PLAYERS} in all`);
});
