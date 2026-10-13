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
const MAX_BLOCK_ID = 299;       // highest block id a player may place (see BLOCKS in index.html: MAX_ID there must match)
const COLORS = ['#e6594b', '#4b9be6', '#58c25a', '#e6c44b', '#b35ae6', '#4be6d6', '#e6894b', '#e64b9b'];
const DAY_LEN = 480;            // seconds for one full day (the same as in index.html)
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
function codeDigest(s) { return crypto.createHash('sha256').update(String(s)).digest(); }
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
  w.mob = null;
  w.clock = { t: DAY_LEN * 0.3, at: Date.now() };    // the world time is w.clock.t at the moment w.clock.at; it then runs on in real time
  w.saveTimer = null;
  w.loaded = false;                                 // only a world that loaded cleanly is ever saved, so a bad file is never overwritten
  try {
    for (const [k, v] of JSON.parse(fs.readFileSync(w.file, 'utf8'))) w.edits.set(k, v);
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
  const tmp = w.file + '.tmp';
  try {
    fs.writeFileSync(tmp, JSON.stringify([...w.edits]));
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
    return fs.readFile(path.join(__dirname, 'public', rel), (err, data) => {
      if (err) { res.writeHead(404, { 'Content-Type': 'text/plain' }); return res.end('not found'); }
      res.writeHead(200, { 'Content-Type': type, 'Cache-Control': 'max-age=3600' });
      res.end(data);
    });
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
  p.world = w; p.joined = true;
  p.name = cleanName(m.name);
  const list = [];
  for (const [oid, o] of players) if (oid !== id && o.joined && o.world === w) list.push({ id: oid, name: o.name, color: o.color, x: o.x, y: o.y, z: o.z, yaw: o.yaw, sleeping: o.sleeping, hidden: o.hidden, role: o.role });
  const all = [];
  for (const [k, v] of w.edits) { const [x, y, z] = k.split(',').map(Number); all.push([x, y, z, v]); }
  sendTo(p, { type: 'welcome', id, world: w.key, worldName: w.name, edits: all, players: list, time: worldTime(w), mob: w.mob });
  broadcast(w, { type: 'join', id, name: p.name, color: p.color, x: p.x, y: p.y, z: p.z, yaw: p.yaw, role: p.role }, id);
  broadcast(w, { type: 'system', text: p.name + ' joined' }, id);
}

wss.on('connection', (ws) => {
  if (players.size >= MAX_PLAYERS) { ws.close(1013, 'server full'); return; }
  const id = nextId++;
  const p = { ws, world: null, name: 'Builder' + id, color: COLORS[id % COLORS.length], x: 8.5, y: 40, z: 8.5, yaw: 0, pitch: 0,
              tokens: 60, lastTick: Date.now(), joined: false, sleeping: false, hidden: false, role: null };
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
      p.yaw = m.yaw; p.pitch = m.pitch;
      if (!p.hidden) broadcast(w, { type: 'move', id, x: p.x, y: p.y, z: p.z, yaw: p.yaw, pitch: p.pitch }, id);
      return;
    }

    if (m.type === 'edit') {
      if (!isInt(m.x) || !isInt(m.y) || !isInt(m.z) || !isInt(m.id)) return;
      if (m.y < 0 || m.y >= CH || m.id < 0 || m.id > MAX_BLOCK_ID) return;   // 0 = air, 1-25 = block types (see BLOCKS in index.html)
      const dx = m.x + 0.5 - p.x, dy = m.y + 0.5 - p.y, dz = m.z + 0.5 - p.z;
      if (dx * dx + dy * dy + dz * dz > REACH * REACH) return;   // too far from where this player last was
      w.edits.set(m.x + ',' + m.y + ',' + m.z, m.id);
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
setInterval(() => { for (const w of Object.values(WORLDS)) broadcast(w, { type: 'time', time: worldTime(w) }); }, 5000);

server.listen(PORT, HOST, () => {
  console.log(`Block Realm server on ${useTls ? 'https' : 'http'}://${HOST === '0.0.0.0' ? 'localhost' : HOST}:${PORT}  (game page and ws://.../ws)`);
  console.log(`worlds: ${Object.values(WORLDS).map(w => w.name + (w.passDigest ? ' (password)' : ' (public)')).join(', ')}`);
  console.log(`players up to ${MAX_PLAYERS} in all`);
});
