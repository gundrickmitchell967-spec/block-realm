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
function lockOpenFor(p, lock) { return lock.owner === p.pid || lock.allowed.has(p.pid) || canBypass(p); }
// what one player is told about a door's lock: whether it is locked, whether it is theirs, and whether they may open it
function lockMsg(w, q, lo, lock) {
  return { type: 'lock', x: lo[0], y: lo[1], z: lo[2], locked: !!lock, mine: w.owners.get(lo.join(',')) === q.pid, ok: !!lock && lockOpenFor(q, lock) };
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
  w.mob = null;
  w.clock = { t: DAY_LEN * 0.3, at: Date.now() };    // the world time is w.clock.t at the moment w.clock.at; it then runs on in real time
  w.saveTimer = null;
  w.loaded = false;                                 // only a world that loaded cleanly is ever saved, so a bad file is never overwritten
  try {
    const data = JSON.parse(fs.readFileSync(w.file, 'utf8'));
    const list = Array.isArray(data) ? data : data.edits;          // older saves were just the list of edits
    for (const [k, v, o] of list) { w.edits.set(k, v); if (o !== undefined) w.owners.set(k, o); }
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
    fs.writeFileSync(tmp, JSON.stringify({ edits, locks }));
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
  sendTo(p, { type: 'welcome', id, world: w.key, worldName: w.name, edits: all, players: list, time: worldTime(w), mob: w.mob, tvs: tvList(w), sources: tvSources(w), locks: lockList(w, p) });
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
      p.yaw = m.yaw; p.pitch = m.pitch;
      if (!p.hidden) broadcast(w, { type: 'move', id, x: p.x, y: p.y, z: p.z, yaw: p.yaw, pitch: p.pitch }, id);
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
    if (m.type === 'edit') {
      if (!isInt(m.x) || !isInt(m.y) || !isInt(m.z) || !isInt(m.id)) return;
      if (m.y < 0 || m.y >= CH || m.id < 0 || m.id > MAX_BLOCK_ID) return;   // 0 = air, 1-25 = block types (see BLOCKS in index.html)
      const dx = m.x + 0.5 - p.x, dy = m.y + 0.5 - p.y, dz = m.z + 0.5 - p.z;
      if (dx * dx + dy * dy + dz * dz > REACH * REACH) return;   // too far from where this player last was
      const key = m.x + ',' + m.y + ',' + m.z;
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
