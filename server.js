// Minimal multiplayer server for the bird game.
// Responsibilities (kept intentionally small):
//   1. Serve the game's static files (public/index.html and friends).
//   2. Keep a live list of connected players (position, hp, species, angle...).
//   3. Broadcast every player's updates to everyone else in real time via WebSocket.
//   4. Relay chat messages.
//   5. Referee bird-vs-bird (PvP) combat: damage between players is decided and
//      stored here, not trusted from the client. Damage dealt by a player to an
//      NPC (mouse/hamster/cat/etc.) is a completely separate concern and is still
//      resolved entirely client-side, exactly as before — this server never sees it.
//
// This server still does NOT validate movement or NPC/food eating — clients remain
// trusted for their own physics and PvE outcomes (same as before). It only makes
// players visible to each other and now also referees PvP hits. See README.md for
// how this could grow into a fully authoritative server later.

const path = require('path');
const express = require('express');
const http = require('http');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: { origin: '*' }, // relax CORS since the client may be hosted separately during development
  // Force WebSocket only. Without this, Socket.IO will happily fall back to HTTP
  // long-polling if the WebSocket upgrade fails (e.g. a proxy/host that doesn't
  // pass it through) — and long-polling adds noticeable latency to *every* single
  // event (player movement, prey positions, eating), which reads to players as
  // "everything is delayed". Better to fail the connection loudly than degrade
  // silently into a laggy fallback. The client must also request 'websocket' only
  // (see io(..., { transports: ['websocket'] })) or it will still probe polling first.
  transports: ['websocket'],
  // Skip per-message deflate compression — it costs CPU on every single emit for
  // payloads this small (player/prey position updates), which isn't worth it here.
  perMessageDeflate: false,
});

app.use(express.static(path.join(__dirname, 'public')));

// socket.id -> player state
const players = new Map();
// socket.id -> last time we actually broadcast that player's 'update' to everyone
// else (see the throttle in socket.on('update') below).
const lastBroadcastAt = new Map();
const UPDATE_BROADCAST_MIN_INTERVAL_MS = 40; // caps fan-out at 25/s per player, well above any normal client's send rate

function sanitize(d) {
  d = d || {};
  return {
    name: String(d.name || '???').slice(0, 14),
    species: String(d.species || 'sparrow').slice(0, 20),
    x: Number.isFinite(d.x) ? d.x : 0,
    y: Number.isFinite(d.y) ? d.y : 0,
    hp: Number.isFinite(d.hp) ? d.hp : 0,
    maxHp: Number.isFinite(d.maxHp) ? d.maxHp : 1,
    totalScore: Number.isFinite(d.totalScore) ? d.totalScore : 0,
    angle: Number.isFinite(d.angle) ? d.angle : 0,
    flying: !!d.flying,
    // Sent by the client so the server can honor the same brief spawn/respawn
    // invulnerability window the client itself uses — a player can't be hit
    // by PvP while it's active.
    invulnUntil: Number.isFinite(d.invulnUntil) ? d.invulnUntil : 0,
    // Special-ability activation state (Phase 4) — kept here so the server can referee
    // stork dash / pelican water bomb / cassowary kick hits using its own copy of the
    // *attacker's* state, instead of trusting whichever client claims to have been hit.
    dashActive: !!d.dashActive, dashUntil: Number.isFinite(d.dashUntil) ? d.dashUntil : 0, dashId: Number.isFinite(d.dashId) ? d.dashId : 0,
    waterX: Number.isFinite(d.waterX) ? d.waterX : 0, waterY: Number.isFinite(d.waterY) ? d.waterY : 0,
    waterId: Number.isFinite(d.waterId) ? d.waterId : 0, waterUntil: Number.isFinite(d.waterUntil) ? d.waterUntil : 0,
    cassowaryKickId: Number.isFinite(d.cassowaryKickId) ? d.cassowaryKickId : 0,
    cassowaryKickAt: Number.isFinite(d.cassowaryKickAt) ? d.cassowaryKickAt : 0,
    eagleCarryKey: typeof d.eagleCarryKey === 'string' ? d.eagleCarryKey : null,
    eagleGrabId: Number.isFinite(d.eagleGrabId) ? d.eagleGrabId : 0,
    eagleDropId: Number.isFinite(d.eagleDropId) ? d.eagleDropId : 0,
  };
}

// ---------------- PvP combat (server-authoritative) ----------------
// This table mirrors the subset of the client's SPECIES data (radius + attack,
// plus the evolution order used to compare "who is bigger") that's needed to
// referee a hit. It intentionally does NOT include anything about NPCs/food —
// that stays purely client-side and never touches this server.
const PVP_ORDER = [
  'sparrow', 'pigeon', 'crow', 'stork', 'owl', 'hawk', 'pelican',
  'eagle', 'griffin', 'blackgoose', 'ostrich', 'cassowary', 'phoenix',
];
const PVP_SPECIES = {
  sparrow:    { radius: 16,  attack: 0 },
  pigeon:     { radius: 24,  attack: 20 },
  crow:       { radius: 34,  attack: 50 },
  stork:      { radius: 48,  attack: 85 },
  owl:        { radius: 54,  attack: 160 },
  hawk:       { radius: 69,  attack: 225 },
  pelican:    { radius: 82,  attack: 285 },
  eagle:      { radius: 88,  attack: 360 },
  griffin:    { radius: 92,  attack: 440 },
  blackgoose: { radius: 98,  attack: 500 },
  ostrich:    { radius: 107, attack: 650 },
  cassowary:  { radius: 116, attack: 750 },
  phoenix:    { radius: 124, attack: 950 },
};
const PVP_HIT_RANGE_MULT = 0.75; // matches the client's `me.radius + oSpec.radius*0.75` reach
const PVP_HIT_COOLDOWN = 1500;   // ms, matches the client's old per-target cooldown

// `${attackerId}>${targetId}` -> next time (ms) that attacker is allowed to land another hit on that target
const pvpCooldowns = new Map();

function pvpTier(speciesKey) {
  const i = PVP_ORDER.indexOf(speciesKey);
  return i === -1 ? 0 : i;
}

// Referees one bird-vs-bird hit attempt. Only ever called from the 'pvpHit' socket
// event below, where `attackerId` is always the reporting socket's own id — a
// client can only ever claim to be the attacker, never the target, of a hit.
function resolvePvpHit(attackerId, targetId) {
  if (!targetId || targetId === attackerId) return null;
  const attacker = players.get(attackerId);
  const target = players.get(targetId);
  if (!attacker || !target) return null;
  if (attacker.flying || target.flying) return null; // flying birds can't peck or be pecked

  const now = Date.now();
  if (now < (target.invulnUntil || 0)) return null; // target is still spawn-invulnerable

  const attackerTier = pvpTier(attacker.species);
  const targetTier = pvpTier(target.species);
  if (attackerTier <= targetTier) return null; // only a strictly bigger bird can deal PvP damage

  const aSpec = PVP_SPECIES[attacker.species] || PVP_SPECIES.sparrow;
  const tSpec = PVP_SPECIES[target.species] || PVP_SPECIES.sparrow;
  const dist = Math.hypot(attacker.x - target.x, attacker.y - target.y);
  // Mirrors the client's own `me.radius + oSpec.radius*0.75` reach check, from the attacker's perspective.
  if (dist > aSpec.radius + tSpec.radius * PVP_HIT_RANGE_MULT) return null; // out of range

  const cdKey = attackerId + '>' + targetId;
  const nextAllowed = pvpCooldowns.get(cdKey) || 0;
  if (now < nextAllowed) return null; // this attacker/target pair is still on cooldown
  pvpCooldowns.set(cdKey, now + PVP_HIT_COOLDOWN);

  const damage = aSpec.attack;
  if (damage <= 0) return null;

  target.hp = Math.max(0, (target.hp || 0) - damage);
  return { damage, targetHp: target.hp, targetMaxHp: target.maxHp };
}

function clearPvpCooldownsFor(id) {
  for (const key of pvpCooldowns.keys()) {
    if (key.startsWith(id + '>') || key.endsWith('>' + id)) pvpCooldowns.delete(key);
  }
}

// ---------------- World state (server-authoritative food & prey) ----------------
// PHASE 1 of the "shared world" migration: the server now owns where every piece of
// food/prey is, whether it's been eaten, and when it respawns, so every connected
// client renders the exact same world instead of each generating its own at random.
//
// Still client-side for now (future phases): PvE combat/poison/ability damage,
// evolution scoring, seasons, ostrich eggs, flame patches. Score/heal/poison are
// still applied by the client itself once the server confirms an eat — the server
// only referees *what* got eaten and *where things are*, not yet HP/combat math for PvE.
const MAP_W = 3200, MAP_H = 3200 * 9;
const BIOME_MAIN = { yStart: 0, yEnd: 19200 };
const BIOME_TROPICAL = { yStart: 19200, yEnd: 28800 };
function biomeBounds(name) { return name === 'tropical' ? BIOME_TROPICAL : BIOME_MAIN; }
function biomeAtY(y) { return (y >= BIOME_TROPICAL.yStart && y < BIOME_TROPICAL.yEnd) ? 'tropical' : 'main'; }

// Mirrors the client's FOOD_TYPES (size for eat-distance checks, points for
// score/respawn timing, maxHp for the "tough plants must be pecked down" mechanic).
const FOOD_TYPES = {
  seed:         { points: 1,        size: 4 },
  bread:        { points: 10,       size: 6.5 },
  apple:        { points: 50,       size: 8 },
  meat:         { points: 250,      size: 10 },
  redcurrant:   { points: 2,        size: 4 },
  banana:       { points: 75,       size: 7.5 },
  mango:        { points: 375,      size: 9 },
  dragonfruit:  { points: 2200,     size: 16.5 },
  coconut:      { points: 250000,   size: 16.9, maxHp: 2500 },
  passionfruit: { points: 375000,   size: 21 },
  wildorchid:   { points: 500000,   size: 21.43 },
  wildmelon:    { points: 18000000, size: 42,   maxHp: 22000, respawn: 25000 },
  watermelon:   { points: 225000,   size: 19.2 },
  pumpkin:      { points: 600000,   size: 24.2, maxHp: 4500 },
  cactus:       { points: 4000000,  size: 27.5, maxHp: 4850 },
  aloe:         { points: 100000,   size: 20.25 },
};

// Mirrors the client's PREY_TYPES. Sizes are pre-multiplied by 2.5 below, same as the client does.
const PREY_TYPES = {
  mouse:          { points: 1000,     size: 7,  speed: 55,   maxHp: 500,  mobile: true },
  hamster:        { points: 2000,     size: 8,  speed: 42,   maxHp: 880,  mobile: true },
  cat:            { points: 4000,     size: 13, speed: 70,   maxHp: 1300, mobile: true },
  starfish:       { points: 2500,     size: 10, speed: 0,    maxHp: 1500, mobile: false },
  crab:           { points: 10000,    size: 12, speed: 30,   maxHp: 2200, mobile: true },
  dog:            { points: 25000,    size: 16, speed: 45,   maxHp: 2500, mobile: true },
  rat:            { points: 50000,    size: 18, speed: 48,   maxHp: 3500, mobile: true },
  bones:          { points: 95000,    size: 14, speed: 0,    maxHp: 2000, mobile: false },
  scorpion:       { points: 310000,   size: 17, speed: 40,   maxHp: 3200, mobile: true },
  zombie:         { points: 10000000, size: 31, speed: 33,   maxHp: 5800, mobile: true, respawn: 25000 },
  mummy:          { points: 15000000, size: 44, speed: 30,   maxHp: 7500, mobile: true, respawn: 35000 },
  worm:           { points: 20,       size: 6,  speed: 40,   maxHp: 75,   mobile: true },
  flyingsquirrel: { points: 3000,     size: 10, speed: 48,   maxHp: 900,  mobile: true },
  tarantula:      { points: 5500,     size: 12, speed: 30,   maxHp: 1500, mobile: true },
  lobster:        { points: 16000,    size: 15, speed: 26,   maxHp: 2600, mobile: true },
  blacktaipan:    { points: 65000,    size: 18, speed: 60,   maxHp: 2800, mobile: true },
  boa:            { points: 425000,   size: 17, speed: 40,   maxHp: 4000, mobile: true },
  leshy:          { points: 20000000, size: 36, speed: 31.5, maxHp: 9000, mobile: true },
};
Object.values(PREY_TYPES).forEach(pt => { pt.size *= 2.5; });

// Which species can eat which food/prey type — mirrors the client's SPECIES[x].eats tables.
const SPECIES_EAT = {
  sparrow:    ['seed', 'redcurrant'],
  pigeon:     ['seed', 'bread', 'redcurrant', 'worm'],
  crow:       ['seed', 'bread', 'apple', 'redcurrant', 'banana', 'worm'],
  stork:      ['seed', 'bread', 'apple', 'meat', 'redcurrant', 'banana', 'mango', 'worm'],
  owl:        ['seed', 'bread', 'apple', 'meat', 'mouse', 'hamster', 'redcurrant', 'banana', 'mango', 'worm', 'flyingsquirrel'],
  hawk:       ['seed', 'bread', 'apple', 'meat', 'mouse', 'hamster', 'cat', 'redcurrant', 'banana', 'mango', 'worm', 'flyingsquirrel', 'tarantula'],
  pelican:    ['seed', 'bread', 'apple', 'meat', 'mouse', 'hamster', 'cat', 'starfish', 'crab', 'redcurrant', 'banana', 'mango', 'dragonfruit', 'worm', 'flyingsquirrel', 'tarantula', 'lobster'],
  eagle:      ['seed', 'bread', 'apple', 'meat', 'mouse', 'hamster', 'cat', 'starfish', 'crab', 'dog', 'rat', 'redcurrant', 'banana', 'mango', 'dragonfruit', 'worm', 'flyingsquirrel', 'tarantula', 'lobster', 'blacktaipan'],
  griffin:    ['seed', 'bread', 'apple', 'meat', 'mouse', 'hamster', 'cat', 'starfish', 'crab', 'dog', 'rat', 'bones', 'scorpion', 'redcurrant', 'banana', 'mango', 'dragonfruit', 'coconut', 'worm', 'flyingsquirrel', 'tarantula', 'lobster', 'blacktaipan', 'boa'],
  blackgoose: ['seed', 'bread', 'apple', 'meat', 'mouse', 'hamster', 'cat', 'starfish', 'crab', 'dog', 'rat', 'bones', 'scorpion', 'redcurrant', 'banana', 'mango', 'dragonfruit', 'coconut', 'passionfruit', 'wildorchid', 'watermelon', 'pumpkin', 'worm', 'flyingsquirrel', 'tarantula', 'lobster', 'blacktaipan', 'boa'],
  ostrich:    ['seed', 'bread', 'apple', 'meat', 'mouse', 'hamster', 'cat', 'starfish', 'crab', 'dog', 'rat', 'bones', 'scorpion', 'redcurrant', 'banana', 'mango', 'dragonfruit', 'coconut', 'passionfruit', 'wildorchid', 'wildmelon', 'watermelon', 'pumpkin', 'cactus', 'aloe', 'worm', 'flyingsquirrel', 'tarantula', 'lobster', 'blacktaipan', 'boa'],
  cassowary:  ['seed', 'bread', 'apple', 'meat', 'mouse', 'hamster', 'cat', 'starfish', 'crab', 'dog', 'rat', 'bones', 'scorpion', 'zombie', 'mummy', 'redcurrant', 'banana', 'mango', 'dragonfruit', 'coconut', 'passionfruit', 'wildorchid', 'wildmelon', 'watermelon', 'pumpkin', 'cactus', 'aloe', 'worm', 'flyingsquirrel', 'tarantula', 'lobster', 'blacktaipan', 'boa', 'leshy'],
  phoenix:    ['seed', 'bread', 'apple', 'meat', 'mouse', 'hamster', 'cat', 'starfish', 'crab', 'dog', 'rat', 'bones', 'scorpion', 'zombie', 'mummy', 'redcurrant', 'banana', 'mango', 'dragonfruit', 'coconut', 'passionfruit', 'wildorchid', 'wildmelon', 'watermelon', 'pumpkin', 'cactus', 'aloe', 'worm', 'flyingsquirrel', 'tarantula', 'lobster', 'blacktaipan', 'boa', 'leshy'],
};
// Turn each list into a fast lookup set.
const SPECIES_EAT_SET = {};
for (const [sp, list] of Object.entries(SPECIES_EAT)) SPECIES_EAT_SET[sp] = new Set(list);
function canEat(species, type) {
  const set = SPECIES_EAT_SET[species];
  return !!set && set.has(type);
}

let food = [];
let prey = [];
let foodSeq = 0, preySeq = 0;

function spawnFoodItem(type, biome) {
  const b = biomeBounds(biome);
  const ft = FOOD_TYPES[type];
  return {
    id: 'f' + (foodSeq++), type, biome,
    x: Math.random() * MAP_W, y: b.yStart + Math.random() * (b.yEnd - b.yStart),
    collected: false, respawnAt: 0, hp: ft.maxHp || 0, nextHitAt: 0,
  };
}
// Same as spawnFoodItem but at a fixed point instead of a random one — used when an
// ability (pigeon dig, crow's meat-shatter-on-takeoff) drops food where a player
// currently is, instead of the world's normal random distribution.
function spawnFoodItemAt(type, x, y) {
  const cx = Math.max(0, Math.min(MAP_W, x));
  const cy = Math.max(0, Math.min(MAP_H, y));
  const biome = biomeAtY(cy);
  const ft = FOOD_TYPES[type];
  return {
    id: 'f' + (foodSeq++), type, biome,
    x: cx, y: cy,
    collected: false, respawnAt: 0, hp: ft.maxHp || 0, nextHitAt: 0,
  };
}
function spawnPreyItem(type, biome) {
  const b = biomeBounds(biome);
  const pt = PREY_TYPES[type];
  const angle = Math.random() * Math.PI * 2;
  return {
    id: 'p' + (preySeq++), type, biome,
    x: Math.random() * MAP_W, y: b.yStart + Math.random() * (b.yEnd - b.yStart),
    vx: pt.mobile ? Math.cos(angle) : 0, vy: pt.mobile ? Math.sin(angle) : 0,
    hp: pt.maxHp, collected: false, respawnAt: 0, nextTurnAt: 0,
  };
}

function initWorld() {
  const pushFood = (type, n, biome = 'main') => { for (let i = 0; i < n; i++) food.push(spawnFoodItem(type, biome)); };
  pushFood('seed', 170); pushFood('bread', 45); pushFood('apple', 16); pushFood('meat', 10);
  pushFood('watermelon', 18); pushFood('pumpkin', 28); pushFood('cactus', 9); pushFood('aloe', 20);
  pushFood('redcurrant', 120, 'tropical'); pushFood('banana', 80, 'tropical'); pushFood('mango', 55, 'tropical');
  pushFood('dragonfruit', 35, 'tropical'); pushFood('coconut', 20, 'tropical'); pushFood('passionfruit', 12, 'tropical');
  pushFood('wildorchid', 8, 'tropical'); pushFood('wildmelon', 3, 'tropical');

  const pushPrey = (type, n, biome = 'main') => { for (let i = 0; i < n; i++) prey.push(spawnPreyItem(type, biome)); };
  pushPrey('mouse', 10); pushPrey('hamster', 6); pushPrey('cat', 4); pushPrey('starfish', 8); pushPrey('crab', 5);
  pushPrey('dog', 3); pushPrey('rat', 3); pushPrey('bones', 2); pushPrey('scorpion', 2);
  pushPrey('zombie', 1); pushPrey('mummy', 1);
  pushPrey('worm', 8, 'tropical'); pushPrey('flyingsquirrel', 6, 'tropical'); pushPrey('tarantula', 5, 'tropical');
  pushPrey('lobster', 4, 'tropical'); pushPrey('blacktaipan', 3, 'tropical'); pushPrey('boa', 2, 'tropical'); pushPrey('leshy', 1, 'tropical');
}
initWorld();

function respawnFood(f) {
  const b = biomeBounds(f.biome);
  const ft = FOOD_TYPES[f.type];
  f.x = Math.random() * MAP_W; f.y = b.yStart + Math.random() * (b.yEnd - b.yStart);
  f.collected = false; f.hp = ft.maxHp || 0; f.respawnAt = 0; f.nextHitAt = 0;
  io.emit('foodUpdate', f);
}
function respawnPrey(pr) {
  const b = biomeBounds(pr.biome);
  const pt = PREY_TYPES[pr.type];
  const angle = Math.random() * Math.PI * 2;
  pr.x = Math.random() * MAP_W; pr.y = b.yStart + Math.random() * (b.yEnd - b.yStart);
  pr.vx = pt.mobile ? Math.cos(angle) : 0; pr.vy = pt.mobile ? Math.sin(angle) : 0;
  pr.hp = pt.maxHp; pr.collected = false; pr.respawnAt = 0;
  io.emit('preyUpdate', pr);
}

// Referees one "I'm trying to eat this" attempt. Re-checks species-can-eat and
// distance server-side, exactly like resolvePvpHit does for combat — the client
// is only ever trusted to say *what* it's trying to eat, not whether it succeeded.
function resolveEat(player, kind, id) {
  const arr = kind === 'food' ? food : prey;
  const typeTable = kind === 'food' ? FOOD_TYPES : PREY_TYPES;
  const item = arr.find(it => it.id === id);
  if (!item || item.collected) return null;
  const info = typeTable[item.type];
  if (!info || !canEat(player.species, item.type)) return null;

  const spec = PVP_SPECIES[player.species] || PVP_SPECIES.sparrow;
  const dist = Math.hypot(player.x - item.x, player.y - item.y);
  if (dist > spec.radius + info.size + 4) return null;

  const now = Date.now();
  if (info.maxHp) {
    // Tough plants/prey (cactus, pumpkin, coconut, wildmelon...) must be pecked down over time.
    if (now < (item.nextHitAt || 0)) return null;
    item.nextHitAt = now + 1500;
    if (item.hp == null) item.hp = info.maxHp;
    item.hp -= (spec.attack || info.maxHp);
    if (item.hp > 0) return { partial: true, item };
  }

  item.collected = true;
  const baseRespawn = info.respawn || (kind === 'food'
    ? 3500 + Math.random() * 2500 + info.points * 40
    : 5000 + Math.random() * 3000 + info.points * 3);
  item.respawnAt = now + baseRespawn;
  return { partial: false, item, points: info.points, type: item.type };
}

function tickWorldMovement(dtMs) {
  const now = Date.now();
  const dt = dtMs / 1000;
  // Collect the prey that actually moved this tick so we can broadcast their
  // fresh x/y *and* vx/vy together, right away — instead of a separate, lower-rate
  // timer re-reading whatever vx/vy happens to be sitting on the object later.
  // That old setup was the root cause of prey visually "moving sideways": the
  // random direction change below could happen several ticks before a client
  // ever heard about the new vx/vy, so a client rotating a sprite from vx/vy
  // would show it facing stale directions while x/y kept moving correctly.
  const moved = [];
  for (const pr of prey) {
    if (pr.collected) { if (now >= pr.respawnAt) respawnPrey(pr); continue; }
    const pt = PREY_TYPES[pr.type];
    if (!pt.mobile) continue;
    if (now >= (pr.nextTurnAt || 0)) {
      const angle = Math.random() * Math.PI * 2;
      pr.vx = Math.cos(angle); pr.vy = Math.sin(angle);
      pr.nextTurnAt = now + 800 + Math.random() * 1400;
    }
    const b = biomeBounds(pr.biome);
    let nx = pr.x + pr.vx * pt.speed * dt;
    let ny = pr.y + pr.vy * pt.speed * dt;
    if (nx < 0 || nx > MAP_W) { pr.vx *= -1; nx = Math.max(0, Math.min(MAP_W, nx)); }
    if (ny < b.yStart || ny > b.yEnd) { pr.vy *= -1; ny = Math.max(b.yStart, Math.min(b.yEnd, ny)); }
    pr.x = nx; pr.y = ny;
    moved.push({ id: pr.id, x: pr.x, y: pr.y, vx: pr.vx, vy: pr.vy });
  }
  for (const f of food) {
    if (f.collected && now >= f.respawnAt) respawnFood(f);
  }
  // Broadcast on the very same tick the positions were computed on — this also
  // halves the old worst-case broadcast latency (100ms tick vs the previous
  // 200ms timer that ran independently of the movement calc).
  if (moved.length) io.emit('preyPositions', moved);
}
setInterval(() => tickWorldMovement(100), 100);

// ---------------- Ostrich eggs & Phoenix fire trail (server-authoritative) ----------------
// PHASE 6. Both of these were 100% client-local arrays before this — an ostrich's eggs and
// a phoenix's flame trail only ever existed in that one player's own browser. Other players
// couldn't see them, eat them, burn in them, or damage them — two of the game's twelve unique
// abilities simply didn't work at all when playing with others. The server now owns both lists.
const OSTRICH_EGG_RADIUS = 16;
const OSTRICH_EGG_MAX_HP = 6500;
const OSTRICH_EGG_POINTS_PER_SEC = 50000;
const OSTRICH_EGG_POINTS_EATER = 5000000;
const EGG_LAY_COOLDOWN = 32000;        // ms, matches the client's ABILITY_COOLDOWN.ostrich
const PHOENIX_ARM_COOLDOWN = 41000;    // ms, matches the client's ABILITY_COOLDOWN.phoenix
const PHOENIX_TRAIL_ARM_DURATION = 15000;
const PHOENIX_TRAIL_LIFETIME = 3000;
const PHOENIX_TRAIL_DPS = 500;
const PHOENIX_TRAIL_RADIUS = 170;
const PHOENIX_TRAIL_DROP_INTERVAL = 140;
const PHOENIX_BURN_TICK_COOLDOWN = 300; // ms between server-validated player burn ticks per patch
const ABILITY_WORLD_TICK_MS = 200;

let ostrichEggs = [];
let eggSeq = 0;
let flamePatches = [];
let flameSeq = 0;

function layEgg(playerId) {
  const player = players.get(playerId);
  if (!player || player.species !== 'ostrich' || player.flying) return null;
  const now = Date.now();
  if (now < (player.nextEggLayAt || 0)) return null;
  player.nextEggLayAt = now + EGG_LAY_COOLDOWN;
  const egg = { id: 'e' + (eggSeq++), x: player.x, y: player.y, hp: OSTRICH_EGG_MAX_HP, ownerId: playerId, ownerName: player.name, createdAt: now };
  ostrichEggs.push(egg);
  return egg;
}

function eatEgg(playerId, eggId) {
  const player = players.get(playerId);
  if (!player || (player.species !== 'cassowary' && player.species !== 'phoenix') || player.flying) return null;
  const egg = ostrichEggs.find(e => e.id === eggId);
  if (!egg) return null;
  const spec = PVP_SPECIES[player.species] || PVP_SPECIES.sparrow;
  const dist = Math.hypot(player.x - egg.x, player.y - egg.y);
  if (dist > spec.radius + OSTRICH_EGG_RADIUS + 4) return null;
  ostrichEggs = ostrichEggs.filter(e => e.id !== eggId);
  return egg;
}

function armPhoenixTrail(playerId) {
  const player = players.get(playerId);
  if (!player || player.species !== 'phoenix') return null;
  const now = Date.now();
  if (now < (player.nextPhoenixArmAt || 0)) return null;
  player.nextPhoenixArmAt = now + PHOENIX_ARM_COOLDOWN;
  player.phoenixTrailUntil = now + PHOENIX_TRAIL_ARM_DURATION;
  player.nextPhoenixDropAt = now;
  return true;
}

function dropFlamePatch(playerId) {
  const player = players.get(playerId);
  if (!player || player.species !== 'phoenix') return null;
  const now = Date.now();
  if (now >= (player.phoenixTrailUntil || 0)) return null;
  if (now < (player.nextPhoenixDropAt || 0)) return null;
  player.nextPhoenixDropAt = now + PHOENIX_TRAIL_DROP_INTERVAL;
  const patch = { id: 'fl' + (flameSeq++), x: player.x, y: player.y, expiresAt: now + PHOENIX_TRAIL_LIFETIME, ownerId: playerId };
  flamePatches.push(patch);
  return patch;
}

// Runs every ABILITY_WORLD_TICK_MS: prunes dead flame patches, lets dangerous prey chip away
// at eggs, lets flame patches burn prey (crediting whichever phoenix owns that patch), and
// pays out the ostrich's per-second "uneaten egg" score to each egg's own owner — not to
// whichever client happens to be running the loop, which is what the old local-only code did.
function tickAbilityWorld() {
  const now = Date.now();

  if (flamePatches.length) flamePatches = flamePatches.filter(fp => now < fp.expiresAt);

  if (ostrichEggs.length) {
    for (const pr of prey) {
      if (pr.collected) continue;
      const dmg = DANGEROUS_PREY[pr.type];
      if (!dmg) continue;
      const pt = PREY_TYPES[pr.type];
      for (let i = ostrichEggs.length - 1; i >= 0; i--) {
        const egg = ostrichEggs[i];
        const d = Math.hypot(egg.x - pr.x, egg.y - pr.y);
        if (d < OSTRICH_EGG_RADIUS + pt.size + 4 && now >= (pr.nextEggBiteAt || 0)) {
          pr.nextEggBiteAt = now + 1500;
          egg.hp -= dmg;
          if (egg.hp <= 0) {
            ostrichEggs.splice(i, 1);
            io.emit('eggRemove', { id: egg.id });
          } else {
            io.emit('eggHpUpdate', { id: egg.id, hp: egg.hp });
          }
        }
      }
    }
  }

  if (flamePatches.length) {
    for (const pr of prey) {
      if (pr.collected) continue;
      const pt = PREY_TYPES[pr.type];
      let burningOwner = null;
      for (const fp of flamePatches) {
        const d = Math.hypot(pr.x - fp.x, pr.y - fp.y);
        if (d < PHOENIX_TRAIL_RADIUS + pt.size) { burningOwner = fp.ownerId; break; }
      }
      if (!burningOwner) continue;
      pr.hp -= PHOENIX_TRAIL_DPS * (ABILITY_WORLD_TICK_MS / 1000);
      if (pr.hp <= 0) {
        pr.collected = true;
        const baseRespawn = pt.respawn || (5000 + Math.random() * 3000 + pt.points * 3);
        pr.respawnAt = now + baseRespawn;
        io.emit('preyUpdate', pr);
        if (players.has(burningOwner)) {
          io.to(burningOwner).emit('eatResult', { kind: 'prey', type: pr.type, points: pt.points });
        }
      }
    }
  }

  if (ostrichEggs.length) {
    const countByOwner = {};
    for (const egg of ostrichEggs) countByOwner[egg.ownerId] = (countByOwner[egg.ownerId] || 0) + 1;
    for (const [ownerId, count] of Object.entries(countByOwner)) {
      if (!players.has(ownerId)) continue;
      const points = OSTRICH_EGG_POINTS_PER_SEC * count * (ABILITY_WORLD_TICK_MS / 1000);
      io.to(ownerId).emit('eggPoints', { points });
    }
  }
}
setInterval(tickAbilityWorld, ABILITY_WORLD_TICK_MS);

// ---------------- PvE combat (server-authoritative) ----------------
// PHASE 3 of the "shared world" migration: prey that fight back against birds too
// weak to eat them, and food that stings everyone (cactus), are now refereed here
// instead of each client just quietly subtracting its own hp. Poison's initial
// application is validated server-side too; the actual hp-drain-over-time tick
// stays client-side for smoothness (same as the client's own hp regen elsewhere).
//
// Prey that bite back a bird too small/weak to eat them (only if that species can't eat them).
const DANGEROUS_PREY = { flyingsquirrel: 30, cat: 60, crab: 50, lobster: 120, dog: 160, rat: 200, blacktaipan: 100, scorpion: 175, boa: 500, zombie: 900, mummy: 1500, leshy: 2000 };
// Food that stings EVERY bird that touches it, even species that can eat it (e.g. cactus).
const ALWAYS_DANGEROUS_PREY = { cactus: 450 };
// Poison inflicted by a bite — duration (ms) + damage/sec while active. The client owns the
// tick-down math; this table only needs to match keys/values so the client applies the same effect.
const POISON_SOURCES = {
  tarantula: { duration: 3000, dps: 30 },
  scorpion: { duration: 5000, dps: 60 },
  blacktaipan: { duration: 10000, dps: 100 },
};

const PVE_HIT_COOLDOWN = 1500; // ms, matches the client's old per-item bite cadence
// `${playerId}>${kind}:${itemId}` -> next time (ms) that player is allowed to be bitten by that item again
const pveCooldowns = new Map();

// Ability-driven food spawns (pigeon dig -> bread, crow meat-shatter -> apples) used to be
// 100% client-local: the client pushed the new item straight into its own `food` array with
// a locally-generated id that the server never heard about. That meant the server's own
// eatItem referee (resolveEat) could never find that id, so eating what you just spawned
// silently failed every time — the item just sat there, invisible to `food.find(...)`, forever
// re-appearing once the client's optimistic "hide" prediction expired. Now the server owns the
// spawn (so it gets a real 'f...' id everyone including the requester can actually eat) — this
// cooldown map just stops a modified client from spamming the map with free food.
// `${playerId}:${kind}` -> next time (ms) that player is allowed to trigger that spawn again
const abilitySpawnCooldowns = new Map();

// Referees one "something dangerous just touched me" attempt. Re-checks flying/invuln/species/
// distance/cooldown server-side using its own stored copies before applying any damage — the
// reporting client is only ever trusted to say *what* touched it, not the damage or outcome.
function resolvePveBite(playerId, kind, id) {
  const player = players.get(playerId);
  if (!player || player.flying) return null;

  const now = Date.now();
  if (now < (player.invulnUntil || 0)) return null; // spawn-invulnerable

  if (kind === 'flame') {
    const patch = flamePatches.find(fp => fp.id === id);
    if (!patch || now >= patch.expiresAt) return null;
    const spec = PVP_SPECIES[player.species] || PVP_SPECIES.sparrow;
    const dist = Math.hypot(player.x - patch.x, player.y - patch.y);
    if (dist > PHOENIX_TRAIL_RADIUS + spec.radius) return null;
    const cdKey = playerId + '>flame:' + id;
    const nextAllowed = pveCooldowns.get(cdKey) || 0;
    if (now < nextAllowed) return null;
    pveCooldowns.set(cdKey, now + PHOENIX_BURN_TICK_COOLDOWN);
    const damage = Math.round(PHOENIX_TRAIL_DPS * (PHOENIX_BURN_TICK_COOLDOWN / 1000));
    player.hp = Math.max(0, (player.hp || 0) - damage);
    return { damage, poisonKey: null, hp: player.hp, maxHp: player.maxHp, x: patch.x, y: patch.y };
  }

  const arr = kind === 'food' ? food : prey;
  const item = arr.find(it => it.id === id);
  if (!item || item.collected) return null;

  let damage = 0, poisonKey = null;
  if (kind === 'food') {
    damage = ALWAYS_DANGEROUS_PREY[item.type] || 0;
    if (!damage) return null; // not a "stings everyone" food item
  } else {
    if (canEat(player.species, item.type)) return null; // only bites back if this bird can't eat it
    damage = DANGEROUS_PREY[item.type] || 0;
    if (POISON_SOURCES[item.type]) poisonKey = item.type;
    if (!damage && !poisonKey) return null;
  }

  const typeTable = kind === 'food' ? FOOD_TYPES : PREY_TYPES;
  const info = typeTable[item.type];
  const spec = PVP_SPECIES[player.species] || PVP_SPECIES.sparrow;
  const dist = Math.hypot(player.x - item.x, player.y - item.y);
  if (dist > spec.radius + info.size + 4) return null; // out of range

  const cdKey = playerId + '>' + kind + ':' + id;
  const nextAllowed = pveCooldowns.get(cdKey) || 0;
  if (now < nextAllowed) return null; // this player/item pair is still on cooldown
  pveCooldowns.set(cdKey, now + PVE_HIT_COOLDOWN);

  if (damage) player.hp = Math.max(0, (player.hp || 0) - damage);
  return { damage, poisonKey, hp: player.hp, maxHp: player.maxHp, x: item.x, y: item.y };
}

function clearPveCooldownsFor(id) {
  for (const key of pveCooldowns.keys()) {
    if (key.startsWith(id + '>')) pveCooldowns.delete(key);
  }
}
function clearAbilitySpawnCooldownsFor(id) {
  for (const key of abilitySpawnCooldowns.keys()) {
    if (key.startsWith(id + ':')) abilitySpawnCooldowns.delete(key);
  }
}

// ---------------- Special-ability PvP damage (server-authoritative) ----------------
// PHASE 4 of the "shared world" migration. Stork dash / pelican water bomb / cassowary
// kick / eagle drop deal damage to OTHER PLAYERS. Previously each victim's own client
// silently decided whether it got hit and subtracted its own hp — real, but a modified
// client could just skip that check and become immune to these abilities specifically
// (basic pecks were already safe from this since they go through resolvePvpHit). Now
// the *victim's* client still does the same local hit-detection (it already knows the
// attacker's broadcast state), but only to decide when to ask the server to referee —
// the server re-validates using its own stored copy of the attacker's ability state
// before applying any damage, exactly like resolvePvpHit/resolvePveBite above.
//
// Evolution scoring, seasons, ostrich eggs and the phoenix flame trail's continuous
// tick remain client-side for now — see the game's own code comments for why.
const ABILITY_DASH_DAMAGE = 170;
const ABILITY_WATER_DAMAGE = 500;
const ABILITY_KICK_DAMAGE = 2000;
const ABILITY_EAGLE_DROP_DAMAGE = 850;
const ABILITY_WATER_RADIUS = 110;
const ABILITY_KICK_RANGE = 46;   // extra reach beyond the two birds' radii
const ABILITY_KICK_WINDOW = 380; // ms, matches the client's CASSOWARY_KICK_WINDOW
const ABILITY_DASH_WINDOW = 150; // ms, matches the client's dashUntil+150 grace window

// `${targetId}>${attackerId}:${kind}` -> the last ability-activation id already applied,
// so the same dash/splash/kick/drop can't be reported (and paid out) more than once.
const abilityHitLog = new Map();

function resolveAbilityHit(targetId, attackerId, kind) {
  if (!targetId || !attackerId || targetId === attackerId) return null;
  const target = players.get(targetId);
  const attacker = players.get(attackerId);
  if (!target || !attacker) return null;
  if (target.flying) return null;

  const now = Date.now();
  if (now < (target.invulnUntil || 0)) return null; // target is spawn-invulnerable

  const tSpec = PVP_SPECIES[target.species] || PVP_SPECIES.sparrow;
  const aSpec = PVP_SPECIES[attacker.species] || PVP_SPECIES.sparrow;

  let damage = 0, instanceId = 0, applyKnockback = false;
  if (kind === 'dash') {
    if (attacker.species !== 'stork' || !attacker.dashActive) return null;
    if (now >= (attacker.dashUntil || 0) + ABILITY_DASH_WINDOW) return null;
    const dist = Math.hypot(attacker.x - target.x, attacker.y - target.y);
    if (dist > tSpec.radius + aSpec.radius + 20) return null;
    damage = ABILITY_DASH_DAMAGE; instanceId = attacker.dashId; applyKnockback = true;
  } else if (kind === 'water') {
    if (attacker.species !== 'pelican' || !attacker.waterId) return null;
    if (now >= (attacker.waterUntil || 0)) return null;
    const dist = Math.hypot(attacker.waterX - target.x, attacker.waterY - target.y);
    if (dist > ABILITY_WATER_RADIUS + tSpec.radius) return null;
    damage = ABILITY_WATER_DAMAGE; instanceId = attacker.waterId;
  } else if (kind === 'kick') {
    if (attacker.species !== 'cassowary' || !attacker.cassowaryKickId) return null;
    if (now >= (attacker.cassowaryKickAt || 0) + ABILITY_KICK_WINDOW) return null;
    const dist = Math.hypot(attacker.x - target.x, attacker.y - target.y);
    if (dist > tSpec.radius + aSpec.radius + ABILITY_KICK_RANGE) return null;
    damage = ABILITY_KICK_DAMAGE; instanceId = attacker.cassowaryKickId; applyKnockback = true;
  } else if (kind === 'eagleDrop') {
    if (attacker.species !== 'eagle' || !attacker.eagleDropId) return null;
    if (attacker.eagleCarryKey !== targetId) return null; // must actually be carrying THIS target
    damage = ABILITY_EAGLE_DROP_DAMAGE; instanceId = attacker.eagleDropId;
  } else {
    return null;
  }
  if (!instanceId) return null;

  const dedupKey = targetId + '>' + attackerId + ':' + kind;
  if (abilityHitLog.get(dedupKey) === instanceId) return null; // this exact activation was already paid out
  abilityHitLog.set(dedupKey, instanceId);

  target.hp = Math.max(0, (target.hp || 0) - damage);
  return { damage, hp: target.hp, maxHp: target.maxHp, x: attacker.x, y: attacker.y, knockback: applyKnockback };
}

function clearAbilityHitLogFor(id) {
  for (const key of abilityHitLog.keys()) {
    if (key.startsWith(id + '>') || key.includes('>' + id + ':')) abilityHitLog.delete(key);
  }
}

// ---------------- Shared season / day-night / time overrides (server-authoritative) ----------------
// PHASE 5. The default wall-clock season cycle was already the same for every client (a pure
// function of Date.now()) — no server involvement needed there. What WASN'T shared: the game's
// built-in "/admin" debug commands (force a season, eternal summer, force day/night, speed up
// time). Those only ever changed state on whichever client typed them. The server now holds
// this as shared state and broadcasts it to everyone, so a forced season/day-night is the same
// for every connected player, not just its own little bubble.
//
// Note: there's still no access control on these commands — anyone can type them. This phase
// only makes their *effect* consistent across players; it doesn't add permissions.
let seasonOverride = null;   // { key, startedAt } | null — manual season force (server epoch ms)
let eternalSummer = false;
let dayNightOverride = null; // { phase, startedAt } | null
let gameTimeMult = 1;

const SEASON_DURATIONS = { summer: 240 * 60000, winter: 120 * 60000, cold_winter: 120 * 60000 };
const DAYNIGHT_DURATIONS = {
  summer:      { day: 15 * 60000, night: 9 * 60000 },
  winter:      { day: 11 * 60000, night: 14 * 60000 },
  cold_winter: { day: 8 * 60000,  night: 16 * 60000 },
};

function worldTimeState() {
  return { seasonOverride, eternalSummer, dayNightOverride, gameTimeMult };
}

// Manual overrides auto-expire after their normal duration, same as the client always did locally.
setInterval(() => {
  const now = Date.now();
  let changed = false;
  if (seasonOverride) {
    const dur = SEASON_DURATIONS[seasonOverride.key] || SEASON_DURATIONS.summer;
    if (now - seasonOverride.startedAt >= dur) { seasonOverride = null; changed = true; }
  }
  if (dayNightOverride) {
    const seasonKey = seasonOverride ? seasonOverride.key : 'summer';
    const c = DAYNIGHT_DURATIONS[seasonKey] || DAYNIGHT_DURATIONS.summer;
    const dur = dayNightOverride.phase === 'day' ? c.day : c.night;
    if (now - dayNightOverride.startedAt >= dur) { dayNightOverride = null; changed = true; }
  }
  if (changed) io.emit('worldTime', worldTimeState());
}, 5000);

io.on('connection', (socket) => {
  console.log('[+] connected', socket.id);

  socket.on('join', (data) => {
    const p = sanitize(data);
    players.set(socket.id, p);

    // Give the newcomer a snapshot of everyone already in the world.
    const state = {};
    for (const [id, pl] of players) state[id] = pl;
    socket.emit('state', state);

    // ...and the authoritative food/prey world, so every client renders the same map.
    socket.emit('worldState', { food, prey, eggs: ostrichEggs, flames: flamePatches });

    // ...and whatever season/day-night/time override is currently in effect for everyone.
    socket.emit('worldTime', worldTimeState());

    // Tell everyone else the newcomer arrived.
    socket.broadcast.emit('playerUpdate', { id: socket.id, ...p });
  });

  // Caps how often we FAN OUT a given player's movement to everyone else — not how
  // often we accept it. `players.set()` below always runs at full rate so distance
  // checks elsewhere (eating, PvP, abilities) stay accurate; only the O(n) broadcast
  // to every other connected socket is capped, since that's what turns into O(n²)
  // total traffic as the player count grows.
  socket.on('update', (data) => {
    if (!players.has(socket.id)) return; // must join first
    const p = sanitize(data);
    players.set(socket.id, p);
    const now = Date.now();
    if (now - (lastBroadcastAt.get(socket.id) || 0) < UPDATE_BROADCAST_MIN_INTERVAL_MS) return;
    lastBroadcastAt.set(socket.id, now);
    socket.broadcast.emit('playerUpdate', { id: socket.id, ...p });
  });

  // A player claiming to be the (bigger) attacker asks the server to referee a hit
  // on `targetId`. The server independently re-checks distance, size and cooldown
  // using its own stored copy of both players' state before applying any damage —
  // the reporting client is never trusted for the damage amount or the outcome.
  socket.on('pvpHit', (data) => {
    const targetId = data && typeof data.targetId === 'string' ? data.targetId : null;
    const result = resolvePvpHit(socket.id, targetId);
    if (!result) return;

    const target = players.get(targetId);

    // Tell the victim's own client the authoritative damage it just took, so it
    // (and only it) applies the hp loss to itself — this is the one and only
    // place PvP hp changes now happen; the victim's client no longer computes
    // this on its own.
    io.to(targetId).emit('pvpDamage', {
      from: socket.id,
      damage: result.damage,
      hp: result.targetHp,
      maxHp: result.targetMaxHp,
    });

    // Let the attacker show a damage number over the target immediately, without
    // waiting for the target's next periodic position update.
    socket.emit('pvpHitResult', {
      targetId,
      damage: result.damage,
      targetHp: result.targetHp,
      targetX: target.x,
      targetY: target.y,
    });

    // Broadcast the target's updated hp to everyone else right away (their own
    // next 'update' would carry it anyway, but this keeps leaderboards/HP bars
    // on other clients from lagging behind by up to one update tick).
    socket.broadcast.emit('playerUpdate', { id: targetId, ...target });
  });

  // A player claiming to be within reach of a food/prey item asks the server to
  // referee eating it. The server independently re-checks the player's species,
  // distance, and item state before marking anything collected — same trust model
  // as pvpHit above. Score/heal/poison from the eat are still applied by the
  // requester's own client once it gets 'eatResult' back (Phase 2 will move that
  // math server-side too).
  socket.on('eatItem', (data) => {
    const player = players.get(socket.id);
    if (!player) return;
    const kind = data && data.kind === 'prey' ? 'prey' : 'food';
    const id = data && typeof data.id === 'string' ? data.id : null;
    if (!id) return;

    const result = resolveEat(player, kind, id);
    if (!result) return;

    io.emit(kind === 'food' ? 'foodUpdate' : 'preyUpdate', result.item);
    if (!result.partial) {
      socket.emit('eatResult', { kind, id, type: result.type, points: result.points });
    }
  });

  // Pigeon's dig ability: drops 1-4 bread around the pigeon once its dig animation
  // finishes (the client tells us only when digging completed — timing/cooldown UI stays
  // client-side, this just makes the resulting food a real, eatable, server-owned item).
  // 16000ms mirrors the client's ABILITY_COOLDOWN.pigeon; only guards against a modified
  // client spamming this event, since the client's own cooldown already paces normal play.
  socket.on('pigeonDig', () => {
    const player = players.get(socket.id);
    if (!player || player.species !== 'pigeon') return;
    const now = Date.now();
    const cdKey = socket.id + ':pigeonDig';
    if (now < (abilitySpawnCooldowns.get(cdKey) || 0)) return;
    abilitySpawnCooldowns.set(cdKey, now + 16000);

    const count = 1 + Math.floor(Math.random() * 4);
    for (let i = 0; i < count; i++) {
      const a = Math.random() * Math.PI * 2;
      const r = 20 + Math.random() * 46;
      const item = spawnFoodItemAt('bread', player.x + Math.cos(a) * r, player.y + Math.sin(a) * r);
      food.push(item);
      io.emit('foodUpdate', item);
    }
  });

  // Crow's ability payoff: meat carried in the beak shatters into 5 apples the instant the
  // crow takes off. Same reasoning as pigeonDig above — server owns the spawn so it's a real,
  // eatable item. 15000ms mirrors the client's ABILITY_COOLDOWN.crow.
  socket.on('crowShatterMeat', () => {
    const player = players.get(socket.id);
    if (!player || player.species !== 'crow') return;
    const now = Date.now();
    const cdKey = socket.id + ':crowShatterMeat';
    if (now < (abilitySpawnCooldowns.get(cdKey) || 0)) return;
    abilitySpawnCooldowns.set(cdKey, now + 15000);

    for (let i = 0; i < 5; i++) {
      const a = (Math.PI * 2 * i / 5) + Math.random() * 0.5;
      const r = 26 + Math.random() * 34;
      const item = spawnFoodItemAt('apple', player.x + Math.cos(a) * r, player.y + Math.sin(a) * r);
      food.push(item);
      io.emit('foodUpdate', item);
    }
  });

  // A player reporting that dangerous prey/food/fire just touched them asks the server to
  // referee the hit. Same trust model as pvpHit/eatItem — the server independently
  // re-checks distance, cooldown and whether this bird can even be hurt by it.
  socket.on('pveBite', (data) => {
    const kind = data && (data.kind === 'prey' || data.kind === 'flame') ? data.kind : 'food';
    const id = data && typeof data.id === 'string' ? data.id : null;
    if (!id) return;
    const result = resolvePveBite(socket.id, kind, id);
    if (!result) return;
    socket.emit('pveHit', { kind, id, ...result });
  });

  // Ostrich lays an egg where it's currently standing.
  socket.on('layEgg', () => {
    const egg = layEgg(socket.id);
    if (!egg) return;
    io.emit('eggSpawn', egg);
  });

  // Cassowary/phoenix eats a specific egg.
  socket.on('eatEgg', (data) => {
    const id = data && typeof data.id === 'string' ? data.id : null;
    if (!id) return;
    const egg = eatEgg(socket.id, id);
    if (!egg) return;
    io.emit('eggRemove', { id: egg.id });
    socket.emit('eatResult', { kind: 'egg', type: 'ostrichEgg', points: OSTRICH_EGG_POINTS_EATER });
  });

  // Phoenix arms its fire trail ability.
  socket.on('armPhoenixTrail', () => {
    armPhoenixTrail(socket.id);
  });

  // Phoenix (while armed & flying) drops one flame patch at its current position.
  socket.on('dropFlamePatch', () => {
    const patch = dropFlamePatch(socket.id);
    if (!patch) return;
    io.emit('flamePatchAdd', patch);
  });

  // The reporting client is the potential VICTIM of a special-ability hit (it already
  // did its own local hit-detection against the attacker's broadcast state to decide
  // when to ask). The server re-validates using its own stored copy of the attacker's
  // state before applying any damage — the reporting client can't inflate the damage
  // or fake an activation that didn't happen.
  socket.on('abilityHit', (data) => {
    const attackerId = data && typeof data.attackerId === 'string' ? data.attackerId : null;
    const kind = data && typeof data.kind === 'string' ? data.kind : null;
    if (!attackerId || !kind) return;
    const result = resolveAbilityHit(socket.id, attackerId, kind);
    if (!result) return;
    socket.emit('abilityHitResult', { kind, attackerId, ...result });
  });

  // Admin debug commands (see the shared season/day-night/time-override block above).
  // No permission check exists here (matching the client's own unauthenticated /admin
  // commands) — this only ensures the *effect*, once triggered by anyone, is the same
  // world for every connected player instead of a local-only bubble.
  socket.on('adminSetSeason', (data) => {
    const key = data && typeof data.key === 'string' ? data.key : null;
    if (!key || !SEASON_DURATIONS[key]) return;
    eternalSummer = false;
    seasonOverride = { key, startedAt: Date.now() };
    io.emit('worldTime', worldTimeState());
  });
  socket.on('adminEternalSummer', () => {
    eternalSummer = true;
    seasonOverride = null;
    io.emit('worldTime', worldTimeState());
  });
  socket.on('adminSetDayNight', (data) => {
    const phase = data && (data.phase === 'day' || data.phase === 'night') ? data.phase : null;
    if (!phase) return;
    dayNightOverride = { phase, startedAt: Date.now() };
    io.emit('worldTime', worldTimeState());
  });
  socket.on('adminSetTimeMult', (data) => {
    const value = Number(data && data.value);
    if (!Number.isFinite(value) || value < 0) return;
    gameTimeMult = value;
    io.emit('worldTime', worldTimeState());
  });

  socket.on('chat', (text) => {
    const p = players.get(socket.id);
    if (!p || typeof text !== 'string') return;
    const clean = text.slice(0, 200).trim();
    if (!clean) return;
    io.emit('chat', { name: p.name, text: clean, ts: Date.now() });
  });

  socket.on('disconnect', () => {
    players.delete(socket.id);
    lastBroadcastAt.delete(socket.id);
    clearPvpCooldownsFor(socket.id);
    clearPveCooldownsFor(socket.id);
    clearAbilityHitLogFor(socket.id);
    clearAbilitySpawnCooldownsFor(socket.id);
    io.emit('playerLeft', socket.id);
    console.log('[-] disconnected', socket.id);
  });
});

// pvpCooldowns/pveCooldowns entries are just "next allowed timestamp" values that
// are useless once that timestamp has passed — clearPvpCooldownsFor/clearPveCooldownsFor
// only run per-player on disconnect, so on a long-running server with players who
// stay connected for hours these would otherwise just keep accumulating stale
// already-expired entries (a slow memory creep, and slightly more work for every
// future cooldown lookup). Sweep them out periodically instead.
setInterval(() => {
  const now = Date.now();
  for (const [key, nextAllowed] of pvpCooldowns) if (now >= nextAllowed) pvpCooldowns.delete(key);
  for (const [key, nextAllowed] of pveCooldowns) if (now >= nextAllowed) pveCooldowns.delete(key);
  for (const [key, nextAllowed] of abilitySpawnCooldowns) if (now >= nextAllowed) abilitySpawnCooldowns.delete(key);
}, 60000);

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`Bird game server listening on http://localhost:${PORT}`);
});
