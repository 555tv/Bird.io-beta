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
  cors: { origin: '*' } // relax CORS since the client may be hosted separately during development
});

app.use(express.static(path.join(__dirname, 'public')));

// socket.id -> player state
const players = new Map();

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
  sparrow:    { radius: 15,  attack: 0 },
  pigeon:     { radius: 23,  attack: 20 },
  crow:       { radius: 32,  attack: 50 },
  stork:      { radius: 42,  attack: 100 },
  owl:        { radius: 52,  attack: 180 },
  hawk:       { radius: 64,  attack: 350 },
  pelican:    { radius: 70,  attack: 550 },
  eagle:      { radius: 78,  attack: 850 },
  griffin:    { radius: 86,  attack: 1500 },
  blackgoose: { radius: 94,  attack: 2500 },
  ostrich:    { radius: 102, attack: 3850 },
  cassowary:  { radius: 110, attack: 5600 },
  phoenix:    { radius: 118, attack: 8900 },
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

io.on('connection', (socket) => {
  console.log('[+] connected', socket.id);

  socket.on('join', (data) => {
    const p = sanitize(data);
    players.set(socket.id, p);

    // Give the newcomer a snapshot of everyone already in the world.
    const state = {};
    for (const [id, pl] of players) state[id] = pl;
    socket.emit('state', state);

    // Tell everyone else the newcomer arrived.
    socket.broadcast.emit('playerUpdate', { id: socket.id, ...p });
  });

  socket.on('update', (data) => {
    if (!players.has(socket.id)) return; // must join first
    const p = sanitize(data);
    players.set(socket.id, p);
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

  socket.on('chat', (text) => {
    const p = players.get(socket.id);
    if (!p || typeof text !== 'string') return;
    const clean = text.slice(0, 200).trim();
    if (!clean) return;
    io.emit('chat', { name: p.name, text: clean, ts: Date.now() });
  });

  socket.on('disconnect', () => {
    players.delete(socket.id);
    clearPvpCooldownsFor(socket.id);
    io.emit('playerLeft', socket.id);
    console.log('[-] disconnected', socket.id);
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`Bird game server listening on http://localhost:${PORT}`);
});
