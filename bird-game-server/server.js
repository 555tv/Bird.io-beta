// Minimal multiplayer server for the bird game.
// Responsibilities (kept intentionally small):
//   1. Serve the game's static files (public/index.html and friends).
//   2. Keep a live list of connected players (position, hp, species, angle...).
//   3. Broadcast every player's updates to everyone else in real time via WebSocket.
//   4. Relay chat messages.
//
// This server does NOT validate movement, hits, or eating — every client is still
// trusted for its own physics (same as before). It only makes players visible to
// each other. See README.md for how this could grow into a fully authoritative
// server later.

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
  };
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

  socket.on('chat', (text) => {
    const p = players.get(socket.id);
    if (!p || typeof text !== 'string') return;
    const clean = text.slice(0, 200).trim();
    if (!clean) return;
    io.emit('chat', { name: p.name, text: clean, ts: Date.now() });
  });

  socket.on('disconnect', () => {
    players.delete(socket.id);
    io.emit('playerLeft', socket.id);
    console.log('[-] disconnected', socket.id);
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`Bird game server listening on http://localhost:${PORT}`);
});
