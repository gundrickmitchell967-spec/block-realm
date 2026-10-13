# Block Realm multiplayer server

This folder runs Block Realm for several players at once. The server keeps the shared world
(every block anyone has broken or placed), shows players to each other, and serves the game page.

## Run it

1. Install Node.js 18 or newer from https://nodejs.org
2. In this folder, install the one dependency:

       npm install

3. Start the server:

       npm start

4. Open http://localhost:8080 in a browser. Choose MULTIPLAYER, enter a name, and press CONNECT.
   Open the same address in a second browser window to play with yourself.

To let people on your local network join, give them your computer's address, for example
http://192.168.1.20:8080. Players outside your network need the server running on a host that
accepts incoming connections (a server or a hosting service that runs Node.js and allows WebSockets).
Forwarding port 8080 on your router also works.

## Settings (environment variables)

| Variable      | Default                 | What it does                                  |
|---------------|-------------------------|-----------------------------------------------|
| `PORT`        | `8080`                  | Port the server listens on                    |
| `HOST`        | `0.0.0.0`               | Address to listen on                          |
| `MAX_PLAYERS` | `16`                    | Most players connected at once                |
| `WORLD_FILE`  | `world.json` next to server.js | Where the shared block changes are saved |

Example: `PORT=9000 MAX_PLAYERS=8 npm start`

## Notes

- The shared world is saved to `world.json` a couple of seconds after each change, and when the
  server is stopped with Ctrl+C. Delete that file to start over with a fresh world.
- Terrain is generated in each player's browser from a fixed seed, so only block changes are stored.
- There are no accounts or passwords. Anyone who can reach the server can join and change blocks.
  Only run it for people you trust, or add a password before putting it on the open internet.
- Block changes further than 12 blocks from a player's last reported position are ignored.
- Single-player still works without the server; it keeps its own saved world in the browser.
