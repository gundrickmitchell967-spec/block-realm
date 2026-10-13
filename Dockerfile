# Builds the Block Realm server into a container image.
FROM node:22-alpine
WORKDIR /app
COPY package.json ./
RUN npm install --omit=dev
COPY server.js ./
COPY index.html ./public/index.html
# Saved world changes go in /data, which should be a persistent volume on the host.
ENV PORT=8080 HOST=0.0.0.0 WORLD_FILE=/data/world.json
EXPOSE 8080
CMD ["node", "server.js"]
