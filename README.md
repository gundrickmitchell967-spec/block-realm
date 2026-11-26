# HOMELINK — Private Family Hub

A private family app built with HTML, CSS, and JavaScript, backed by Supabase.

## Project structure

```
index.html          Main entry point
css/styles.css      All styling
js/config.js        Public Supabase settings (URL + anon key)
js/preferences.js   Per-user settings storage
js/services.js      Data layer (the only file that talks to the backend)
js/app.js           UI controller
```

## Run locally

No build step is needed. Open `index.html` in a browser, or run a local server:

```
python3 -m http.server 8000
```

Then visit http://localhost:8000

## Deploy

Pushing to the `main` branch on GitHub automatically publishes the site through Cloudflare Pages.

## Security rules

- Never commit `service_role` keys, passwords, or `.env` files.
- The Supabase anon key may be public, but every table must have Row Level Security enabled.
- The current login is a development placeholder. Do not use real family data until Supabase Auth is connected.
