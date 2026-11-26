/* =========================================================
   HOMELINK — Application controller
   Handles login state, navigation, rendering, fullscreen,
   personal settings, chores, and messaging interface.
   UI logic only: data comes from HomeLinkServices and
   preferences from HomeLinkPrefs.
   ========================================================= */

(() => {
  const S = HomeLinkServices;
  const P = HomeLinkPrefs;

  const state = {
    user: null,
    prefs: null,
    family: [],
    chores: [],
    completions: {},
    activeTab: "home",
    messagesTab: "group",     // "group" | "private"
    activeDM: null,           // family member id for a private chat
    contactQuery: "",
  };

  // ---------- Icons (inline SVG, no external dependency) ----------
  const ICON = {
    home:     '<path d="M3 10.5 12 3l9 7.5"/><path d="M5 9.5V21h14V9.5"/>',
    chat:     '<path d="M21 12a8 8 0 0 1-11.6 7.1L4 20l1-4.6A8 8 0 1 1 21 12z"/>',
    users:    '<circle cx="9" cy="8" r="3.5"/><path d="M2.5 20a6.5 6.5 0 0 1 13 0"/><path d="M16 4.5a3.5 3.5 0 0 1 0 7"/><path d="M21.5 20a6.5 6.5 0 0 0-4-6"/>',
    grid:     '<rect x="3" y="3" width="7.5" height="7.5" rx="2"/><rect x="13.5" y="3" width="7.5" height="7.5" rx="2"/><rect x="3" y="13.5" width="7.5" height="7.5" rx="2"/><rect x="13.5" y="13.5" width="7.5" height="7.5" rx="2"/>',
    settings: '<circle cx="12" cy="12" r="3"/><path d="M19.4 15a1.7 1.7 0 0 0 .3 1.8l.1.1a2 2 0 1 1-2.8 2.8l-.1-.1a1.7 1.7 0 0 0-1.8-.3 1.7 1.7 0 0 0-1 1.5V21a2 2 0 1 1-4 0v-.1a1.7 1.7 0 0 0-1.1-1.5 1.7 1.7 0 0 0-1.8.3l-.1.1a2 2 0 1 1-2.8-2.8l.1-.1a1.7 1.7 0 0 0 .3-1.8 1.7 1.7 0 0 0-1.5-1H3a2 2 0 1 1 0-4h.1a1.7 1.7 0 0 0 1.5-1.1 1.7 1.7 0 0 0-.3-1.8l-.1-.1a2 2 0 1 1 2.8-2.8l.1.1a1.7 1.7 0 0 0 1.8.3H9a1.7 1.7 0 0 0 1-1.5V3a2 2 0 1 1 4 0v.1a1.7 1.7 0 0 0 1 1.5 1.7 1.7 0 0 0 1.8-.3l.1-.1a2 2 0 1 1 2.8 2.8l-.1.1a1.7 1.7 0 0 0-.3 1.8V9a1.7 1.7 0 0 0 1.5 1H21a2 2 0 1 1 0 4h-.1a1.7 1.7 0 0 0-1.5 1z"/>',
    expand:   '<path d="M8 3H5a2 2 0 0 0-2 2v3"/><path d="M16 3h3a2 2 0 0 1 2 2v3"/><path d="M8 21H5a2 2 0 0 1-2-2v-3"/><path d="M16 21h3a2 2 0 0 0 2-2v-3"/>',
    shrink:   '<path d="M9 3v3a2 2 0 0 1-2 2H4"/><path d="M15 3v3a2 2 0 0 0 2 2h3"/><path d="M9 21v-3a2 2 0 0 0-2-2H4"/><path d="M15 21v-3a2 2 0 0 1 2-2h3"/>',
    logout:   '<path d="M15 3h4a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2h-4"/><path d="M10 17l5-5-5-5"/><path d="M15 12H3"/>',
    search:   '<circle cx="11" cy="11" r="7"/><path d="M21 21l-4.3-4.3"/>',
    send:     '<path d="M22 2 11 13"/><path d="M22 2 15 22l-4-9-9-4z"/>',
    plus:     '<path d="M12 5v14M5 12h14"/>',
    check:    '<path d="M20 6 9 17l-5-5"/>',
    camera:   '<path d="M23 19a2 2 0 0 1-2 2H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h4l2-3h6l2 3h4a2 2 0 0 1 2 2z"/><circle cx="12" cy="13" r="4"/>',
    image:    '<rect x="3" y="3" width="18" height="18" rx="3"/><circle cx="8.5" cy="8.5" r="1.5"/><path d="M21 15l-5-5L5 21"/>',
    chevron:  '<path d="M9 18l6-6-6-6"/>',
    book:     '<path d="M4 19.5A2.5 2.5 0 0 1 6.5 17H20V3H6.5A2.5 2.5 0 0 0 4 5.5z"/><path d="M4 19.5A2.5 2.5 0 0 0 6.5 22H20v-5"/>',
    calendar: '<rect x="3" y="4" width="18" height="18" rx="3"/><path d="M16 2v4M8 2v4M3 10h18"/>',
    cart:     '<circle cx="9" cy="21" r="1"/><circle cx="20" cy="21" r="1"/><path d="M1 1h4l2.7 13.4a2 2 0 0 0 2 1.6h9.7a2 2 0 0 0 2-1.6L23 6H6"/>',
    phone:    '<path d="M22 16.9v3a2 2 0 0 1-2.2 2 19.8 19.8 0 0 1-8.6-3.1 19.5 19.5 0 0 1-6-6A19.8 19.8 0 0 1 2.1 4.2 2 2 0 0 1 4.1 2h3a2 2 0 0 1 2 1.7c.1.9.4 1.8.7 2.7a2 2 0 0 1-.5 2.1L8 9.8a16 16 0 0 0 6 6l1.3-1.3a2 2 0 0 1 2.1-.4c.9.3 1.8.6 2.7.7a2 2 0 0 1 1.7 2z"/>',
    lock:     '<rect x="4" y="11" width="16" height="10" rx="2"/><path d="M8 11V7a4 4 0 0 1 8 0v4"/>',
    eye:      '<path d="M1 12s4-7 11-7 11 7 11 7-4 7-11 7S1 12 1 12z"/><circle cx="12" cy="12" r="3"/>',
    info:     '<circle cx="12" cy="12" r="10"/><path d="M12 16v-4M12 8h.01"/>',
    pen:      '<path d="M12 20h9"/><path d="M16.5 3.5a2.1 2.1 0 0 1 3 3L7 19l-4 1 1-4z"/>',
  };
  const icon = (name, cls = "") =>
    `<svg class="icon ${cls}" viewBox="0 0 24 24" aria-hidden="true">${ICON[name] || ""}</svg>`;

  // ---------- Element helpers ----------
  const $ = (sel, root = document) => root.querySelector(sel);
  const $$ = (sel, root = document) => Array.from(root.querySelectorAll(sel));
  const esc = (s) => String(s ?? "").replace(/[&<>"']/g, c =>
    ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));

  const initials = (name) => String(name).trim().split(/\s+/).map(w => w[0]).slice(0, 2).join("").toUpperCase();

  function avatarHTML(member, size = "") {
    const isMe = state.user && member.id === state.user.id;
    const p = isMe ? state.prefs : null;
    const img = p && p.avatarData ? `background-image:url('${p.avatarData}')` : "";
    const label = p && p.avatarData ? "" : esc(initials(isMe && p?.displayName ? p.displayName : member.name));
    return `<div class="avatar ${member.color} ${size}" style="${img}" aria-hidden="true">${label}</div>`;
  }

  function displayName(member) {
    if (state.user && member.id === state.user.id && state.prefs.displayName) return state.prefs.displayName;
    return member.name;
  }

  function toast(msg) {
    const el = $("#toast");
    el.textContent = msg;
    el.classList.add("show");
    clearTimeout(toast._t);
    toast._t = setTimeout(() => el.classList.remove("show"), 2200);
  }

  function haptic() {
    if (state.prefs?.sound && navigator.vibrate) navigator.vibrate(8);
  }

  // ---------- Theme & wallpaper ----------
  function applyPrefs() {
    const p = state.prefs;
    const root = document.documentElement;
    root.setAttribute("data-theme", p.theme === "light" ? "light" : "dark");

    const app = $("#app");
    if (p.wallpaper === "custom" && p.wallpaperData) {
      root.style.setProperty("--wallpaper", `url('${p.wallpaperData}')`);
      app.classList.add("has-wallpaper");
    } else if (p.wallpaper === "gradient") {
      root.style.setProperty("--wallpaper",
        "radial-gradient(900px 600px at 20% 0%, rgba(124,156,255,.45), transparent 60%), radial-gradient(700px 500px at 100% 100%, rgba(167,139,250,.4), transparent 60%)");
      app.classList.add("has-wallpaper");
    } else {
      root.style.setProperty("--wallpaper", "none");
      app.classList.remove("has-wallpaper");
    }
  }

  // ---------- Login ----------
  function renderFamilyPicker() {
    const picker = $("#family-picker");
    picker.innerHTML = state.family.map(m => `
      <button type="button" class="member-chip" data-name="${esc(m.name)}" aria-label="Sign in as ${esc(m.name)}">
        ${avatarHTML(m, "sm")}
        <span>${esc(m.name)}</span>
      </button>`).join("");
  }

  function showLogin() {
    $("#login-screen").classList.remove("hidden", "leaving");
    $("#app-shell").classList.add("hidden");
    setTimeout(() => $("#login-username").focus({ preventScroll: true }), 300);
  }

  async function handleLogin(e) {
    e.preventDefault();
    const btn = $("#login-submit");
    const err = $("#login-error");
    err.textContent = "";
    btn.disabled = true;
    btn.textContent = "Signing in…";

    try {
      const { user } = await S.signIn({
        username: $("#login-username").value,
        password: $("#login-password").value,
        remember: $("#remember-me").checked,
      });
      await enterApp(user);
    } catch (ex) {
      err.textContent = ex.message || "Sign in failed. Please try again.";
      btn.disabled = false;
      btn.textContent = "Sign in";
    }
  }

  // ---------- Enter / leave app ----------
  async function enterApp(user) {
    state.user = user;
    state.prefs = P.load(user.id);
    applyPrefs();

    const [family, chores, completions] = await Promise.all([
      S.getFamilyMembers(),
      S.getChores(),
      S.getCompletions(user.id),
    ]);
    state.family = family;
    state.chores = chores;
    state.completions = completions;

    $("#login-screen").classList.add("leaving");
    setTimeout(() => $("#login-screen").classList.add("hidden"), 500);
    $("#app-shell").classList.remove("hidden");

    renderAll();
    switchTab("home");

    if (state.prefs.fullscreenOnLaunch) {
      toast("Tap the expand button for fullscreen");
    }
  }

  async function handleLogout() {
    await S.signOut();
    state.user = null;
    state.prefs = null;
    document.documentElement.removeAttribute("data-theme");
    document.documentElement.style.removeProperty("--wallpaper");
    $("#app").classList.remove("has-wallpaper");
    $("#login-password").value = "";
    $("#login-error").textContent = "";
    closeSheet();
    showLogin();
    renderFamilyPicker();
  }

  // ---------- Navigation ----------
  const TABS = {
    home:     { title: "Home",     eyebrow: null },
    messages: { title: "Messages", eyebrow: "Family" },
    contacts: { title: "Contacts", eyebrow: "Family" },
    resources:{ title: "Resources",eyebrow: "Shared" },
    settings: { title: "Settings", eyebrow: "Personal" },
  };

  function switchTab(tab) {
    if (!TABS[tab]) return;
    state.activeTab = tab;

    $$(".view").forEach(v => v.classList.toggle("active", v.dataset.view === tab));
    $$(".nav-item").forEach(b => {
      const on = b.dataset.tab === tab;
      b.classList.toggle("active", on);
      b.setAttribute("aria-current", on ? "page" : "false");
    });

    $("#view-container").scrollTop = 0;
    $("#topbar-title").textContent = TABS[tab].title;
    const eyebrow = $("#topbar-eyebrow");
    if (tab === "home") {
      eyebrow.textContent = greeting();
    } else {
      eyebrow.textContent = TABS[tab].eyebrow;
    }

    if (tab === "messages") renderMessages();
    if (tab === "contacts") renderContacts();
    if (tab === "resources") renderResources();
    if (tab === "settings") renderSettings();
    if (tab === "home") renderHome();
    haptic();
  }

  function greeting() {
    const h = new Date().getHours();
    const part = h < 12 ? "Good morning" : h < 18 ? "Good afternoon" : "Good evening";
    return `${part}, ${displayName(state.user)}`;
  }

  // ---------- Home ----------
  function renderHome() {
    const first = displayName(state.user).split(" ")[0];
    const myDone = Object.values(state.completions).filter(Boolean).length;
    const myChores = state.chores.filter(c => c.assignee === state.user.id);
    const myCompleted = myChores.filter(c => state.completions[c.id]).length;
    const online = state.family.filter(m => m.online).length;

    $("#home-hero").innerHTML = `
      <div class="eyebrow">${esc(new Date().toLocaleDateString(undefined, { weekday: "long", month: "long", day: "numeric" }))}</div>
      <h2>Welcome home, ${esc(first)}</h2>
      <p>${myCompleted} of ${myChores.length} of your chores done today. ${online} family members online.</p>`;

    $("#home-stats").innerHTML = `
      <div class="stat">
        <div class="ico">${icon("check")}</div>
        <div class="num">${myCompleted}/${myChores.length}</div>
        <div class="label">My chores</div>
      </div>
      <div class="stat">
        <div class="ico">${icon("users")}</div>
        <div class="num">${state.family.length}</div>
        <div class="label">Family members</div>
      </div>`;

    $("#home-quick").innerHTML = [
      { t: "tab", v: "messages", ic: "chat", label: "Messages" },
      { t: "tab", v: "contacts", ic: "users", label: "Contacts" },
      { t: "tab", v: "resources", ic: "grid", label: "Chores" },
      { t: "tab", v: "settings", ic: "settings", label: "Settings" },
    ].map(q => `
      <button class="quick-item" data-go="${q.v}" type="button">
        <span class="qi-ico">${icon(q.ic)}</span>
        <span>${q.label}</span>
      </button>`).join("");

    const todays = state.chores.slice(0, 3);
    $("#home-chores").innerHTML = todays.length ? `
      <div class="list">
        ${todays.map(c => {
          const who = state.family.find(m => m.id === c.assignee);
          const done = !!state.completions[c.id];
          return `
          <div class="row">
            <div class="grow">
              <div class="title" style="${done ? "text-decoration:line-through;color:var(--text-faint)" : ""}">${esc(c.title)}</div>
              <div class="sub">${who ? esc(displayName(who)) : ""}</div>
            </div>
            <span class="badge ${done ? "online" : ""}">${done ? "Done" : "To do"}</span>
          </div>`;
        }).join("")}
      </div>` : `<div class="card">No chores yet.</div>`;
  }

  // ---------- Messages ----------
  async function renderMessages() {
    const seg = $("#msg-segmented");
    seg.querySelectorAll("button").forEach(b =>
      b.classList.toggle("active", b.dataset.msg === state.messagesTab));

    $("#msg-group").classList.toggle("hidden", state.messagesTab !== "group");
    $("#msg-private").classList.toggle("hidden", state.messagesTab !== "private");

    if (state.messagesTab === "group") {
      await renderThread("group", $("#group-bubbles"));
    } else {
      renderPrivateList();
    }
  }

  async function renderThread(threadId, container) {
    const msgs = await S.getMessages(threadId);
    container.innerHTML = msgs.map(m => bubbleHTML(m)).join("");
    container.scrollTop = container.scrollHeight;
  }

  function bubbleHTML(m) {
    const author = state.family.find(f => f.id === m.from);
    const me = m.from === state.user.id;
    const time = new Date(m.t).toLocaleTimeString([], { hour: "numeric", minute: "2-digit" });
    return `
      <div class="bubble-row ${me ? "me" : ""}">
        ${me ? "" : avatarHTML(author || { id: m.from, name: "?", color: "c1" }, "sm")}
        <div class="bubble">
          ${me ? "" : `<div class="who">${esc(author ? displayName(author) : "Unknown")}</div>`}
          <div>${esc(m.text)}</div>
          <div class="time">${time}</div>
        </div>
      </div>`;
  }

  function renderPrivateList() {
    const list = $("#dm-list");
    const others = state.family.filter(m => m.id !== state.user.id);
    list.innerHTML = others.map(m => `
      <button class="row" data-dm="${m.id}" type="button">
        <div class="${m.online ? "online-dot" : ""}">${avatarHTML(m)}</div>
        <div class="grow">
          <div class="title">${esc(displayName(m))}</div>
          <div class="sub">${m.online ? "Online" : "Offline"} · ${esc(m.role)}</div>
        </div>
        <span class="chev">${icon("chevron")}</span>
      </button>`).join("");
  }

  async function openDM(id) {
    const member = state.family.find(m => m.id === id);
    if (!member) return;
    state.activeDM = id;
    $("#dm-list").classList.add("hidden");
    $("#dm-chat").classList.remove("hidden");
    $("#dm-header").innerHTML = `
      <button class="icon-btn" id="dm-back" type="button" aria-label="Back to conversations">${icon("chevron", "flip")}</button>
      ${avatarHTML(member, "sm")}
      <div class="grow">
        <div class="title" style="font-weight:600">${esc(displayName(member))}</div>
        <div class="sub" style="font-size:.8rem;color:var(--text-dim)">${member.online ? "Online" : "Offline"}</div>
      </div>`;
    const thread = await S.getMessages("dm:" + [state.user.id, id].sort().join(":"));
    $("#dm-bubbles").innerHTML = thread.map(bubbleHTML).join("") ||
      `<div class="preview-note">Start a private conversation with ${esc(displayName(member))}.</div>`;
    $("#dm-bubbles").scrollTop = $("#dm-bubbles").scrollHeight;
  }

  function closeDM() {
    state.activeDM = null;
    $("#dm-chat").classList.add("hidden");
    $("#dm-list").classList.remove("hidden");
  }

  // ---------- Contacts ----------
  function renderContacts() {
    const q = state.contactQuery.trim().toLowerCase();
    const list = state.family.filter(m =>
      !q || displayName(m).toLowerCase().includes(q) || m.role.toLowerCase().includes(q));

    $("#contacts-list").innerHTML = list.length ? `<div class="list">${list.map(m => `
      <div class="row">
        <div class="${m.online ? "online-dot" : ""}">${avatarHTML(m)}</div>
        <div class="grow">
          <div class="title">${esc(displayName(m))}${state.user && m.id === state.user.id ? ' <span class="badge accent">You</span>' : ""}</div>
          <div class="sub">${esc(m.role)} · ${m.online ? "Online now" : "Offline"}</div>
        </div>
        ${state.user && m.id !== state.user.id
          ? `<button class="icon-btn" data-message="${m.id}" type="button" aria-label="Message ${esc(displayName(m))}">${icon("chat")}</button>`
          : ""}
      </div>`).join("")}</div>`
      : `<div class="card" style="text-align:center;color:var(--text-dim)">No family members match “${esc(state.contactQuery)}”.</div>`;

    $("#contacts-count").textContent = `${state.family.length} registered family members`;
  }

  // ---------- Resources ----------
  function renderResources() {
    const me = state.user.id;
    const mine = state.chores.filter(c => c.assignee === me);
    const others = state.chores.filter(c => c.assignee !== me);
    const doneCount = state.chores.filter(c => state.completions[c.id]).length;
    const pct = state.chores.length ? Math.round((doneCount / state.chores.length) * 100) : 0;

    $("#chore-progress-label").textContent = `${doneCount} of ${state.chores.length} complete`;
    $("#chore-progress-bar").style.width = pct + "%";

    const row = (c) => {
      const done = !!state.completions[c.id];
      const who = state.family.find(f => f.id === c.assignee);
      return `
      <div class="chore ${done ? "done" : ""}" data-chore="${c.id}" role="checkbox"
           aria-checked="${done}" tabindex="0">
        <div class="box">${icon("check")}</div>
        <div class="title">${esc(c.title)}</div>
        <span class="tag">${esc(who ? displayName(who) : "")}</span>
      </div>`;
    };

    $("#chores-mine").innerHTML = mine.length
      ? `<div class="list">${mine.map(row).join("")}</div>`
      : `<div class="card" style="color:var(--text-dim)">No chores assigned to you.</div>`;

    $("#chores-others").innerHTML = others.length
      ? `<div class="list">${others.map(row).join("")}</div>`
      : "";
  }

  async function toggleChore(choreId) {
    const next = !state.completions[choreId];
    state.completions[choreId] = next;
    haptic();
    await S.setChoreComplete(state.user.id, choreId, next);
    renderResources();
    toast(next ? "Chore marked complete" : "Chore marked incomplete");
  }

  // ---------- Settings ----------
  function renderSettings() {
    const u = state.user;
    const p = state.prefs;
    const name = displayName(u);

    $("#settings-profile").innerHTML = `
      <div class="profile-hero">
        <div class="avatar-wrap">
          ${avatarHTML(u, "xl")}
          <button class="edit-badge" id="change-avatar" type="button" aria-label="Change profile picture">${icon("camera")}</button>
        </div>
        <div class="name">${esc(name)}</div>
        <div class="role">${esc(u.role)} · Family account</div>
        <button class="btn-ghost" id="edit-name" type="button" style="margin-top:14px">Edit profile name</button>
      </div>`;

    $("#settings-appearance").innerHTML = `
      <div class="list">
        <div class="row">
          <div class="grow"><div class="title">Light appearance</div>
          <div class="sub">Switch between dark and light</div></div>
          ${toggleHTML("theme-toggle", p.theme === "light")}
        </div>
        <div class="row" style="flex-direction:column;align-items:stretch">
          <div class="title" style="margin-bottom:10px">Wallpaper</div>
          <div class="wallpaper-preview" style="${wallpaperPreviewStyle(p)}"></div>
          <div class="segmented" id="wallpaper-seg" style="margin:12px 0 0">
            <button type="button" data-wp="none" class="${p.wallpaper === "none" ? "active" : ""}">None</button>
            <button type="button" data-wp="gradient" class="${p.wallpaper === "gradient" ? "active" : ""}">Gradient</button>
            <button type="button" data-wp="custom" class="${p.wallpaper === "custom" ? "active" : ""}">Photo</button>
          </div>
          <button class="btn-ghost" id="upload-wallpaper" type="button" style="margin-top:10px">
            ${icon("image", "inline")}Upload my wallpaper
          </button>
          <input type="file" id="wallpaper-file" accept="image/*" class="hidden" />
        </div>
      </div>`;

    $("#settings-prefs").innerHTML = `
      <div class="list">
        <div class="row">
          <div class="grow"><div class="title">Sound & haptics</div>
          <div class="sub">Tones and vibration feedback</div></div>
          ${toggleHTML("sound-toggle", p.sound)}
        </div>
        <div class="row">
          <div class="grow"><div class="title">Notifications</div>
          <div class="sub">New messages from family</div></div>
          ${toggleHTML("notif-toggle", p.notifications)}
        </div>
        <div class="row">
          <div class="grow"><div class="title">Open in fullscreen</div>
          <div class="sub">Prompt to expand the app on launch</div></div>
          ${toggleHTML("fs-toggle", p.fullscreenOnLaunch)}
        </div>
      </div>`;

    $("#settings-account").innerHTML = `
      <div class="list">
        <div class="row"><span class="chev">${icon("lock")}</span>
          <div class="grow"><div class="title">Security</div><div class="sub">Password and sign-in options</div></div>
          <span class="badge">Coming soon</span></div>
        <div class="row"><span class="chev">${icon("eye")}</span>
          <div class="grow"><div class="title">Privacy</div><div class="sub">Who can see your activity</div></div>
          <span class="badge">Coming soon</span></div>
        <div class="row"><span class="chev">${icon("info")}</span>
          <div class="grow"><div class="title">About HOMELINK</div><div class="sub">Version 0.1 · Prototype</div></div></div>
      </div>`;
  }

  function toggleHTML(id, on) {
    return `<label class="toggle"><input type="checkbox" id="${id}" ${on ? "checked" : ""}><span class="track"></span></label>`;
  }

  function wallpaperPreviewStyle(p) {
    if (p.wallpaper === "custom" && p.wallpaperData) return `background-image:url('${p.wallpaperData}')`;
    if (p.wallpaper === "gradient") return "background:radial-gradient(900px 600px at 20% 0%, rgba(124,156,255,.6), transparent 60%), radial-gradient(700px 500px at 100% 100%, rgba(167,139,250,.55), transparent 60%), var(--surface-2)";
    return "background:var(--surface-2)";
  }

  function updatePref(patch, msg) {
    state.prefs = P.update(state.user.id, patch);
    applyPrefs();
    if (msg) toast(msg);
  }

  // Compress uploaded wallpapers / avatars so they fit in storage
  function fileToCompressedDataURL(file, maxW = 1280, quality = 0.82) {
    return new Promise((resolve, reject) => {
      const reader = new FileReader();
      reader.onerror = () => reject(new Error("Could not read the file"));
      reader.onload = () => {
        const img = new Image();
        img.onerror = () => reject(new Error("That file isn't a valid image"));
        img.onload = () => {
          const scale = Math.min(1, maxW / img.width);
          const canvas = document.createElement("canvas");
          canvas.width = Math.round(img.width * scale);
          canvas.height = Math.round(img.height * scale);
          canvas.getContext("2d").drawImage(img, 0, 0, canvas.width, canvas.height);
          resolve(canvas.toDataURL("image/jpeg", quality));
        };
        img.src = reader.result;
      };
      reader.readAsDataURL(file);
    });
  }

  // ---------- Bottom sheet ----------
  function openSheet(title, bodyHTML) {
    $("#sheet-title").textContent = title;
    $("#sheet-body").innerHTML = bodyHTML;
    $("#sheet").classList.add("show");
    $("#sheet-backdrop").classList.add("show");
  }

  function closeSheet() {
    $("#sheet").classList.remove("show");
    $("#sheet-backdrop").classList.remove("show");
  }

  function openNameEditor() {
    const current = state.prefs.displayName || state.user.name;
    openSheet("Profile name", `
      <div class="field">
        <label for="name-input">Display name</label>
        <input class="input" id="name-input" maxlength="32" value="${esc(current)}" />
      </div>
      <button class="btn-primary" id="save-name" type="button">Save</button>`);
    setTimeout(() => $("#name-input")?.focus(), 350);
  }

  // ---------- Fullscreen ----------
  function isFullscreen() {
    return !!(document.fullscreenElement || document.webkitFullscreenElement);
  }

  async function toggleFullscreen() {
    const el = document.documentElement;
    try {
      if (!isFullscreen()) {
        const req = el.requestFullscreen || el.webkitRequestFullscreen;
        if (!req) throw new Error("unsupported");
        await req.call(el, { navigationUI: "hide" });
      } else {
        const exit = document.exitFullscreen || document.webkitExitFullscreen;
        await exit.call(document);
      }
    } catch {
      toast("Fullscreen isn't available in this browser. On iPhone, use Share → Add to Home Screen.");
    }
  }

  function syncFullscreenIcon() {
    const on = isFullscreen();
    const btn = $("#fullscreen-btn");
    btn.innerHTML = icon(on ? "shrink" : "expand");
    btn.setAttribute("aria-label", on ? "Exit fullscreen" : "Enter fullscreen");
    btn.setAttribute("aria-pressed", String(on));
  }

  // ---------- Event wiring ----------
  function bindEvents() {
    // Login
    $("#login-form").addEventListener("submit", handleLogin);
    $("#family-picker").addEventListener("click", (e) => {
      const chip = e.target.closest(".member-chip");
      if (!chip) return;
      $$(".member-chip").forEach(c => c.classList.toggle("active", c === chip));
      $("#login-username").value = chip.dataset.name;
      $("#login-password").focus();
    });
    $("#toggle-password").addEventListener("click", () => {
      const input = $("#login-password");
      const show = input.type === "password";
      input.type = show ? "text" : "password";
      $("#toggle-password").setAttribute("aria-label", show ? "Hide password" : "Show password");
    });

    // Bottom nav
    $("#bottom-nav").addEventListener("click", (e) => {
      const btn = e.target.closest(".nav-item");
      if (btn) switchTab(btn.dataset.tab);
    });

    // Home quick actions
    $("#view-home").addEventListener("click", (e) => {
      const go = e.target.closest("[data-go]");
      if (go) switchTab(go.dataset.go);
    });

    // Messages segmented
    $("#msg-segmented").addEventListener("click", (e) => {
      const b = e.target.closest("button[data-msg]");
      if (!b) return;
      state.messagesTab = b.dataset.msg;
      if (state.messagesTab === "private") closeDM();
      renderMessages();
    });

    // Group send
    const sendGroup = async () => {
      const input = $("#group-input");
      const text = input.value.trim();
      if (!text) return;
      input.value = "";
      const msg = await S.sendMessage("group", state.user.id, text);
      $("#group-bubbles").insertAdjacentHTML("beforeend", bubbleHTML(msg));
      $("#group-bubbles").scrollTop = $("#group-bubbles").scrollHeight;
      haptic();
    };
    $("#group-form").addEventListener("submit", (e) => { e.preventDefault(); sendGroup(); });

    // Private messages
    $("#dm-list").addEventListener("click", (e) => {
      const row = e.target.closest("[data-dm]");
      if (row) openDM(row.dataset.dm);
    });
    $("#dm-chat").addEventListener("click", (e) => {
      if (e.target.closest("#dm-back")) closeDM();
    });
    $("#dm-form").addEventListener("submit", async (e) => {
      e.preventDefault();
      const input = $("#dm-input");
      const text = input.value.trim();
      if (!text || !state.activeDM) return;
      input.value = "";
      const threadId = "dm:" + [state.user.id, state.activeDM].sort().join(":");
      const msg = await S.sendMessage(threadId, state.user.id, text);
      const box = $("#dm-bubbles");
      box.querySelector(".preview-note")?.remove();
      box.insertAdjacentHTML("beforeend", bubbleHTML(msg));
      box.scrollTop = box.scrollHeight;
    });

    // Contacts
    $("#contacts-search").addEventListener("input", (e) => {
      state.contactQuery = e.target.value;
      renderContacts();
    });
    $("#contacts-list").addEventListener("click", (e) => {
      const btn = e.target.closest("[data-message]");
      if (!btn) return;
      state.messagesTab = "private";
      switchTab("messages");
      openDM(btn.dataset.message);
    });

    // Resources: chores
    $("#view-resources").addEventListener("click", (e) => {
      const row = e.target.closest("[data-chore]");
      if (row && !row.closest("#chores-others")) toggleChore(row.dataset.chore);
    });
    $("#view-resources").addEventListener("keydown", (e) => {
      const row = e.target.closest?.("[data-chore]");
      if (row && (e.key === "Enter" || e.key === " ")) {
        e.preventDefault();
        if (!row.closest("#chores-others")) toggleChore(row.dataset.chore);
      }
    });

    // Settings delegated handlers
    $("#view-settings").addEventListener("click", (e) => {
      if (e.target.closest("#edit-name")) openNameEditor();
      if (e.target.closest("#change-avatar")) $("#avatar-file").click();
      if (e.target.closest("#upload-wallpaper")) $("#wallpaper-file").click();

      const wp = e.target.closest("#wallpaper-seg button[data-wp]");
      if (wp) {
        const mode = wp.dataset.wp;
        if (mode === "custom" && !state.prefs.wallpaperData) {
          $("#wallpaper-file").click();
          return;
        }
        updatePref({ wallpaper: mode }, "Wallpaper updated");
        renderSettings();
      }
    });

    $("#view-settings").addEventListener("change", async (e) => {
      const t = e.target;
      if (t.id === "theme-toggle") updatePref({ theme: t.checked ? "light" : "dark" }, "Appearance updated");
      if (t.id === "sound-toggle") updatePref({ sound: t.checked });
      if (t.id === "notif-toggle") updatePref({ notifications: t.checked });
      if (t.id === "fs-toggle") updatePref({ fullscreenOnLaunch: t.checked });

      if (t.id === "wallpaper-file" || t.id === "avatar-file") {
        const file = t.files?.[0];
        if (!file) return;
        try {
          const data = await fileToCompressedDataURL(file, t.id === "avatar-file" ? 512 : 1280);
          if (t.id === "wallpaper-file") {
            updatePref({ wallpaper: "custom", wallpaperData: data }, "Your wallpaper was saved");
          } else {
            updatePref({ avatarData: data }, "Profile picture updated");
          }
          renderSettings();
          renderBottomAvatar();
        } catch (ex) {
          toast(ex.message);
        }
        t.value = "";
      }
    });

    // Hidden avatar input (created once)
    if (!$("#avatar-file")) {
      const inp = document.createElement("input");
      inp.type = "file"; inp.id = "avatar-file"; inp.accept = "image/*"; inp.className = "hidden";
      document.body.appendChild(inp);
    }

    // Logout
    $("#logout-btn").addEventListener("click", () => {
      openSheet("Sign out?", `
        <p style="color:var(--text-dim);margin:0 0 18px;line-height:1.5">You'll need to sign in again to see family messages and chores.</p>
        <button class="btn-primary" id="confirm-logout" type="button" style="background:var(--danger);box-shadow:none">Sign out</button>
        <button class="btn-ghost" id="cancel-logout" type="button" style="width:100%;margin-top:10px">Cancel</button>`);
    });

    // Sheet (delegated because body is replaced)
    $("#sheet").addEventListener("click", async (e) => {
      if (e.target.closest("#save-name")) {
        const v = $("#name-input").value.trim();
        updatePref({ displayName: v || null }, "Name updated");
        closeSheet();
        renderAll();
      }
      if (e.target.closest("#confirm-logout")) handleLogout();
      if (e.target.closest("#cancel-logout")) closeSheet();
    });
    $("#sheet-backdrop").addEventListener("click", closeSheet);

    // Top bar
    $("#fullscreen-btn").addEventListener("click", toggleFullscreen);
    document.addEventListener("fullscreenchange", syncFullscreenIcon);
    document.addEventListener("webkitfullscreenchange", syncFullscreenIcon);
    // Top-right avatar opens Settings
    $("#topbar-avatar-btn").addEventListener("click", () => switchTab("settings"));
  }

  function renderBottomAvatar() {
    if (!state.user) return;
    $("#topbar-avatar").innerHTML = avatarHTML(state.user, "sm");
  }

  function renderAll() {
    renderBottomAvatar();
    renderHome();
    renderContacts();
    renderResources();
    renderSettings();
    $("#topbar-eyebrow").textContent = state.activeTab === "home" ? greeting() : TABS[state.activeTab].eyebrow;
  }

  // ---------- Boot ----------
  async function boot() {
    bindEvents();
    syncFullscreenIcon();
    state.family = await S.getFamilyMembers();
    renderFamilyPicker();

    const session = await S.restoreSession();
    if (session) {
      await enterApp(session.user);
    } else {
      showLogin();
    }
  }

  document.addEventListener("DOMContentLoaded", boot);
})();
