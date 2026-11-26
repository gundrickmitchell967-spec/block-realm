/* =========================================================
   HOMELINK — Services layer
   This file is the ONLY place that talks to a backend.
   Right now it uses a local development placeholder so the
   interface can be tested. When Supabase is connected, replace
   the internals of each method — the UI code will not change.

   SECURITY NOTE: No passwords are stored or compared on the
   client in a real deployment. The demo accounts below exist
   only for previewing the interface.
   ========================================================= */

const HomeLinkServices = (() => {
  // ---- Development placeholder data (replace with Supabase tables) ----
  const DEV_FAMILY = [
    { id: "u_mom",   name: "Mom",    role: "Parent",  color: "c2", online: true  },
    { id: "u_dad",   name: "Dad",    role: "Parent",  color: "c1", online: false },
    { id: "u_alex",  name: "Alex",   role: "Sibling", color: "c3", online: true  },
    { id: "u_jamie", name: "Jamie",  role: "Sibling", color: "c4", online: false },
    { id: "u_gran",  name: "Grandma",role: "Family",  color: "c5", online: false },
  ];

  // Demo chore list — only the administrator can change this list
  const DEV_CHORES = [
    { id: "ch1", title: "Empty the dishwasher",    assignee: "u_alex"  },
    { id: "ch2", title: "Take out the recycling",  assignee: "u_jamie" },
    { id: "ch3", title: "Water the plants",        assignee: "u_mom"   },
    { id: "ch4", title: "Walk the dog",            assignee: "u_dad"   },
    { id: "ch5", title: "Tidy the living room",    assignee: "u_alex"  },
  ];

  const DEV_SESSION_KEY = "homelink.dev.session";

  // ---- Auth (placeholder) ----
  // Replace with supabase.auth.signInWithPassword(...) later.
  async function signIn({ username, password, remember }) {
    await delay(900);
    const member = DEV_FAMILY.find(
      m => m.name.toLowerCase() === String(username).trim().toLowerCase()
    );
    // Development only: any non-empty password is accepted.
    if (!member || !password) {
      throw new Error("We couldn't find that family account. Check the name and try again.");
    }
    const session = { userId: member.id, remember: !!remember, issuedAt: Date.now() };
    // Session token only — never a password. Real sessions will be managed by Supabase.
    const store = remember ? localStorage : sessionStorage;
    store.setItem(DEV_SESSION_KEY, JSON.stringify(session));
    return { user: member };
  }

  async function signOut() {
    localStorage.removeItem(DEV_SESSION_KEY);
    sessionStorage.removeItem(DEV_SESSION_KEY);
  }

  async function restoreSession() {
    const raw = localStorage.getItem(DEV_SESSION_KEY) || sessionStorage.getItem(DEV_SESSION_KEY);
    if (!raw) return null;
    try {
      const { userId } = JSON.parse(raw);
      const user = DEV_FAMILY.find(m => m.id === userId);
      return user ? { user } : null;
    } catch {
      return null;
    }
  }

  // ---- Family & contacts ----
  async function getFamilyMembers() {
    await delay(120);
    return DEV_FAMILY.map(m => ({ ...m }));
  }

  // ---- Chores (read-only for family members) ----
  async function getChores() {
    await delay(120);
    return DEV_CHORES.map(c => ({ ...c }));
  }

  // Completion state is per-member and will live in the database.
  // Kept locally for the prototype so checkboxes respond.
  const completionKey = (userId) => `homelink.dev.chores.${userId}`;

  async function getCompletions(userId) {
    await delay(60);
    try {
      return JSON.parse(localStorage.getItem(completionKey(userId)) || "{}");
    } catch {
      return {};
    }
  }

  async function setChoreComplete(userId, choreId, done) {
    const map = await getCompletions(userId);
    map[choreId] = !!done;
    localStorage.setItem(completionKey(userId), JSON.stringify(map));
    return map;
  }

  // ---- Messaging (interface only; real-time comes with Supabase) ----
  const seedThreads = {
    group: [
      { id: "m1", from: "u_mom",  text: "Dinner is at 7 tonight, everyone please be home!", t: Date.now() - 3600e3 },
      { id: "m2", from: "u_alex", text: "On my way 🚲",                                      t: Date.now() - 2400e3 },
      { id: "m3", from: "u_dad",  text: "Grandma says she's bringing dessert.",               t: Date.now() - 1200e3 },
    ],
  };

  async function getMessages(threadId) {
    await delay(100);
    return (seedThreads[threadId] || []).slice();
  }

  async function sendMessage(threadId, fromId, text) {
    await delay(80);
    const msg = { id: "m" + Date.now(), from: fromId, text, t: Date.now() };
    (seedThreads[threadId] = seedThreads[threadId] || []).push(msg);
    return msg;
  }

  // ---- Helpers ----
  function delay(ms) {
    return new Promise(r => setTimeout(r, ms));
  }

  return {
    signIn,
    signOut,
    restoreSession,
    getFamilyMembers,
    getChores,
    getCompletions,
    setChoreComplete,
    getMessages,
    sendMessage,
  };
})();
