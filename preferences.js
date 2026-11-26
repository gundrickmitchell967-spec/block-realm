/* =========================================================
   HOMELINK — Per-user preferences
   Each family member's settings are stored under their own key,
   so one person's wallpaper or theme never touches anyone else.
   Later this will sync to the database instead of localStorage.
   ========================================================= */

const HomeLinkPrefs = (() => {
  const DEFAULTS = {
    theme: "dark",            // "dark" | "light"
    accent: "c1",             // accent colour key
    wallpaper: "none",        // "none" | "gradient" | "custom"
    wallpaperData: null,      // data URL for custom upload (kept small)
    sound: true,
    notifications: true,
    fullscreenOnLaunch: false,
    displayName: null,        // override for profile name
    avatarData: null,         // data URL for custom profile picture
  };

  const key = (userId) => `homelink.prefs.${userId}`;

  function load(userId) {
    try {
      const raw = localStorage.getItem(key(userId));
      return { ...DEFAULTS, ...(raw ? JSON.parse(raw) : {}) };
    } catch {
      return { ...DEFAULTS };
    }
  }

  function save(userId, prefs) {
    try {
      localStorage.setItem(key(userId), JSON.stringify(prefs));
      return true;
    } catch (err) {
      // Most likely the storage quota was exceeded by a large image
      console.warn("Could not save preferences:", err);
      return false;
    }
  }

  function update(userId, patch) {
    const next = { ...load(userId), ...patch };
    save(userId, next);
    return next;
  }

  return { DEFAULTS, load, save, update };
})();
