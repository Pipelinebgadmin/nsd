/* ============================
   BACK BUTTON + FORM DRAFTS
   ============================
   Back: every page records itself in a small "pages visited" list kept in
   sessionStorage. The top-level page and each floating window (iframe) keep
   their own list, so going back in a window never moves the page behind it
   (the browser's own history mixes the two together).

   Drafts: anything typed into a data-entry form is saved to localStorage as
   you go. Come back to the page within 15 minutes and it's filled back in.
   A draft is thrown away once its form submits successfully, kept if the
   submit came back with an error, and can be wiped with the "Clear" button
   that sits next to the form's submit button.

   Opt a form out with data-no-draft. Forms with a password field and small
   one-field action forms (delete buttons, etc.) are skipped automatically.
*/
(function () {
  const DRAFT_TTL_MS = 15 * 60 * 1000;
  const DRAFT_PREFIX = 'nstock-draft:';
  const TAB_PREFIX = 'nstock-tab:';
  const MAX_HISTORY = 50;

  function lsGet(key) { try { return localStorage.getItem(key); } catch (e) { return null; } }
  function lsSet(key, val) { try { localStorage.setItem(key, val); } catch (e) { /* storage full/blocked */ } }
  function lsDel(key) { try { localStorage.removeItem(key); } catch (e) { /* blocked */ } }
  function ssGet(key) { try { return sessionStorage.getItem(key); } catch (e) { return null; } }
  function ssSet(key, val) { try { sessionStorage.setItem(key, val); } catch (e) { /* blocked */ } }
  function ssDel(key) { try { sessionStorage.removeItem(key); } catch (e) { /* blocked */ } }

  const inFrame = window.self !== window.top;

  // Page identity without the window-only ?embed=1 flag, so a page keeps the
  // same draft whether it's opened full-screen or inside a floating window.
  function pageKey() {
    const u = new URL(window.location.href);
    u.searchParams.delete('embed');
    return u.pathname + (u.search || '');
  }

  // =====================================================================
  // BACK
  // =====================================================================
  const histKey = 'nstock-history:' + (inFrame ? (window.name || 'frame') : 'top');
  const goingBackKey = histKey + ':back';

  function readHistory() {
    try { return JSON.parse(ssGet(histKey) || '[]'); } catch (e) { return []; }
  }
  function writeHistory(list) { ssSet(histKey, JSON.stringify(list.slice(-MAX_HISTORY))); }

  (function recordVisit() {
    const here = window.location.pathname + window.location.search;
    const list = readHistory();
    if (ssGet(goingBackKey)) {
      ssDel(goingBackKey);       // arrived via Back: the list was already trimmed
    }
    if (list[list.length - 1] !== here) list.push(here);
    writeHistory(list);
  })();

  function canGoBack() { return readHistory().length > 1; }

  window.NStockBack = function () {
    const list = readHistory();
    if (list.length < 2) return false;
    list.pop();                                   // this page
    const prev = list[list.length - 1];
    writeHistory(list);
    ssSet(goingBackKey, '1');
    if (typeof flushDrafts === 'function') flushDrafts();
    window.location.href = prev;
    return true;
  };
  window.NStockCanGoBack = canGoBack;

  // =====================================================================
  // REMEMBERED TABS (so a draft on a non-default tab is visible again)
  // =====================================================================
  window.NStockTabs = {
    save: function (name, value) {
      lsSet(TAB_PREFIX + pageKey() + ':' + name, JSON.stringify({ t: Date.now(), v: value }));
    },
    load: function (name) {
      const key = TAB_PREFIX + pageKey() + ':' + name;
      try {
        const rec = JSON.parse(lsGet(key) || 'null');
        if (rec && Date.now() - rec.t < DRAFT_TTL_MS) return rec.v;
      } catch (e) { /* bad JSON */ }
      lsDel(key);
      return null;
    }
  };

  // =====================================================================
  // DRAFTS
  // =====================================================================
  const SKIP_TYPES = ['hidden', 'password', 'file', 'submit', 'button', 'reset', 'image'];

  function fieldName(el) { return el.getAttribute('name') || el.id || ''; }

  function draftFields(form) {
    return Array.from(form.elements).filter(function (el) {
      if (!el.tagName || !/^(INPUT|SELECT|TEXTAREA)$/.test(el.tagName)) return false;
      if (SKIP_TYPES.indexOf((el.type || '').toLowerCase()) > -1) return false;
      if (el.name === 'csrf_token' || el.hasAttribute('data-no-draft')) return false;
      return !!fieldName(el);
    });
  }

  function isDraftForm(form) {
    if (form.hasAttribute('data-no-draft')) return false;
    if ((form.getAttribute('method') || '').toLowerCase() === 'get') return false;  // searches & report filters
    if (form.querySelector('input[type="password"]')) return false;                  // never store passwords
    return draftFields(form).length >= 2;                                            // skip one-button action forms
  }

  function formKey(form) {
    const forms = Array.from(document.forms);
    const ident = form.id || (form.getAttribute('action') || '') + '#' + forms.indexOf(form);
    return DRAFT_PREFIX + pageKey() + '|' + ident;
  }

  function readDraft(key) {
    try {
      const rec = JSON.parse(lsGet(key) || 'null');
      if (rec && Date.now() - rec.t < DRAFT_TTL_MS) return rec;
    } catch (e) { /* bad JSON */ }
    lsDel(key);
    return null;
  }

  function snapshot(form) {
    // [name, occurrence, value|checked] — occurrence handles repeated names like product_id[]
    const seen = {};
    return draftFields(form).map(function (el) {
      const n = fieldName(el);
      const i = seen[n] = (seen[n] === undefined ? 0 : seen[n] + 1);
      const isCheck = el.type === 'checkbox' || el.type === 'radio';
      return [n, i, isCheck ? (el.checked ? (el.value || 'on') : null) : el.value, isCheck ? 1 : 0];
    });
  }

  function saveDraft(form) {
    lsSet(formKey(form), JSON.stringify({ t: Date.now(), fields: snapshot(form) }));
  }

  // Put saved values back. A select whose option isn't there yet (e.g. a tank
  // list that loads after a location is picked) is left for a later pass.
  function applyDraft(form, rec, fireEvents) {
    const byName = {};
    draftFields(form).forEach(function (el) {
      const n = fieldName(el);
      (byName[n] = byName[n] || []).push(el);
    });
    rec.fields.forEach(function (f) {
      const el = (byName[f[0]] || [])[f[1]];
      if (!el) return;
      let changed = false;
      if (f[3]) {
        const want = f[2] !== null && (el.value || 'on') === f[2];
        if (el.checked !== want) { el.checked = want; changed = true; }
      } else if (el.value !== f[2]) {
        el.value = f[2];
        if (el.value !== f[2]) return;   // option not there yet
        changed = true;
      }
      if (changed && fireEvents) {
        el.dispatchEvent(new Event('input', { bubbles: true }));
        el.dispatchEvent(new Event('change', { bubbles: true }));
      }
    });
  }

  function restoreDraft(form) {
    const rec = readDraft(formKey(form));
    if (!rec) return;
    restoring = true;
    // First pass fires change events so dependent fields (tanks, units,
    // package lists) rebuild; later passes fill in anything that had to
    // wait for those lists to load.
    applyDraft(form, rec, true);
    restoring = false;
    [100, 400, 1200].forEach(function (ms) {
      setTimeout(function () {
        // Only touches fields that still don't match, so it's safe to repeat
        if (!readDraft(formKey(form))) return;   // cleared in the meantime
        restoring = true; applyDraft(form, rec, true); restoring = false;
      }, ms);
    });
  }

  function clearDraft(form) { lsDel(formKey(form)); }

  // Successful submit -> drop the draft. We can't know the outcome until the
  // next page loads, so mark it pending and settle it there.
  const PENDING_KEY = 'nstock-draft-pending';
  function markPending(form) {
    if (!isDraftForm(form)) return;
    saveDraft(form);
    let list = [];
    try { list = JSON.parse(lsGet(PENDING_KEY) || '[]'); } catch (e) { /* bad JSON */ }
    list.push({ key: formKey(form), t: Date.now() });
    lsSet(PENDING_KEY, JSON.stringify(list));
  }

  function settlePending() {
    let list = [];
    try { list = JSON.parse(lsGet(PENDING_KEY) || '[]'); } catch (e) { /* bad JSON */ }
    lsDel(PENDING_KEY);
    if (!list.length) return;
    const meta = document.querySelector('meta[name="nstock-form-error"]');
    const failed = meta && meta.content === '1';
    if (!failed) list.forEach(function (p) { lsDel(p.key); });
  }

  // Drop drafts older than 15 minutes so storage doesn't fill up
  function sweepExpired() {
    try {
      for (let i = localStorage.length - 1; i >= 0; i--) {
        const k = localStorage.key(i);
        if (k && (k.indexOf(DRAFT_PREFIX) === 0 || k.indexOf(TAB_PREFIX) === 0)) {
          try {
            const rec = JSON.parse(localStorage.getItem(k) || 'null');
            if (!rec || Date.now() - rec.t >= DRAFT_TTL_MS) localStorage.removeItem(k);
          } catch (e) { localStorage.removeItem(k); }
        }
      }
    } catch (e) { /* storage blocked */ }
  }

  // ---- Clear button next to each draft form's main submit button ----
  function addClearButton(form) {
    let submits = form.querySelectorAll('button[type="submit"], input[type="submit"]');
    if (!submits.length) submits = form.querySelectorAll('button:not([type])');
    const main = submits[submits.length - 1];
    if (!main || form.querySelector('.nstock-clear-btn')) return;
    const btn = document.createElement('button');
    btn.type = 'button';
    btn.className = 'btn btn-outline-secondary nstock-clear-btn' +
      (main.classList.contains('btn-sm') ? ' btn-sm' : '') +
      (main.classList.contains('btn-lg') ? ' btn-lg' : '');
    btn.textContent = 'Clear';
    btn.title = 'Clear this form';
    btn.style.marginLeft = '8px';
    btn.addEventListener('click', function () {
      clearDraft(form);
      flushDrafts();                         // keep any other forms on the page
      // Reload the page fresh (GET) so added rows and computed totals reset too
      window.location.replace(window.location.href);
    });
    main.insertAdjacentElement('afterend', btn);
  }

  // ---- Wire it all up ----
  let restoring = false;
  const timers = new Map();
  let draftForms = [];

  function flushDrafts() {
    timers.forEach(function (t, form) { clearTimeout(t); saveDraft(form); });
    timers.clear();
  }

  function onEdit(e) {
    if (restoring) return;
    const form = e.target && e.target.form;
    if (!form || draftForms.indexOf(form) === -1) return;
    clearTimeout(timers.get(form));
    timers.set(form, setTimeout(function () { timers.delete(form); saveDraft(form); }, 300));
  }

  // Programmatic form.submit() skips the submit event, so catch it here too
  const nativeSubmit = HTMLFormElement.prototype.submit;
  HTMLFormElement.prototype.submit = function () {
    try { markPending(this); } catch (e) { /* never block a submit */ }
    return nativeSubmit.apply(this, arguments);
  };

  document.addEventListener('DOMContentLoaded', function () {
    settlePending();
    sweepExpired();

    draftForms = Array.from(document.forms).filter(isDraftForm);
    draftForms.forEach(function (form) {
      restoreDraft(form);
      addClearButton(form);
    });

    document.addEventListener('input', onEdit, true);
    document.addEventListener('change', onEdit, true);
    // Bubble phase on window: runs after the page's own submit handlers, so a
    // submit they cancelled (validation, AJAX) isn't treated as sent.
    window.addEventListener('submit', function (e) {
      if (!e.defaultPrevented && e.target && e.target.tagName === 'FORM') markPending(e.target);
    });
    window.addEventListener('pagehide', flushDrafts);

    // Header Back button
    const back = document.getElementById('navBackBtn');
    if (back) {
      if (!document.getElementById('winHeaderControls') || document.getElementById('winHeaderControls').hidden) {
        back.disabled = !canGoBack();
      }
      back.addEventListener('click', function () {
        if (window.nstockWindowBack && window.nstockWindowBack()) return;
        window.NStockBack();
      });
    }
  });

  // For pages whose entries don't live in a plain <form> (e.g. Blend Builder
  // ingredient rows): save/load any object under a name, same 15-minute rule.
  window.NStockDrafts = {
    clear: function (form) { clearDraft(form); },
    flush: function () { flushDrafts(); },
    put: function (name, data) {
      lsSet(DRAFT_PREFIX + pageKey() + '|custom:' + name, JSON.stringify({ t: Date.now(), data: data }));
    },
    get: function (name) {
      const rec = readDraft(DRAFT_PREFIX + pageKey() + '|custom:' + name);
      return rec ? rec.data : null;
    },
    drop: function (name) { lsDel(DRAFT_PREFIX + pageKey() + '|custom:' + name); }
  };
})();
