/* ============================
   MASTER SEARCH (toolbar)
   ============================
   Type anywhere in the toolbar search box to see matching pages, products,
   locations, transactions, receipts... grouped. The server only returns what
   this user is allowed to see. Results open as floating windows.

   Ctrl+K (Cmd+K on Mac) jumps to the box, even from inside a window.
   Up/Down picks a result, Enter opens it (or the full results page), Esc closes.
*/
(function () {
  const isMac = /Mac|iPhone|iPad/.test(navigator.platform || "");

  function topInput() {
    try { return window.top.document.getElementById("nsInput"); } catch (e) { return null; }
  }

  // Shortcut works on every page, including pages inside a window (the box lives in the top page)
  document.addEventListener("keydown", function (e) {
    if ((e.ctrlKey || e.metaKey) && !e.shiftKey && !e.altKey && (e.key || "").toLowerCase() === "k") {
      const box = topInput();
      if (!box) return;
      e.preventDefault();
      box.focus();
      box.select();
    }
  });

  const form = document.getElementById("nsForm");
  const input = document.getElementById("nsInput");
  const panel = document.getElementById("nsResults");
  if (!form || !input || !panel || window.top !== window.self) return;

  const kbd = form.querySelector("kbd");
  if (kbd && isMac) kbd.textContent = "⌘K";

  let timer = null, seq = 0, sel = -1, lastQ = "";

  function esc(t) {
    return String(t == null ? "" : t).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  }
  // Highlight each typed word (split the raw text, then escape every piece)
  function mark(text, terms) {
    text = String(text == null ? "" : text);
    if (!terms.length) return esc(text);
    const re = new RegExp("(" + terms.map(t => t.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join("|") + ")", "gi");
    return text.split(re).map((part, i) => i % 2 ? "<mark>" + esc(part) + "</mark>" : esc(part)).join("");
  }

  function open(url, title) {
    close();
    input.blur();
    if (window.openWindow) window.openWindow(url, title || "Search");
    else window.location.href = url;
  }
  function allUrl() { return form.action + "?q=" + encodeURIComponent(input.value.trim()); }

  function close() {
    panel.hidden = true;
    input.setAttribute("aria-expanded", "false");
    sel = -1;
  }
  function options() { return Array.from(panel.querySelectorAll(".ns-item, .ns-all")); }
  function highlight(i) {
    const opts = options();
    opts.forEach(o => o.classList.remove("sel"));
    sel = Math.max(-1, Math.min(i, opts.length - 1));
    if (sel >= 0) { opts[sel].classList.add("sel"); opts[sel].scrollIntoView({ block: "nearest" }); }
  }

  function render(q, groups) {
    const terms = q.toLowerCase().split(/\s+/).filter(Boolean);
    let html = "";
    if (!groups.length) {
      html = '<div class="ns-empty">Nothing found for “' + esc(q) + '”.</div>';
    } else {
      groups.forEach(function (g) {
        html += '<div class="ns-group">' + esc(g.group) + (g.more ? " · " + (g.items.length + g.more) + " found" : "") + "</div>";
        g.items.forEach(function (it) {
          html += '<a class="ns-item" role="option" href="' + esc(it.url) + '" data-title="' + esc(it.title) + '">' +
                  '<div class="ns-t">' + mark(it.title, terms) + "</div>" +
                  (it.sub ? '<div class="ns-s">' + mark(it.sub, terms) + "</div>" : "") + "</a>";
        });
      });
      html += '<a class="ns-all" href="' + esc(allUrl()) + '" data-title="Search">See all results for “' + esc(q) + '”</a>';
    }
    panel.innerHTML = html;
    panel.hidden = false;
    input.setAttribute("aria-expanded", "true");
    sel = -1;
  }

  function run() {
    const q = input.value.trim();
    if (q === lastQ && !panel.hidden) return;
    lastQ = q;
    if (!q) { close(); return; }
    const mine = ++seq;
    fetch(input.dataset.api + "?q=" + encodeURIComponent(q), { headers: { Accept: "application/json" } })
      .then(r => r.json())
      .then(j => { if (mine === seq) render(q, j.groups || []); })
      .catch(() => {});
  }

  input.addEventListener("input", function () {
    clearTimeout(timer);
    timer = setTimeout(run, 180);
  });
  input.addEventListener("focus", function () { if (input.value.trim()) { lastQ = ""; run(); } });

  input.addEventListener("keydown", function (e) {
    if (e.key === "ArrowDown") { e.preventDefault(); if (panel.hidden) run(); else highlight(sel + 1); }
    else if (e.key === "ArrowUp") { e.preventDefault(); highlight(sel - 1); }
    else if (e.key === "Escape") { close(); input.blur(); }
    else if (e.key === "Enter") {
      e.preventDefault();
      const opts = options();
      if (sel >= 0 && opts[sel]) open(opts[sel].getAttribute("href"), opts[sel].dataset.title);
      else if (input.value.trim()) open(allUrl(), "Search");
    }
  });

  panel.addEventListener("click", function (e) {
    const a = e.target.closest(".ns-item, .ns-all");
    if (!a) return;
    e.preventDefault();
    open(a.getAttribute("href"), a.dataset.title);
  });
  form.addEventListener("submit", function (e) { e.preventDefault(); if (input.value.trim()) open(allUrl(), "Search"); });

  document.addEventListener("mousedown", function (e) { if (!form.contains(e.target)) close(); });
})();
