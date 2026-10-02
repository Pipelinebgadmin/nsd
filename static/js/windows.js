/* ============================
   FLOATING WINDOW MANAGER
   ============================
   Any link marked with data-win="1" opens its href in a floating,
   draggable, resizable window (via iframe) instead of navigating away.
   Works from any page, and bubbles up to the true top-level document
   when clicked from inside a nested window, so windows never nest.

   Clicking anywhere on the real page behind the windows (not on a
   window itself) rolls every open window up to just its title bar,
   revealing the full page underneath. Each rolled-up title bar stays
   put and visible — click it to pop that window back open.
*/
(function () {

  function attachLinkInterception() {
    document.addEventListener('click', function (e) {
      const link = e.target.closest('[data-win]');
      if (!link) return;
      const href = link.getAttribute('href');
      if (!href) return;
      e.preventDefault();
      const title = link.getAttribute('data-win-title') || link.textContent.trim();
      window.openWindow(href, title);
    });
  }

  // ---- Inside a nested iframe: delegate to the real top-level manager ----
  if (window.top !== window.self) {
    window.openWindow = function (url, title) {
      try {
        window.top.openWindow(url, title);
      } catch (err) {
        window.top.location.href = url;
      }
    };
    attachLinkInterception();
    return;
  }

  // ---- Top-level implementation ----

  let zTop = 1000;
  let cascadeCount = 0;
  const openWindows = {}; // normalized url -> window element

  // While dragging or resizing, the mouse often has to pass over a
  // window's iframe. An iframe is a separate document, so it swallows
  // mousemove/mouseup instead of letting them bubble to us — which is
  // why shrinking (moving the cursor inward, over the iframe) could
  // stop responding while growing (moving outward, over the empty page)
  // worked fine. A transparent overlay above everything keeps the
  // mouse on our document for the whole drag.
  let inputBlocker = null;
  function startInputBlocker(cursor) {
    if (inputBlocker) return;
    inputBlocker = document.createElement('div');
    inputBlocker.style.position = 'fixed';
    inputBlocker.style.inset = '0';
    inputBlocker.style.zIndex = '999999';
    inputBlocker.style.cursor = cursor || 'default';
    document.body.appendChild(inputBlocker);
  }
  function stopInputBlocker() {
    if (inputBlocker) {
      inputBlocker.remove();
      inputBlocker = null;
    }
  }
  function cursorForDir(dir) {
    if (dir === 'n' || dir === 's') return 'ns-resize';
    if (dir === 'e' || dir === 'w') return 'ew-resize';
    if (dir === 'ne' || dir === 'sw') return 'nesw-resize';
    return 'nwse-resize'; // nw, se
  }

  function ensureRoot() {
    let root = document.getElementById('windows-root');
    if (!root) {
      root = document.createElement('div');
      root.id = 'windows-root';
      document.body.appendChild(root);
    }
    return root;
  }

  function normalizeUrl(url) {
    try {
      const u = new URL(url, window.location.origin);
      u.searchParams.delete('embed');
      return u.pathname + (u.search ? u.search : '');
    } catch (e) {
      return url;
    }
  }

  function focusWindow(win) {
    win.style.zIndex = ++zTop;
    if (typeof updateHeaderControls === 'function') updateHeaderControls();
  }

  function shadeWindow(win) {
    if (win._shaded) return;
    win._shadeRect = { height: win.style.height };
    win.classList.add('is-shaded');
    win.style.height = '40px';
    win._shaded = true;
  }

  function unshadeWindow(win) {
    if (!win._shaded) return;
    win.style.height = (win._shadeRect && win._shadeRect.height) || '620px';
    win.classList.remove('is-shaded');
    win._shaded = false;
  }

  function toggleShade(win) {
    if (win._shaded) unshadeWindow(win); else shadeWindow(win);
    focusWindow(win);
  }

  // Roll every open window up to its title bar, revealing the real page.
  function shadeAllWindows() {
    Object.keys(openWindows).forEach(function (key) {
      const w = openWindows[key];
      if (!w._mode || w._mode === 'float') shadeWindow(w);
    });
    updateHeaderControls();
  }

  // ---- Window modes: 'float' (normal), 'max' (fills the screen, flush),
  //      'left' / 'right' (split screen halves) ----
  function headerHeight() {
    const h = document.querySelector('.nstock-header');
    return h ? h.offsetHeight : 0;
  }

  function saveFloatRect(win) {
    if (win._mode && win._mode !== 'float') return;
    win._prevRect = {
      left: win.style.left, top: win.style.top,
      width: win.style.width, height: win.style.height
    };
  }

  function setMode(win, mode) {
    if (win._shaded) unshadeWindow(win);
    if (mode !== 'float') saveFloatRect(win);
    win.classList.remove('is-max', 'is-split', 'is-left', 'is-right');
    const top = headerHeight() + 'px';
    const fullH = 'calc(100vh - ' + headerHeight() + 'px)';

    if (mode === 'max') {
      win.classList.add('is-max');
      Object.assign(win.style, { left: '0px', top: top, width: '100vw', height: fullH });
    } else if (mode === 'left' || mode === 'right') {
      win.classList.add('is-split', 'is-' + mode);
      Object.assign(win.style, {
        left: mode === 'left' ? '0px' : '50vw', top: top, width: '50vw', height: fullH
      });
    } else {
      Object.assign(win.style, win._prevRect || { left: '70px', top: '60px', width: '900px', height: '620px' });
    }
    win._mode = mode;
    focusWindow(win);
    updateHeaderControls();
  }

  function toggleMaximize(win) {
    setMode(win, win._mode === 'max' ? 'float' : 'max');
  }

  // Split screen: first press snaps to whichever half is free (left first),
  // pressing again flips it to the other side.
  function splitWindow(win) {
    if (win._mode === 'left') return setMode(win, 'right');
    if (win._mode === 'right') return setMode(win, 'left');
    const leftTaken = Object.keys(openWindows).some(function (k) {
      const w = openWindows[k];
      return w !== win && w._mode === 'left';
    });
    setMode(win, leftTaken ? 'right' : 'left');
  }

  // Minimize: a maximized or split window drops back to its normal size
  // and rolls up to its title bar.
  function minimizeWindow(win) {
    if (win._mode && win._mode !== 'float') setMode(win, 'float');
    shadeWindow(win);
    updateHeaderControls();
  }

  function closeWindow(win) {
    Object.keys(openWindows).forEach(function (k) {
      if (openWindows[k] === win) delete openWindows[k];
    });
    win.remove();
    updateHeaderControls();
  }

  // When the front-most window is maximized, its controls move up into the
  // app header (like QuickBooks) since the window itself has no title bar.
  function topMaximized() {
    let best = null;
    Object.keys(openWindows).forEach(function (k) {
      const w = openWindows[k];
      if (w._mode === 'max' && !w._shaded) {
        if (!best || (parseInt(w.style.zIndex, 10) || 0) > (parseInt(best.style.zIndex, 10) || 0)) best = w;
      }
    });
    return best;
  }

  function updateHeaderControls() {
    const box = document.getElementById('winHeaderControls');
    if (!box) return;
    const win = topMaximized();
    // The header Back button works on a maximized window (its own title bar is hidden)
    const navBack = document.getElementById('navBackBtn');
    if (navBack) {
      let can = window.NStockCanGoBack ? window.NStockCanGoBack() : false;
      if (win) {
        try { can = win.querySelector('.fw-iframe').contentWindow.NStockCanGoBack(); } catch (e) { can = false; }
      }
      navBack.disabled = !can;
    }
    box.hidden = !win;
    box._win = win;
    if (win) box.querySelector('.whc-title').textContent = win.querySelector('.fw-title').textContent;
  }

  function setupHeaderControls() {
    const box = document.getElementById('winHeaderControls');
    if (!box) return;
    box.addEventListener('click', function (e) {
      const btn = e.target.closest('[data-act]');
      if (!btn || !box._win) return;
      const win = box._win;
      if (btn.dataset.act === 'min') minimizeWindow(win);
      if (btn.dataset.act === 'split') splitWindow(win);
      if (btn.dataset.act === 'close') closeWindow(win);
    });
  }

  // Title bar: drag to move; a plain click (no meaningful movement) on a
  // shaded window's title bar restores it instead.
  function setupDrag(win) {
    const bar = win.querySelector('.fw-titlebar');
    let sx, sy, ox, oy, dragging = false, moved = false;

    bar.addEventListener('mousedown', function (e) {
      if (e.target.closest('.fw-btn')) return;
      dragging = true;
      moved = false;
      sx = e.clientX;
      sy = e.clientY;
      ox = win.offsetLeft;
      oy = win.offsetTop;
      document.body.style.userSelect = 'none';
      focusWindow(win);
    });

    document.addEventListener('mousemove', function (e) {
      if (!dragging) return;
      const dx = e.clientX - sx;
      const dy = e.clientY - sy;
      if (Math.abs(dx) > 3 || Math.abs(dy) > 3) moved = true;
      if (win._shaded && !moved) return; // don't drag a shaded window until it clearly moves
      if (!moved) return;
      // Cover the iframes only once a real drag starts, so plain clicks and
      // double-clicks on the title bar still reach it.
      startInputBlocker('move');
      // Dragging a split window pulls it back to its normal size, centered under the cursor
      if (win._mode === 'left' || win._mode === 'right') {
        setMode(win, 'float');
        ox = Math.max(0, sx - win.offsetWidth / 2);
        oy = Math.max(headerHeight(), sy - 20);
      }
      win.style.left = (ox + dx) + 'px';
      win.style.top = Math.max(headerHeight(), oy + dy) + 'px';
    });

    document.addEventListener('mouseup', function () {
      if (dragging && !moved && win._shaded) {
        unshadeWindow(win);
      }
      dragging = false;
      document.body.style.userSelect = '';
      stopInputBlocker();
    });
  }

  // Generic resize handler used by all 8 handles (n/s/e/w + corners).
  function setupResizeHandle(win, handle, dir) {
    let sx, sy, sw, sh, sl, st, resizing = false;

    handle.addEventListener('mousedown', function (e) {
      resizing = true;
      sx = e.clientX;
      sy = e.clientY;
      sw = win.offsetWidth;
      sh = win.offsetHeight;
      sl = win.offsetLeft;
      st = win.offsetTop;
      document.body.style.userSelect = 'none';
      e.preventDefault();
      e.stopPropagation();
      startInputBlocker(cursorForDir(dir));
      focusWindow(win);
    });

    document.addEventListener('mousemove', function (e) {
      if (!resizing) return;
      const dx = e.clientX - sx;
      const dy = e.clientY - sy;
      let newW = sw, newH = sh, newL = sl, newT = st;

      if (dir.indexOf('e') > -1) newW = Math.max(360, sw + dx);
      if (dir.indexOf('s') > -1) newH = Math.max(140, sh + dy);
      if (dir.indexOf('w') > -1) {
        newW = Math.max(360, sw - dx);
        newL = sl + (sw - newW);
      }
      if (dir.indexOf('n') > -1) {
        newH = Math.max(140, sh - dy);
        newT = st + (sh - newH);
      }

      win.style.width = newW + 'px';
      win.style.height = newH + 'px';
      win.style.left = newL + 'px';
      win.style.top = newT + 'px';
    });

    document.addEventListener('mouseup', function () {
      resizing = false;
      document.body.style.userSelect = '';
      stopInputBlocker();
    });
  }

  function setupResize(win) {
    ['n', 's', 'e', 'w', 'ne', 'nw', 'se', 'sw'].forEach(function (dir) {
      const handle = win.querySelector('.fw-resize-' + dir);
      if (handle) setupResizeHandle(win, handle, dir);
    });
  }

  function setupControls(win, key) {
    win.querySelector('.fw-back').addEventListener('click', function (e) {
      e.stopPropagation();
      try {
        const cw = win.querySelector('.fw-iframe').contentWindow;
        if (cw.NStockBack) cw.NStockBack();
      } catch (err) { /* page not loaded yet */ }
    });
    win.querySelector('.fw-close').addEventListener('click', function (e) {
      e.stopPropagation();
      closeWindow(win);
    });
    win.querySelector('.fw-max').addEventListener('click', function (e) {
      e.stopPropagation();
      toggleMaximize(win);
    });
    win.querySelector('.fw-split').addEventListener('click', function (e) {
      e.stopPropagation();
      splitWindow(win);
    });
    win.querySelector('.fw-shade').addEventListener('click', function (e) {
      e.stopPropagation();
      if (win._mode && win._mode !== 'float') minimizeWindow(win); else toggleShade(win);
    });
    // Double-click the title bar to maximize / restore
    win.querySelector('.fw-titlebar').addEventListener('dblclick', function (e) {
      if (e.target.closest('.fw-btn')) return;
      toggleMaximize(win);
    });
  }

  window.openWindow = function (url, title) {
    const key = normalizeUrl(url);

    if (openWindows[key]) {
      const win = openWindows[key];
      unshadeWindow(win);
      focusWindow(win);
      return;
    }

    const root = ensureRoot();
    const win = document.createElement('div');
    win.className = 'floating-window';

    const offset = (cascadeCount % 8) * 28;
    win.style.width = '900px';
    win.style.height = '620px';
    win.style.left = (70 + offset) + 'px';
    win.style.top = (headerHeight() + 16 + offset) + 'px';
    win._mode = 'float';
    cascadeCount++;

    win.innerHTML =
      '<div class="fw-inner">' +
        '<div class="fw-titlebar">' +
          '<button class="fw-btn fw-back" title="Back to the last page in this window" disabled>' +
            '<svg viewBox="0 0 16 16" width="13" height="13" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M10 3 5 8l5 5"/></svg>' +
          '</button>' +
          '<span class="fw-title"></span>' +
          '<div class="fw-controls">' +
            '<button class="fw-btn fw-shade" title="Minimize">\u2013</button>' +
            '<button class="fw-btn fw-split" title="Split screen">' +
              '<svg viewBox="0 0 16 16" width="13" height="13" fill="none" stroke="currentColor" stroke-width="1.5"><rect x="1.5" y="2.5" width="13" height="11" rx="1"/><line x1="8" y1="2.5" x2="8" y2="13.5"/></svg>' +
            '</button>' +
            '<button class="fw-btn fw-max" title="Maximize">\u25A2</button>' +
            '<button class="fw-btn fw-close" title="Close">\u00D7</button>' +
          '</div>' +
        '</div>' +
        '<div class="fw-body"><iframe class="fw-iframe" src=""></iframe></div>' +
      '</div>' +
      '<div class="fw-resize fw-resize-n"></div>' +
      '<div class="fw-resize fw-resize-s"></div>' +
      '<div class="fw-resize fw-resize-e"></div>' +
      '<div class="fw-resize fw-resize-w"></div>' +
      '<div class="fw-resize fw-resize-ne"></div>' +
      '<div class="fw-resize fw-resize-nw"></div>' +
      '<div class="fw-resize fw-resize-se"></div>' +
      '<div class="fw-resize fw-resize-sw"></div>';

    win.querySelector('.fw-title').textContent = title || 'Window';

    const iframeSrc = url + (url.indexOf('?') > -1 ? '&' : '?') + 'embed=1';
    const iframe = win.querySelector('.fw-iframe');
    // A name per window gives each one its own Back history (see nstock-nav.js)
    iframe.name = 'nstock-win-' + Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
    iframe.src = iframeSrc;
    // When you move to another page inside the window, retitle the window
    // from that page's heading so the title bar (and header) stay accurate.
    iframe.addEventListener('load', function () {
      try {
        const cw = iframe.contentWindow;
        win.querySelector('.fw-back').disabled = !(cw.NStockCanGoBack && cw.NStockCanGoBack());
      } catch (e) { /* not ready */ }
      updateHeaderControls();
      try {
        const h = iframe.contentDocument.querySelector('main h1, main h2, h1, h2');
        const text = h && h.textContent.trim().replace(/\s+/g, ' ');
        if (text) {
          win.querySelector('.fw-title').textContent = text;
          updateHeaderControls();
        }
      } catch (e) { /* different origin or not ready: keep the old title */ }
    });

    root.appendChild(win);
    openWindows[key] = win;

    win.addEventListener('mousedown', function () { focusWindow(win); });

    setupDrag(win);
    setupResize(win);
    setupControls(win, key);
    focusWindow(win);
  };

  // Click anywhere on the real page (not on a floating window) reveals it
  // by rolling every open window up to its title bar.
  document.addEventListener('mousedown', function (e) {
    if (!e.target.closest('.floating-window, .nstock-header, .nstock-sidebar, .nstock-backdrop')) {
      shadeAllWindows();
    }
  });

  // Header Back: step back inside the maximized window if one is in front,
  // otherwise let nstock-nav.js go back on the page itself.
  window.nstockWindowBack = function () {
    const win = topMaximized();
    if (!win) return false;
    try { win.querySelector('.fw-iframe').contentWindow.NStockBack(); } catch (e) { /* not loaded */ }
    return true;
  };

  setupHeaderControls();
  attachLinkInterception();

})();