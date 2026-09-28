// Adds the CSRF security token to every POST this app makes:
// normal forms (including ones added later or submitted from code),
// fetch() calls, and navigator.sendBeacon() saves.
(function () {
  var meta = document.querySelector('meta[name="csrf-token"]');
  if (!meta) return;
  var token = meta.getAttribute("content");

  function sameOrigin(url) {
    try { return new URL(url, window.location.href).origin === window.location.origin; }
    catch (e) { return false; }
  }

  function addToForm(form) {
    if ((form.getAttribute("method") || "get").toLowerCase() !== "post") return;
    if (!sameOrigin(form.getAttribute("action") || window.location.href)) return;
    var input = form.querySelector('input[name="csrf_token"]');
    if (!input) {
      input = document.createElement("input");
      input.type = "hidden";
      input.name = "csrf_token";
      form.appendChild(input);
    }
    input.value = token;
  }

  function addToAllForms() { document.querySelectorAll("form").forEach(addToForm); }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", addToAllForms);
  else addToAllForms();
  // Forms created after the page loads
  document.addEventListener("submit", function (e) { addToForm(e.target); }, true);
  // Forms submitted from code with form.submit(), which skips the submit event
  var nativeSubmit = HTMLFormElement.prototype.submit;
  HTMLFormElement.prototype.submit = function () { addToForm(this); return nativeSubmit.call(this); };

  var nativeFetch = window.fetch;
  window.fetch = function (input, init) {
    init = init || {};
    var method = (init.method || (input && input.method) || "GET").toUpperCase();
    var url = typeof input === "string" ? input : (input && input.url) || "";
    if (method !== "GET" && method !== "HEAD" && sameOrigin(url)) {
      var headers = new Headers(init.headers || (input && input.headers) || {});
      headers.set("X-CSRFToken", token);
      init.headers = headers;
    }
    return nativeFetch.call(this, input, init);
  };

  if (navigator.sendBeacon) {
    var nativeBeacon = navigator.sendBeacon.bind(navigator);
    navigator.sendBeacon = function (url, data) {
      if (sameOrigin(url)) {
        url += (url.indexOf("?") === -1 ? "?" : "&") + "csrf_token=" + encodeURIComponent(token);
      }
      return nativeBeacon(url, data);
    };
  }
})();