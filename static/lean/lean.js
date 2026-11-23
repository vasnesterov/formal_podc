// Lean code pages: definition links of names in source listings, and taps on touch screens.
// Listings carry no <a> per name (to keep pages small); the definition URL is in the hover text
// of the paper's hover table (window.versoHoversUrl), as `p.def-link a`.
(function () {
  "use strict";
  // `?touch` in the URL forces the touch behaviour (for testing on desktop).
  var touch = (window.matchMedia && window.matchMedia("(hover: none)").matches) || /[?&]touch\b/.test(location.search);
  var links = null;
  if (window.versoHoversUrl) {
    fetch(window.versoHoversUrl).then(function (r) { return r.json(); })
      .then(function (d) { links = d; }).catch(function () { links = {}; });
  }
  document.addEventListener("click", function (e) {
    var tok = e.target.closest(".hl.lean .const.token");
    if (!tok) return;
    var a = tok.closest("a");
    // On touch screens the first tap shows the hover; a tap while it is shown follows the link.
    if (touch && tok._tippy && !tok._tippy.state.isVisible) {
      e.preventDefault();
      tok._tippy.show();
      return;
    }
    if (!a && links) {
      var html = links[tok.dataset.versoHover], href = null;
      if (html) {
        var div = document.createElement("div");
        div.innerHTML = html;
        var link = div.querySelector("p.def-link a");
        href = link && link.getAttribute("href");
      }
      if (href) {
        if (e.ctrlKey || e.metaKey) window.open(href, "_blank");
        else window.location.href = new URL(href, document.baseURI).href;
      }
    }
  }, true);
})();
