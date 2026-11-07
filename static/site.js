// Filter and sort for the papers table on the index page (progressive enhancement:
// without JavaScript the full table, in README order, is shown).
(function () {
  "use strict";
  function init() {
    var table = document.querySelector("table.papers");
    if (!table || !table.querySelector("th.year")) return;
    var tbody = table.tBodies[0];
    var rows = Array.prototype.slice.call(tbody.rows);
    rows.forEach(function (r, i) { r.dataset.order = String(i); });

    var labels = { correct: "✅ correct", slip: "✏️ slip", easy: "🔧 easy fix", hard: "🛠️ hard fix",
      weakened: "⚠️ weakened", lost: "❌ intent lost" };
    var counts = {};
    var years = [];
    rows.forEach(function (r) {
      counts[r.dataset.verdict] = (counts[r.dataset.verdict] || 0) + 1;
      if (years.indexOf(r.dataset.year) < 0) years.push(r.dataset.year);
    });
    years.sort();

    var state = { verdict: "", year: "", q: "" };
    var box = document.createElement("div");
    box.className = "filters";

    var search = document.createElement("input");
    search.type = "search";
    search.placeholder = "Search title, authors, verdict…";
    search.setAttribute("aria-label", "Search papers");

    var chips = document.createElement("div");
    chips.className = "chips";
    chips.setAttribute("role", "group");
    chips.setAttribute("aria-label", "Filter by verdict");
    var buttons = [];
    [["", "All (" + rows.length + ")"]].concat(
      ["correct", "slip", "easy", "hard", "weakened", "lost"]
        .filter(function (v) { return counts[v]; })
        .map(function (v) { return [v, labels[v] + " (" + counts[v] + ")"]; })
    ).forEach(function (pair) {
      var b = document.createElement("button");
      b.type = "button";
      b.textContent = pair[1];
      b.dataset.verdict = pair[0];
      b.setAttribute("aria-pressed", pair[0] === "" ? "true" : "false");
      b.addEventListener("click", function () {
        state.verdict = pair[0];
        buttons.forEach(function (x) { x.setAttribute("aria-pressed", x === b ? "true" : "false"); });
        apply();
      });
      buttons.push(b);
      chips.appendChild(b);
    });

    var select = document.createElement("select");
    select.setAttribute("aria-label", "Filter by year");
    var all = document.createElement("option");
    all.value = ""; all.textContent = "All years";
    select.appendChild(all);
    years.forEach(function (y) {
      var o = document.createElement("option");
      o.value = y; o.textContent = "PODC " + y;
      select.appendChild(o);
    });
    select.addEventListener("change", function () { state.year = select.value; apply(); });
    search.addEventListener("input", function () { state.q = search.value.trim().toLowerCase(); apply(); });

    var count = document.createElement("span");
    count.className = "count";
    count.setAttribute("aria-live", "polite");

    box.appendChild(search);
    box.appendChild(chips);
    box.appendChild(select);
    box.appendChild(count);
    var wrap = table.closest(".table-wrap") || table;
    wrap.parentNode.insertBefore(box, wrap);

    function apply() {
      var shown = 0;
      rows.forEach(function (r) {
        var ok = (!state.verdict || r.dataset.verdict === state.verdict) &&
          (!state.year || r.dataset.year === state.year) &&
          (!state.q || r.textContent.toLowerCase().indexOf(state.q) >= 0);
        r.classList.toggle("hidden", !ok);
        if (ok) shown++;
      });
      count.textContent = shown === rows.length ? "" : shown + " of " + rows.length + " shown";
    }

    // Sorting: click "Year" or "Citations" to sort; a third click restores the README order.
    var sortState = { key: null, dir: 0 };
    function cellNum(r, cls) {
      var c = r.querySelector("td." + cls);
      return c ? parseInt(c.textContent, 10) || 0 : 0;
    }
    ["year", "cites"].forEach(function (cls) {
      var th = table.querySelector("th." + cls);
      if (!th) return;
      th.style.cursor = "pointer";
      th.title = "Sort";
      th.setAttribute("tabindex", "0");
      function sort() {
        if (sortState.key !== cls) { sortState.key = cls; sortState.dir = -1; }
        else if (sortState.dir === -1) sortState.dir = 1;
        else { sortState.key = null; sortState.dir = 0; }
        var sorted = rows.slice().sort(function (a, b) {
          if (!sortState.key) return a.dataset.order - b.dataset.order;
          var d = (cellNum(a, cls) - cellNum(b, cls)) * sortState.dir;
          return d || a.dataset.order - b.dataset.order;
        });
        sorted.forEach(function (r) { tbody.appendChild(r); });
        table.querySelectorAll("th").forEach(function (h) { h.removeAttribute("aria-sort"); });
        if (sortState.key) th.setAttribute("aria-sort", sortState.dir < 0 ? "descending" : "ascending");
      }
      th.addEventListener("click", sort);
      th.addEventListener("keydown", function (e) { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); sort(); } });
    });
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", init);
  else init();
})();

// Paper pages: a link to an anchor inside a collapsed section (<details>) opens the section.
(function () {
  "use strict";
  function reveal() {
    var id = location.hash.slice(1);
    if (!id) return;
    try { id = decodeURIComponent(id); } catch (e) { /* keep it as is */ }
    var el = document.getElementById(id);
    if (!el) return;
    var opened = false;
    for (var p = el; p; p = p.parentElement) {
      if (p.tagName === "DETAILS" && !p.open) { p.open = true; opened = true; }
    }
    if (opened) el.scrollIntoView();
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", reveal);
  else reveal();
  window.addEventListener("hashchange", reveal);
})();
