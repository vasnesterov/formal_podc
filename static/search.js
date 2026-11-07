// Search page of formal_podc: client-side search over the paper database.
// The metadata (titles, authors, years, verdicts) is inlined in the page as JSON
// (#search-meta); the full text of the READMEs and differencies.md is fetched from
// search-text.json. Both are generated from the Markdown sources by the site generator.
(function () {
  "use strict";
  var meta = JSON.parse(document.getElementById("search-meta").textContent);
  var papers = meta.papers, authors = meta.authors;
  var qEl = document.getElementById("q"), yearEl = document.getElementById("year");
  var statusEl = document.getElementById("status");
  var chipEls = Array.prototype.slice.call(document.querySelectorAll(".vchip"));
  var authorEl = document.getElementById("author"), countEl = document.getElementById("count");
  var listEl = document.getElementById("results"), clearEl = document.querySelector(".search .clear");
  // The labels of the README legend, plus ⏳ for papers not formalized yet.
  var badge = { correct: ["✅", "correct"], slip: ["✏️", "slip"], easy: ["🔧", "easy fix"], hard: ["🛠️", "hard fix"],
    weakened: ["⚠️", "weakened"], lost: ["❌", "intent lost"], todo: ["⏳", "not yet verified"] };

  // Lowercase, strip diacritics (same folding as `foldStr` in PodcSite/Search.lean).
  var extra = { "ł": "l", "ø": "o", "đ": "d", "ı": "i", "ß": "ss", "æ": "ae", "œ": "oe" };
  function foldChar(c) {
    var l = c.toLowerCase();
    return extra[l] || l.normalize("NFD").replace(/[̀-ͯ]/g, "");
  }
  function fold(s) { var o = ""; for (var c of s) o += foldChar(c); return o; }
  // Folded text plus, for each folded position, the index of the original character.
  function foldMap(s) {
    var f = "", map = [], i = 0;
    for (var c of s) { var x = foldChar(c); for (var k = 0; k < x.length; k++) { f += x[k]; map.push(i); } i += c.length; }
    map.push(i);
    return { f: f, map: map };
  }
  function esc(s) {
    return s.replace(/[&<>"]/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]; });
  }
  // HTML of `s` with every occurrence of the (folded) terms wrapped in <mark>.
  function highlight(s, terms) {
    if (!terms.length) return esc(s);
    var fm = foldMap(s), marks = [];
    terms.forEach(function (t) {
      for (var p = fm.f.indexOf(t); p >= 0; p = fm.f.indexOf(t, p + 1)) marks.push([fm.map[p], fm.map[p + t.length]]);
    });
    marks.sort(function (a, b) { return a[0] - b[0]; });
    var out = "", pos = 0;
    marks.forEach(function (m) {
      if (m[0] < pos) { if (m[1] > pos) { out += "<mark>" + esc(s.slice(pos, m[1])) + "</mark>"; pos = m[1]; } return; }
      out += esc(s.slice(pos, m[0])) + "<mark>" + esc(s.slice(m[0], m[1])) + "</mark>";
      pos = m[1];
    });
    return out + esc(s.slice(pos));
  }
  // A ~200-character excerpt of `text` around the first occurrence of `term`.
  function snippet(text, term, terms) {
    var fm = foldMap(text), p = fm.f.indexOf(term);
    if (p < 0) return "";
    var start = Math.max(0, fm.map[p] - 90), end = Math.min(text.length, fm.map[p] + 110);
    while (start > 0 && text[start - 1] !== " ") start--;
    while (end < text.length && text[end] !== " ") end++;
    return (start > 0 ? "… " : "") + highlight(text.slice(start, end), terms) + (end < text.length ? " …" : "");
  }

  papers.forEach(function (p, i) {
    p.i = i;
    p.names = p.a.map(function (k) { return authors[k]; });
    p.ft = fold(p.t + " " + (p.s || ""));
    p.fa = p.names.map(fold);
    p.fm = fold((p.m || "") + " " + p.y);
  });
  var foldedAuthors = authors.map(fold);
  var texts = null;
  fetch("search-text.json").then(function (r) { return r.json(); }).then(function (d) {
    texts = d;
    papers.forEach(function (p, i) { p.fb = fold(d.b[i] || ""); p.fd = fold(d.d[i] || ""); });
    run(false);
  }).catch(function () { texts = false; });

  function state() {
    var v = chipEls.filter(function (c) { return c.getAttribute("aria-pressed") === "true"; })
      .map(function (c) { return c.dataset.v; });
    return { q: qEl.value.trim(), year: yearEl.value, status: statusEl.value, verdicts: v, author: authorEl.value.trim() };
  }
  function setChips(vs) {
    chipEls.forEach(function (c) { c.setAttribute("aria-pressed", vs.indexOf(c.dataset.v) >= 0 ? "true" : "false"); });
  }
  function selectValue(el, v) {
    el.value = Array.prototype.some.call(el.options, function (o) { return o.value === v; }) ? v : "";
  }
  function readUrl() {
    var u = new URLSearchParams(location.search);
    qEl.value = u.get("q") || "";
    selectValue(yearEl, u.get("year") || "");
    // verdict=weakened,lost; the single form status=<label> is understood too
    var vs = (u.get("verdict") || "").split(",").filter(Boolean), st = u.get("status") || "";
    if (chipEls.some(function (c) { return c.dataset.v === st; })) { vs.push(st); st = ""; }
    selectValue(statusEl, st);
    setChips(vs);
    authorEl.value = u.get("author") || "";
  }
  function urlOf(s) {
    var u = new URLSearchParams();
    if (s.q) u.set("q", s.q);
    if (s.year) u.set("year", s.year);
    if (s.status) u.set("status", s.status);
    if (s.verdicts.length) u.set("verdict", s.verdicts.join(","));
    if (s.author) u.set("author", s.author);
    var qs = u.toString().replace(/%2C/g, ",");
    return location.pathname + (qs ? "?" + qs : "");
  }

  function run(push) {
    var s = state(), terms = fold(s.q).split(/\s+/).filter(Boolean);
    var fa = fold(s.author);
    // An author name chosen from the list matches exactly; anything else is a substring match.
    var exact = foldedAuthors.indexOf(fa) >= 0;
    var hits = [];
    papers.forEach(function (p) {
      if (s.year && p.y !== s.year) return;
      if (s.status && !(s.status === p.v || (s.status === "formalized" && p.v !== "todo"))) return;
      // "responded" narrows the other chips: papers with a response from their authors
      var vs = s.verdicts.filter(function (v) { return v !== "responded"; });
      if (vs.length && vs.indexOf(p.v) < 0) return;
      if (s.verdicts.indexOf("responded") >= 0 && !p.r) return;
      if (fa && !p.fa.some(function (a) { return exact ? a === fa : a.indexOf(fa) >= 0; })) return;
      var score = 0, bodyTerm = null;
      for (var k = 0; k < terms.length; k++) {
        var t = terms[k], sc = 0;
        if (p.ft.indexOf(t) >= 0) sc = 10;
        else if (p.fa.some(function (a) { return a.indexOf(t) >= 0; })) sc = 8;
        else if (p.fm.indexOf(t) >= 0) sc = 3;
        else if (texts && p.fb.indexOf(t) >= 0) { sc = 1; bodyTerm = bodyTerm || [t, "b"]; }
        else if (texts && p.fd.indexOf(t) >= 0) { sc = 0.5; bodyTerm = bodyTerm || [t, "d"]; }
        if (!sc) return;
        score += sc;
      }
      hits.push({ p: p, score: score, bodyTerm: bodyTerm });
    });
    hits.sort(function (a, b) { return b.score - a.score || a.p.i - b.p.i; });
    render(hits, terms);
    var n = hits.length, total = papers.length;
    var filtered = terms.length || s.year || s.status || s.verdicts.length || s.author;
    countEl.textContent = (filtered ? n + " of " + total : total) + " paper" + (total === 1 ? "" : "s") +
      (terms.length && texts === null ? " (loading full text…)" : "");
    clearEl.hidden = !filtered;
    var url = urlOf(s);
    if (url !== location.pathname + location.search) history[push ? "pushState" : "replaceState"](null, "", url);
  }

  function render(hits, terms) {
    if (!hits.length) { listEl.innerHTML = '<li class="none">No papers match.</li>'; return; }
    listEl.innerHTML = hits.map(function (h) {
      var p = h.p, b = badge[p.v] || ["?", "verdict unknown"];
      var names = p.names.map(function (n) {
        return '<button type="button" class="author-link" data-author="' + esc(n) + '">' + highlight(n, terms) + "</button>";
      }).join(", ");
      var snip = "";
      if (h.bodyTerm && texts) {
        var src = h.bodyTerm[1] === "b" ? texts.b[p.i] : texts.d[p.i];
        snip = '<p class="snippet">' + (h.bodyTerm[1] === "d" ? '<span class="src">differences:</span> ' : "") +
          snippet(src, h.bodyTerm[0], terms) + "</p>";
      }
      return '<li class="result v-' + p.v + '">' +
        '<div class="r-head"><a class="r-title" href="' + esc(p.u) + '">' + highlight(p.t, terms) + "</a></div>" +
        '<p class="r-meta"><span class="badge v-' + p.v + '">' + b[0] + " " + b[1] + "</span> " +
          (p.r ? '<span class="badge v-responded">💬 author responded</span> ' : "") +
        names + ' · <span class="r-year">PODC ' + p.y + "</span>" +
        (p.c ? " · " + p.c + " citations" : "") +
        (p.v === "todo" ? ' · <a href="' + esc(p.u) + '">DOI</a>' +
          (p.x ? ' · <a href="https://arxiv.org/abs/' + esc(p.x) + '">arXiv</a>' : "") : "") + "</p>" +
        (p.m ? '<p class="r-summary">' + highlight(p.m, terms) + "</p>" : "") + snip + "</li>";
    }).join("");
  }

  // Typing updates the current history entry; the first keystroke after a pause of 800 ms (or a
  // filter change) starts a new one, so back/forward steps through searches, not keystrokes.
  var pushNext = true, timer = null;
  qEl.addEventListener("input", function () {
    run(pushNext);
    pushNext = false;
    clearTimeout(timer);
    timer = setTimeout(function () { pushNext = true; }, 800);
  });
  yearEl.addEventListener("change", function () { run(true); });
  statusEl.addEventListener("change", function () {
    if (statusEl.value === "todo") setChips([]);
    run(true);
  });
  chipEls.forEach(function (c) {
    c.addEventListener("click", function () {
      c.setAttribute("aria-pressed", c.getAttribute("aria-pressed") === "true" ? "false" : "true");
      if (statusEl.value === "todo") statusEl.value = "";
      run(true);
    });
  });
  authorEl.addEventListener("change", function () { run(true); });
  authorEl.addEventListener("input", function () { run(false); });
  document.querySelector("form.search").addEventListener("submit", function (e) { e.preventDefault(); run(true); });
  clearEl.addEventListener("click", function (e) {
    e.preventDefault(); qEl.value = ""; yearEl.value = ""; statusEl.value = ""; setChips([]); authorEl.value = "";
    run(true); qEl.focus();
  });
  listEl.addEventListener("click", function (e) {
    var a = e.target.closest(".author-link");
    if (a) { authorEl.value = a.dataset.author; run(true); window.scrollTo(0, 0); }
  });
  window.addEventListener("popstate", function () { readUrl(); run(false); });

  readUrl();
  run(false);
  if (!qEl.value) qEl.focus();
})();
