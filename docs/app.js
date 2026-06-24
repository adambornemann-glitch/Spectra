/* ============================================================
   Spectra docs — shared client utilities  (no dependencies)
   ============================================================ */
(function () {
  const D = window.SPECTRA;
  window.S = D;

  // ---- area color palette (stable, hashed-but-curated) -------------------
  const PALETTE = [
    "#8b6cff", "#46e0d0", "#5b7cff", "#ff6ec7", "#ffb454",
    "#5ddc8c", "#ff6b81", "#36c5f0", "#c792ff", "#f7768e",
    "#73daca", "#e0af68", "#7aa2f7", "#bb9af7", "#9ece6a",
    "#ff9e64", "#2ac3de", "#b4f9f8", "#ff7eb6",
  ];
  const areaColor = (() => {
    const order = (D.areas || []).map(a => a.name);
    const map = {};
    order.forEach((n, i) => { map[n] = PALETTE[i % PALETTE.length]; });
    return name => map[name] || "#8b94b4";
  })();
  window.areaColor = areaColor;

  // ---- number helpers ----------------------------------------------------
  const fmt = n => n.toLocaleString("en-US");
  window.fmt = fmt;

  function countUp(el, target, opts = {}) {
    const dur = opts.dur || 1100;
    const dec = opts.dec || 0;
    const suffix = opts.suffix || "";
    const final = (dec ? target.toFixed(dec) : target.toLocaleString("en-US")) + suffix;
    const start = performance.now();
    let done = false;
    function snap() { if (!done) { done = true; el.textContent = final; } }
    function tick(now) {
      if (done) return;
      const t = Math.min(1, (now - start) / dur);
      const e = 1 - Math.pow(1 - t, 3); // easeOutCubic
      const v = target * e;
      el.textContent = (dec ? v.toFixed(dec) : Math.round(v).toLocaleString("en-US")) + suffix;
      if (t < 1) requestAnimationFrame(tick);
      else snap();
    }
    requestAnimationFrame(tick);
    // wall-clock guard: guarantees the true value lands even if rAF is throttled
    // (e.g. the tab was in the background during the animation window).
    setTimeout(snap, dur + 400);
  }
  window.countUp = countUp;

  // reveal-on-load: trigger count-ups when scrolled into view
  function observeCounters() {
    const items = [...document.querySelectorAll("[data-count]")];
    const run = (el) => {
      if (el.dataset.done) return;
      el.dataset.done = "1";
      countUp(el, parseFloat(el.dataset.count), {
        dec: el.dataset.dec ? +el.dataset.dec : 0,
        suffix: el.dataset.suffix || "",
      });
    };
    const io = new IntersectionObserver((entries) => {
      entries.forEach(en => { if (en.isIntersecting) { run(en.target); io.unobserve(en.target); } });
    }, { threshold: 0.4 });
    const vh = window.innerHeight || 800;
    items.forEach(el => {
      const r = el.getBoundingClientRect();
      if (r.top < vh && r.bottom > 0) run(el);   // already on screen → don't wait on IO
      else io.observe(el);
    });
    // ultimate safety: every counter lands its true value even if rAF/IO are throttled
    setTimeout(() => items.forEach(run), 2600);
  }
  window.observeCounters = observeCounters;

  // ---- shared chrome (background + top nav) ------------------------------
  const PAGES = [
    ["index.html",    "Overview"],
    ["theorems.html", "Crown Jewels"],
    ["areas.html",    "Atlas"],
    ["graph.html",    "Dependency Galaxy"],
    ["files.html",    "Module Index"],
    ["roadmap.html",  "Frontier"],
  ];

  function mountChrome(active) {
    const bgField = document.createElement("div"); bgField.className = "bg-field";
    const bgGrid = document.createElement("div");  bgGrid.className = "bg-grid";
    document.body.prepend(bgGrid); document.body.prepend(bgField);

    const tabs = PAGES.map(([href, label]) =>
      `<a href="${href}" class="${href === active ? "active" : ""}">${label}</a>`
    ).join("");

    const header = document.createElement("header");
    header.className = "topbar";
    header.innerHTML = `
      <div class="wrap"><div class="row">
        <a class="brand" href="index.html" style="color:var(--ink)">
          <span class="glyph">σ</span>
          <span><b>Spectra</b> &nbsp;<span class="sub">Lean&nbsp;4 · mathematical physics</span></span>
        </a>
        <nav class="tabs">${tabs}</nav>
      </div></div>`;
    document.body.prepend(header);
  }
  window.mountChrome = mountChrome;

  function mountFooter() {
    const f = document.createElement("footer");
    f.className = "foot wrap";
    const when = (D.generated || "").slice(0, 10);
    f.innerHTML = `
      Snapshot of <span class="mono">${D.totals.files}</span> source files ·
      <span class="mono">${fmt(D.totals.lines)}</span> lines ·
      branch <span class="mono">${D.branch || "?"}</span> ·
      <span class="mono">${D.totals.sorries}</span> open proofs ·
      <span class="mono">0</span> local axioms<br>
      Generated from the live tree${when ? " · last commit " + when : ""} ·
      built with hand-rolled SVG &amp; canvas, no external libraries.`;
    document.body.appendChild(f);
  }
  window.mountFooter = mountFooter;

  // ---- misc dom helper ---------------------------------------------------
  // attrs may be a className string (common shorthand) or an attribute object.
  window.el = (tag, attrs = {}, html) => {
    const e = document.createElement(tag);
    if (typeof attrs === "string") {
      e.className = attrs;
    } else {
      for (const k in attrs) {
        if (k === "class") e.className = attrs[k];
        else if (k === "style") e.style.cssText = attrs[k];
        else e.setAttribute(k, attrs[k]);
      }
    }
    if (html != null) e.innerHTML = html;
    return e;
  };

  // describe a Lean module name compactly: drop "Spectra." prefix
  window.shortMod = m => m.replace(/^Spectra\./, "");
})();
