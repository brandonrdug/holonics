// ===== paper.js — the presentation face: Canvas 2D at device grain (outer carrier) + a vector codec carrying exact source values =====
(function (HR) {
  const isRat = (v) => v instanceof HR.Rat;
  class Paper {
    constructor(canvas, opts = {}) {
      this.canvas = canvas; this.ctx = canvas.getContext('2d'); this.dpr = opts.dpr || (typeof window !== 'undefined' ? window.devicePixelRatio || 1 : 1);
      this.resize(opts.width || canvas.clientWidth || 800, opts.height || canvas.clientHeight || 600);
      this.ink = opts.ink || '#101214'; this.paper = opts.paper || '#f6f7f4'; this.unit = opts.unit || 40; this.origin = opts.origin || [0, 0]; this.marks = [];
    }
    resize(w, h) { this.w = w; this.h = h; this.canvas.width = Math.round(w * this.dpr); this.canvas.height = Math.round(h * this.dpr); this.canvas.style.width = w + 'px'; this.canvas.style.height = h + 'px'; }
    px(p) { const x = isRat(p[0]) ? p[0].toNumber() : p[0], y = isRat(p[1]) ? p[1].toNumber() : p[1]; return [(this.origin[0] + x * this.unit) * this.dpr, (this.h - (this.origin[1] + y * this.unit)) * this.dpr]; }
    rec(kind, pts, attrs) { this.marks.push({ kind, pts: pts.map((p) => [isRat(p[0]) ? p[0].toString() : String(p[0]), isRat(p[1]) ? p[1].toString() : String(p[1])]), exact: pts.length > 0 && isRat(pts[0][0]), ...attrs }); }
    clear() { const c = this.ctx; c.setTransform(1, 0, 0, 1, 0, 0); c.fillStyle = this.paper; c.fillRect(0, 0, this.canvas.width, this.canvas.height); this.marks = []; }
    line(points, opts = {}) { const c = this.ctx; if (points.length < 2) return; const w = Math.max(1, Math.round(opts.width || 1)); this.rec('line', points, { width: w, role: opts.role || 'trace', colour: opts.color || null, dash: !!opts.dash, source: opts.source || null });
      c.lineWidth = w; c.strokeStyle = opts.color || this.ink; c.lineCap = opts.cap || 'butt'; c.lineJoin = 'miter'; c.setLineDash(opts.dash ? opts.dash.map((d) => d * this.dpr) : []); c.globalAlpha = opts.alpha ?? 1;
      const snap = (v) => (w % 2 === 1 ? Math.floor(v) + 0.5 : Math.round(v)); c.beginPath(); points.forEach((p, i) => { const [x, y] = this.px(p); if (i === 0) c.moveTo(snap(x), snap(y)); else c.lineTo(snap(x), snap(y)); }); c.stroke(); c.globalAlpha = 1; c.setLineDash([]); }
    fill(points, color, alpha = 1, role = 'face') { const c = this.ctx; this.rec('fill', points, { colour: color, role }); c.fillStyle = color; c.globalAlpha = alpha; c.beginPath(); points.forEach((p, i) => { const [x, y] = this.px(p); if (i === 0) c.moveTo(x, y); else c.lineTo(x, y); }); c.closePath(); c.fill(); c.globalAlpha = 1; }
    dot(p, rpx = 2, color) { const c = this.ctx; this.rec('dot', [p], { r: rpx, role: 'site', colour: color || null }); const [x, y] = this.px(p); c.fillStyle = color || this.ink; c.beginPath(); c.arc(x, y, rpx * this.dpr, 0, 2 * Math.PI); c.fill(); }
    ring(p, rpx = 3, color) { const c = this.ctx; this.rec('ring', [p], { r: rpx, role: 'mark', colour: color || null }); const [x, y] = this.px(p); c.strokeStyle = color || this.ink; c.lineWidth = 1; c.beginPath(); c.arc(Math.floor(x) + 0.5, Math.floor(y) + 0.5, rpx * this.dpr, 0, 2 * Math.PI); c.stroke(); }
    text(p, s, opts = {}) { const c = this.ctx; const [x, y] = this.px(p); c.fillStyle = opts.color || this.ink; c.font = `${(opts.size || 10) * this.dpr}px ${opts.font || 'ui-monospace, Menlo, monospace'}`; c.textBaseline = 'middle'; c.textAlign = opts.align || 'left'; c.fillText(s, x + (opts.dx || 0) * this.dpr, y + (opts.dy || 0) * this.dpr); }
    // raster face for a lattice field: one cell per site; `colour(k)` returns [r,g,b] for site k (the receiver's transduction lives in the caller)
    raster(N, colourAt) { const c = this.ctx; const img = c.createImageData(N, N);
      for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { const [r, g, b] = colourAt(i * N + j); const k = 4 * ((N - 1 - j) * N + i); img.data[k] = r; img.data[k + 1] = g; img.data[k + 2] = b; img.data[k + 3] = 255; }
      const off = (typeof OffscreenCanvas !== 'undefined') ? new OffscreenCanvas(N, N) : document.createElement('canvas'); off.width = N; off.height = N; off.getContext('2d').putImageData(img, 0, 0);
      const [x0, y0] = this.px([0, N]); const [x1, y1] = this.px([N, 0]); c.imageSmoothingEnabled = false; c.drawImage(off, x0, y0, x1 - x0, y1 - y0); c.imageSmoothingEnabled = true; this.rec('raster', [[0, 0], [N, N]], { role: 'field', colour: null, N }); }
    // the vector codec: every mark carries its source coordinates (exact when the source was exact); the gauge is a parameter
    svg(gauge = { name: 'declared', ink: '#101214', paper: '#f6f7f4' }) {
      const num = (s) => (s.includes('/') ? HR.R(s).toNumber() : parseFloat(s)); const P = (p) => this.px([num(p[0]), num(p[1])]).map((v) => (v / this.dpr).toFixed(2));
      const el = [`<svg xmlns="http://www.w3.org/2000/svg" width="${this.w}" height="${this.h}" data-gauge="${gauge.name}"><metadata>holonic-render-v1 presentation face; every mark carries its source value in data-source; the gauge carries no structure</metadata><rect width="${this.w}" height="${this.h}" fill="${gauge.paper}"/>`];
      for (const m of this.marks) { const dx = ` data-exact="${m.exact || m.source ? 1 : 0}"`; const src = ` data-source="${m.source ? m.source.replace(/"/g, '&quot;') : m.pts.map((q) => q.join(',')).join(';')}"`; const pts = m.pts.map(P);
        if (m.kind === 'line') el.push(`<polyline fill="none" stroke="${m.colour || gauge.ink}" stroke-width="${m.width}"${m.dash ? ' stroke-dasharray="2 3"' : ''} data-role="${m.role}"${src}${dx} points="${pts.map((q) => q.join(',')).join(' ')}"/>`);
        else if (m.kind === 'fill') el.push(`<polygon fill="${m.colour}" stroke="none" data-role="${m.role}"${src}${dx} points="${pts.map((q) => q.join(',')).join(' ')}"/>`);
        else if (m.kind === 'dot') el.push(`<circle fill="${m.colour || gauge.ink}" r="${m.r}" cx="${pts[0][0]}" cy="${pts[0][1]}" data-role="${m.role}"${src}${dx}/>`);
        else if (m.kind === 'ring') el.push(`<circle fill="none" stroke="${m.colour || gauge.ink}" r="${m.r}" cx="${pts[0][0]}" cy="${pts[0][1]}" data-role="${m.role}"${src}${dx}/>`);
        else if (m.kind === 'raster') el.push(`<!-- raster field ${m.N}×${m.N}: a receiver quotient rendered by the outer carrier -->`); }
      el.push('</svg>'); return el.join('\n'); }
  }
  // the gauge falsifier (presentation_gauge.rs structural_residue): mask every fill / stroke / data-gauge value; two gauges must agree byte for byte
  function structuralResidue(svg) { return svg.replace(/(fill|stroke|data-gauge)="[^"]*"/g, '$1="GAUGE"'); }
  HR.Paper = Paper; HR.structuralResidue = structuralResidue;
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
