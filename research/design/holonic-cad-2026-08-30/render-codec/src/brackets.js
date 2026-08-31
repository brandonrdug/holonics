// ===== brackets.js — witnessed level brackets of an EXACT function on a rational grid, and their isolation =====
// model_surface.rs certified_crossings: a level is a certified sign change of reading − level between consecutive stations; the crossing is
// bracketed exactly and the bracket is what is drawn. certified_face.rs: count == 1 → isolate it and deposit a located feature.
// presentation_gauge.rs: a feature's drawn coordinate is its interval midpoint — "a chart convenience, not a claim that the root is there;
// the exact isolating interval travels with the mark". Isolation here is exact bisection along a grid edge: every midpoint is rational,
// every sign is exact, and the interval shrinks to h/2^k. The picture then looks continuous while every vertex is a witnessed interval.
(function (HR) {
  const { Rat, R } = HR;
  const half = R('1/2');
  // ---- dual-lattice brackets (the coarse form; kept for Float64 fields where no exact function exists) ----
  function levelBrackets(f, win, n, levels) {
    const x0 = R(win.x0), x1 = R(win.x1), y0 = R(win.y0), y1 = R(win.y1); const nx = typeof n === 'number' ? n : n.nx, ny = typeof n === 'number' ? n : n.ny;
    const hx = x1.sub(x0).div(nx), hy = y1.sub(y0).div(ny); const L = levels.map(R);
    const band = new Int32Array((nx + 1) * (ny + 1)); const stations = []; const X = [], Y = [];
    for (let i = 0; i <= nx; i++) X.push(x0.add(hx.mul(i))); for (let j = 0; j <= ny; j++) Y.push(y0.add(hy.mul(j)));
    for (let i = 0; i <= nx; i++) for (let j = 0; j <= ny; j++) { const v = f(X[i], Y[j]); let b = 0; while (b < L.length && v.gt(L[b])) b++; band[i * (ny + 1) + j] = b; if (b < L.length && v.eq(L[b])) stations.push({ p: [X[i], Y[j]], level: L[b] }); }
    const clampY = (y) => Rat.max(y0, Rat.min(y1, y)), clampX = (x) => Rat.max(x0, Rat.min(x1, x));
    const segs = [];
    for (let i = 0; i <= nx; i++) for (let j = 0; j <= ny; j++) {
      const k = i * (ny + 1) + j;
      if (i < nx) { const kk = (i + 1) * (ny + 1) + j; if (band[k] !== band[kk]) { const xm = x0.add(hx.mul(R(i).add(half))); segs.push({ a: [xm, clampY(y0.add(hy.mul(R(j).sub(half))))], b: [xm, clampY(y0.add(hy.mul(R(j).add(half))))], between: [Math.min(band[k], band[kk]), Math.max(band[k], band[kk])] }); } }
      if (j < ny) { const kk = i * (ny + 1) + j + 1; if (band[k] !== band[kk]) { const ym = y0.add(hy.mul(R(j).add(half))); segs.push({ a: [clampX(x0.add(hx.mul(R(i).sub(half)))), ym], b: [clampX(x0.add(hx.mul(R(i).add(half)))), ym], between: [Math.min(band[k], band[kk]), Math.max(band[k], band[kk])] }); } }
    }
    return { segs, stations, band, nx, ny, hx, hy, evaluations: (nx + 1) * (ny + 1) };
  }
  function components(segs) {
    const parent = new Map(); const find = (k) => { while (parent.get(k) !== k) { parent.set(k, parent.get(parent.get(k))); k = parent.get(k); } return k; }; const add = (k) => { if (!parent.has(k)) parent.set(k, k); };
    for (const s of segs) { const a = HR.pkey(s.a), b = HR.pkey(s.b); add(a); add(b); parent.set(find(a), find(b)); }
    const roots = new Set(); for (const k of parent.keys()) roots.add(find(k)); return roots.size;
  }
  // ---- isolated contour of f = level: exact bisection on every grid edge with a sign change; cells joined under their exact sign pattern ----
  // f: (x, y) → Rat exact. Returns segments whose endpoints are interval midpoints, each carrying its isolating interval.
  function isolate(f, win, n, level, k = 6) {
    const x0 = R(win.x0), x1 = R(win.x1), y0 = R(win.y0), y1 = R(win.y1); const nx = typeof n === 'number' ? n : n.nx, ny = typeof n === 'number' ? n : n.ny; const L = R(level);
    const hx = x1.sub(x0).div(nx), hy = y1.sub(y0).div(ny); const X = [], Y = []; for (let i = 0; i <= nx; i++) X.push(x0.add(hx.mul(i))); for (let j = 0; j <= ny; j++) Y.push(y0.add(hy.mul(j)));
    const S = new Int8Array((nx + 1) * (ny + 1)); let evals = 0; const stations = [];
    for (let i = 0; i <= nx; i++) for (let j = 0; j <= ny; j++) { const s = f(X[i], Y[j]).sub(L).sign(); evals++; S[i * (ny + 1) + j] = s; if (s === 0) stations.push([X[i], Y[j]]); }
    // a node exactly on the level is a witness; for pairing it is read as +, and its vertex is the node itself
    const sg = (i, j) => (S[i * (ny + 1) + j] === 0 ? 1 : S[i * (ny + 1) + j]);
    // bisect along the edge A→B (parameter t ∈ [0,1]) k times; exact rational midpoints
    const bisect = (A, B, sA) => { let lo = Rat.ZERO, hi = Rat.ONE; for (let it = 0; it < k; it++) { const m = lo.add(hi).div(2); const P = [A[0].add(B[0].sub(A[0]).mul(m)), A[1].add(B[1].sub(A[1]).mul(m))]; const s = f(P[0], P[1]).sub(L).sign(); evals++; if (s === 0) { lo = m; hi = m; break; } if (s === sA) lo = m; else hi = m; }
      const mid = lo.add(hi).div(2); return { p: [A[0].add(B[0].sub(A[0]).mul(mid)), A[1].add(B[1].sub(A[1]).mul(mid))], t: [lo, hi] }; };
    // vertices on horizontal edges (i,j)→(i+1,j) and vertical edges (i,j)→(i,j+1)
    const H = new Map(), V = new Map(); const nodeZero = (i, j) => S[i * (ny + 1) + j] === 0;
    for (let i = 0; i < nx; i++) for (let j = 0; j <= ny; j++) { if (sg(i, j) !== sg(i + 1, j)) { if (nodeZero(i, j)) H.set(i + ',' + j, { p: [X[i], Y[j]], t: [Rat.ZERO, Rat.ZERO] }); else if (nodeZero(i + 1, j)) H.set(i + ',' + j, { p: [X[i + 1], Y[j]], t: [Rat.ONE, Rat.ONE] }); else H.set(i + ',' + j, bisect([X[i], Y[j]], [X[i + 1], Y[j]], sg(i, j))); } }
    for (let i = 0; i <= nx; i++) for (let j = 0; j < ny; j++) { if (sg(i, j) !== sg(i, j + 1)) { if (nodeZero(i, j)) V.set(i + ',' + j, { p: [X[i], Y[j]], t: [Rat.ZERO, Rat.ZERO] }); else if (nodeZero(i, j + 1)) V.set(i + ',' + j, { p: [X[i], Y[j + 1]], t: [Rat.ONE, Rat.ONE] }); else V.set(i + ',' + j, bisect([X[i], Y[j]], [X[i], Y[j + 1]], sg(i, j))); } }
    const segs = []; let ambiguous = 0;
    for (let i = 0; i < nx; i++) for (let j = 0; j < ny; j++) {
      const e = [H.get(i + ',' + j), V.get((i + 1) + ',' + j), H.get(i + ',' + (j + 1)), V.get(i + ',' + j)]; // bottom, right, top, left
      const on = e.map((v, idx) => (v ? idx : -1)).filter((idx) => idx >= 0);
      if (on.length === 2) segs.push({ a: e[on[0]].p, b: e[on[1]].p, ta: e[on[0]].t, tb: e[on[1]].t });
      else if (on.length === 4) { // saddle cell: the centre's exact sign is the witness that decides the pairing
        ambiguous++; const c = f(X[i].add(hx.div(2)), Y[j].add(hy.div(2))).sub(L).sign(); evals++; const sBL = sg(i, j);
        // corners: BL (i,j), BR (i+1,j), TR (i+1,j+1), TL (i,j+1); with sBL = sTR ≠ sBR = sTL. If centre sign equals sBL, the BL and TR corners join through the centre: pair (left,bottom) and (top,right)? No — BL-region contains the centre, so the contour separates BR and TL from it: pair (bottom,right) and (top,left).
        if (c === sBL || c === 0) { segs.push({ a: e[0].p, b: e[1].p, ta: e[0].t, tb: e[1].t }); segs.push({ a: e[2].p, b: e[3].p, ta: e[2].t, tb: e[3].t }); }
        else { segs.push({ a: e[3].p, b: e[0].p, ta: e[3].t, tb: e[0].t }); segs.push({ a: e[1].p, b: e[2].p, ta: e[1].t, tb: e[2].t }); } }
    }
    return { segs, stations, ambiguous, evaluations: evals, vertices: H.size + V.size, width: { x: hx.div(R(2n ** BigInt(k))), y: hy.div(R(2n ** BigInt(k))) } };
  }
  HR.Brackets = { levelBrackets, components, isolate };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
