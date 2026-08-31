// ===== circuit.js — a finite lattice that transports action: exact Kirchhoff over the Gaussian rationals ℚ(i) on ℤ³ =====
// The Complex Parametron carrier as data: nodes, incidence B, admittances M (a diagonal of ℚ(i)), G = BᵀMB, a pump; potentials and
// currents solved exactly by Gaussian elimination with BigInt. Nets are stored as the node–edge INCIDENCE (a hypergraph's incidence
// matrix); the vertex–vertex matrix A = MMᵀ − diag loses which terminals share a net (MathWorld, Hypergraph) and is never the store.
(function (HR) {
  const { Rat, R } = HR;
  class GRat { // a + b i over ℚ
    constructor(re, im = 0) { this.re = R(re); this.im = R(im); }
    static of(x) { if (x instanceof GRat) return x; if (x && typeof x === 'object' && 're' in x) return new GRat(x.re, x.im || 0); return new GRat(x, 0); }
    add(o) { o = GRat.of(o); return new GRat(this.re.add(o.re), this.im.add(o.im)); }
    sub(o) { o = GRat.of(o); return new GRat(this.re.sub(o.re), this.im.sub(o.im)); }
    mul(o) { o = GRat.of(o); return new GRat(this.re.mul(o.re).sub(this.im.mul(o.im)), this.re.mul(o.im).add(this.im.mul(o.re))); }
    neg() { return new GRat(this.re.neg(), this.im.neg()); }
    conj() { return new GRat(this.re, this.im.neg()); }
    abs2() { return this.re.mul(this.re).add(this.im.mul(this.im)); }
    div(o) { o = GRat.of(o); const n = o.abs2(); if (n.isZero()) throw new Error('ℚ(i): division by zero'); const p = this.mul(o.conj()); return new GRat(p.re.div(n), p.im.div(n)); }
    isZero() { return this.re.isZero() && this.im.isZero(); }
    toString() { return this.im.isZero() ? this.re.toString() : `${this.re}${this.im.sign() < 0 ? '−' : '+'}${this.im.abs()}i`; }
  }
  // Gauss–Jordan over ℚ(i); any nonzero pivot is exact, so the first one found is taken
  function solve(A, b) {
    const n = A.length; const M = A.map((row, i) => [...row.map(GRat.of), GRat.of(b[i])]);
    for (let c = 0; c < n; c++) { let p = -1; for (let r = c; r < n; r++) if (!M[r][c].isZero()) { p = r; break; } if (p < 0) throw new Error('singular: the lattice has a floating component'); [M[c], M[p]] = [M[p], M[c]];
      const inv = new GRat(1).div(M[c][c]); for (let j = c; j <= n; j++) M[c][j] = M[c][j].mul(inv);
      for (let r = 0; r < n; r++) { if (r === c || M[r][c].isZero()) continue; const f = M[r][c]; for (let j = c; j <= n; j++) M[r][j] = M[r][j].sub(f.mul(M[c][j])); } }
    return M.map((row) => row[n]);
  }
  // ℤ³ lattice [0,g)³ with an admittance per direction and pumps at named nodes; ground fixes one potential
  function LatticeCircuit(spec) {
    const g = spec.g; const nodes = [], index = new Map(); const key = (c) => c.join(',');
    for (let i = 0; i < g; i++) for (let j = 0; j < g; j++) for (let k = 0; k < g; k++) { index.set(key([i, j, k]), nodes.length); nodes.push({ id: nodes.length, ints: [i, j, k], coords: [R(i), R(j), R(k)] }); }
    const adm = ['x', 'y', 'z'].map((d) => GRat.of(spec.admittance[d]));
    const edges = []; for (const v of nodes) for (let d = 0; d < 3; d++) { const n = v.ints.slice(); n[d] += 1; const w = index.get(key(n)); if (w === undefined) continue; edges.push({ id: edges.length, from: v.id, to: w, direction: d, y: adm[d] }); }
    const N = nodes.length; const J = nodes.map(() => new GRat(0)); let sum = new GRat(0);
    for (const s of spec.sources) { const n = index.get(key(s.node)); if (n === undefined) throw new Error('source off the lattice'); J[n] = J[n].add(GRat.of(s.current)); sum = sum.add(GRat.of(s.current)); }
    if (!sum.isZero()) throw new Error('pumps must sum to zero: charge has nowhere to go');
    // G = Bᵀ Y B assembled from the incidence: G[a][a] += y, G[b][b] += y, G[a][b] −= y, G[b][a] −= y
    const G = nodes.map(() => nodes.map(() => new GRat(0)));
    for (const e of edges) { const a = e.from, b = e.to; G[a][a] = G[a][a].add(e.y); G[b][b] = G[b][b].add(e.y); G[a][b] = G[a][b].sub(e.y); G[b][a] = G[b][a].sub(e.y); }
    const ground = index.get(key(spec.ground)); const keep = nodes.map((n) => n.id).filter((i) => i !== ground);
    const A = keep.map((i) => keep.map((j) => G[i][j])), rhs = keep.map((i) => J[i]);
    const t0 = Date.now(); const sol = solve(A, rhs); const ms = Date.now() - t0;
    const phi = nodes.map(() => new GRat(0)); keep.forEach((i, k) => { phi[i] = sol[k]; });
    // I_e = y_e (φ_from − φ_to): positive when action flows from → to
    for (const e of edges) e.I = e.y.mul(phi[e.from].sub(phi[e.to]));
    // KCL as an exact receipt: outflow − inflow = injection at every node
    let worst = Rat.ZERO; const kcl = nodes.map((n) => { let s = new GRat(0); for (const e of edges) { if (e.from === n.id) s = s.add(e.I); if (e.to === n.id) s = s.sub(e.I); } const r = s.sub(J[n.id]); if (r.abs2().gt(worst)) worst = r.abs2(); return r; });
    // dissipation Σ Re(conj(I) (φ_from − φ_to)) and reactive Σ Im(...)
    let P = new GRat(0); for (const e of edges) P = P.add(e.I.conj().mul(phi[e.from].sub(phi[e.to])));
    // incidence (the hypergraph store): each node is a net; its hyperedge is the set of edge terminals meeting it
    const incidence = nodes.map((n) => edges.filter((e) => e.from === n.id || e.to === n.id).map((e) => e.id));
    return { g, nodes, edges, phi, J, ground, kcl, kclWorst: worst, power: P, incidence, solveMs: ms, unknowns: keep.length };
  }
  // exact integer ceiling of √(q) for a rational q ≥ 0: the smallest k with k² ≥ q
  function ceilSqrt(q) { q = R(q); if (q.sign() <= 0) return 0n; let k = BigInt(Math.floor(Math.sqrt(Number(q.n) / Number(q.d)))); while (k * k * q.d < q.n) k++; while (k > 0n && (k - 1n) * (k - 1n) * q.d >= q.n) k--; return k; }
  // stroke law for a complex current: width = ⌈|I| / unit⌉ device pixels, computed without a float on |I|
  function widthPx(I, unit) { const u = R(unit); const q = I.abs2().div(u.mul(u)); return Math.max(1, Number(ceilSqrt(q))); }
  // the schematic receiver: symbols along the projected lattice, width by current, hand by the real part's sign, colour by transduction
  function schematicPlan(circ, chart, opts = {}) {
    const P = circ.nodes.map((n) => chart.project([...n.coords, Rat.ZERO]));
    const segs = circ.edges.map((e) => ({ a: P[e.from].xy, b: P[e.to].xy, depthA: P[e.from].depth, depthB: P[e.to].depth, source: { edge: e.id } }));
    const map = HR.PlanarMap.build(segs);
    const gap = R(opts.gap || '1/6'); const unit = opts.unit || '1/4'; const kappa = opts.aperture || '1/2';
    // under-strand gaps: the topological trace of depth at a crossing (CrossingRole::Under) — the under edge is cut ±gap around the point
    const cuts = circ.edges.map(() => []);
    for (const c of map.crossings) { if (c.over === null) continue; const under = c.over === c.first ? c.second : c.first; const tu = c.over === c.first ? c.u : c.t; cuts[under].push(tu); }
    const edges = circ.edges.map((e, i) => { const a = segs[i].a, b = segs[i].b; const d = [b[0].sub(a[0]), b[1].sub(a[1])]; const len2 = d[0].mul(d[0]).add(d[1].mul(d[1]));
      // gap in parameter: gap / |d| — |d| is irrational in general; the cut is taken as ±gap² / len2 in t² terms via the exact bound t = gap·⌈..⌉: use t_gap = gap / ceilSqrt(len2) (a rational ≤ the true value, so the gap is never larger than declared)
      const tg = gap.div(R(ceilSqrt(len2) || 1n)); let ts = [Rat.ZERO, Rat.ONE]; const holes = cuts[i].map((t) => [Rat.max(Rat.ZERO, t.sub(tg)), Rat.min(Rat.ONE, t.add(tg))]).sort((p, q) => p[0].cmp(q[0]));
      const pieces = []; let cur = Rat.ZERO; for (const [h0, h1] of holes) { if (h0.gt(cur)) pieces.push([cur, h0]); cur = Rat.max(cur, h1); } if (cur.lt(Rat.ONE)) pieces.push([cur, Rat.ONE]);
      const at = (t) => [a[0].add(d[0].mul(t)), a[1].add(d[1].mul(t))];
      const hand = e.I.re.sign() !== 0 ? e.I.re.sign() : e.I.im.sign(); const resp = HR.Colour.transduceExact([{ re: e.I.re, im: e.I.im }], kappa);
      return { edge: e, a, b, depth: segs[i].depthA.add(segs[i].depthB).div(2), pieces: pieces.map(([t0, t1]) => [at(t0), at(t1)]), width: widthPx(e.I, unit), hand, response: resp, cuts: cuts[i].length }; });
    const nodes = circ.nodes.map((n) => ({ node: n, p: P[n.id].xy, depth: P[n.id].depth, phi: circ.phi[n.id], response: HR.Colour.transduceExact([{ re: circ.phi[n.id].re, im: circ.phi[n.id].im }], kappa), pump: !circ.J[n.id].isZero(), ground: n.id === circ.ground }));
    return { nodes, edges, map, crossings: map.crossings.filter((c) => c.over !== null).length, openCrossings: map.crossings.filter((c) => c.over === null).length, discriminants: map.discriminants };
  }
  HR.GRat = GRat; HR.Circuit = { solve, LatticeCircuit, schematicPlan, widthPx, ceilSqrt };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
