// ===== holonic render codec — exact core (no libraries) =====
// Rat: exact rationals over BigInt. Every identity-bearing decision in this library goes through Rat.
const HR = (typeof window !== 'undefined' ? (window.HR = window.HR || {}) : (globalThis.HR = globalThis.HR || {}));
(function (HR) {
  const B = (x) => (typeof x === 'bigint' ? x : BigInt(x));
  const babs = (a) => (a < 0n ? -a : a);
  function bgcd(a, b) { a = babs(a); b = babs(b); while (b) { [a, b] = [b, a % b]; } return a; }
  class Rat {
    constructor(n, d = 1n) {
      n = B(n); d = B(d);
      if (d === 0n) throw new Error('Rat: zero denominator');
      if (d < 0n) { n = -n; d = -d; }
      const g = bgcd(n, d) || 1n;
      this.n = n / g; this.d = d / g;
    }
    static of(x) {
      if (x instanceof Rat) return x;
      if (typeof x === 'bigint' || Number.isInteger(x)) return new Rat(x, 1n);
      if (typeof x === 'string') {
        const s = x.trim();
        if (s.includes('/')) { const [a, b] = s.split('/'); return new Rat(BigInt(a.trim()), BigInt(b.trim())); }
        if (s.includes('.')) { const neg = s.startsWith('-'); const t = neg ? s.slice(1) : s; const [i, f] = t.split('.'); const d = 10n ** BigInt(f.length); const n = BigInt(i || '0') * d + BigInt(f || '0'); return new Rat(neg ? -n : n, d); }
        return new Rat(BigInt(s), 1n);
      }
      if (typeof x === 'number') { // a float is a dyadic and a deleted tail: admit only exact dyadics
        if (!Number.isFinite(x)) throw new Error('Rat: non-finite');
        let d = 1n, v = x; let k = 0; while (!Number.isInteger(v) && k < 60) { v *= 2; d *= 2n; k++; }
        return new Rat(BigInt(Math.round(v)), d);
      }
      throw new Error('Rat: cannot admit ' + typeof x);
    }
    add(o) { o = Rat.of(o); return new Rat(this.n * o.d + o.n * this.d, this.d * o.d); }
    sub(o) { o = Rat.of(o); return new Rat(this.n * o.d - o.n * this.d, this.d * o.d); }
    mul(o) { o = Rat.of(o); return new Rat(this.n * o.n, this.d * o.d); }
    div(o) { o = Rat.of(o); return new Rat(this.n * o.d, this.d * o.n); }
    neg() { return new Rat(-this.n, this.d); }
    abs() { return new Rat(babs(this.n), this.d); }
    sign() { return this.n === 0n ? 0 : (this.n < 0n ? -1 : 1); }
    cmp(o) { o = Rat.of(o); const l = this.n * o.d, r = o.n * this.d; return l === r ? 0 : (l < r ? -1 : 1); }
    eq(o) { return this.cmp(o) === 0; }
    lt(o) { return this.cmp(o) < 0; }
    le(o) { return this.cmp(o) <= 0; }
    gt(o) { return this.cmp(o) > 0; }
    isZero() { return this.n === 0n; }
    floor() { let q = this.n / this.d; if (this.n < 0n && q * this.d !== this.n) q -= 1n; return q; }
    toNumber() { // the only float face: rendering coordinates
      const q = this.n / this.d, r = this.n - q * this.d; return Number(q) + Number(r) / Number(this.d);
    }
    toString() { return this.d === 1n ? this.n.toString() : this.n.toString() + '/' + this.d.toString(); }
    key() { return this.toString(); }
    static min(a, b) { return a.le(b) ? a : b; }
    static max(a, b) { return a.ge ? (a.cmp(b) >= 0 ? a : b) : (a.cmp(b) >= 0 ? a : b); }
  }
  Rat.ZERO = new Rat(0n); Rat.ONE = new Rat(1n);
  const R = (x) => Rat.of(x);
  // exact 2-D predicates (mirroring relational-geometry's orient/segment predicates)
  const cross2 = (ax, ay, bx, by) => ax.mul(by).sub(ay.mul(bx));
  function orient2d(a, b, c) { return cross2(b[0].sub(a[0]), b[1].sub(a[1]), c[0].sub(a[0]), c[1].sub(a[1])).sign(); }
  // segment intersection over Q: returns {kind:'proper'|'touch'|'none'|'collinear', point, t, u}
  function segIntersect(a, b, c, d) {
    const r = [b[0].sub(a[0]), b[1].sub(a[1])], s = [d[0].sub(c[0]), d[1].sub(c[1])];
    const denom = cross2(r[0], r[1], s[0], s[1]);
    const ca = [c[0].sub(a[0]), c[1].sub(a[1])];
    if (denom.isZero()) {
      if (!cross2(ca[0], ca[1], r[0], r[1]).isZero()) return { kind: 'none' };
      // collinear: overlap in a positive-length interval is the discriminant; sharing exactly one point is a touch; otherwise disjoint
      const rr = r[0].mul(r[0]).add(r[1].mul(r[1])); if (rr.isZero()) return { kind: 'none' };
      const tc = ca[0].mul(r[0]).add(ca[1].mul(r[1])).div(rr), td = d[0].sub(a[0]).mul(r[0]).add(d[1].sub(a[1]).mul(r[1])).div(rr);
      const lo = Rat.max(Rat.min(tc, td), Rat.ZERO), hi = Rat.min(Rat.max(tc, td), Rat.ONE);
      if (lo.lt(hi)) return { kind: 'collinear' };
      if (lo.gt(hi)) return { kind: 'none' };
      const t = lo; const u = tc.eq(td) ? Rat.ZERO : t.sub(tc).div(td.sub(tc));
      return { kind: 'touch', t, u, point: [a[0].add(r[0].mul(t)), a[1].add(r[1].mul(t))] };
    }
    const t = cross2(ca[0], ca[1], s[0], s[1]).div(denom), u = cross2(ca[0], ca[1], r[0], r[1]).div(denom);
    if (t.lt(0) || t.gt(1) || u.lt(0) || u.gt(1)) return { kind: 'none' };
    const inner = t.gt(0) && t.lt(1) && u.gt(0) && u.lt(1);
    return { kind: inner ? 'proper' : 'touch', t, u, point: [a[0].add(r[0].mul(t)), a[1].add(r[1].mul(t))] };
  }
  // angular order of a direction vector without atan2: half-plane class then cross product
  function halfPlane(dx, dy) { const sy = dy.sign(); if (sy > 0) return 0; if (sy < 0) return 1; return dx.sign() >= 0 ? 0 : 1; }
  function angleCmp(ax, ay, bx, by) { const ha = halfPlane(ax, ay), hb = halfPlane(bx, by); if (ha !== hb) return ha - hb; return -cross2(ax, ay, bx, by).sign(); }
  HR.Rat = Rat; HR.R = R; HR.orient2d = orient2d; HR.segIntersect = segIntersect; HR.angleCmp = angleCmp; HR.cross2 = cross2;
  HR.pkey = (p) => p[0].key() + ',' + p[1].key();
})(HR);

// ===== PlanarMap: the receiver's planar map, built exactly from projected segments =====
(function (HR) {
  const { Rat, R, segIntersect, angleCmp, cross2, pkey } = HR;
  // segments: [{a:[x,y], b:[x,y], depthA, depthB, source:{entity, segment}}] with Rat coords
  function build(segments, opts = {}) {
    const discriminants = [];
    const cuts = segments.map(() => []); // t values per segment
    const crossings = [];
    for (let i = 0; i < segments.length; i++) for (let j = i + 1; j < segments.length; j++) {
      const s = segments[i], q = segments[j];
      // exact bounding-box prefilter
      if (Rat.max(s.a[0], s.b[0]).lt(Rat.min(q.a[0], q.b[0])) || Rat.max(q.a[0], q.b[0]).lt(Rat.min(s.a[0], s.b[0])) ||
          Rat.max(s.a[1], s.b[1]).lt(Rat.min(q.a[1], q.b[1])) || Rat.max(q.a[1], q.b[1]).lt(Rat.min(s.a[1], s.b[1]))) continue;
      const x = segIntersect(s.a, s.b, q.a, q.b);
      if (x.kind === 'none') continue;
      if (x.kind === 'collinear') { discriminants.push({ kind: 'collinear-overlap', first: i, second: j }); continue; }
      cuts[i].push(x.t); cuts[j].push(x.u);
      if (x.kind === 'proper') {
        const dI = s.depthA && s.depthB ? s.depthA.add(s.depthB.sub(s.depthA).mul(x.t)) : null;
        const dJ = q.depthA && q.depthB ? q.depthA.add(q.depthB.sub(q.depthA).mul(x.u)) : null;
        let over = null; if (dI && dJ) { const c = dI.cmp(dJ); over = c < 0 ? i : (c > 0 ? j : null); if (c === 0) discriminants.push({ kind: 'equal-depth-crossing', first: i, second: j }); }
        const osign = cross2(s.b[0].sub(s.a[0]), s.b[1].sub(s.a[1]), q.b[0].sub(q.a[0]), q.b[1].sub(q.a[1])).sign();
        crossings.push({ first: i, second: j, point: x.point, t: x.t, u: x.u, firstDepth: dI, secondDepth: dJ, over, orientationSign: osign });
      }
    }
    // nodes and sub-edges
    const nodeIndex = new Map(); const nodes = [];
    const node = (p) => { const k = pkey(p); let id = nodeIndex.get(k); if (id === undefined) { id = nodes.length; nodeIndex.set(k, id); nodes.push({ id, p, out: [] }); } return id; };
    const edges = [];
    segments.forEach((s, si) => {
      const ts = [Rat.ZERO, Rat.ONE, ...cuts[si]].sort((a, b) => a.cmp(b));
      const uniq = []; for (const t of ts) if (!uniq.length || !uniq[uniq.length - 1].eq(t)) uniq.push(t);
      const r = [s.b[0].sub(s.a[0]), s.b[1].sub(s.a[1])];
      for (let k = 0; k + 1 < uniq.length; k++) {
        const p = [s.a[0].add(r[0].mul(uniq[k])), s.a[1].add(r[1].mul(uniq[k]))];
        const q = [s.a[0].add(r[0].mul(uniq[k + 1])), s.a[1].add(r[1].mul(uniq[k + 1]))];
        const u = node(p), v = node(q); if (u === v) continue;
        const dA = s.depthA && s.depthB ? s.depthA.add(s.depthB.sub(s.depthA).mul(uniq[k])) : null;
        const dB = s.depthA && s.depthB ? s.depthA.add(s.depthB.sub(s.depthA).mul(uniq[k + 1])) : null;
        edges.push({ id: edges.length, from: u, to: v, source: si, t0: uniq[k], t1: uniq[k + 1], depthA: dA, depthB: dB });
      }
    });
    // darts: 2 per edge; rotation order at each node, exact
    const darts = []; for (const e of edges) { darts.push({ id: darts.length, edge: e.id, from: e.from, to: e.to, forward: true }); darts.push({ id: darts.length, edge: e.id, from: e.to, to: e.from, forward: false }); }
    for (const d of darts) nodes[d.from].out.push(d.id);
    for (const nd of nodes) nd.out.sort((x, y) => { const dx = darts[x], dy = darts[y]; const px = nodes[dx.to].p, py = nodes[dy.to].p; return angleCmp(px[0].sub(nd.p[0]), px[1].sub(nd.p[1]), py[0].sub(nd.p[0]), py[1].sub(nd.p[1])); });
    const twin = (d) => (d ^ 1);
    // next dart in a face: at head v of dart d, take the dart just before twin(d) in v's counter-clockwise rotation
    const nextInFace = (d) => { const v = darts[d].to; const rot = nodes[v].out; const i = rot.indexOf(twin(d)); return rot[(i - 1 + rot.length) % rot.length]; };
    const faceOf = new Array(darts.length).fill(-1); const faces = [];
    for (let d0 = 0; d0 < darts.length; d0++) {
      if (faceOf[d0] !== -1) continue;
      const cycle = []; let d = d0, guard = 0;
      while (faceOf[d] === -1 && guard++ < darts.length + 2) { faceOf[d] = faces.length; cycle.push(d); d = nextInFace(d); }
      // signed double area by shoelace over the cycle's node sequence
      let A = Rat.ZERO; for (const dd of cycle) { const p = nodes[darts[dd].from].p, q = nodes[darts[dd].to].p; A = A.add(cross2(p[0], p[1], q[0], q[1])); }
      faces.push({ id: faces.length, darts: cycle, signedDoubleArea: A, bounded: A.sign() > 0 });
    }
    // adjacency of faces across edges
    const adjacency = new Map(); const addAdj = (a, b) => { if (a === b) return; if (!adjacency.has(a)) adjacency.set(a, new Set()); adjacency.get(a).add(b); };
    for (const e of edges) { const f1 = faceOf[2 * e.id], f2 = faceOf[2 * e.id + 1]; addAdj(f1, f2); addAdj(f2, f1); }
    return { nodes, edges, darts, faces, faceOf, crossings, discriminants, adjacency };
  }
  // exact point-in-polygon (node cycle) by ray parity, with an exact interior point for a bounded face
  function interiorPoint(map, face) {
    const pts = face.darts.map((d) => map.nodes[map.darts[d].from].p);
    // ear-style: try the midpoint of a diagonal from vertex 0 to vertex k that lies inside
    for (let k = 2; k < pts.length - 0; k++) {
      const a = pts[0], c = pts[k % pts.length], b = pts[1];
      const m = [a[0].add(c[0]).div(2), a[1].add(c[1]).div(2)];
      if (pointInCycle(pts, m)) return m;
    }
    // fallback: centroid of first three
    const a = pts[0], b = pts[1], c = pts[2 % pts.length];
    return [a[0].add(b[0]).add(c[0]).div(3), a[1].add(b[1]).add(c[1]).div(3)];
  }
  function pointInCycle(pts, p) {
    let inside = false; const n = pts.length;
    for (let i = 0, j = n - 1; i < n; j = i++) {
      const a = pts[i], b = pts[j];
      const yi = a[1], yj = b[1];
      if ((yi.gt(p[1])) !== (yj.gt(p[1]))) {
        // x of the crossing of edge with horizontal line through p
        const x = a[0].add(b[0].sub(a[0]).mul(p[1].sub(yi)).div(yj.sub(yi)));
        if (p[0].lt(x)) inside = !inside;
      }
    }
    return inside;
  }
  HR.PlanarMap = { build, interiorPoint, pointInCycle };
})(HR);

// ===== FourColor: the colour law of the receiver's planar map =====
(function (HR) {
  // Graph colouring with 4 colours by DSATUR + backtracking; planar maps admit 4 (Four Colour theorem);
  // if the search exceeds its budget, return a 5-colouring (5-degeneracy greedy) and report the obstruction.
  function colour(nFaces, adjacency, opts = {}) {
    const budget = opts.budget || 200000; const K = opts.k || 4;
    const adj = []; for (let i = 0; i < nFaces; i++) adj.push([...(adjacency.get(i) || [])]);
    const col = new Array(nFaces).fill(-1);
    // smallest-last (degeneracy) ordering
    const deg = adj.map((a) => a.length); const removed = new Array(nFaces).fill(false); const order = [];
    for (let k = 0; k < nFaces; k++) { let best = -1; for (let i = 0; i < nFaces; i++) if (!removed[i] && (best < 0 || deg[i] < deg[best])) best = i; removed[best] = true; order.push(best); for (const j of adj[best]) if (!removed[j]) deg[j]--; }
    order.reverse();
    let steps = 0;
    const ok = (v, c) => adj[v].every((u) => col[u] !== c);
    function bt(i) {
      if (i === order.length) return true;
      if (++steps > budget) return false;
      // pick the uncoloured vertex with max saturation among remaining (DSATUR)
      let v = -1, sat = -1; for (let k = i; k < order.length; k++) { const u = order[k]; const s = new Set(adj[u].map((w) => col[w]).filter((c) => c >= 0)).size; if (s > sat) { sat = s; v = k; } }
      [order[i], order[v]] = [order[v], order[i]]; const u = order[i];
      for (let c = 0; c < K; c++) if (ok(u, c)) { col[u] = c; if (bt(i + 1)) return true; col[u] = -1; }
      return false;
    }
    if (bt(0)) return { colours: col, chromatic: Math.max(-1, ...col) + 1, exact: true, steps };
    // obstruction: fall back to greedy on the degeneracy order (≤ 6 colours on a planar map, usually 5)
    col.fill(-1); for (const u of order) { let c = 0; while (!ok(u, c)) c++; col[u] = c; }
    return { colours: col, chromatic: Math.max(...col) + 1, exact: false, steps, obstruction: 'four-colour search exceeded its budget; greedy colouring returned' };
  }
  HR.FourColor = { colour };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
