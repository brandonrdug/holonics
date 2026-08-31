// ===== receivers.js — receivers all the way down: monitor, window, element, mounted object; each a chart with discrete cells =====
// Mirrors canon/TABLET_THE_CHART.md (a chart is a receiver's declaration; two charts compare only through a declared FrameRelation),
// relational-geometry/src/receiver_atlas.rs (apertures; a seam point addresses two or four cells; never one by array convention),
// and holonic-engine/examples/layout_curvature_consumption.rs (a layout's cycle deficit is its curvature; a flat layout stays exactly fixed).
(function (HR) {
  const { Rat, R } = HR;
  // ---- exact affine map of the plane: p -> M p + t ----
  class Affine2 {
    constructor(m, t) { this.m = m.map((r) => r.map(R)); this.t = t.map(R); }
    static identity() { return new Affine2([[1, 0], [0, 1]], [0, 0]); }
    static scale(sx, sy = sx) { return new Affine2([[sx, 0], [0, sy]], [0, 0]); }
    static translate(tx, ty) { return new Affine2([[1, 0], [0, 1]], [tx, ty]); }
    static flipY(height) { return new Affine2([[1, 0], [0, -1]], [0, height]); } // row downward <-> y upward
    apply(p) { const x = R(p[0]), y = R(p[1]); return [this.m[0][0].mul(x).add(this.m[0][1].mul(y)).add(this.t[0]), this.m[1][0].mul(x).add(this.m[1][1].mul(y)).add(this.t[1])]; }
    linear(v) { const x = R(v[0]), y = R(v[1]); return [this.m[0][0].mul(x).add(this.m[0][1].mul(y)), this.m[1][0].mul(x).add(this.m[1][1].mul(y))]; }
    compose(o) { // this ∘ o : apply o first, then this
      const a = this.m, b = o.m; const m = [[a[0][0].mul(b[0][0]).add(a[0][1].mul(b[1][0])), a[0][0].mul(b[0][1]).add(a[0][1].mul(b[1][1]))], [a[1][0].mul(b[0][0]).add(a[1][1].mul(b[1][0])), a[1][0].mul(b[0][1]).add(a[1][1].mul(b[1][1]))]];
      return new Affine2(m, this.apply(o.t)); }
    det() { return this.m[0][0].mul(this.m[1][1]).sub(this.m[0][1].mul(this.m[1][0])); }
    inverse() { const d = this.det(); if (d.isZero()) throw new Error('Affine2: singular relation'); const inv = [[this.m[1][1].div(d), this.m[0][1].neg().div(d)], [this.m[1][0].neg().div(d), this.m[0][0].div(d)]]; const r = new Affine2(inv, [0, 0]); const t = r.linear(this.t); return new Affine2(inv, [t[0].neg(), t[1].neg()]); }
    gram() { const m = this.m; return [[m[0][0].mul(m[0][0]).add(m[1][0].mul(m[1][0])), m[0][0].mul(m[0][1]).add(m[1][0].mul(m[1][1]))], [m[0][1].mul(m[0][0]).add(m[1][1].mul(m[1][0])), m[0][1].mul(m[0][1]).add(m[1][1].mul(m[1][1]))]]; } // MᵀM: what escapes is the metric, not the hand
    hand() { return this.det().sign(); }
    deficit() { return { m: [[this.m[0][0].sub(1), this.m[0][1]], [this.m[1][0], this.m[1][1].sub(1)]], t: this.t.slice() }; }
    isIdentity() { const d = this.deficit(); return d.m.every((r) => r.every((x) => x.isZero())) && d.t.every((x) => x.isZero()); }
    toString() { return `[[${this.m[0][0]}, ${this.m[0][1]}], [${this.m[1][0]}, ${this.m[1][1]}]] + (${this.t[0]}, ${this.t[1]})`; }
  }
  // ---- a receiver: a rectangle of discrete cells (grain w × h) with a chart whose coordinates are its own cells (column right, row down as the platform declares) ----
  class Receiver {
    constructor(name, grain, toParent = null, parent = null, meta = {}) { this.name = name; this.grain = { w: R(grain.w), h: R(grain.h) }; this.toParent = toParent; this.parent = parent; this.meta = meta; this.children = []; if (parent) parent.children.push(this); }
    toRoot() { let m = Affine2.identity(); let r = this; while (r.parent) { m = r.toParent.compose(m); r = r.parent; } return m; }
    // exact map from this receiver's cells to another receiver's cells through the tree (the only lawful comparison: declared relations composed)
    to(other) { return other.toRoot().inverse().compose(this.toRoot()); }
    // seam-aware address of a point in cell coordinates: an integer coordinate lies on a seam and addresses both neighbours
    address(p) {
      const axis = (v, n) => { v = R(v); if (v.lt(0) || v.gt(n)) return []; const fl = v.floor(); const onSeam = v.eq(R(fl)); const cells = onSeam ? [fl - 1n, fl] : [fl]; return cells.filter((c) => c >= 0n && c < n.floor()).map(Number); };
      const cs = axis(p[0], this.grain.w), rs = axis(p[1], this.grain.h); const out = []; for (const c of cs) for (const r of rs) out.push([c, r]); return out;
    }
    aperture(c, r) { return { lower: [R(c), R(r)], upper: [R(c).add(1), R(r).add(1)] }; }
    corners() { return [[Rat.ZERO, Rat.ZERO], [this.grain.w, Rat.ZERO], [this.grain.w, this.grain.h], [Rat.ZERO, this.grain.h]]; }
    depth() { let d = 0, r = this; while (r.parent) { d++; r = r.parent; } return d; }
  }
  // holonomy of a cycle of declared relations: compose in order; the deficit from identity is the layout's curvature
  function cycleDeficit(maps) { let m = Affine2.identity(); for (const f of maps) m = f.compose(m); return { map: m, deficit: m.deficit(), flat: m.isIdentity() }; }
  // pullback Gram of a 3→2 projection law at a point (projection.rs projection_pullback_gram): the metric a receiver induces, its hand kept apart
  function pullbackGram(law, p) {
    const x = R(p[0]), y = R(p[1]), z = R(p[2]); let rows;
    if (law.kind === 'oblique') rows = [[Rat.ONE, Rat.ZERO, R(law.a)], [Rat.ZERO, Rat.ONE, R(law.b)]];
    else { const f = R(law.distance); const den = f.add(z); if (den.isZero()) return null; const q = f.div(den), q2 = den.mul(den); rows = [[q, Rat.ZERO, f.mul(x).neg().div(q2)], [Rat.ZERO, q, f.mul(y).neg().div(q2)]]; }
    const G = [[], [], []]; for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) G[i][j] = rows[0][i].mul(rows[0][j]).add(rows[1][i].mul(rows[1][j])); return G;
  }
  // ---- the atlas: charts on one sheet must stay distinct. Build the planar map of every receiver boundary; each bounded face belongs to the
  // deepest receiver containing it; receivers whose faces share an edge are adjacent; the receiver graph is properly coloured (≤ 4 classes,
  // exact search). The class is a receiver coordinate of the GAUGE (a ground tint and a D4 cell-mark direction) — never a source label.
  function atlas(receivers) {
    // every receiver's closed rectangle in root cells (exact); a nested child is a hole in its parent's ground, so parent and child share a boundary
    const box = receivers.map((r) => { const cs = r.corners().map((c) => r.toRoot().apply(c)); const xs = cs.map((c) => c[0]), ys = cs.map((c) => c[1]); return { x0: xs.reduce((a, b) => Rat.min(a, b)), x1: xs.reduce((a, b) => Rat.max(a, b)), y0: ys.reduce((a, b) => Rat.min(a, b)), y1: ys.reduce((a, b) => Rat.max(a, b)) }; });
    const meets = (a, b) => !(a.x1.lt(b.x0) || b.x1.lt(a.x0) || a.y1.lt(b.y0) || b.y1.lt(a.y0)); // closed rectangles intersect (touching counts)
    const contains = (a, b) => a.x0.le(b.x0) && b.x1.le(a.x1) && a.y0.le(b.y0) && b.y1.le(a.y1);
    const adj = new Map(); receivers.forEach((_, i) => adj.set(i, new Set())); const link = (i, j) => { adj.get(i).add(j); adj.get(j).add(i); };
    for (let i = 0; i < receivers.length; i++) for (let j = i + 1; j < receivers.length; j++) { const a = receivers[i], b = receivers[j];
      if (a.parent === b || b.parent === a) { link(i, j); continue; } // the child's boundary is shared with the parent's ground
      if (contains(box[i], box[j]) || contains(box[j], box[i])) continue; // nested but not parent–child: separated by the intermediate receiver
      if (meets(box[i], box[j])) link(i, j); } // overlapping or touching charts on one ground must differ
    const col = HR.FourColor.colour(receivers.length, adj, { budget: 200000 });
    return { boxes: box, adjacency: adj, classes: col.colours, chromatic: col.chromatic, exact: col.exact, edges: [...adj.entries()].reduce((s, [, v]) => s + v.size, 0) / 2 };
  }
  HR.Affine2 = Affine2; HR.Receiver = Receiver; HR.Receivers = { cycleDeficit, pullbackGram, atlas };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
