// ===== bord.js — Bord components (Leinster, math/0106240 p.8): manifolds with corners as exact polynomial level sets in a slab =====
// A 2-cell N : M ⇒ M′ of Bord is a 2-manifold with corners between the 1-manifolds M (bottom plane) and M′ (top plane), whose own
// boundary meets the slab walls in the corners L = L′. Each cell is the zero set of an exact polynomial g(x, y, z) on a box. Its picture
// is (i) the ISOLATED contours of the horizontal slices g(·,·,z_k) = 0 — every vertex a certified isolating interval — (ii) the wall traces
// g(±X,·,·) = 0, g(·,±Y,·) = 0 (the corners), and (iii) intaglio hatch strokes along an exact principal direction at contour stations,
// cross-hatched only where the exact foreshortening predicate admits it. Nothing is sampled at a pixel; nothing is interpolated.
(function (HR) {
  const { Rat, R, Poly3 } = HR;
  const X = Poly3.x(), Y = Poly3.y(), Z = Poly3.z(); const C = Poly3.c;
  const CELLS = {
    // pair of pants: Cassini ovals with foci (±a, 0); c(z) = a⁴ + κ(z₀ − z): one oval below z₀, a lemniscate at z₀, two ovals above
    pants: { params: { a: '1', kappa: '1', z0: '1/2' }, box: { x: ['-2', '2'], y: ['-5/4', '5/4'], z: ['0', '1'] }, g: (P) => { const a = R(P.a); const l = X.sub(a).sq().add(Y.sq()), r = X.add(a).sq().add(Y.sq()); return l.mul(r).sub(C(a.mul(a).mul(a).mul(a)).add(C(R(P.z0)).sub(Z).scale(P.kappa))); }, notation: { L: '∅', M: 'one circle', Mprime: 'two circles', N: 'pants' } },
    // the saddle with corners: x² − y² = s (z − ½). Bottom slice: y² − x² = s/2 (cup and cap, M); top slice: x² − y² = s/2 (two branches, M′)
    saddle: { params: { s: '1' }, box: { x: ['-1', '1'], y: ['-1', '1'], z: ['0', '1'] }, g: (P) => X.sq().sub(Y.sq()).sub(Z.sub(C('1/2')).scale(P.s)), notation: { L: 'two points', Lprime: 'two points', M: 'cup and cap', Mprime: 'two branches', N: 'saddle' } },
    // cylinder: circle × interval — the identity 2-cell on a circle
    cylinder: { params: { r: '3/4' }, box: { x: ['-1', '1'], y: ['-1', '1'], z: ['0', '1'] }, g: (P) => X.sq().add(Y.sq()).sub(C(R(P.r).mul(R(P.r)))), notation: { M: 'circle', Mprime: 'circle', N: 'identity' } },
    // cap: the disk closing a circle — x² + y² = 1 − z
    cap: { params: {}, box: { x: ['-5/4', '5/4'], y: ['-5/4', '5/4'], z: ['0', '1'] }, g: () => X.sq().add(Y.sq()).sub(C(1).sub(Z)), notation: { M: 'circle', Mprime: '∅', N: 'cap' } },
  };
  function circlePoints(cx, cy, r, n = 24) { const out = []; for (let k = 0; k < n; k++) { const t = R(k * 4 - 2 * n).div(n); const d = Rat.ONE.add(t.mul(t)); out.push([R(cx).add(R(r).mul(Rat.ONE.sub(t.mul(t)).div(d))), R(cy).add(R(r).mul(t.mul(2).div(d)))]); } out.push([R(cx).sub(R(r)), R(cy)]); out.push(out[0]); return out; }
  // slices: isolated contours per horizontal level, wall traces, hatch stations
  function slices(kind, opts = {}) {
    const cell = CELLS[kind]; if (!cell) throw new Error('unknown Bord cell ' + kind); const P = { ...cell.params, ...(opts.params || {}) }; const g = cell.g(P); const box = cell.box;
    const m = opts.slices || 24, n = opts.grid || 32, k = opts.bisections || 7; const out = { kind, params: P, box, poly: g, horizontal: [], walls: [], components: {}, notation: cell.notation, evaluations: 0, ambiguous: 0 };
    const gz = (z) => (x, y) => g.eval(x, y, z);
    for (let kk = 0; kk <= m; kk++) { const z = R(box.z[0]).add(R(box.z[1]).sub(R(box.z[0])).mul(R(kk).div(m))); const iso = HR.Brackets.isolate(gz(z), { x0: box.x[0], x1: box.x[1], y0: box.y[0], y1: box.y[1] }, n, 0, k); out.evaluations += iso.evaluations; out.ambiguous += iso.ambiguous;
      out.horizontal.push({ z, segs: iso.segs.map((s) => ({ a: [s.a[0], s.a[1], z], b: [s.b[0], s.b[1], z], ta: s.ta, tb: s.tb })), stations: iso.stations.length, components: HR.Brackets.components(iso.segs), vertices: iso.vertices }); }
    out.components.bottom = out.horizontal[0].components; out.components.top = out.horizontal[m].components;
    const nz = Math.max(8, Math.round(n / 2));
    for (const Xw of [box.x[0], box.x[1]]) { const iso = HR.Brackets.isolate((y, z) => g.eval(R(Xw), y, z), { x0: box.y[0], x1: box.y[1], y0: box.z[0], y1: box.z[1] }, { nx: n, ny: nz }, 0, k); out.evaluations += iso.evaluations; out.walls.push({ wall: 'x=' + Xw, segs: iso.segs.map((s) => ({ a: [R(Xw), s.a[0], s.a[1]], b: [R(Xw), s.b[0], s.b[1]] })) }); }
    for (const Yw of [box.y[0], box.y[1]]) { const iso = HR.Brackets.isolate((x, z) => g.eval(x, R(Yw), z), { x0: box.x[0], x1: box.x[1], y0: box.z[0], y1: box.z[1] }, { nx: n, ny: nz }, 0, k); out.evaluations += iso.evaluations; out.walls.push({ wall: 'y=' + Yw, segs: iso.segs.map((s) => ({ a: [s.a[0], R(Yw), s.a[1]], b: [s.b[0], R(Yw), s.b[1]] })) }); }
    const rect = (z) => [[R(box.x[0]), R(box.y[0]), R(z)], [R(box.x[1]), R(box.y[0]), R(z)], [R(box.x[1]), R(box.y[1]), R(z)], [R(box.x[0]), R(box.y[1]), R(z)]];
    out.slab = [rect(box.z[0]), rect(box.z[1])];
    return out;
  }
  // hatch stations: every `stride`-th contour vertex of every `sliceStride`-th slice; principal direction and the tone predicate at each
  function hatches(plan, opts = {}) {
    const stride = opts.stride || 3, sliceStride = opts.sliceStride || 1, view = opts.view || ['-2/5', '-2/7', '1'], tone = opts.tone || '1/4', L = opts.length || 0.12;
    const strokes = []; let singular = 0, elliptic = 0, hyperbolic = 0, parabolic = 0, crossed = 0;
    plan.horizontal.forEach((h, hi) => { if (hi % sliceStride) return; h.segs.forEach((s, si) => { if (si % stride) return; const st = HR.Hatch.station(plan.poly, s.a, { view, tone }); if (!st || st.singular) { singular++; return; }
      if (st.gaussSign > 0) elliptic++; else if (st.gaussSign < 0) hyperbolic++; else parabolic++;
      const d = HR.Hatch.transverse(st); const sk = HR.Hatch.stroke(st.P, d, L); strokes.push({ ...sk, gauss: st.gaussSign, grazing: st.grazing, delta: st.delta, family: 'primary' });
      if (st.grazing) { crossed++; const other = st.dirs[0] === d ? st.dirs[1] : st.dirs[0]; const sk2 = HR.Hatch.stroke(st.P, other, L); strokes.push({ ...sk2, gauss: st.gaussSign, grazing: true, delta: st.delta, family: 'cross' }); } }); });
    return { strokes, singular, elliptic, hyperbolic, parabolic, crossed };
  }
  // project every 3-vector of a plan through a chart (models.js Chart, padded to four coordinates)
  function project(plan, chart, hatchPlan) {
    const pr = (p) => { const q = chart.project([R(p[0]), R(p[1]), R(p[2]), Rat.ZERO]); return { xy: q.xy, depth: q.depth }; };
    const segs = []; for (const h of plan.horizontal) for (const s of h.segs) { const a = pr(s.a), b = pr(s.b); segs.push({ a: a.xy, b: b.xy, depth: a.depth.add(b.depth).div(2), z: h.z, role: 'contour', source: `iso t∈[${s.ta.join(',')}] → t∈[${s.tb.join(',')}] at z=${h.z}` }); }
    for (const w of plan.walls) for (const s of w.segs) { const a = pr(s.a), b = pr(s.b); segs.push({ a: a.xy, b: b.xy, depth: a.depth.add(b.depth).div(2), role: 'corner' }); }
    const hatch = (hatchPlan ? hatchPlan.strokes : []).map((s) => { const a = chart.project([R(s.a[0]), R(s.a[1]), R(s.a[2]), Rat.ZERO]).xy, b = chart.project([R(s.b[0]), R(s.b[1]), R(s.b[2]), Rat.ZERO]).xy; return { a, b, family: s.family, gauss: s.gauss, source: s.source }; });
    const slab = plan.slab.map((r) => r.map((p) => pr(p).xy));
    return { segs, slab, hatch };
  }
  HR.Bord = { CELLS, slices, hatches, project, circlePoints };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
