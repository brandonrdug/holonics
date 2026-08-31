// ===== models.js — exact lattice models through a receiver chart; depth traces =====
(function (HR) {
  const { Rat, R, cross2, PlanarMap } = HR;
  // Z^4 cubic lattice on a fundamental domain [0,g)^4 (wrap optional). Vertices carry exact integer coordinates.
  function Lattice4(g, opts = {}) {
    const wrap = !!opts.wrap; const V = [], index = new Map();
    const key = (c) => c.join(',');
    for (let i = 0; i < g; i++) for (let j = 0; j < g; j++) for (let k = 0; k < g; k++) for (let l = 0; l < g; l++) { index.set(key([i, j, k, l]), V.length); V.push({ id: V.length, coords: [R(i), R(j), R(k), R(l)], ints: [i, j, k, l] }); }
    const E = [], F = [];
    const nb = (c, d) => { const n = c.slice(); n[d] += 1; if (n[d] >= g) { if (!wrap) return -1; n[d] = 0; } return index.get(key(n)); };
    for (const v of V) for (let d = 0; d < 4; d++) { const w = nb(v.ints, d); if (w >= 0 && (wrap || true)) E.push({ id: E.length, from: v.id, to: w, direction: d, cycleWrap: wrap && v.ints[d] === g - 1 }); }
    for (const v of V) for (let a = 0; a < 4; a++) for (let b = a + 1; b < 4; b++) { const va = nb(v.ints, a), vb = nb(v.ints, b); if (va < 0 || vb < 0) continue; const nn = v.ints.slice(); nn[a] += 1; nn[b] += 1; for (const d of [a, b]) if (nn[d] >= g) { if (!wrap) { nn[d] = -1; break; } nn[d] = 0; } if (nn.includes(-1)) continue; const vab = index.get(key(nn)); F.push({ id: F.length, corners: [v.id, va, vab, vb], directions: [a, b] }); }
    return { g, wrap, V, E, F, dims: 4 };
  }
  // Chart: an exact linear presentation Q^4 -> Q^3 (three shown axes, the fourth folded by an offset), then a 3->2 law with depth.
  // law: {kind:'oblique', a, b} : x' = x + a z, y' = y + b z, depth = z      (exact)
  //      {kind:'perspective', distance D} : x' = D x/(D+z), y' = D y/(D+z), depth = z (exact for rational D, z > -D)
  function Chart(spec) {
    const shown = spec.shown || [0, 1, 2], folded = spec.folded ?? 3; const fold = (spec.fold || ['1/3', '1/5', '1/4']).map(R);
    const law = spec.law || { kind: 'oblique', a: '1/2', b: '1/3' };
    const to3 = (c) => { const p = shown.map((d) => c[d]); const w = c[folded] === undefined ? Rat.ZERO : c[folded]; return [p[0].add(w.mul(fold[0])), p[1].add(w.mul(fold[1])), p[2].add(w.mul(fold[2]))]; };
    const to2 = (p) => {
      if (law.kind === 'oblique') return { xy: [p[0].add(p[2].mul(R(law.a))), p[1].add(p[2].mul(R(law.b)))], depth: p[2] };
      const D = R(law.distance); const den = D.add(p[2]); if (den.sign() <= 0) throw new Error('perspective: point behind the eye'); return { xy: [D.mul(p[0]).div(den), D.mul(p[1]).div(den)], depth: p[2] };
    };
    return { spec, shown, folded, law, project: (c) => to2(to3(c)), to3 };
  }
  // Project a lattice: segments with depths; quads with projected corners and depths
  function project(lattice, chart) {
    const P = lattice.V.map((v) => chart.project(v.coords));
    const segments = lattice.E.map((e) => ({ a: P[e.from].xy, b: P[e.to].xy, depthA: P[e.from].depth, depthB: P[e.to].depth, source: { edge: e.id } }));
    const quads = lattice.F.map((f) => ({ id: f.id, corners: f.corners.map((c) => P[c].xy), depths: f.corners.map((c) => P[c].depth), directions: f.directions }));
    return { points: P, segments, quads };
  }
  // exact visibility per planar-map face: the topmost (minimal-depth) quad covering an interior point
  function visibleQuads(map, quads) {
    const result = new Map();
    for (const f of map.faces) {
      if (!f.bounded) continue;
      const p = PlanarMap.interiorPoint(map, f); let best = null;
      for (const q of quads) {
        // bbox prefilter
        let minx = q.corners[0][0], maxx = minx, miny = q.corners[0][1], maxy = miny; for (const c of q.corners) { if (c[0].lt(minx)) minx = c[0]; if (c[0].gt(maxx)) maxx = c[0]; if (c[1].lt(miny)) miny = c[1]; if (c[1].gt(maxy)) maxy = c[1]; }
        if (p[0].lt(minx) || p[0].gt(maxx) || p[1].lt(miny) || p[1].gt(maxy)) continue;
        if (!PlanarMap.pointInCycle(q.corners, p)) continue;
        const d = depthAt(q, p); if (d === null) continue;
        if (!best || d.lt(best.depth)) best = { quad: q.id, depth: d, open: false };
        else if (d.eq(best.depth)) best.open = true; // OcclusionFace::Open — the receiver has not proved a winner
      }
      if (best) result.set(f.id, best);
    }
    return result;
  }
  // depth is affine over a projected parallelogram: solve p = c0 + s (c1-c0) + t (c3-c0) exactly
  function depthAt(q, p) {
    const [c0, c1, , c3] = q.corners; const u = [c1[0].sub(c0[0]), c1[1].sub(c0[1])], v = [c3[0].sub(c0[0]), c3[1].sub(c0[1])];
    const det = cross2(u[0], u[1], v[0], v[1]); if (det.isZero()) return null;
    const w = [p[0].sub(c0[0]), p[1].sub(c0[1])]; const s = cross2(w[0], w[1], v[0], v[1]).div(det), t = cross2(u[0], u[1], w[0], w[1]).div(det);
    return q.depths[0].add(q.depths[1].sub(q.depths[0]).mul(s)).add(q.depths[3].sub(q.depths[0]).mul(t));
  }
  // exact depth gradient of a projected parallelogram in the receiver's chart: the face's modal current (gx + i gy)
  function depthGradient(q) {
    const [c0, c1, , c3] = q.corners; const u = [c1[0].sub(c0[0]), c1[1].sub(c0[1])], v = [c3[0].sub(c0[0]), c3[1].sub(c0[1])];
    const det = cross2(u[0], u[1], v[0], v[1]); if (det.isZero()) return null;
    const dz1 = q.depths[1].sub(q.depths[0]), dz3 = q.depths[3].sub(q.depths[0]);
    return { re: dz1.mul(v[1]).sub(dz3.mul(u[1])).div(det), im: dz3.mul(u[0]).sub(dz1.mul(v[0])).div(det), parity: det.sign() };
  }
  // depth level lines on a quad at spacing delta: exact segments (depth is affine in (s,t))
  function depthLines(q, delta) {
    const [c0, c1, c2, c3] = q.corners; const [z0, z1, z2, z3] = q.depths; delta = R(delta);
    const zmin = [z0, z1, z2, z3].reduce((a, b) => Rat.min(a, b)), zmax = [z0, z1, z2, z3].reduce((a, b) => Rat.max(a, b));
    const out = []; let k = zmin.div(delta).floor() + 1n;
    for (; delta.mul(k).lt(zmax); k++) {
      const z = delta.mul(k); // intersect level z with the four boundary edges (linear depth along each edge)
      const pts = []; const edges = [[c0, c1, z0, z1], [c1, c2, z1, z2], [c2, c3, z2, z3], [c3, c0, z3, z0]];
      for (const [a, b, za, zb] of edges) { if (za.eq(zb)) continue; const lo = Rat.min(za, zb), hi = Rat.max(za, zb); if (z.lt(lo) || z.gt(hi)) continue; const t = z.sub(za).div(zb.sub(za)); if (t.lt(0) || t.gt(1)) continue; pts.push([a[0].add(b[0].sub(a[0]).mul(t)), a[1].add(b[1].sub(a[1]).mul(t))]); }
      // dedupe exact
      const uniq = []; for (const p of pts) if (!uniq.some((u) => u[0].eq(p[0]) && u[1].eq(p[1]))) uniq.push(p);
      if (uniq.length >= 2) out.push({ level: z, a: uniq[0], b: uniq[1] });
    }
    return out;
  }
  // clip a segment to a simple polygon (node cycle) exactly: parametric intervals inside
  function clipToCycle(a, b, pts) {
    const d = [b[0].sub(a[0]), b[1].sub(a[1])]; const ts = [];
    const n = pts.length;
    for (let i = 0; i < n; i++) { const p = pts[i], q = pts[(i + 1) % n]; const e = [q[0].sub(p[0]), q[1].sub(p[1])]; const den = cross2(d[0], d[1], e[0], e[1]); if (den.isZero()) continue; const ap = [p[0].sub(a[0]), p[1].sub(a[1])]; const t = cross2(ap[0], ap[1], e[0], e[1]).div(den), u = cross2(ap[0], ap[1], d[0], d[1]).div(den); if (u.lt(0) || u.gt(1)) continue; ts.push(t); }
    ts.push(Rat.ZERO, Rat.ONE); ts.sort((x, y) => x.cmp(y));
    const out = [];
    for (let i = 0; i + 1 < ts.length; i++) { const t0 = Rat.max(ts[i], Rat.ZERO), t1 = Rat.min(ts[i + 1], Rat.ONE); if (t1.le(t0)) continue; const tm = t0.add(t1).div(2); const m = [a[0].add(d[0].mul(tm)), a[1].add(d[1].mul(tm))]; if (PlanarMap.pointInCycle(pts, m)) out.push([[a[0].add(d[0].mul(t0)), a[1].add(d[1].mul(t0))], [a[0].add(d[0].mul(t1)), a[1].add(d[1].mul(t1))]]); }
    return out;
  }
  // full model render plan: visible edges (hidden-line by depth per sub-edge), depth traces per visible face, colour classes
  function renderPlan(lattice, chart, opts = {}) {
    const pr = project(lattice, chart); const map = PlanarMap.build(pr.segments); const vis = visibleQuads(map, pr.quads);
    // sub-edge visibility: an edge piece is hidden if some quad covers its midpoint with strictly smaller depth
    const edgePieces = map.edges.map((e) => { const a = map.nodes[e.from].p, b = map.nodes[e.to].p; const m = [a[0].add(b[0]).div(2), a[1].add(b[1]).div(2)]; const dm = e.depthA && e.depthB ? e.depthA.add(e.depthB).div(2) : null; let hidden = false;
      if (dm) for (const q of pr.quads) { if (!PlanarMap.pointInCycle(q.corners, m)) continue; const dq = depthAt(q, m); if (dq && dq.lt(dm)) { hidden = true; break; } }
      return { edge: e, a, b, hidden, depth: dm }; });
    const traces = [];
    if (opts.hatch !== false) {
      const delta = R(opts.delta || '1/4');
      for (const f of map.faces) { const v = vis.get(f.id); if (!v || v.open) continue; const q = pr.quads[v.quad]; const cyc = f.darts.map((d) => map.nodes[map.darts[d].from].p);
        for (const ln of depthLines(q, delta)) for (const seg of clipToCycle(ln.a, ln.b, cyc)) traces.push({ face: f.id, level: ln.level, a: seg[0], b: seg[1] }); }
    }
    // colour: the receiver transduces each visible face's modal current (its exact depth gradient); κ is the declared aperture
    const kappa = opts.aperture || '1/2'; const fills = new Map();
    for (const [fid, v] of vis) { if (v.open) continue; const g = depthGradient(pr.quads[v.quad]); if (!g) continue; fills.set(fid, { current: g, response: HR.Colour.transduceExact([{ re: g.re, im: g.im }], kappa) }); }
    // testimony, not a colour law: the chromatic number of the receiver's face-dual graph (the corpus keeps NO four-colour governor)
    const classes = HR.FourColor.colour(map.faces.length, map.adjacency, { budget: 100000 });
    return { projection: pr, map, visible: vis, edgePieces, traces, fills, classes, openFaces: [...vis.values()].filter((v) => v.open).length };
  }
  // Z^3 slab [-g,g]^3 translated by a rational offset: sites with exact coordinates, edges in three directions
  function Lattice3(g, offset) {
    const off = offset.map(R); const V = [], index = new Map(); const key = (c) => c.join(',');
    for (let i = -g; i <= g; i++) for (let j = -g; j <= g; j++) for (let k = -g; k <= g; k++) { index.set(key([i, j, k]), V.length); V.push({ id: V.length, ints: [i, j, k], coords: [off[0].add(i), off[1].add(j), off[2].add(k)] }); }
    const E = []; for (const v of V) for (let d = 0; d < 3; d++) { const n = v.ints.slice(); n[d] += 1; const w = index.get(key(n)); if (w !== undefined) E.push({ id: E.length, from: v.id, to: w, direction: d }); }
    return { g, V, E, F: [], dims: 3 };
  }
  HR.Models = { Lattice3, Lattice4, Chart, project, visibleQuads, depthAt, depthGradient, depthLines, clipToCycle, renderPlan };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
