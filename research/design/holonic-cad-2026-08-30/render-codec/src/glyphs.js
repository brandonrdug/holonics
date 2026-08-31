// ===== glyphs.js — the rigid symbol library: rational polylines on a unit cell, named anchors, hand marks =====
// Laws: (1) no arrowheads — orientation is the hand mark, a tick of length 1/8 on the + side at the target end;
//       (2) stroke width is 1 device pixel unless a declared quantity sets it (width = ceil(q/unit) px);
//       (3) orientations are the lattice's own symmetry group D4 (exact integer matrices); nothing else is admitted;
//       (4) every mark corresponds to an occurrence, port, hand, or declared quantity — nothing decorative.
(function (HR) {
  const { Rat, R } = HR;
  const P = (x, y) => [R(x), R(y)];
  const poly = (...pts) => pts.map(([x, y]) => P(x, y));
  const D4 = { r0: [[1, 0], [0, 1]], r90: [[0, -1], [1, 0]], r180: [[-1, 0], [0, -1]], r270: [[0, 1], [-1, 0]], mx: [[-1, 0], [0, 1]], my: [[1, 0], [0, -1]], d1: [[0, 1], [1, 0]], d2: [[0, -1], [-1, 0]] };
  // hand mark for an oriented segment a->b with hand +1/-1: a tick at b, perpendicular, on the hand's side, length 1/8 of the unit
  function handMark(a, b, hand = 1, len = R('1/8')) {
    const d = [b[0].sub(a[0]), b[1].sub(a[1])]; // perpendicular (-dy, dx) is the + side (counter-clockwise)
    const n = [d[1].neg(), d[0]]; // normalise exactly only for axis-aligned/diagonal lattice directions: divide by max(|dx|,|dy|)
    const m = Rat.max(d[0].abs(), d[1].abs()); if (m.isZero()) return null; const s = len.div(m).mul(hand);
    return [b, [b[0].add(n[0].mul(s)), b[1].add(n[1].mul(s))]];
  }
  // a sinusoid is not rational; the pump glyph carries it as a declared polyline of dyadic samples (a codec face of the symbol, not a quantity)
  const sine = (n = 16, amp = '1/4') => { const out = []; for (let k = 0; k <= n; k++) { const x = R(k).div(n).mul(R('1/2')).sub(R('1/4')); out.push([x, R(amp).mul(R(Math.round(Math.sin(2 * Math.PI * k / n) * 4096) / 4096))]); } return out; };
  // exact rational points ON the circle: t ↦ ((1 − t²)/(1 + t²), 2t/(1 + t²)) closed through the point at infinity (−1, 0); no π, no float
  const circle = (cx, cy, r, n = 16) => { const out = []; for (let k = 0; k < n; k++) { const t = R(4 * k - 2 * n).div(n); const d = Rat.ONE.add(t.mul(t)); out.push([R(cx).add(R(r).mul(Rat.ONE.sub(t.mul(t)).div(d))), R(cy).add(R(r).mul(t.mul(2).div(d)))]); } out.push([R(cx).sub(R(r)), R(cy)]); out.push(out[0]); return out; };
  // an arc of the same parametrisation between two parameter values (a cup is t ∈ [−1, 1] rotated: the lower half from (0,−r) to (0, r)… we take the half x ≥ 0 and rotate by D4)
  const arc = (cx, cy, r, t0, t1, n = 8) => { const out = []; for (let k = 0; k <= n; k++) { const t = R(t0).add(R(t1).sub(R(t0)).mul(R(k).div(n))); const d = Rat.ONE.add(t.mul(t)); out.push([R(cx).add(R(r).mul(Rat.ONE.sub(t.mul(t)).div(d))), R(cy).add(R(r).mul(t.mul(2).div(d)))]); } return out; };
  // Each symbol: {strokes: [polyline], anchors: {name: [x,y]}, hands: [[a,b,sign]], ports: {name: kind}, quantity: name of the declared quantity that sets width (or null)}
  const SYMBOLS = {
    site:      { strokes: [], dots: [P(0, 0)], anchors: { c: P(0, 0) }, ports: { c: 'shared' }, kind: 'occurrence' },
    edge:      { strokes: [poly(['-1/2', 0], ['1/2', 0])], anchors: { a: P('-1/2', 0), b: P('1/2', 0) }, hands: [[P('-1/2', 0), P('1/2', 0), 1]], ports: { a: 'shared', b: 'shared' }, kind: 'passage', quantity: 'current' },
    junction:  { strokes: [poly(['-1/2', 0], ['1/2', 0]), poly([0, 0], [0, '1/2'])], dots: [P(0, 0)], anchors: { a: P('-1/2', 0), b: P('1/2', 0), c: P(0, '1/2') }, hands: [[P('-1/2', 0), P(0, 0), 1], [P(0, '1/2'), P(0, 0), -1]], ports: { a: 'shared', b: 'emission', c: 'shared' }, kind: 'construction' },
    receiver:  { strokes: [poly(['1/8', '-3/16'], ['-1/8', 0], ['1/8', '3/16']), poly(['-1/8', 0], ['-1/2', 0])], anchors: { in: P('-1/2', 0) }, ports: { in: 'receiver' }, kind: 'receiver' },
    deposit:   { strokes: [poly(['-1/2', 0], ['-1/16', 0]), poly(['-1/16', '-1/4'], ['-1/16', '1/4']), poly(['1/16', '-1/4'], ['1/16', '1/4']), poly(['1/16', 0], ['1/2', 0])], anchors: { pole: P('-1/2', 0), read: P('1/2', 0) }, ports: { pole: 'shared', read: 'shared' }, kind: 'deposit' },
    transport: { strokes: [poly(['-1/2', 0], ['-1/4', 0]), poly(['-1/4', '-1/8'], ['1/4', '-1/8'], ['1/4', '1/8'], ['-1/4', '1/8'], ['-1/4', '-1/8']), poly(['1/4', 0], ['1/2', 0])], anchors: { a: P('-1/2', 0), b: P('1/2', 0) }, hands: [[P('1/4', 0), P('1/2', 0), 1]], ports: { a: 'shared', b: 'shared' }, kind: 'transport', quantity: 'current' },
    pump:      { strokes: [poly(['-1/2', 0], ['-1/4', 0]), circle(0, 0, '1/4'), sine(16, '1/8'), poly(['1/4', 0], ['1/2', 0])], anchors: { out: P('1/2', 0) }, hands: [[P('1/4', 0), P('1/2', 0), 1]], ports: { out: 'pump' }, kind: 'drive', quantity: 'amplitude' },
    coupling:  { strokes: [poly(['-1/2', '-1/4'], ['1/2', '-1/4']), poly(['-1/2', '1/4'], ['1/2', '1/4']), poly([0, '-1/4'], [0, '-1/8']), poly([0, '1/8'], [0, '1/4'])], anchors: { a1: P('-1/2', '-1/4'), a2: P('1/2', '-1/4'), b1: P('-1/2', '1/4'), b2: P('1/2', '1/4') }, ports: { a1: 'shared', a2: 'shared', b1: 'shared', b2: 'shared' }, kind: 'coupling', quantity: 'mutual' },
    quotient:  { strokes: [poly(['-1/2', '-1/4'], ['-1/8', 0]), poly(['-1/2', '1/4'], ['-1/8', 0]), poly(['-1/8', 0], ['1/2', 0]), poly(['-1/8', '-1/8'], ['-1/8', '1/8'])], anchors: { in1: P('-1/2', '-1/4'), in2: P('-1/2', '1/4'), face: P('1/2', 0) }, ports: { in1: 'return', in2: 'return', face: 'emission' }, kind: 'quotient' },
    membrane:  { strokes: [], dashed: [poly(['-1/2', '-1/2'], ['1/2', '-1/2'], ['1/2', '1/2'], ['-1/2', '1/2'], ['-1/2', '-1/2'])], anchors: { w: P('-1/2', 0), e: P('1/2', 0), n: P(0, '1/2'), s: P(0, '-1/2') }, ports: { w: 'return', e: 'emission', n: 'feedback', s: 'exterior' }, kind: 'membrane' },
    chart:     { strokes: [poly(['-3/8', '-1/4'], ['1/8', '-1/4'], ['3/8', '1/4'], ['-1/8', '1/4'], ['-3/8', '-1/4']), poly([0, 0], [0, '1/2'])], dots: [P(0, 0)], anchors: { origin: P(0, 0), normal: P(0, '1/2') }, ports: { origin: 'shared' }, kind: 'chart' },
    parametron:{ strokes: [poly([0, '3/8'], ['-3/8', '-3/16']), poly(['-3/8', '-3/16'], ['3/8', '-3/16']), poly(['3/8', '-3/16'], [0, '3/8']), poly([0, '3/8'], [0, '1/2']), poly(['-3/8', '-3/16'], ['-1/2', '-1/4']), poly(['3/8', '-3/16'], ['1/2', '-1/4'])], dots: [P(0, '3/8'), P('-3/8', '-3/16'), P('3/8', '-3/16')],
                 hands: [[P(0, '3/8'), P('-3/8', '-3/16'), 1], [P('-3/8', '-3/16'), P('3/8', '-3/16'), 1], [P('3/8', '-3/16'), P(0, '3/8'), 1]], anchors: { n0: P(0, '1/2'), n1: P('-1/2', '-1/4'), n2: P('1/2', '-1/4'), c: P(0, 0) }, ports: { n0: 'shared', n1: 'shared', n2: 'shared' }, kind: 'carrier', quantity: 'current' },
    exterior:  { strokes: [circle(0, 0, '1/8', 12), poly(['-1/2', 0], ['-1/8', 0])], anchors: { a: P('-1/2', 0) }, ports: { a: 'exterior' }, kind: 'port' },
    vertex:    { strokes: [poly(['-1/2', '-1/4'], [0, 0]), poly(['-1/2', '1/4'], [0, 0]), poly([0, 0], ['1/2', 0])], dots: [P(0, 0)], hands: [[P('-1/2', '-1/4'), P(0, 0), 1], [P('-1/2', '1/4'), P(0, 0), -1], [P(0, 0), P('1/2', 0), 1]], anchors: { in1: P('-1/2', '-1/4'), in2: P('-1/2', '1/4'), out: P('1/2', 0) }, ports: { in1: 'return', in2: 'return', out: 'emission' }, kind: 'interaction' },
    // a net with more than two terminals is a hyperedge (MathWorld): its incidence is the star; the vertex–vertex reading would lose it
    hyperedge: { strokes: [poly(['-1/2', 0], [0, 0]), poly(['1/2', 0], [0, 0]), poly([0, '1/2'], [0, 0]), poly([0, '-1/2'], [0, 0])], dots: [P(0, 0)], anchors: { w: P('-1/2', 0), e: P('1/2', 0), n: P(0, '1/2'), s: P(0, '-1/2') }, ports: { w: 'shared', e: 'shared', n: 'shared', s: 'shared' }, kind: 'net' },
    // Bord 1-cells (Leinster p.8): oriented arcs and the circle, as exact rational points on the circle
    // the right half-circle t ∈ [−1, 1] turned by an exact quarter turn: cup = lower half about (0, ¼), cap = upper half about (0, −¼)
    cup:       { strokes: [arc(0, 0, '1/4', -1, 1, 8).map(([x, y]) => [y, x.neg().add(R('1/4'))])], anchors: { a: P('-1/4', '1/4'), b: P('1/4', '1/4') }, hands: [[P('-1/4', '1/4'), P(0, 0), 1]], ports: { a: 'shared', b: 'shared' }, kind: 'bord-1' },
    cap:       { strokes: [arc(0, 0, '1/4', -1, 1, 8).map(([x, y]) => [y.neg(), x.sub(R('1/4'))])], anchors: { a: P('1/4', '-1/4'), b: P('-1/4', '-1/4') }, hands: [[P('1/4', '-1/4'), P(0, 0), -1]], ports: { a: 'shared', b: 'shared' }, kind: 'bord-1' },
    circle:    { strokes: [circle(0, 0, '1/4', 16)], anchors: { c: P(0, 0) }, hands: [[P('1/4', 0), P('1/4', '1/16'), 1]], ports: {}, kind: 'bord-1' },
    // an event on a Minkowski chart and the two null legs of its cone (unit length, the cone itself is exact lines in the chart)
    event:     { strokes: [poly(['-1/2', '1/2'], [0, 0], ['1/2', '1/2']), poly(['-1/2', '-1/2'], [0, 0], ['1/2', '-1/2'])], dots: [P(0, 0)], anchors: { e: P(0, 0) }, ports: { e: 'receiver' }, kind: 'event' },
  };
  function place(name, at, orient = 'r0', scale = 1) {
    const sym = SYMBOLS[name]; if (!sym) throw new Error('unknown symbol ' + name); const M = D4[orient] || D4.r0; const s = R(scale); const o = [R(at[0]), R(at[1])];
    const tf = (p) => [o[0].add(s.mul(p[0].mul(M[0][0]).add(p[1].mul(M[0][1])))), o[1].add(s.mul(p[0].mul(M[1][0]).add(p[1].mul(M[1][1]))))];
    const det = M[0][0] * M[1][1] - M[0][1] * M[1][0]; // reflections reverse hands
    return { name, kind: sym.kind, quantity: sym.quantity || null, strokes: (sym.strokes || []).map((pl) => pl.map(tf)), dashed: (sym.dashed || []).map((pl) => pl.map(tf)), dots: (sym.dots || []).map(tf),
      hands: (sym.hands || []).map(([a, b, h]) => handMark(tf(a), tf(b), h * det, R('1/8').mul(s))).filter(Boolean), anchors: Object.fromEntries(Object.entries(sym.anchors).map(([k, p]) => [k, tf(p)])), ports: sym.ports };
  }
  // place a symbol along a projected lattice edge a→b: the unit cell's x-axis is carried to b − a and its y-axis to the exact quarter turn
  // (−dy, dx) of the same length — an exact similarity over ℚ, so the symbol's orientation is the chart's image of a lattice direction, never free
  function placeAlong(name, a, b, scale = 1) {
    const sym = SYMBOLS[name]; if (!sym) throw new Error('unknown symbol ' + name); const s = R(scale); const d = [R(b[0]).sub(R(a[0])), R(b[1]).sub(R(a[1]))]; const m = [R(a[0]).add(d[0].div(2)), R(a[1]).add(d[1].div(2))];
    const tf = (p) => [m[0].add(s.mul(p[0].mul(d[0]).sub(p[1].mul(d[1])))), m[1].add(s.mul(p[0].mul(d[1]).add(p[1].mul(d[0]))))];
    return { name, kind: sym.kind, quantity: sym.quantity || null, strokes: (sym.strokes || []).map((pl) => pl.map(tf)), dashed: (sym.dashed || []).map((pl) => pl.map(tf)), dots: (sym.dots || []).map(tf),
      hands: (sym.hands || []).map(([p, q, h]) => handMark(tf(p), tf(q), h, R('1/8').mul(s))).filter(Boolean), anchors: Object.fromEntries(Object.entries(sym.anchors).map(([k, p]) => [k, tf(p)])), ports: sym.ports };
  }
  // width law: 1 device px, or ceil(q / unit) px for a declared quantity q (exact integer face)
  function widthPx(q, unit) { if (q == null) return 1; const r = R(q).abs().div(R(unit || 1)); const f = r.floor(); const c = r.eq(R(f)) ? f : f + 1n; return Math.max(1, Number(c)); }
  // a schematic: instances + lattice wires; nets by exact anchor coincidence; crossings from the planar map (co-presence, not contact)
  function assemble(doc) {
    const placed = doc.instances.map((inst) => ({ inst, glyph: place(inst.symbol, inst.at, inst.orient, inst.scale || 1) }));
    const terminals = []; // [{point, inst, port, kind}]
    placed.forEach(({ inst, glyph }, i) => { for (const [port, p] of Object.entries(glyph.anchors)) if (glyph.ports[port]) terminals.push({ point: p, inst: i, port, kind: glyph.ports[port] }); });
    const wires = (doc.wires || []).map((w, wi) => ({ id: wi, points: w.map((p) => [R(p[0]), R(p[1])]) }));
    // nets: union-find over terminals and wire vertices by exact coincidence
    const keyOf = HR.pkey; const parent = new Map(); const find = (k) => { while (parent.get(k) !== k) { parent.set(k, parent.get(parent.get(k))); k = parent.get(k); } return k; }; const add = (k) => { if (!parent.has(k)) parent.set(k, k); }; const union = (a, b) => { parent.set(find(a), find(b)); };
    for (const t of terminals) add(keyOf(t.point));
    for (const w of wires) { for (const p of w.points) add(keyOf(p)); for (let i = 0; i + 1 < w.points.length; i++) union(keyOf(w.points[i]), keyOf(w.points[i + 1])); }
    // terminals lying in the interior of a wire segment (axis-aligned lattice wires) also join
    for (const t of terminals) for (const w of wires) for (let i = 0; i + 1 < w.points.length; i++) { const a = w.points[i], b = w.points[i + 1]; if (HR.orient2d(a, b, t.point) === 0) { const inx = Rat.min(a[0], b[0]).le(t.point[0]) && t.point[0].le(Rat.max(a[0], b[0])), iny = Rat.min(a[1], b[1]).le(t.point[1]) && t.point[1].le(Rat.max(a[1], b[1])); if (inx && iny) union(keyOf(t.point), keyOf(a)); } }
    const nets = new Map(); for (const t of terminals) { const r = find(keyOf(t.point)); if (!nets.has(r)) nets.set(r, []); nets.get(r).push(t); }
    // contact rules (Library 0)
    const RULE = (a, b) => { if (a === 'receiver' && b === 'receiver') return 'refused: nothing is read'; if (a === 'emission' && b === 'emission') return 'refused: two drivers, no junction'; if (a === 'return' && b === 'return') return 'warn: co-presence is not contact'; if (a === 'exterior' || b === 'exterior') return 'open: stays visible'; return 'ok'; };
    const checks = []; for (const [net, ts] of nets) { const kinds = ts.map((t) => t.kind); const findings = new Set(); for (let i = 0; i < kinds.length; i++) for (let j = i + 1; j < kinds.length; j++) { const r = RULE(kinds[i], kinds[j]); if (r !== 'ok') findings.add(r); } if (ts.length === 1 && ts[0].kind !== 'exterior') findings.add('open: single terminal'); checks.push({ net, terminals: ts.length, kinds, findings: [...findings] }); }
    // crossings: all strokes + wires through the exact planar map (depth-less: a crossing is co-presence, not contact)
    const segs = []; for (const w of wires) for (let i = 0; i + 1 < w.points.length; i++) segs.push({ a: w.points[i], b: w.points[i + 1] });
    const map = HR.PlanarMap.build(segs);
    return { placed, terminals, wires, nets: [...nets.values()], checks, crossings: map.crossings, map };
  }
  HR.Glyphs = { SYMBOLS, D4, place, placeAlong, handMark, widthPx, assemble, circle, arc };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
