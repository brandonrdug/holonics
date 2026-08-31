// ===== polygraph.js — a document's cells as an n-polygraph (Ara, Burroni, Guiraud, Malbos, Métayer, Mimram 2312.00429) =====
// Σ₀ generators; Σ₁ generators with s₀, t₀ in Σ₀; Σ₂ generators whose source and target are parallel paths in the free category Σ₁*;
// Σ₃ generators whose source and target are pastings of 2-cells with equal 1-boundary. Globular relations are checked exactly on chains:
// for a 2-cell, s₀(src) = s₀(tgt) and t₀(src) = t₀(tgt); for a 3-cell, ∂(src pasting) = ∂(tgt pasting) as integer 1-chains.
// The receiver reading of a schematic (Brown–Porter, math/0306223): a lattice's 2-cells are commuting squares composed in two directions.
(function (HR) {
  class Polygraph {
    constructor(name) { this.name = name; this.cells = [[], [], [], []]; this.obstructions = []; }
    add0(label) { const c = { id: this.cells[0].length, label }; this.cells[0].push(c); return c.id; }
    add1(label, s, t) { const c = { id: this.cells[1].length, label, s, t }; this.cells[1].push(c); return c.id; }
    // a path is a list of [1-cell id, sign] (sign −1 walks the 1-cell backwards, admitted only in the groupoid reading)
    path0(path) { if (!path.length) return null; const first = path[0], last = path[path.length - 1]; const c = (p) => this.cells[1][p[0]]; return { s: p0(first, c), t: p1(last, c) }; }
    add2(label, src, tgt) { const a = this.path0(src), b = this.path0(tgt); const ok = a && b && a.s === b.s && a.t === b.t; for (let i = 0; i + 1 < src.length; i++) if (p1(src[i], (p) => this.cells[1][p[0]]) !== p0(src[i + 1], (p) => this.cells[1][p[0]])) this.obstructions.push({ dim: 2, label, reason: 'source path not composable at ' + i });
      for (let i = 0; i + 1 < tgt.length; i++) if (p1(tgt[i], (p) => this.cells[1][p[0]]) !== p0(tgt[i + 1], (p) => this.cells[1][p[0]])) this.obstructions.push({ dim: 2, label, reason: 'target path not composable at ' + i });
      if (!ok) this.obstructions.push({ dim: 2, label, reason: 'globular: s₀(src) ≠ s₀(tgt) or t₀(src) ≠ t₀(tgt)' }); const c = { id: this.cells[2].length, label, src, tgt, s0: a && a.s, t0: a && a.t }; this.cells[2].push(c); return c.id; }
    // ∂ of a 2-cell as an integer 1-chain: tgt − src
    chain2(id) { const c = this.cells[2][id]; const ch = new Map(); const add = (p, k) => ch.set(p[0], (ch.get(p[0]) || 0) + k * p[1]); for (const p of c.tgt) add(p, 1); for (const p of c.src) add(p, -1); return ch; }
    add3(label, src, tgt) { // src, tgt: lists of [2-cell id, sign]
      const sum = (list) => { const ch = new Map(); for (const [id, sg] of list) for (const [e, k] of this.chain2(id)) ch.set(e, (ch.get(e) || 0) + sg * k); return ch; };
      const a = sum(src), b = sum(tgt); let ok = true; const keys = new Set([...a.keys(), ...b.keys()]); for (const k of keys) if ((a.get(k) || 0) !== (b.get(k) || 0)) { ok = false; break; }
      if (!ok) this.obstructions.push({ dim: 3, label, reason: 'globular: ∂(source pasting) ≠ ∂(target pasting)' }); const c = { id: this.cells[3].length, label, src, tgt }; this.cells[3].push(c); return c.id; }
    counts() { return this.cells.map((c) => c.length); }
    euler() { return this.cells.reduce((s, c, k) => s + (k % 2 ? -c.length : c.length), 0); }
  }
  const p0 = (p, c) => (p[1] > 0 ? c(p).s : c(p).t), p1 = (p, c) => (p[1] > 0 ? c(p).t : c(p).s);
  // the 3-polygraph of the cubic lattice [0,g)³: nodes, oriented edges, commuting squares, cubes (a search assigns the pasting signs;
  // failure would be an obstruction, and it is reported rather than repaired)
  function fromLattice3(g) {
    const P = new Polygraph('ℤ³ [0,' + g + ')³'); const idx = new Map(); const key = (c) => c.join(',');
    for (let i = 0; i < g; i++) for (let j = 0; j < g; j++) for (let k = 0; k < g; k++) idx.set(key([i, j, k]), P.add0(key([i, j, k])));
    const e = new Map(); const ekey = (c, d) => key(c) + '|' + d;
    for (const [k, id] of idx) { const c = k.split(',').map(Number); for (let d = 0; d < 3; d++) { const n = c.slice(); n[d]++; const w = idx.get(key(n)); if (w === undefined) continue; e.set(ekey(c, d), P.add1('e' + d + '(' + k + ')', id, w)); } }
    const sq = new Map();
    for (const [k] of idx) { const c = k.split(',').map(Number); for (let a = 0; a < 3; a++) for (let b = a + 1; b < 3; b++) { const ca = c.slice(); ca[a]++; const cb = c.slice(); cb[b]++; const ea = e.get(ekey(c, a)), eb = e.get(ekey(c, b)), eab = e.get(ekey(ca, b)), eba = e.get(ekey(cb, a)); if ([ea, eb, eab, eba].some((x) => x === undefined)) continue;
      sq.set(key(c) + '|' + a + b, P.add2('□' + a + b + '(' + k + ')', [[ea, 1], [eab, 1]], [[eb, 1], [eba, 1]])); } }
    let cubes = 0, unresolved = 0;
    for (const [k] of idx) { const c = k.split(',').map(Number); const mn = [sq.get(key(c) + '|01'), sq.get(key(c) + '|12'), sq.get(key(c) + '|02')]; const cz = c.slice(); cz[2]++; const cx = c.slice(); cx[0]++; const cy = c.slice(); cy[1]++; const mx = [sq.get(key(cz) + '|01'), sq.get(key(cx) + '|12'), sq.get(key(cy) + '|02')]; if ([...mn, ...mx].some((x) => x === undefined)) continue;
      // find signs so that ∂(Σ ε_i max faces) = ∂(Σ δ_j min faces); δ = (1,1,1) for the min pasting is not forced either — search both
      let found = null; for (let sm = 0; sm < 8 && found === null; sm++) for (let sx = 0; sx < 8 && found === null; sx++) { const S = (m, i) => ((m >> i) & 1 ? 1 : -1); const src = mn.map((id, i) => [id, S(sm, i)]), tgt = mx.map((id, i) => [id, S(sx, i)]); const before = P.obstructions.length; const id = P.add3('cube(' + k + ')', src, tgt); if (P.obstructions.length === before) found = id; else { P.cells[3].pop(); P.obstructions.pop(); } }
      if (found !== null) cubes++; else { unresolved++; P.obstructions.push({ dim: 3, label: 'cube(' + k + ')', reason: 'no pasting signs close the boundary' }); } }
    return { polygraph: P, cubes, unresolved };
  }
  // the 2-polygraph of a receiver's planar map: nodes, edges, and every bounded face as a 2-cell between its two boundary paths from the
  // lexicographically least node to the greatest (the pasting-diagram reading of a planar map)
  function fromPlanarMap(map) {
    const P = new Polygraph('planar map'); map.nodes.forEach((n) => P.add0(HR.pkey(n.p))); map.edges.forEach((e) => P.add1('e' + e.id, e.from, e.to));
    const lex = (a, b) => { const c = map.nodes[a].p[0].cmp(map.nodes[b].p[0]); return c !== 0 ? c : map.nodes[a].p[1].cmp(map.nodes[b].p[1]); };
    let faces = 0; for (const f of map.faces) { if (!f.bounded) continue; const seq = f.darts.map((d) => map.darts[d]); const nodesCyc = seq.map((d) => d.from); let imin = 0, imax = 0; nodesCyc.forEach((n, i) => { if (lex(n, nodesCyc[imin]) < 0) imin = i; if (lex(n, nodesCyc[imax]) > 0) imax = i; });
      const L = seq.length; const walk = (from, to) => { const out = []; for (let i = from; i !== to; i = (i + 1) % L) out.push([seq[i].edge, seq[i].forward ? 1 : -1]); return out; };
      const rev = (path) => path.slice().reverse().map(([e, s]) => [e, -s]);
      const p1 = walk(imin, imax), p2 = rev(walk(imax, imin)); if (!p1.length || !p2.length) continue; P.add2('face' + f.id, p1, p2); faces++; }
    return { polygraph: P, faces };
  }
  HR.Polygraph = Polygraph; HR.Polygraphs = { fromLattice3, fromPlanarMap };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
