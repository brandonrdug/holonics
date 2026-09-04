// ===== minkowski.js — the Minkowski chart between two objects: events, worldlines, cones, boosts, proper times, all exact in ℚ (c = 1 cell/tick) =====
// docs/canon/TABLET_THE_MANIFOLD.md §22: a receiver sits at an event; its reach is the causal cone; inside / on the null boundary / outside are
// three regions, and on the boundary the returned difference is exactly zero. In 1+1 dimensions the cone is two lines, so the retarded
// event of a uniformly moving object is RATIONAL. For a Pythagorean speed u = (m²−n²)/(m²+n²): γ = (m²+n²)/(2mn) and the Doppler factor
// √((1−u)/(1+u)) = n/m are rational — the dilating terms of the relation between two frames are exact factors, not floats.
(function (HR) {
  const { Rat, R } = HR;
  const ev = (e) => [R(e[0]), R(e[1])]; // [t, x]
  function interval(e1, e2) { const a = ev(e1), b = ev(e2); const dt = b[0].sub(a[0]), dx = b[1].sub(a[1]); const s2 = dt.mul(dt).sub(dx.mul(dx)); const s = s2.sign(); return { s2, dt, dx, kind: s > 0 ? 'timelike' : (s < 0 ? 'spacelike' : 'null') }; }
  // exact square root of a rational if it is a perfect square, else null
  function sqrtRat(q) { q = R(q); if (q.sign() < 0) return null; const sq = (x) => { const r = BigInt(Math.round(Math.sqrt(Number(x)))); for (const c of [r - 1n, r, r + 1n]) if (c >= 0n && c * c === x) return c; return null; }; const a = sq(q.n), b = sq(q.d); return a === null || b === null ? null : new Rat(a, b); }
  function boost(beta) { const b = R(beta); const g = HR.Relativity.gamma(b); if (g === null) return null; const L = [[g, g.mul(b).neg()], [g.mul(b).neg(), g]]; const D = sqrtRat(Rat.ONE.sub(b).div(Rat.ONE.add(b)));
    return { beta: b, gamma: g, doppler: D, apply: (e) => { const p = ev(e); return [L[0][0].mul(p[0]).add(L[0][1].mul(p[1])), L[1][0].mul(p[0]).add(L[1][1].mul(p[1]))]; }, matrix: L, unitT: [g, g.mul(b)], unitX: [g.mul(b), g], calibration: g.mul(g).sub(g.mul(g).mul(b).mul(b)) }; }
  function worldline(spec) { const at = ev(spec.at), u = R(spec.u); if (u.abs().cmp(Rat.ONE) >= 0) throw new Error('worldline: |u| ≥ 1 is not timelike'); const g = HR.Relativity.gamma(u); return { at, u, gamma: g, doppler: g ? sqrtRat(Rat.ONE.sub(u).div(Rat.ONE.add(u))) : null, name: spec.name || 'object', x: (t) => at[1].add(u.mul(R(t).sub(at[0]))) }; }
  // proper-time ticks along a worldline: τ = k ⇒ t = t₀ + γ k (exact when γ is rational)
  function properTicks(w, win, step = 1) { if (!w.gamma) return { ticks: [], exact: false }; const ticks = []; const t0 = R(win.t0), t1 = R(win.t1); const s = R(step); for (let k = -200; k <= 200; k++) { const t = w.at[0].add(w.gamma.mul(s).mul(k)); if (t.lt(t0) || t.gt(t1)) continue; const x = w.x(t); if (x.lt(R(win.x0)) || x.gt(R(win.x1))) continue; ticks.push({ tau: s.mul(k), event: [t, x] }); } return { ticks, exact: true }; }
  function retarded(w, E) { const e = ev(E); const out = []; for (const s of [Rat.ONE, Rat.ONE.neg()]) { const den = w.u.sub(s); if (den.isZero()) continue; const t = e[1].sub(w.at[1]).add(w.u.mul(w.at[0])).sub(s.mul(e[0])).div(den); if (t.lt(e[0])) out.push({ event: [t, w.x(t)], leg: s.sign(), check: interval([t, w.x(t)], e) }); } return out; }
  function advanced(w, E) { const e = ev(E); const out = []; for (const s of [Rat.ONE, Rat.ONE.neg()]) { const den = w.u.sub(s); if (den.isZero()) continue; const t = e[1].sub(w.at[1]).add(w.u.mul(w.at[0])).sub(s.mul(e[0])).div(den); if (t.gt(e[0])) out.push({ event: [t, w.x(t)], leg: s.sign() }); } return out; }
  function clipLine(P, d, win) { const p = ev(P); const dx = R(d[1]), dt = R(d[0]); let lo = null, hi = null; const push = (a, b) => { if (lo === null || a.gt(lo)) lo = a; if (hi === null || b.lt(hi)) hi = b; };
    const rng = (p0, dd, v0, v1) => { if (dd.isZero()) return p0.lt(R(v0)) || p0.gt(R(v1)) ? [Rat.ONE, Rat.ZERO] : [R(-1e9), R(1e9)]; const a = R(v0).sub(p0).div(dd), b = R(v1).sub(p0).div(dd); return a.lt(b) ? [a, b] : [b, a]; };
    const [a1, b1] = rng(p[0], dt, win.t0, win.t1), [a2, b2] = rng(p[1], dx, win.x0, win.x1); push(a1, b1); push(a2, b2); if (lo.gt(hi)) return null; return [[p[0].add(dt.mul(lo)), p[1].add(dx.mul(lo))], [p[0].add(dt.mul(hi)), p[1].add(dx.mul(hi))]]; }
  function cone(E, win) { const e = ev(E); const legs = []; for (const s of [1, -1]) for (const sheet of [1, -1]) { const seg = clipLine(e, [sheet, s * sheet], win); if (!seg) continue; const tE = e[0]; const inSheet = (q) => (sheet > 0 ? q[0].cmp(tE) >= 0 : q[0].cmp(tE) <= 0); const a = inSheet(seg[0]) ? seg[0] : e, b = inSheet(seg[1]) ? seg[1] : e; if (a[0].eq(b[0]) && a[1].eq(b[1])) continue; legs.push({ a, b, sheet: sheet > 0 ? 'future' : 'past', leg: s }); } return legs; }
  function plan(spec) {
    const win = spec.window; const A = worldline(spec.objects[0]), B = worldline(spec.objects[1]); const E = ev(spec.receiver);
    const bst = spec.beta !== undefined ? boost(spec.beta) : null;
    const lines = [];
    for (const w of [A, B]) { const seg = clipLine(w.at, [Rat.ONE, w.u], win); if (seg) lines.push({ a: seg[0], b: seg[1], role: 'worldline', name: w.name }); }
    for (const c of cone(E, win)) lines.push({ a: c.a, b: c.b, role: c.sheet === 'past' ? 'cone-past' : 'cone-future' });
    if (bst) { const s1 = clipLine([0, 0], [Rat.ONE, bst.beta], win), s2 = clipLine([0, 0], [bst.beta, Rat.ONE], win); if (s1) lines.push({ a: s1[0], b: s1[1], role: 'axis-t-prime' }); if (s2) lines.push({ a: s2[0], b: s2[1], role: 'axis-x-prime' });
      const sim = clipLine(E, [bst.beta, Rat.ONE], win); if (sim) lines.push({ a: sim[0], b: sim[1], role: 'simultaneity-prime' }); }
    const ax1 = clipLine([0, 0], [1, 0], win), ax2 = clipLine([0, 0], [0, 1], win); if (ax1) lines.push({ a: ax1[0], b: ax1[1], role: 'axis-t' }); if (ax2) lines.push({ a: ax2[0], b: ax2[1], role: 'axis-x' });
    // calibration hyperbolae x² − t² = ±k² as isolated contours (every vertex a certified isolating interval)
    const hyp = (spec.hyperbolae || ['1']).map(R); const levels = [...hyp.map((k) => k.mul(k).neg()), ...hyp.map((k) => k.mul(k))];
    const n = spec.grid || 32; const kb = spec.bisections || 6; const contours = levels.map((lv) => ({ level: lv, iso: HR.Brackets.isolate((t, x) => x.mul(x).sub(t.mul(t)), { x0: win.t0, x1: win.t1, y0: win.x0, y1: win.x1 }, n, lv, kb) }));
    const ret = [A, B].map((w) => retarded(w, E)); const iv = interval(A.at, B.at);
    const ticks = [A, B].map((w) => properTicks(w, win, spec.properStep || 1));
    // the relation between the two frames as dilating terms: u_rel = (u_B − u_A)/(1 − u_A u_B), γ_rel, D_rel — all rational when both speeds are Pythagorean
    const uRel = B.u.sub(A.u).div(Rat.ONE.sub(A.u.mul(B.u))); const gRel = HR.Relativity.gamma(uRel); const dRel = gRel ? sqrtRat(Rat.ONE.sub(uRel).div(Rat.ONE.add(uRel))) : null;
    return { A, B, E, boost: bst, lines, contours, retarded: ret, interval: iv, levels, ticks, relation: { u: uRel, gamma: gRel, doppler: dRel } };
  }
  HR.Minkowski = { interval, boost, worldline, properTicks, retarded, advanced, cone, clipLine, plan, sqrtRat };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
