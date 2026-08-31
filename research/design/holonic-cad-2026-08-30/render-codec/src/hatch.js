// ===== hatch.js — intaglio: hatch strokes along exact principal directions of an implicit polynomial surface =====
// At a rational station P on g = 0: n = ∇g(P), H = Hess g(P), a rational tangent basis (t₁, t₂) = (n × e, n × t₁); first and second
// fundamental forms I = [tᵢ·tⱼ], II = [tᵢᵀ H tⱼ] (the common factor 1/|n| dropped: it moves no direction); A = I⁻¹ II; principal
// directions are the eigenvectors of A, which live in ℚ(√Δ) with Δ = tr² − 4 det, per station (quadfield.js). The sign of det II is the
// sign of the Gaussian curvature, exact. Tone is an exact predicate, never a shade: cross-hatching is admitted where the surface turns
// away from the chart's viewing direction v, (n·v)² ≤ τ (n·n)(v·v). This is the engraver's rule with a witness at every stroke.
// Akleman's plain-weaving (SIGGRAPH 2009) is the topological reading: two families of cycles on a mesh crossing over and under.
(function (HR) {
  const { Rat, R, QF } = HR;
  const dot = (a, b) => a[0].mul(b[0]).add(a[1].mul(b[1])).add(a[2].mul(b[2]));
  const cross = (a, b) => [a[1].mul(b[2]).sub(a[2].mul(b[1])), a[2].mul(b[0]).sub(a[0].mul(b[2])), a[0].mul(b[1]).sub(a[1].mul(b[0]))];
  function station(g, P, opts = {}) {
    const [x, y, z] = P.map(R); const grad = g.grad().map((d) => d.eval(x, y, z)); const Hp = g.hessian().map((row) => row.map((d) => d.eval(x, y, z)));
    const nn = dot(grad, grad); if (nn.isZero()) return { singular: true, P };
    // tangent basis: cross with the axis least aligned with n (exact comparison of squares)
    const ax = [0, 1, 2].reduce((best, i) => (grad[i].mul(grad[i]).lt(grad[best].mul(grad[best])) ? i : best), 0); const e = [Rat.ZERO, Rat.ZERO, Rat.ZERO]; e[ax] = Rat.ONE;
    const t1 = cross(grad, e), t2 = cross(grad, t1);
    const Hv = (v) => [0, 1, 2].map((i) => Hp[i][0].mul(v[0]).add(Hp[i][1].mul(v[1])).add(Hp[i][2].mul(v[2])));
    const I = [[dot(t1, t1), dot(t1, t2)], [dot(t2, t1), dot(t2, t2)]]; const II = [[dot(t1, Hv(t1)), dot(t1, Hv(t2))], [dot(t2, Hv(t1)), dot(t2, Hv(t2))]];
    const detI = I[0][0].mul(I[1][1]).sub(I[0][1].mul(I[1][0])); const Iinv = [[I[1][1].div(detI), I[0][1].neg().div(detI)], [I[1][0].neg().div(detI), I[0][0].div(detI)]];
    const A = [[Iinv[0][0].mul(II[0][0]).add(Iinv[0][1].mul(II[1][0])), Iinv[0][0].mul(II[0][1]).add(Iinv[0][1].mul(II[1][1]))], [Iinv[1][0].mul(II[0][0]).add(Iinv[1][1].mul(II[1][0])), Iinv[1][0].mul(II[0][1]).add(Iinv[1][1].mul(II[1][1]))]];
    const tr = A[0][0].add(A[1][1]), det = A[0][0].mul(A[1][1]).sub(A[0][1].mul(A[1][0])); const delta = tr.mul(tr).sub(det.mul(4));
    const gaussSign = II[0][0].mul(II[1][1]).sub(II[0][1].mul(II[1][0])).sign(); // sign of K (det II / (|n|² det I), det I > 0)
    let dirs;
    if (delta.sign() < 0) return { singular: true, P, reason: 'non-real principal directions (numerical impossibility for a symmetric pencil; reported, not repaired)' };
    const lam = [new QF(tr.div(2), R('1/2'), delta), new QF(tr.div(2), R('-1/2'), delta)]; // (tr ± √Δ)/2
    const umbilic = delta.isZero();
    dirs = lam.map((l) => { // eigenvector of A: (A12, λ − A11) unless A12 = 0, then (λ − A22, A21) or an axis
      let v; if (!A[0][1].isZero()) v = [QF.rat(A[0][1], delta), l.sub(A[0][0])]; else if (!A[1][0].isZero()) v = [l.sub(A[1][1]), QF.rat(A[1][0], delta)]; else v = l.sub(A[0][0]).isZero() ? [QF.rat(Rat.ONE, delta), QF.rat(Rat.ZERO, delta)] : [QF.rat(Rat.ZERO, delta), QF.rat(Rat.ONE, delta)];
      // 3-D direction v₁ t₁ + v₂ t₂ in ℚ(√Δ)³
      return [0, 1, 2].map((i) => v[0].mul(t1[i]).add(v[1].mul(t2[i]))); });
    // foreshortening predicate against the chart's viewing direction
    let grazing = null; if (opts.view) { const v = opts.view.map(R); const nv = dot(grad, v); grazing = nv.mul(nv).mul(R(opts.tone || '1/4') === null ? 1 : 1).cmp(nn.mul(dot(v, v)).mul(R(opts.tone || '1/4'))) <= 0; }
    return { P: [x, y, z], n: grad, nn, I, II, A, tr, det, delta, gaussSign, umbilic, dirs, lambdaScaled: lam, grazing };
  }
  // choose the direction more transverse to the horizontal slices (larger z-component, compared exactly by squares in ℚ(√Δ))
  function transverse(st) { if (!st || st.singular) return null; const [d0, d1] = st.dirs; const z0 = d0[2].mul(d0[2]), z1 = d1[2].mul(d1[2]); return z0.sub(z1).sign() >= 0 ? d0 : d1; }
  // a hatch stroke at P along direction d (QF³) of declared length L in chart units: endpoints as float faces, the exact direction carried as source
  function stroke(P, d, L) { const f = d.map((q) => q.toNumber()); const m = Math.hypot(f[0], f[1], f[2]) || 1; const e = f.map((q) => (q / m) * L); const p = P.map((q) => q.toNumber()); return { a: [p[0] - e[0] / 2, p[1] - e[1] / 2, p[2] - e[2] / 2], b: [p[0] + e[0] / 2, p[1] + e[1] / 2, p[2] + e[2] / 2], source: `P=(${P.join(',')}) d=(${d.map(String).join(';')})` }; }
  HR.Hatch = { station, transverse, stroke };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
