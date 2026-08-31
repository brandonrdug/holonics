// ===== quadfield.js — Q(√Δ): the one algebraic irrationality of the receiver's light cone, carried exactly =====
// A static site at rational offset r from the receiver is seen on the past cone at t = −√(r·r); Δ = r·r is rational.
// Every later quantity (aberrated offset, Doppler factor, projected coordinate) lies in Q(√Δ) and is carried as a + b√Δ.
(function (HR) {
  const { Rat, R } = HR;
  class QF {
    constructor(a, b, delta) { this.a = R(a); this.b = R(b); this.delta = R(delta); }
    static rat(x, delta) { return new QF(x, 0, delta); }
    static root(delta) { return new QF(0, 1, delta); }
    same(o) { if (!this.delta.eq(o.delta)) throw new Error('Q(√Δ): mixed fields'); }
    add(o) { if (o instanceof Rat) return new QF(this.a.add(o), this.b, this.delta); this.same(o); return new QF(this.a.add(o.a), this.b.add(o.b), this.delta); }
    sub(o) { if (o instanceof Rat) return new QF(this.a.sub(o), this.b, this.delta); this.same(o); return new QF(this.a.sub(o.a), this.b.sub(o.b), this.delta); }
    mul(o) { if (o instanceof Rat) return new QF(this.a.mul(o), this.b.mul(o), this.delta); this.same(o); return new QF(this.a.mul(o.a).add(this.b.mul(o.b).mul(this.delta)), this.a.mul(o.b).add(this.b.mul(o.a)), this.delta); }
    conj() { return new QF(this.a, this.b.neg(), this.delta); }
    norm() { return this.a.mul(this.a).sub(this.b.mul(this.b).mul(this.delta)); } // (a+b√Δ)(a−b√Δ)
    div(o) { if (o instanceof Rat) return new QF(this.a.div(o), this.b.div(o), this.delta); this.same(o); const n = o.norm(); if (n.isZero()) throw new Error('Q(√Δ): division by zero'); const p = this.mul(o.conj()); return new QF(p.a.div(n), p.b.div(n), this.delta); }
    sign() { // exact sign of a + b√Δ (Δ > 0): compare a² with b²Δ when signs disagree
      const sa = this.a.sign(), sb = this.b.sign(); if (sb === 0) return sa; if (sa === 0) return sb; if (sa === sb) return sa;
      const c = this.a.mul(this.a).cmp(this.b.mul(this.b).mul(this.delta)); return c === 0 ? 0 : (c > 0 ? sa : sb); }
    isZero() { return this.a.isZero() && this.b.isZero(); }
    toNumber() { return this.a.toNumber() + this.b.toNumber() * Math.sqrt(this.delta.toNumber()); } // the float face
    toString() { return `${this.a}${this.b.sign() >= 0 ? '+' : '−'}${this.b.abs()}√${this.delta}`; }
  }
  // Pythagorean speeds: β = p/q with q² − p² a perfect square ⇒ γ rational
  const PYTHAGOREAN = ['3/5', '4/5', '5/13', '12/13', '8/17', '15/17', '7/25', '24/25', '20/29', '21/29'];
  function gamma(beta) { const b = R(beta); const one = Rat.ONE.sub(b.mul(b)); // 1 − β² = s²/q² exactly for the list above
    const num = one.n, den = one.d; const sq = (x) => { const r = BigInt(Math.round(Math.sqrt(Number(x)))); for (const c of [r - 1n, r, r + 1n]) if (c >= 0n && c * c === x) return c; return null; };
    const sn = sq(num), sd = sq(den); if (sn === null || sd === null) return null; return new Rat(sd, sn); }
  // Receiver-relative reading of a static site at rational offset r (3-vector of Rat), receiver velocity β along axis k (Rat), c = 1.
  // Returns retarded tick, aberrated offset r' in Q(√Δ)³, Doppler factor D in Q(√Δ), and the perspective screen point in Q(√Δ)².
  function readStaticSite(r, beta, axis, focal) {
    const delta = r[0].mul(r[0]).add(r[1].mul(r[1])).add(r[2].mul(r[2])); if (delta.isZero()) return null;
    const n = QF.root(delta); // n = |r| = −t_ret exactly; the light-cone condition itself
    const b = R(beta); const g = gamma(b); if (g === null) throw new Error('receiver speed is not Pythagorean; γ would be a float face');
    const rp = r.map((c) => QF.rat(c, delta)); // r' = r with the parallel part boosted: r'_∥ = γ (r_∥ + |β| n)
    rp[axis] = QF.rat(r[axis], delta).add(n.mul(b.abs())).mul(g);
    const rAbs = n.mul(b).add(QF.rat(r[axis], delta).mul(b)).mul(Rat.ONE).add(QF.rat(Rat.ZERO, delta)); // placeholder not used
    // Doppler: D = n / (γ (n + β·r)) with β·r = β r_axis (source-direction convention; D<1 blue-shift ahead)
    const D = n.div((n.add(QF.rat(r[axis].mul(b), delta))).mul(g));
    // perspective screen point (f x'/z', f y'/z') when z' > 0 (receiver looks along +z)
    const z = rp[2]; if (z.sign() <= 0) return { delta, n, rp, D, screen: null, behind: true };
    const f = R(focal); const sx = rp[0].mul(f).div(z), sy = rp[1].mul(f).div(z);
    return { delta, n, rp, D, screen: [sx, sy], depth: z, tRet: n.mul(Rat.ONE.neg()) };
  }
  HR.QF = QF; HR.Relativity = { PYTHAGOREAN, gamma, readStaticSite };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
