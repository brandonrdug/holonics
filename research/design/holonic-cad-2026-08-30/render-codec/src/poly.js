// ===== poly.js — exact multivariate polynomials over ℚ: the source of every surface, its gradient and its Hessian =====
// A surface is never a closure to be sampled; it is a polynomial whose value, gradient and second derivatives are exact at every
// rational station. Monomials are keyed by their exponent triple; coefficients are Rat.
(function (HR) {
  const { Rat, R } = HR;
  class Poly3 {
    constructor(terms) { this.t = new Map(); if (terms) for (const [k, c] of terms) { const v = R(c); if (!v.isZero()) this.t.set(k, v); } }
    static c(v) { return new Poly3([['0,0,0', v]]); }
    static x() { return new Poly3([['1,0,0', 1]]); } static y() { return new Poly3([['0,1,0', 1]]); } static z() { return new Poly3([['0,0,1', 1]]); }
    static var(i) { return [Poly3.x, Poly3.y, Poly3.z][i](); }
    add(o) { o = Poly3.lift(o); const out = new Poly3(this.t); for (const [k, c] of o.t) { const v = (out.t.get(k) || Rat.ZERO).add(c); if (v.isZero()) out.t.delete(k); else out.t.set(k, v); } return out; }
    sub(o) { return this.add(Poly3.lift(o).scale(-1)); }
    scale(s) { s = R(s); const out = new Poly3(); if (s.isZero()) return out; for (const [k, c] of this.t) out.t.set(k, c.mul(s)); return out; }
    mul(o) { o = Poly3.lift(o); const out = new Poly3(); for (const [ka, ca] of this.t) for (const [kb, cb] of o.t) { const a = ka.split(',').map(Number), b = kb.split(',').map(Number); const k = [a[0] + b[0], a[1] + b[1], a[2] + b[2]].join(','); const v = (out.t.get(k) || Rat.ZERO).add(ca.mul(cb)); if (v.isZero()) out.t.delete(k); else out.t.set(k, v); } return out; }
    sq() { return this.mul(this); }
    static lift(o) { return o instanceof Poly3 ? o : Poly3.c(o); }
    d(i) { const out = new Poly3(); for (const [k, c] of this.t) { const e = k.split(',').map(Number); if (e[i] === 0) continue; const v = c.mul(e[i]); e[i] -= 1; const kk = e.join(','); out.t.set(kk, (out.t.get(kk) || Rat.ZERO).add(v)); } return out; }
    eval(x, y, z) { const X = R(x), Y = R(y), Z = R(z ?? 0); let s = Rat.ZERO; const pw = (b, n) => { let r = Rat.ONE; for (let i = 0; i < n; i++) r = r.mul(b); return r; };
      for (const [k, c] of this.t) { const e = k.split(',').map(Number); s = s.add(c.mul(pw(X, e[0])).mul(pw(Y, e[1])).mul(pw(Z, e[2]))); } return s; }
    grad() { return [this.d(0), this.d(1), this.d(2)]; }
    hessian() { const g = this.grad(); return [[g[0].d(0), g[0].d(1), g[0].d(2)], [g[1].d(0), g[1].d(1), g[1].d(2)], [g[2].d(0), g[2].d(1), g[2].d(2)]]; }
    degree() { let d = 0; for (const k of this.t.keys()) { const e = k.split(',').map(Number); d = Math.max(d, e[0] + e[1] + e[2]); } return d; }
    toString() { const parts = []; for (const [k, c] of [...this.t.entries()].sort()) { const e = k.split(',').map(Number); const mon = ['x', 'y', 'z'].map((v, i) => (e[i] === 0 ? '' : e[i] === 1 ? v : v + '^' + e[i])).join(''); parts.push((c.eq(Rat.ONE) && mon ? '' : c.toString()) + mon); } return parts.join(' + ') || '0'; }
  }
  HR.Poly3 = Poly3;
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
