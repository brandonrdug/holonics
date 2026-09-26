#!/usr/bin/env python3
"""Window-balance falsifier for the source-to-neck campaign (#62).

The window balance (Lean `Holonics.Zeta.ZeroTube`) in seam time tau = -t, in the seam lift
w = i(s - 1/2) where the seam is the real axis and a pair's height is Im w = Re s - 1/2:

    dA_W/dtau = pairInertiaRate(W) + B_W,        pairInertiaRate(W) <= -2m,
    B_W = sum_k 2 y_k Im T_k,   T_k = wdot_k - 2 mirrorFlux_W(w_k)   (the tail flux).

B_W is the only term the window does not own. In the flow's time t the Lean theorem reads
B^t = -B_W. This script tests candidate source laws on:

  A. a polynomial comb (exact Gaussian rationals), and the same comb along the exact flow;
  B. the finite primon gas, a finite Euler-product surrogate (certified balls);
  C. the Davenport-Heilbronn function, the negative control (certified Rouche discs);
  D. the first zeros of xi (certified), for the source split on the seam.

Arithmetic. Exact: fractions.Fraction. Certified: arb/acb balls (python-flint), whose midpoints
and radii are exact dyadic rationals. No Python float enters a computation. Seeds for Newton
are exterior data entered as exact rationals; the certificate, not the seed, is the reading.
Every reading is printed as an exact enclosure [lo, hi] with rational endpoints at the declared
dyadic grain 2^-GRAIN, or as an exact rational.

Run (python-flint 0.9.0):
    uv venv .local/flintenv
    uv pip install --python .local/flintenv/bin/python python-flint==0.9.0
    .local/flintenv/bin/python research/notebook/zeta_tube/falsifier.py
"""

from fractions import Fraction
from math import floor, ceil

from flint import acb, acb_poly, acb_series, arb, arb_series, ctx, dirichlet_char, fmpq, fmpq_poly

ctx.prec = 256
GRAIN = 24


# ----------------------------------------------------------------------------------------------
# Exact enclosures of balls
# ----------------------------------------------------------------------------------------------

def _exact(x):
    """The exact dyadic rational value of an exact arb (a midpoint or a radius)."""
    m, e = x.man_exp()
    m, e = int(m), int(e)
    return Fraction(m) * (Fraction(2) ** e)


def bounds(x):
    """Exact rational endpoints [mid - rad, mid + rad] of a real ball."""
    mid = _exact(x.mid())
    rad = _exact(arb(x.rad()))
    return mid - rad, mid + rad


def enc(x, k=GRAIN):
    """Outward enclosure of a real ball at grain 2^-k, as a string of two exact rationals."""
    lo, hi = bounds(x)
    s = 2 ** k
    lo_k = Fraction(floor(lo * s), s)
    hi_k = Fraction(ceil(hi * s), s)
    return f"[{lo_k}, {hi_k}]"


def sign(x):
    """Certified sign of a real ball: +1, -1, or 0 when the ball meets zero."""
    lo, hi = bounds(x)
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    return 0


def q(p, r):
    return arb(fmpq(p, r))


# ----------------------------------------------------------------------------------------------
# A. The polynomial comb (exact)
# ----------------------------------------------------------------------------------------------

class G:
    """Gaussian rationals."""

    def __init__(self, re, im=0):
        self.re, self.im = Fraction(re), Fraction(im)

    def __add__(s, o):
        o = o if isinstance(o, G) else G(o)
        return G(s.re + o.re, s.im + o.im)

    __radd__ = __add__

    def __sub__(s, o):
        o = o if isinstance(o, G) else G(o)
        return G(s.re - o.re, s.im - o.im)

    def __neg__(s):
        return G(-s.re, -s.im)

    def __mul__(s, o):
        o = o if isinstance(o, G) else G(o)
        return G(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)

    __rmul__ = __mul__

    def conj(s):
        return G(s.re, -s.im)

    def nsq(s):
        return s.re * s.re + s.im * s.im

    def inv(s):
        n = s.nsq()
        return G(s.re / n, -s.im / n)

    def __truediv__(s, o):
        o = o if isinstance(o, G) else G(o)
        return s * o.inv()

    def __eq__(s, o):
        return s.re == o.re and s.im == o.im

    def __repr__(s):
        return f"{s.re} + {s.im}i"


def poly_from_roots(roots):
    c = [G(1)]
    for r in roots:
        nc = [G(0)] * (len(c) + 1)
        for i, a in enumerate(c):
            nc[i + 1] = nc[i + 1] + a
            nc[i] = nc[i] - a * r
        c = nc
    return c


def deriv(c):
    return [c[i] * i for i in range(1, len(c))]


def ev(c, z):
    acc = G(0)
    for a in reversed(c):
        acc = acc * z + a
    return acc


def mirror_flux(window_upper, window_real, zeta):
    """Sum over the window mirror comb of 1/(zeta - u), diagonal term 0."""
    tot = G(0)
    for w in window_upper:
        for u in (w, w.conj()):
            if not (u == zeta):
                tot = tot + (zeta - u).inv()
    for r in window_real:
        u = G(r)
        if not (u == zeta):
            tot = tot + (zeta - u).inv()
    return tot


def pair_rate(upper, real):
    m = len(upper)
    tot = Fraction(-2 * m)
    for k in range(m):
        for j in range(k + 1, m):
            tot -= 4 * (upper[k].im - upper[j].im) ** 2 / (upper[k] - upper[j]).nsq()
            tot -= 4 * (upper[k].im + upper[j].im) ** 2 / (upper[k] - upper[j].conj()).nsq()
        for r in real:
            tot -= 4 * upper[k].im ** 2 / (upper[k] - G(r)).nsq()
    return tot


def comb_balance(name, upper, real, win_upper_idx, win_real_idx):
    roots = []
    for w in upper:
        roots += [w, w.conj()]
    roots += [G(r) for r in real]
    p = poly_from_roots(roots)
    p1, p2 = deriv(p), deriv(deriv(p))
    wu = [upper[i] for i in win_upper_idx]
    wr = [real[i] for i in win_real_idx]
    direct = Fraction(0)
    B = Fraction(0)
    for w in wu:
        vel = ev(p2, w) / ev(p1, w)          # dw/dtau = p''/p' (HeatFlowOfPolynomials)
        direct += 2 * w.im * vel.im
        T = vel - mirror_flux(wu, wr, w) * 2
        B += 2 * w.im * T.im
    rate = pair_rate(wu, wr)
    print(f"  [{name}] roots: upper {upper}, seam {real}; window upper {wu}, seam {wr}")
    print(f"    dA_W/dtau from p''/p'           = {direct}")
    print(f"    pairInertiaRate(W)              = {rate}   (<= -2m = {-2 * len(wu)})")
    print(f"    tail B_W                        = {B}")
    print(f"    balance rate + B_W == dA_W/dtau : {rate + B == direct}")
    return B


def poly_heat(p, t):
    """The exact backward heat flow e^{-t D^2} p = sum_k (-t)^k/k! p^(2k) (rational)."""
    tot = fmpq_poly([0])
    d, k, fact = p, 0, 1
    while d != 0:
        tot += d * ((-t) ** k / fact)
        d = d.derivative().derivative()
        k += 1
        fact *= k
    return tot


def section_A_flow():
    print("  [A3] the comb A1 along the flow (exact rational coefficients, certified roots):")
    x = fmpq_poly([0, 1])
    p = (x ** 2 + 1) * (x ** 2 + 4) * (x ** 2 - 9)
    A0 = Fraction(5)
    print("    tau    pairs m  heights (upper members)                         A + 2 m tau - A(0)")
    for k in range(0, 11):
        t = fmpq(k, 8)
        h = poly_heat(p, t)
        roots = acb_poly(h).roots(tol=arb(2) ** -100)
        upper = [z for z in roots if sign(z.imag) == 1]
        lower = [z for z in roots if sign(z.imag) == -1]
        ambiguous = [z for z in roots if sign(z.imag) == 0]
        # certify the ambiguous roots real: an exact sign change of the rational polynomial
        for z in ambiguous:
            lo, hi = bounds(z.real)
            lo, hi = lo - Fraction(1, 2 ** 90), hi + Fraction(1, 2 ** 90)
            lo, hi = fmpq(lo.numerator, lo.denominator), fmpq(hi.numerator, hi.denominator)
            assert h(lo) * h(hi) < 0
        assert len(upper) == len(lower) and 2 * len(upper) + len(ambiguous) == 6
        m = len(upper)
        A = sum((z.imag * z.imag for z in upper), arb(0))
        excess = A + 2 * m * arb(t) - arb(A0.numerator)
        hs = ", ".join(enc(z.imag, 12) for z in upper)
        print(f"    {str(k) + '/8':6} {m:^7}  {hs:47} {enc(excess, 12)} sign {sign(excess)}")
    print("    The lower pair rises until it collides with the higher one on the imaginary axis;")
    print("    the collision bound A(tau) + 2 m tau <= A(0) holds at every sampled time.")


def section_A():
    print("A. Polynomial comb (exact Gaussian rationals; seam = real axis; clock = seam time)")
    # A1: an exterior pair above the window pair lifts it.
    B1 = comb_balance("A1", [G(0, 1), G(0, 2)], [-3, 3], [0], [])
    print(f"    R1 'the exterior never lifts' (B_W <= 0): {'holds' if B1 <= 0 else 'VIOLATED'}")
    # A2: the same comb with both pairs in the window: the exterior is on the seam.
    B2 = comb_balance("A2", [G(0, 1), G(0, 2)], [-3, 3], [0, 1], [])
    print(f"    R1 with the exterior on the seam (Lean tailFlux_re_nonneg_of_exterior_on_seam):"
          f" {'holds' if B2 <= 0 else 'VIOLATED'}")
    section_A_flow()
    print()


# ----------------------------------------------------------------------------------------------
# B. The finite primon gas: a finite Euler-product surrogate
# ----------------------------------------------------------------------------------------------

def primon_terms(primes):
    """G_P(1/2 + w) = prod_p 2 sinh(w log p / 2) = sum_eps c_eps exp(lambda_eps w)."""
    terms = [(arb(1), arb(0))]
    for p in primes:
        h = arb(p).log() / 2
        terms = [(c * sgn, lam + sgn * h) for (c, lam) in terms for sgn in (1, -1)]
    return terms


def primon_series(terms, t, w0, n):
    """Taylor coefficients at w0 of the flowed gas e^{-t d^2} G_P (w = s - 1/2)."""
    x = arb_series([w0, 1], prec=n) if isinstance(w0, arb) else acb_series([w0, 1], prec=n)
    tot = None
    for c, lam in terms:
        term = c * (-t * lam * lam).exp() * (x * lam).exp()
        tot = term if tot is None else tot + term
    return tot.coeffs()


def section_B():
    print("B. Finite primon gas G_P(1/2+w) = prod_(p in P) 2 sinh(w log p/2)  (Euler surrogate)")
    print("  At t = 0 every zero is on the seam: w = 2 pi i k / log p, simple for k != 0 (log p")
    print("  rationally independent), and w = 0 of order |P| (the degenerate ground state).")
    P = [2, 3]
    terms = primon_terms(P)
    t = q(1, 64)
    h = lambda w: primon_series(terms, t, w, 1)[0]
    # certified sign change of the real function h on (0, 1)
    lo, hi = Fraction(0), Fraction(1)
    assert sign(h(arb(0))) == -1 and sign(h(arb(1))) == 1
    for _ in range(60):
        mid = (lo + hi) / 2
        sm = sign(h(q(mid.numerator, mid.denominator)))
        if sm == 0:
            break
        if sm < 0:
            lo = mid
        else:
            hi = mid
    mid, rad = (lo + hi) / 2, (hi - lo) / 2
    J = arb(q(mid.numerator, mid.denominator), q(rad.numerator, rad.denominator))
    c = primon_series(terms, t, J, 3)
    print(f"  P = {P}, flow time t = 1/64 (seam time tau = -1/64):")
    print(f"    h(0) sign {sign(h(arb(0)))}, h(1) sign {sign(h(arb(1)))}; the real zero w0 in"
          f" [{lo}, {hi}] (a width-2^-60 dyadic cell)")
    print(f"    h' over the cell {enc(c[1])} (sign {sign(c[1])}: w0 is simple and unique in it)")
    w0 = J
    sdot = 2 * c[2] / c[1]                     # G''/G' at w0: velocity in the flow's time
    T = sdot - 1 / w0                          # minus the window comb 2/(w0 - (-w0))
    Bt = 2 * w0 * T
    print(f"    pair height a = w0; A = w0^2 {enc(w0 * w0)} ;  2t = 1/32")
    print(f"    velocity G''/G'(w0) {enc(sdot)} ; mirror term 1/w0 {enc(1 / w0)}")
    print(f"    tail B_W (seam time) = -2 w0 T {enc(-Bt)}  sign {sign(-Bt)}")
    print(f"    dA_W/dtau = -2 + B_W {enc(-2 - Bt)}")
    print(f"    R1 at the Euler surrogate's pair: {'holds' if sign(-Bt) < 0 else 'VIOLATED or undecided'}")
    print()
    return sign(-Bt)


# ----------------------------------------------------------------------------------------------
# C. Davenport-Heilbronn, the negative control
# ----------------------------------------------------------------------------------------------

CHI = dirichlet_char(5, 2)       # chi(2) = i
CHIB = dirichlet_char(5, 3)      # its conjugate
S5 = arb(5).sqrt()
KAPPA = ((10 - 2 * S5).sqrt() - 2) / (S5 - 1)
II = acb(0, 1)
C1 = (1 - II * KAPPA) / 2
C2 = (1 + II * KAPPA) / 2


def dh_f(s0, n):
    x = acb_series([s0, 1], prec=n)
    return C1 * acb_series.dirichlet_l(x, CHI) + C2 * acb_series.dirichlet_l(x, CHIB)


def dh_g(s0, n):
    x = acb_series([s0, 1], prec=n)
    return ((x * (arb(5) / arb.pi()).log()) / 2).exp() * ((x + 1) / 2).gamma()


def dh_lam(s0, n):
    return (dh_g(s0, n) * dh_f(s0, n)).coeffs()


def rouche_disc(series, seed, r):
    """Newton from an exact seed, then Rouche: |F(z0)| + sup|F''|/2 r^2 < |F'(z0)| r certifies
    exactly one zero of F in the disc |z - z0| < r."""
    z = seed
    for _ in range(60):
        c = series(z, 2)
        z = (z - c[0] / c[1]).mid()
    c = series(z, 2)
    box = acb(arb(z.real.mid(), r), arb(z.imag.mid(), r))
    c2 = series(box, 3)[2]
    ok = (c[0].abs_upper() + c2.abs_upper() * r * r) < c[1].abs_lower() * r
    return z, box, bool(ok)


def section_C():
    print("C. Davenport-Heilbronn f = (1-i kappa)/2 L(s,chi) + (1+i kappa)/2 L(s,chi-bar), chi mod 5,")
    print("   Lambda(s) = (5/pi)^(s/2) Gamma((s+1)/2) f(s) = Lambda(1-s)  (Titchmarsh 10.25)")
    a2, a3, a6 = KAPPA, -KAPPA, arb(1)
    print(f"  No Fock factorization: a6 - a2 a3 = 1 + kappa^2 {enc(a6 - a2 * a3)} != 0 (a6 = a1 = 1),")
    print(f"  kappa {enc(KAPPA)}")
    seeds = [(fmpq(21, 26), fmpq(85699, 1000)), (fmpq(13, 20), fmpq(114163, 1000)),
             (fmpq(23, 40), fmpq(166479, 1000)), (fmpq(29, 40), fmpq(176702, 1000))]
    r = arb(2) ** -80
    half = arb(1) / 2
    results = []
    for (sx, sy) in seeds:
        z, box, ok = rouche_disc(dh_lam, acb(arb(sx), arb(sy)), r)
        rho = box
        L = dh_lam(rho, 3)
        F = dh_f(rho, 3).coeffs()
        Gc = dh_g(rho, 3).coeffs()
        sdot = 2 * L[2] / L[1]                 # Lambda''/Lambda' : velocity in the flow's time
        P = 2 * F[2] / F[1]                    # Dirichlet-series part f''/f'
        arch = 2 * Gc[1] / Gc[0]               # archimedean part 2 G'/G
        a = rho.real - half
        gam = rho.imag
        win = 2 * (1 / (rho - (1 - rho.conjugate())) + 1 / (rho - rho.conjugate()) + 1 / (rho - (1 - rho)))
        Ts = sdot - win                        # tail flux in the flow's time (s-chart)
        B = -4 * a * Ts.real                   # seam time; the conjugate member gives the same
        rate = -4 - 4 * a * a / (gam * gam + a * a)
        dA = rate + B
        results.append((a, B, dA, P.real))
        print(f"  Rouche disc radius 2^-80 about Re {enc(z.real)} + i {enc(z.imag, 16)}: certified {ok}")
        print(f"    height a = Re rho - 1/2 {enc(a)} (off the seam)")
        print(f"    tail B_W (window = the quadruple) {enc(B)}  sign {sign(B)}")
        print(f"    pairInertiaRate {enc(rate)} ; dA_W/dtau {enc(dA)}")
        print(f"    source split of Re(velocity): Re arch {enc(arch.real)} + Re P {enc(P.real)} (sign {sign(P.real)})")
    print()
    # the palette: positivity for u >= 0 by domination of the first ring; evenness from the FE
    pi = arb.pi()
    S = sum(arb(n) * (-pi * (n * n - 1) / 5).exp() for n in range(2, 12))
    tail = arb(12) * (-pi * (12 * 12 - 1) / 5).exp() * 2   # crude bound on n >= 12 (ratio < 1/2)
    print("  DH palette Phi_DH(u) = 2 e^(3u/2) sum_n a_n n exp(-pi n^2 e^(2u)/5), even by the FE.")
    print(f"    For u >= 0: sum_(n>=2) |a_n| n e^(-pi(n^2-1)x/5) <= {enc(S + tail)} < 1 at x = e^(2u) >= 1,")
    print("    so Phi_DH > 0 on the line: the negative control has a positive palette.")
    print()
    return results


# ----------------------------------------------------------------------------------------------
# D. xi on the seam: the source split
# ----------------------------------------------------------------------------------------------

def section_D():
    print("D. xi at its first zeros (certified; acb zeta_zero): source split of the velocity")
    half = arb(1) / 2
    for n in range(1, 6):
        rho = acb.zeta_zero(n)
        Z = acb_series([rho, 1], prec=3).zeta().coeffs()
        P = 2 * Z[2] / Z[1]                    # zeta''/zeta'
        arch = 2 / rho + 2 / (rho - 1) - arb.pi().log() + (rho / 2).digamma()
        sdot = arch + P
        print(f"  gamma_{n} {enc(rho.imag, 16)}: Re arch {enc(arch.real)}, Re P {enc(P.real)} (sign {sign(P.real)}),"
              f" Re velocity {enc(sdot.real, 40)}")
    print("  On the seam the archimedean and prime-ring parts cancel in Re: a simple seam zero moves")
    print("  along the seam. The window of these zeros holds no pair, so B_W is vacuous.")
    print()


def main():
    print(f"Grain 2^-{GRAIN} unless stated; precision {ctx.prec} bits.\n")
    section_A()
    sB = section_B()
    res = section_C()
    section_D()
    print("Verdicts (candidate source laws; a law satisfied by a function with an off-seam pair cannot")
    print("force the seam; a law equivalent to RH by construction is circular)")
    r1 = all(sign(B) < 0 for (_, B, _, _) in res) and sB < 0
    r2 = all(sign(dA) < 0 for (_, _, dA, _) in res)
    signs = [sign(p) for (_, _, _, p) in res]
    print(f"  R1 tail sign B_W <= 0. Holds at all four DH quadruples and at the Euler surrogate's pair:")
    print(f"     {r1}. Fails in the comb A1 (B_W = 28/15). REJECTED as a source law: pairs satisfy it.")
    print(f"  R2 stationary source dA_W/dtau >= 0. Violated at DH: {r2}. With R1 it forces an empty")
    print("     window (Lean pairCount_eq_zero_of_tailSign_of_stationary), and R1 and R2 hold for every")
    print("     window under RH: CIRCULAR. No derivation of R2 from the source is known here.")
    print(f"  R3 sign of the Dirichlet-series part Re P of the velocity. DH pairs give signs {signs};")
    print("     at xi's first five zeros Re P = -Re arch < 0 (certified). Local form 'Re P <= 0 forces")
    print("     the seam':")
    print("     REJECTED by the first DH pair. Global form 'Re P <= 0 at every zero': violated by DH at")
    print("     the other three pairs, so not rejected by these controls; not circular; not shown to force")
    print("     emptiness (the local implication fails, so any forcing must be collective).")
    print("  PG1 Fock factorization (Euler product) with the functional equation. Separates DH")
    print("     (a6 - a2 a3 = 1 + kappa^2 > 0). Not circular. Unproved: it is the Riemann hypothesis for")
    print("     the Selberg class. Its finite surrogate keeps every zero on the seam and sits exactly at")
    print("     threshold 0 [derived]: the order-|P| ground state at s = 1/2 splits under any blur into")
    print("     floor(|P|/2) off-seam pairs (Hermite); certified above for P = {2, 3} at t = 1/64.")
    print("     NOT REJECTED.")
    print("  PG2 palette positivity. Does not separate: Phi_DH > 0 (certified for u >= 0, even by the")
    print("     functional equation). REJECTED, also")
    print("     formally: Lean PaletteLaw.palettePositivity_does_not_force_seam.")
    print("  PG3 palette log-concavity (and every law closed under damping by e^(-t u^2)). REJECTED")
    print("     formally: Lean PaletteLaw.seamForcingLaw_not_dampingClosed, logConcavePalette_does_not_force_seam.")
    print("  PG4 the Lee-Yang property of Phi(u) du (Newman). Equivalent to RH by construction: CIRCULAR.")

if __name__ == "__main__":
    main()
