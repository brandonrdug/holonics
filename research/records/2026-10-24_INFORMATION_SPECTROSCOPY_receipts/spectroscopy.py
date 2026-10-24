"""Information spectroscopy (exact): a line weighs its load, the clock hides a uniform mass, and a
basin is a boost seen from inside.

Every number is a rational or a Gaussian rational; the roots of unity are carried in the
cyclotomic field Q(zeta_M) as polynomials modulo Phi_M. Nothing is evaluated in floating point.

A. One line, two numbers. A two-site constitution (C, D, K) with Rayleigh damping has the lines
   -3 ± 4i and -5 ± 12i. Under a load (dC, dD, dK) a simple line moves at first order by
   ds = -v^T (s^2 dC + s dD + dK) v / v^T (2sC + D) v; the check is that det P_eps(s + eps ds)
   has no eps^0 and no eps^1 term. On the lossless lines (D = 0, lines ±5i, ±13i) a mass load
   moves the line along the turn only (slower), a stiffness load along the turn only (faster), a
   viscosity load along the boost only (faster decay).
B. The clock gauge. Read on a clock t = lambda tau the constitution is (C, lambda D, lambda^2 K):
   p_lambda(s) = lambda^(2n) p(s/lambda) coefficientwise, every line scales by lambda, line ratios
   and loss invariants gamma^2/|s|^2 are unchanged. A lossless proportional mass load mu C is the
   clock lambda = mu^(-1/2) exactly (mu = 4/9, lambda = 3/2); with the viscosity held it changes
   every loss invariant by 1/mu. At first order a load changes the line ratios by the difference of
   its modal Rayleigh quotients, so the ratios are blind exactly to loads whose quotients agree.
C. The Cayley chart. z = (1 + s)/(1 - s) takes the left half plane into the unit disk and conjugates
   the clock s -> ks to the disk boost phi_a(z) = (z - a)/(1 - az), a = (k - 1)/(k + 1), whose
   longitudinal Doppler (1 + a)/(1 - a) is k; 2a/(1 + a^2) is the velocity (k^2 - 1)/(k^2 + 1).
D. The basin's residence. The all-pass H_a(z) = (1 - conj(a) z)/(z - a) has, on the circle, the
   group delay tau = -Re(z H'/H) = (1 - |a|^2)/|z - a|^2 (the Poisson kernel), and for real a it
   is the Doppler factor sqrt(1 - beta^2)/(1 - beta cos w), beta = 2a/(1 + a^2); k at w = 0, 1/k
   at w = pi, and (k + 1/k)/2 is the Lorentz factor.
E. A receiver with N channels. sum over zeta^N = 1 of (1 - |a|^2)/|zeta - a|^2 equals
   N Re((1 + a^N)/(1 - a^N)), computed in Q(zeta_M), M = lcm(N, 4), for N = 1..12.
F. Shape is what the motion leaves. 1 - |phi(a)|^2 = (1 - |a|^2)(1 - |c|^2)/|1 - conj(c) a|^2 and
   the pseudo-hyperbolic distance |a - b|^2/|1 - conj(a) b|^2 is unchanged by every disk
   automorphism; moving a to the centre puts b at that distance.
G. The basins the magnitude cannot see. H = (z - 2)/(z - 1/3) and H_min = (2z - 1)/(z - 1/3) have
   the same magnitude on the circle; H = H_min B with B = (z - 2)/(2z - 1) unimodular; B's delay is
   the Poisson kernel at 1/2; the windings are -1, 0 and -1. The series of z H_min'/H_min is
   one-sided and that of z B'/B is minus the two-sided Poisson series: both are checked through the
   exact aliasing of their samples on the N-th roots of unity. On N channels the two delay totals
   differ by N (1 + 2^-N)/(1 - 2^-N).
H. The receiver's own mass along a reading. With h = v^T G^-1 v, adding the reading gives
   1/h' = 1/h + 1, and the prediction along v moves by the share h/(1 + h) = m/(M + m) of the
   residual (m = 1 the reading, M = 1/h the receiver); off the range the share is 1.

Writes spectroscopy.json beside this file.
"""

import json
import os
import time
from fractions import Fraction as F
from math import gcd

T0 = time.perf_counter()
OUT = {}


# ---------------------------------------------------------------- Gaussian rationals
class Q:
    __slots__ = ("re", "im")

    def __init__(self, re=0, im=0):
        if isinstance(re, Q):
            self.re, self.im = re.re, re.im
        else:
            self.re, self.im = F(re), F(im)

    def __add__(self, o):
        o = Q(o)
        return Q(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __sub__(self, o):
        o = Q(o)
        return Q(self.re - o.re, self.im - o.im)

    def __rsub__(self, o):
        return Q(o) - self

    def __mul__(self, o):
        o = Q(o)
        return Q(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def __neg__(self):
        return Q(-self.re, -self.im)

    def conj(self):
        return Q(self.re, -self.im)

    def norm(self):
        return self.re * self.re + self.im * self.im

    def __truediv__(self, o):
        o = Q(o)
        n = o.norm()
        assert n != 0
        p = self * o.conj()
        return Q(p.re / n, p.im / n)

    def __rtruediv__(self, o):
        return Q(o) / self

    def __pow__(self, e):
        r = Q(1)
        for _ in range(e):
            r = r * self
        return r

    def __eq__(self, o):
        o = Q(o)
        return self.re == o.re and self.im == o.im

    def __hash__(self):
        return hash((self.re, self.im))

    def s(self):
        if self.im == 0:
            return str(self.re)
        return f"{self.re}{'+' if self.im >= 0 else '-'}{abs(self.im)}i"


I = Q(0, 1)


def on_circle(t):
    """The point ((1 - t^2) + 2ti)/(1 + t^2); t = None gives -1."""
    if t is None:
        return Q(-1)
    t = F(t)
    return Q((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))


# ---------------------------------------------------------------- polynomials in eps over Q
def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else Q(0)) + (b[i] if i < len(b) else Q(0)) for i in range(n)]


def pmul(a, b):
    r = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] = r[i + j] + x * y
    return r


def pscale(a, c):
    return [x * c for x in a]


def det2(m):
    return padd(pmul(m[0][0], m[1][1]), pscale(pmul(m[0][1], m[1][0]), Q(-1)))


def pencil_eps(C, D, K, dC, dD, dK, s_poly):
    """Entries of s(eps)^2 (C + eps dC) + s(eps)(D + eps dD) + K + eps dK as polynomials in eps."""
    s2 = pmul(s_poly, s_poly)
    m = [[None, None], [None, None]]
    for i in range(2):
        for j in range(2):
            c = [Q(C[i][j]), Q(dC[i][j])]
            d = [Q(D[i][j]), Q(dD[i][j])]
            k = [Q(K[i][j]), Q(dK[i][j])]
            m[i][j] = padd(padd(pmul(s2, c), pmul(s_poly, d)), k)
    return m


def quad(M, v, w=None):
    w = v if w is None else w
    return sum((Q(v[i]) * Q(M[i][j]) * Q(w[j]) for i in range(2) for j in range(2)), Q(0))


def mat_lin(*terms):
    """sum of c * M over (c, M), 2 x 2, entries Gaussian rational."""
    r = [[Q(0), Q(0)], [Q(0), Q(0)]]
    for c, M in terms:
        for i in range(2):
            for j in range(2):
                r[i][j] = r[i][j] + Q(c) * Q(M[i][j])
    return r


def first_order_shift(C, D, dC, dD, dK, s, v):
    num = quad(mat_lin((s * s, dC), (s, dD), (1, dK)), v)
    den = quad(mat_lin((2 * s, C), (1, D)), v)
    return -num / den


# ---------------------------------------------------------------- A. one line, two numbers
v1 = (F(3, 5), F(4, 5))
v2 = (F(-4, 5), F(3, 5))
W1, W2 = 25, 169  # omega^2 = 5^2, 13^2


def outer(v, c):
    return [[c * v[i] * v[j] for j in range(2)] for i in range(2)]


Cm = [[F(1), F(0)], [F(0), F(1)]]
Km = [[outer(v1, W1)[i][j] + outer(v2, W2)[i][j] for j in range(2)] for i in range(2)]
ra, rb = F(191, 36), F(1, 36)  # Rayleigh damping D = ra C + rb K: gamma = 3 on mode 1, 5 on mode 2
Dm = [[ra * Cm[i][j] + rb * Km[i][j] for j in range(2)] for i in range(2)]
Z = [[F(0)] * 2 for _ in range(2)]
assert Km == [[F(2929, 25), F(-1728, 25)], [F(-1728, 25), F(1921, 25)]]

lines = [(Q(-3, 4), v1), (Q(-3, -4), v1), (Q(-5, 12), v2), (Q(-5, -12), v2)]
for s, _v in lines:
    d = det2(pencil_eps(Cm, Dm, Km, Z, Z, Z, [s]))
    assert d[0] == 0, s.s()

loads = {
    "mass at site 0": ([[1, 0], [0, 0]], Z, Z),
    "viscosity at site 1": (Z, [[0, 0], [0, F(1, 2)]], Z),
    "stiffness coupling": (Z, Z, [[0, 1], [1, 0]]),
}
loads["all three"] = (loads["mass at site 0"][0], loads["viscosity at site 1"][1], loads["stiffness coupling"][2])
A_out = {}
for name, (dC, dD, dK) in loads.items():
    row = {}
    for s, v in lines:
        ds = first_order_shift(Cm, Dm, dC, dD, dK, s, v)
        d = det2(pencil_eps(Cm, Dm, Km, dC, dD, dK, [s, ds]))
        assert d[0] == 0 and d[1] == 0, (name, s.s())
        row[s.s()] = ds.s()
    A_out[name] = row
# linearity: the combined load's shift is the sum of the three
for s, v in lines:
    tot = sum((first_order_shift(Cm, Dm, *loads[n], s, v) for n in ("mass at site 0", "viscosity at site 1", "stiffness coupling")), Q(0))
    assert tot == first_order_shift(Cm, Dm, *loads["all three"], s, v)

# lossless lines: the kind of each shift
lossless = [(Q(0, 5), v1, 5), (Q(0, 13), v2, 13)]
kinds = {}
for name, (dC, dD, dK) in list(loads.items())[:3]:
    for s, v, w in lossless:
        ds = first_order_shift(Cm, Z, dC, dD, dK, s, v)
        d = det2(pencil_eps(Cm, Z, Km, dC, dD, dK, [s, ds]))
        assert d[0] == 0 and d[1] == 0
        Cv, Dv, Kv = quad(dC, v).re, quad(dD, v).re, quad(dK, v).re
        if name.startswith("mass"):
            assert ds == Q(0, -F(w) * Cv / 2) and Cv > 0  # turn slows by omega dC_v / 2
        elif name.startswith("viscosity"):
            assert ds == Q(-Dv / 2) and Dv > 0  # decay grows by dD_v / 2, no turn
        else:
            assert ds == Q(0, Kv / (2 * w))  # turn moves by dK_v / (2 omega), no decay
        kinds[f"{name} on {s.s()}"] = ds.s()
OUT["A_load_shift"] = {"lines": [s.s() for s, _ in lines], "first_order_shift": A_out, "lossless_kinds": kinds}


# ---------------------------------------------------------------- B. the clock gauge
def charpoly(C, D, K):
    """det(s^2 C + s D + K) as a list of rational coefficients in s (2 x 2)."""
    ent = [[[F(K[i][j]), F(D[i][j]), F(C[i][j])] for j in range(2)] for i in range(2)]

    def pm(a, b):
        r = [F(0)] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                r[i + j] += x * y
        return r

    a = pm(ent[0][0], ent[1][1])
    b = pm(ent[0][1], ent[1][0])
    return [a[i] - b[i] for i in range(5)]


def peval(c, s):
    r = Q(0)
    for x in reversed(c):
        r = r * s + Q(x)
    return r


p = charpoly(Cm, Dm, Km)
lam = F(3, 2)
p_clock = charpoly(Cm, [[lam * x for x in r] for r in Dm], [[lam * lam * x for x in r] for r in Km])
assert all(p_clock[j] == lam ** (4 - j) * p[j] for j in range(5))
for s, _ in lines:
    assert peval(p_clock, s * lam) == 0


def loss(s):
    return s.re * s.re / s.norm()  # gamma^2 / |s|^2, unchanged by every positive clock


s1, s2 = Q(-3, 4), Q(-5, 12)
assert (s1 * lam) / (s2 * lam) == s1 / s2 and loss(s1 * lam) == loss(s1)

# the equivalence: a lossless proportional mass load is a clock
mu = F(4, 9)
p_mass0 = charpoly([[mu * x for x in r] for r in Cm], Z, Km)
p_clock0 = charpoly(Cm, Z, [[lam * lam * x for x in r] for r in Km])
assert lam * lam == 1 / mu
assert all(p_mass0[j] == mu * mu * p_clock0[j] for j in range(5))

# with the viscosity held, the same load is visible in every loss invariant
p_mass = charpoly([[mu * x for x in r] for r in Cm], Dm, Km)


def quadmul(a, b):
    r = [F(0)] * 5
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


assert p_mass == quadmul([F(25), F(6), mu], [F(169), F(10), mu])  # modal: mu s^2 + 2 gamma s + omega^2
loss_mass = {"mode 1": F(9, 25) / mu, "mode 2": F(25, 169) / mu}
assert loss_mass == {"mode 1": F(81, 100), "mode 2": F(225, 676)}
assert loss(s1) == F(9, 25) and loss(s2) == F(25, 169)

# first-order shape: line ratios move by the difference of the modal Rayleigh quotients
ratio_moves = {}
for name, dC in {
    "mass at site 0": [[1, 0], [0, 0]],
    "uniform mass (dC = C)": [[1, 0], [0, 1]],
    "equal quotients, not proportional": [[1 + 2 * v1[0] * v2[0], v1[0] * v2[1] + v2[0] * v1[1]],
                                          [v1[1] * v2[0] + v2[1] * v1[0], 1 + 2 * v1[1] * v2[1]]],
}.items():
    a1 = first_order_shift(Cm, Z, dC, Z, Z, Q(0, 5), v1) / Q(0, 5)
    a2 = first_order_shift(Cm, Z, dC, Z, Z, Q(0, 13), v2) / Q(0, 13)
    q1, q2 = quad(dC, v1).re, quad(dC, v2).re
    assert a1 == Q(-q1 / 2) and a2 == Q(-q2 / 2)
    ratio_moves[name] = {"quotients": [str(q1), str(q2)], "d log(s1/s2)": (a1 - a2).s()}
assert ratio_moves["mass at site 0"]["d log(s1/s2)"] == "7/50"
assert ratio_moves["uniform mass (dC = C)"]["d log(s1/s2)"] == "0"
assert ratio_moves["equal quotients, not proportional"]["d log(s1/s2)"] == "0"
OUT["B_clock_gauge"] = {
    "charpoly": [str(x) for x in p],
    "clock lambda": str(lam),
    "charpoly on the clock": [str(x) for x in p_clock],
    "lossless mass mu = 4/9 equals clock 3/2": True,
    "loss invariants gamma^2/|s|^2": {"mode 1": "9/25", "mode 2": "25/169"},
    "loss invariants after mass 4/9 with viscosity held": {k: str(v) for k, v in loss_mass.items()},
    "first-order ratio moves": ratio_moves,
}


# ---------------------------------------------------------------- C. the Cayley chart
def cay(s):
    return (1 + s) / (1 - s)


def boost(a, z):
    return (z - a) / (1 - a * z)


C_rows = []
for k in [F(2), F(3), F(1, 2), F(5, 3), F(9)]:
    a = (k - 1) / (k + 1)
    assert (1 + a) / (1 - a) == k
    assert 2 * a / (1 + a * a) == (k * k - 1) / (k * k + 1)
    for s in [Q(-1), Q(F(-1, 2), 3), Q(-2, -1), Q(F(-1, 3)), Q(F(-7, 5), F(2, 7))]:
        z = cay(s)
        assert z.norm() < 1
        assert cay(s * k) == boost(a, z)
    C_rows.append({"k": str(k), "a": str(a), "beta": str(2 * a / (1 + a * a))})
OUT["C_cayley_clock_is_disk_boost"] = C_rows


# ---------------------------------------------------------------- D. the basin's residence
def delay(a, z):
    """-Re(z H'/H) for H = (1 - conj(a) z)/(z - a)."""
    zl = -(a.conj() * z) / (1 - a.conj() * z) - z / (z - a)
    return -zl.re


def H_allpass(a, z):
    return (1 - a.conj() * z) / (z - a)


D_rows = []
ts = [F(0), F(1, 3), F(1, 2), F(1), F(2), F(3), F(7), None]
for a in [F(1, 2), F(1, 3), F(-3, 5), F(7, 9), F(0)]:
    aq = Q(a)
    beta = 2 * a / (1 + a * a)
    root = (1 - a * a) / (1 + a * a)  # sqrt(1 - beta^2), positive for |a| < 1
    assert root * root == 1 - beta * beta and root > 0
    k = (1 + a) / (1 - a)
    assert (k + 1 / k) / 2 == 1 / root  # the Lorentz factor
    for t in ts:
        z = on_circle(t)
        assert z.norm() == 1
        assert H_allpass(aq, z).norm() == 1
        tau = delay(aq, z)
        assert tau == (1 - a * a) / (z - aq).norm()
        assert tau == root / (1 - beta * z.re)
    assert delay(aq, Q(1)) == k and delay(aq, Q(-1)) == 1 / k
    D_rows.append({"a": str(a), "k = peak": str(k), "trough": str(1 / k), "beta": str(beta), "lorentz": str(1 / root)})
for a in [Q(F(1, 3), F(1, 3)), Q(F(3, 10), F(-2, 5)), Q(F(-1, 2), F(1, 4)), Q(F(3, 10), F(2, 5))]:
    for t in ts:
        z = on_circle(t)
        assert H_allpass(a, z).norm() == 1
        assert delay(a, z) == (1 - a.norm()) / (z - a).norm()
# a basin of modulus 1/2 at angle (3 + 4i)/5: peak 3 at its line, trough 1/3 opposite
a = Q(F(3, 10), F(2, 5))
assert a.norm() == F(1, 4)
assert delay(a, Q(F(3, 5), F(4, 5))) == 3 and delay(a, Q(F(-3, 5), F(-4, 5))) == F(1, 3)
OUT["D_basin_delay_is_doppler"] = D_rows


# ---------------------------------------------------------------- cyclotomic field Q(zeta_M)
def poly_divmod(a, b):
    a = a[:]
    q = [F(0)] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and any(a):
        if a[-1] == 0:
            a.pop()
            continue
        c = a[-1] / b[-1]
        d = len(a) - len(b)
        q[d] = c
        for i, y in enumerate(b):
            a[i + d] -= c * y
        a.pop()
    while a and a[-1] == 0:
        a.pop()
    return q, a


_PHI = {}


def phi(M):
    if M not in _PHI:
        p = [F(-1)] + [F(0)] * (M - 1) + [F(1)]
        for d in range(1, M):
            if M % d == 0:
                p, r = poly_divmod(p, phi(d))
                assert not r
        while p and p[-1] == 0:
            p.pop()
        _PHI[M] = p
    return _PHI[M]


class Cyc:
    """An element of Q(zeta_M) as a polynomial in x = zeta_M of degree < deg Phi_M."""

    def __init__(self, M, c):
        self.M = M
        _, r = poly_divmod([F(x) for x in c] or [F(0)], phi(M))
        n = len(phi(M)) - 1
        self.c = (r + [F(0)] * n)[:n]

    @staticmethod
    def const(M, q):
        return Cyc(M, [q])

    @staticmethod
    def zeta_pow(M, e):
        e %= M
        return Cyc(M, [F(0)] * e + [F(1)])

    @staticmethod
    def gauss(M, g):
        assert M % 4 == 0
        return Cyc(M, [g.re]) + Cyc.zeta_pow(M, M // 4) * Cyc(M, [g.im])

    def __add__(self, o):
        return Cyc(self.M, [x + y for x, y in zip(self.c, o.c)])

    def __sub__(self, o):
        return Cyc(self.M, [x - y for x, y in zip(self.c, o.c)])

    def __mul__(self, o):
        r = [F(0)] * (2 * len(self.c))
        for i, x in enumerate(self.c):
            if x:
                for j, y in enumerate(o.c):
                    r[i + j] += x * y
        return Cyc(self.M, r)

    def conj(self):
        r = [F(0)] * self.M
        for e, x in enumerate(self.c):
            r[(-e) % self.M] += x
        return Cyc(self.M, r)

    def inv(self):
        # extended Euclid in Q[x] against the irreducible Phi_M
        r0, r1 = phi(self.M)[:], self.c[:]
        while r1 and r1[-1] == 0:
            r1.pop()
        s0, s1 = [F(0)], [F(1)]
        while len(r1) > 1:
            q, r = poly_divmod(r0, r1)
            qs = [F(0)] * (len(q) + len(s1))
            for i, x in enumerate(q):
                for j, y in enumerate(s1):
                    qs[i + j] += x * y
            n = max(len(s0), len(qs))
            s2 = [(s0[i] if i < len(s0) else 0) - (qs[i] if i < len(qs) else 0) for i in range(n)]
            r0, r1, s0, s1 = r1, r, s1, s2
            while r1 and r1[-1] == 0:
                r1.pop()
        assert len(r1) == 1 and r1[0] != 0
        return Cyc(self.M, [x / r1[0] for x in s1])

    def __truediv__(self, o):
        return self * o.inv()

    def rational(self):
        assert all(x == 0 for x in self.c[1:]), "not rational"
        return self.c[0]


def lcm(a, b):
    return a * b // gcd(a, b)


def channel_sum(N, a):
    """sum over the N-th roots of unity of the Poisson kernel at a, in Q(zeta_M)."""
    M = lcm(N, 4)
    A = Cyc.gauss(M, a)
    Ab = A.conj()
    one = Cyc.const(M, 1)
    num = one - A * Ab
    tot = Cyc.const(M, 0)
    for j in range(N):
        zj = Cyc.zeta_pow(M, j * (M // N))
        tot = tot + num / ((zj - A) * (zj.conj() - Ab))
    return tot.rational()


E_rows = []
for a in [Q(F(1, 2)), Q(F(-2, 3)), Q(F(1, 3), F(1, 4)), Q(F(3, 10), F(2, 5))]:
    row = {"a": a.s(), "sums": {}}
    for N in range(1, 13):
        lhs = channel_sum(N, a)
        aN = a ** N
        rhs = N * ((1 + aN) / (1 - aN)).re
        assert lhs == rhs, (a.s(), N)
        row["sums"][N] = str(lhs)
    E_rows.append(row)
OUT["E_N_channel_residence"] = E_rows


# ---------------------------------------------------------------- F. shape is what the motion leaves
def pseudo2(a, b):
    return (a - b).norm() / (1 - a.conj() * b).norm()


def aut(u, c, z):
    return u * (z - c) / (1 - c.conj() * z)


pts = [Q(0), Q(F(1, 2)), Q(F(1, 3), F(-1, 4)), Q(F(-2, 5), F(1, 5)), Q(F(3, 10), F(2, 5))]
u = Q(F(3, 5), F(4, 5))
F_rows = []
for c in [Q(F(1, 2)), Q(F(1, 5), F(2, 5)), Q(0, F(-2, 3))]:
    for x in pts:
        y = aut(u, c, x)
        assert 1 - y.norm() == (1 - x.norm()) * (1 - c.norm()) / (1 - c.conj() * x).norm()
        assert y.norm() < 1
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            a, b = pts[i], pts[j]
            assert pseudo2(aut(u, c, a), aut(u, c, b)) == pseudo2(a, b)
for i in range(len(pts)):
    for j in range(len(pts)):
        if i != j:
            a, b = pts[i], pts[j]
            assert aut(Q(1), a, b).norm() == pseudo2(a, b)
            F_rows.append({"a": a.s(), "b": b.s(), "delta^2": str(pseudo2(a, b))})
assert pseudo2(Q(0), Q(F(1, 2))) == F(1, 4)  # delta = 1/2: the relative Doppler (1 + 1/2)/(1 - 1/2) = 3
OUT["F_shape_invariants"] = F_rows


# ---------------------------------------------------------------- G. the basins the magnitude cannot see
def Hf(z):
    return (z - 2) / (z - Q(F(1, 3)))


def Hmin(z):
    return (2 * z - 1) / (z - Q(F(1, 3)))


def Bf(z):
    return (z - 2) / (2 * z - 1)


def zlog_H(z):
    return z / (z - 2) - z / (z - Q(F(1, 3)))


def zlog_Hmin(z):
    return 2 * z / (2 * z - 1) - z / (z - Q(F(1, 3)))


def zlog_B(z):
    return z / (z - 2) - 2 * z / (2 * z - 1)


for t in ts:
    z = on_circle(t)
    assert Hf(z).norm() == Hmin(z).norm()
    assert Bf(z).norm() == 1 and Hf(z) == Hmin(z) * Bf(z)
    assert zlog_H(z) == zlog_Hmin(z) + zlog_B(z)
    assert -zlog_B(z).re == F(3, 4) / (z - Q(F(1, 2))).norm()  # the Poisson kernel at 1/2
    # on the circle z B'/B is real: it is minus the Poisson kernel, the all-pass carries no gain
    assert zlog_B(z).im == 0 and zlog_B(z) == -(F(3, 4) * z) / ((z - Q(F(1, 2))) * (1 - z * F(1, 2)))
# windings: zeros inside minus poles inside
wind = {"H": 0 - 1, "H_min": 1 - 1, "B": 0 - 1}
assert abs(F(2)) > 1 and abs(F(1, 3)) < 1 and abs(F(1, 2)) < 1
assert wind["H"] == wind["H_min"] + wind["B"]


def aliased(f_zlog, N, m):
    """(1/N) sum_j f(zeta_j) zeta_j^(-m) in Q(zeta_M): the sum of the Laurent coefficients f_(m + lN)."""
    M = lcm(N, 4)
    tot = Cyc.const(M, 0)
    for j in range(N):
        zj = Cyc.zeta_pow(M, j * (M // N))
        tot = tot + f_zlog(zj) * Cyc.zeta_pow(M, -j * m * (M // N))
    return (tot * Cyc.const(M, F(1, N))).rational()


def cz(M, q):
    return Cyc.const(M, F(q))


G_series = {}
for N in [6, 8, 12]:
    M = lcm(N, 4)
    zb = lambda z: z / (z - cz(M, 2)) - cz(M, 2) * z / (cz(M, 2) * z - cz(M, 1))
    zm = lambda z: cz(M, 2) * z / (cz(M, 2) * z - cz(M, 1)) - z / (z - cz(M, F(1, 3)))
    h, t3 = F(1, 2), F(1, 3)
    for m in range(N):
        # z B'/B = - sum over all k of (1/2)^|k| z^k: two-sided, constant term -1 (the winding)
        assert aliased(zb, N, m) == -(h ** m + h ** (N - m)) / (1 - h ** N)
        # z H_min'/H_min = sum_(k >= 1) ((1/2)^k - (1/3)^k) z^-k: one-sided, no constant
        # the sum over l >= 1 of the coefficients at z^-(lN - m)
        assert aliased(zm, N, m) == h ** (N - m) / (1 - h ** N) - t3 ** (N - m) / (1 - t3 ** N)
    # delay totals on N channels
    tot_H = -aliased(lambda z: z / (z - cz(M, 2)) - z / (z - cz(M, F(1, 3))), N, 0) * N
    tot_Hmin = -aliased(zm, N, 0) * N
    tot_B = -aliased(zb, N, 0) * N
    assert tot_H == tot_Hmin + tot_B
    assert tot_B == N * (1 + h ** N) / (1 - h ** N) == channel_sum(N, Q(h))
    G_series[N] = {"delay total H": str(tot_H), "delay total H_min": str(tot_Hmin), "difference (B)": str(tot_B)}
# the magnitude's series: log H_min = log 2 + sum c_k z^-k, c_k = ((1/3)^k - (1/2)^k)/k
c_k = [str((F(1, 3) ** k - F(1, 2) ** k) / k) for k in range(1, 7)]
OUT["G_hidden_basins"] = {"windings": wind, "c_k (k = 1..6)": c_k, "N-channel delay totals": G_series}


# ---------------------------------------------------------------- H. the receiver's own mass
def solve(A, b):
    n = len(A)
    M = [[F(x) for x in A[i]] + [F(b[i])] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]


X = [[1, 2, 0], [0, 1, 1], [1, 0, 3], [2, 1, 1], [1, 1, -1]]
y = [3, -1, 4, 2, 0]
Gm = [[sum(F(x[i] * x[j]) for x in X) for j in range(3)] for i in range(3)]
bv = [sum(F(x[i] * yy) for x, yy in zip(X, y)) for i in range(3)]
w = solve(Gm, bv)
v, yv = [1, -1, 2], F(5)
hv = sum(F(v[i]) * s for i, s in enumerate(solve(Gm, v)))
G2 = [[Gm[i][j] + v[i] * v[j] for j in range(3)] for i in range(3)]
w2 = solve(G2, [bv[i] + v[i] * yv for i in range(3)])
h2 = sum(F(v[i]) * s for i, s in enumerate(solve(G2, v)))
pred = sum(F(v[i]) * w[i] for i in range(3))
pred2 = sum(F(v[i]) * w2[i] for i in range(3))
assert 1 / h2 == 1 / hv + 1
share = hv / (1 + hv)
assert pred2 - pred == share * (yv - pred)
Mrec, mread = 1 / hv, F(1)
assert share == mread / (Mrec + mread)
# off the range: a rank-two Gram and a reading along its kernel; the share is 1
X0 = [[1, 0, 1], [0, 1, 1], [1, 1, 2]]
G0 = [[sum(F(x[i] * x[j]) for x in X0) for j in range(3)] for i in range(3)]
n0 = [1, 1, -1]
assert all(sum(G0[i][j] * n0[j] for j in range(3)) == 0 for i in range(3))
vo, yo = [1, 2, 0], F(7)
# minimum-norm solutions through the range basis e1 = (1,0,1), e2 = (0,1,1) plus, after, the new direction
Gp = [[G0[i][j] + vo[i] * vo[j] for j in range(3)] for i in range(3)]
b0 = [sum(F(x[i]) * yy for x, yy in zip(X0, [1, 2, 3])) for i in range(3)]
wp = solve(Gp, [b0[i] + vo[i] * yo for i in range(3)])
assert sum(F(vo[i]) * wp[i] for i in range(3)) == yo  # the receiver moves all the way: no mass along the open part
OUT["H_reading_mass"] = {"h": str(hv), "h after": str(h2), "1/h after - 1/h": str(1 / h2 - 1 / hv),
                         "share h/(1+h)": str(share), "receiver mass 1/h": str(Mrec),
                         "open-part share": "1"}

OUT["wall_ms"] = round((time.perf_counter() - T0) * 1000)
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "spectroscopy.json"), "w") as fh:
    json.dump(OUT, fh, indent=1, ensure_ascii=False)
print("all checks pass;", OUT["wall_ms"], "ms")
