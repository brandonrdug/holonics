#!/usr/bin/env python3
"""Host rulers for the record of Einstein's field program on the complex (November 11).

Integers and rationals only (Python `fractions`); no state, no private material, no float.
Each ruler checks an identity the record uses and prints what it read. A ruler is an
instrument: nothing here is machinery, and nothing here trains or reads the field.

  python3 einstein_rulers.py > einstein_rulers.txt
"""
from fractions import Fraction as Fr
from itertools import product, combinations
from math import comb, gcd
import sys, time

T0 = time.time()
FAILS = []


def check(name, ok):
    print(f"  [{'ok' if ok else 'FAILED'}] {name}")
    if not ok:
        FAILS.append(name)


def rank(rows):
    """Rank of a rational matrix by elimination."""
    m = [[Fr(x) for x in r] for r in rows]
    r = 0
    cols = len(m[0]) if m else 0
    for c in range(cols):
        p = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


def solve_stationary(P):
    """Stationary law of a rational row-stochastic matrix, by elimination."""
    n = len(P)
    a = [[(P[j][i] - (1 if i == j else 0)) for j in range(n)] + [Fr(0)] for i in range(n)]
    a[-1] = [Fr(1)] * n + [Fr(1)]
    for c in range(n):
        p = next(i for i in range(c, n) if a[i][c] != 0)
        a[c], a[p] = a[p], a[c]
        a[c] = [x / a[c][c] for x in a[c]]
        for i in range(n):
            if i != c and a[i][c] != 0:
                f = a[i][c]
                a[i] = [x - f * y for x, y in zip(a[i], a[c])]
    return [a[i][n] for i in range(n)]


# ---------------------------------------------------------------------------------------
print("1. Strength: the free Taylor data of a system of field equations, order by order")
print("   (Einstein's definition, Appendix II of The Meaning of Relativity, 5th ed.: the fewer")
print("   free data, the stronger the system). In four variables a function has C(n+3, 3)")
print("   coefficients of order n. A term (m, s) below counts m functions whose order is")
print("   shifted by s: an equation of order k binds data at shift -k, a gauge function whose")
print("   derivative of order n+1 moves the field counts at shift +1, an identity of order k")
print("   among the equations returns data at shift -k.")


def z(system, n):
    return sum(m * (comb(n + 3 + s, 3) if n + 3 + s >= 3 else 0) for m, s in system)


def z1(system):
    # z(n) is a cubic in n; fit it on four points and read the n^2 coefficient.
    xs = [10, 11, 12, 13]
    ys = [Fr(z(system, x)) for x in xs]
    # Newton divided differences
    co = ys[:]
    for j in range(1, 4):
        for i in range(3, j - 1, -1):
            co[i] = (co[i] - co[i - 1]) / (xs[i] - xs[i - j])
    # expand to monomial coefficients
    poly = [Fr(0)] * 4
    basis = [Fr(1)]
    for k in range(4):
        for i, b in enumerate(basis):
            poly[i] += co[k] * b
        nb = [Fr(0)] * (len(basis) + 1)
        for i, b in enumerate(basis):
            nb[i + 1] += b
            nb[i] -= xs[k] * b
        basis = nb
    c0, c1, c2, c3 = poly
    return c3, 6 * c2  # leading share z0 = 6 c3, z1 = 6 c2 (C(n+3,3) ~ n^3/6)


systems = {
    "scalar wave equation (1 field; 1 equation of order 2)": [(1, 0), (-1, -2)],
    "Maxwell, field strengths (6; 8 equations of order 1; 2 identities of order 2)": [(6, 0), (-8, -1), (2, -2)],
    "Maxwell, potentials (4; 1 gauge function; 4 equations of order 2; 1 identity of order 3)": [(4, 0), (-1, 1), (-4, -2), (1, -3)],
    "vacuum gravitation (10; 4 coordinate functions; 10 equations of order 2; 4 identities of order 3)": [(10, 0), (-4, 1), (-10, -2), (4, -3)],
}
for name, s in systems.items():
    c3, zz = z1(s)
    print(f"   {name}")
    print(f"     z(10), z(100), z(1000) = {z(s, 10)}, {z(s, 100)}, {z(s, 1000)};  leading share {6*c3},  z1 = {zz},"
          f"  free functions of three variables z1/3 = {zz/3}")
check("each system is determined at leading order (the n^3 share is zero)", all(z1(s)[0] == 0 for s in systems.values()))
check("Maxwell reads the same strength through field strengths and through potentials",
      z1(systems[list(systems)[1]])[1] == z1(systems[list(systems)[2]])[1] == 12)
check("z1 = 3 x (free functions of three variables): wave 6 = 3*2, Maxwell 12 = 3*4, vacuum gravitation 12 = 3*4",
      [z1(s)[1] for s in systems.values()] == [6, 12, 12, 12])
print("   (The figures are this ruler's, under the convention printed above. Einstein's own table is")
print("    in Appendix II and is not in the gathered folder, so none of his figures is quoted.)")

# ---------------------------------------------------------------------------------------
print("\n2. A grain gives the range: the carry's friction is the mass of what it carries")
print("   Q(t) = b(t) + g Q(t-1), |g| = 1/(1+d): a unit at distance k enters at g^k, the reach is")
print("   sum_k g^k = (1+d)/d, and the two-sided kernel g^|t| solves the screened chain equation")
print("   -g f(t-1) + (1+g^2) f(t) - g f(t+1) = (1-g^2) [t = 0], whose mass is mu^2 = (1-g)^2/g = d^2/(1+d).")
for d in [Fr(1, 16), Fr(1, 4), Fr(1, 2), Fr(1), Fr(2)]:
    g = 1 / (1 + d)
    f = lambda t: g ** abs(t)
    ok = all((-g * f(t - 1) + (1 + g * g) * f(t) - g * f(t + 1)) == ((1 - g * g) if t == 0 else 0) for t in range(-6, 7))
    print(f"   d = {d}: |g| = {g}, reach (1+d)/d = {(1+d)/d}, mu^2 = {(1-g)**2/g} = d^2/(1+d) = {d*d/(1+d)},"
          f" a letter 2, 3, 4 sites back enters at {g}, {g**2}, {g**3}; kernel identity {'holds' if ok else 'FAILS'}")
    check(f"screened chain identity at d = {d}", ok and (1 - g) ** 2 / g == d * d / (1 + d) and 1 / (1 - g) == (1 + d) / d)
print("   d = 0: |g| = 1, the reach over N sites is N (no limit): a carry founded without friction sums its whole region.")
# the turn carries no range: |gamma(q, d)|^2 = 1/(1+d)^2 for every q
for q in [Fr(0), Fr(1, 3), Fr(-7, 5), Fr(9)]:
    re, im, den = 4 - q * q, 4 * q, 4 + q * q
    for d in [Fr(0), Fr(1, 4)]:
        mag2 = (re * re + im * im) / (den * den) / (1 + d) ** 2
        check(f"|gamma(q={q}, d={d})|^2 = 1/(1+d)^2 = {1/(1+d)**2}", mag2 == 1 / (1 + d) ** 2)

# ---------------------------------------------------------------------------------------
print("\n3. Four pair readings on a cycle of contexts: where one joint table exists and where it cannot")
print("   Settings a, a' on one side and b, b' on the other; the contexts (a,b), (a,b'), (a',b), (a',b')")
print("   form the 4-cycle a - b - a' - b' - a. S = E(a,b) + E(a,b') + E(a',b) - E(a',b').")
best = max(abs(a * b + a * b2 + a2 * b - a2 * b2) for a, a2, b, b2 in product([-1, 1], repeat=4))
check(f"every one of the 16 assignments of a value to each setting reads |S| <= 2 (max {best})", best == 2)
va, va2, vb, vb2 = (Fr(1), Fr(0)), (Fr(0), Fr(1)), (Fr(4, 5), Fr(3, 5)), (Fr(4, 5), Fr(-3, 5))
dot = lambda u, v: u[0] * v[0] + u[1] * v[1]
E = {("a", "b"): dot(va, vb), ("a", "b'"): dot(va, vb2), ("a'", "b"): dot(va2, vb), ("a'", "b'"): dot(va2, vb2)}
S = E[("a", "b")] + E[("a", "b'")] + E[("a'", "b")] - E[("a'", "b'")]
print(f"   faces as rational unit vectors a=(1,0), a'=(0,1), b=(4/5,3/5), b'=(4/5,-3/5): E = {dict((k, str(v)) for k, v in E.items())}")
check(f"their Gram readings give S = {S} > 2, with S^2 = {S*S} <= 8", S == Fr(14, 5) and S * S <= 8)
tab = lambda e: {(x, y): (1 + x * y * e) / 4 for x in (-1, 1) for y in (-1, 1)}
pab, pab2, pa2b = tab(E[("a", "b")]), tab(E[("a", "b'")]), tab(E[("a'", "b")])
# glue along the path b' - a - b - a' (a tree of three contexts)
q = {}
for b2, a, b, a2 in product((-1, 1), repeat=4):
    q[(b2, a, b, a2)] = pab2[(a, b2)] * pab[(a, b)] * pa2b[(a2, b)] / (Fr(1, 2) * Fr(1, 2))
check("the three contexts on the path b' - a - b - a' glue to one joint table (nonnegative, total 1)",
      sum(q.values()) == 1 and min(q.values()) >= 0)
marg = lambda i, j: {(x, y): sum(v for k, v in q.items() if k[i] == x and k[j] == y) for x in (-1, 1) for y in (-1, 1)}
check("that table returns the three path contexts",
      marg(1, 0) == pab2 and marg(1, 2) == pab and marg(3, 2) == pa2b)
closing = sum(k[3] * k[0] * v for k, v in q.items())
print(f"   the glued table reads the closing context (a',b') at E = {closing}; the faces read {E[(chr(97)+chr(39), chr(98)+chr(39))]};"
      f" the defect on the closing edge is {E[(chr(97)+chr(39), chr(98)+chr(39))] - closing}")
check("the closing edge of the cycle carries the whole defect (48/125 against -3/5)", closing == Fr(48, 125))
# settings at sixths of a turn: every reading rational, the faces on one ring of six
c6 = [Fr(1), Fr(1, 2), Fr(-1, 2), Fr(-1), Fr(-1, 2), Fr(1, 2)]  # cos(k/6 of a turn)
best6 = max((c6[(b - a) % 6] + c6[(b2 - a) % 6] + c6[(b - a2) % 6] - c6[(b2 - a2) % 6], (a, a2, b, b2))
            for a, a2, b, b2 in product(range(6), repeat=4))
print(f"   settings on a ring of six (sixths of a turn): the largest S is {best6[0]} at places (a, a', b, b') = {best6[1]}")
check("four settings at sixths of a turn read S = 5/2 > 2 with every reading in {1, 1/2, -1/2, -1}", best6[0] == Fr(5, 2))
# the Gram bound over a grid of rational unit vectors
unit = lambda t: ((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))
ts = [Fr(n, 6) for n in range(-12, 13)]
mx = Fr(0)
for t1, t2, t3, t4 in product(ts[::3], ts[::3], ts, ts):
    A, A2, B, B2 = unit(t1), unit(t2), unit(t3), unit(t4)
    s = dot(A, B) + dot(A, B2) + dot(A2, B) - dot(A2, B2)
    mx = max(mx, s * s)
check(f"over {len(ts[::3])**2 * len(ts)**2} quadruples of rational unit vectors S^2 <= 8 (largest read {mx})", mx <= 8)

# ---------------------------------------------------------------------------------------
print("\n4. The two-way flow: its symmetric part, its antisymmetric part, and reversal as transposition")
P = [[Fr(1, 10), Fr(6, 10), Fr(1, 10), Fr(2, 10)],
     [Fr(1, 10), Fr(2, 10), Fr(6, 10), Fr(1, 10)],
     [Fr(5, 10), Fr(1, 10), Fr(2, 10), Fr(2, 10)],
     [Fr(3, 10), Fr(3, 10), Fr(3, 10), Fr(1, 10)]]
pi = solve_stationary(P)
n = len(P)
F = [[pi[i] * P[i][j] for j in range(n)] for i in range(n)]
Sm = [[(F[i][j] + F[j][i]) / 2 for j in range(n)] for i in range(n)]
J = [[(F[i][j] - F[j][i]) / 2 for j in range(n)] for i in range(n)]
print(f"   stationary law {[str(x) for x in pi]}")
check("the stationary law is stationary", all(sum(pi[i] * P[i][j] for i in range(n)) == pi[j] for j in range(n)))
check("the antisymmetric part is divergence-free at every cell (sum_j J_ij = 0)", all(sum(J[i]) == 0 for i in range(n)))
Pr = [[pi[j] * P[j][i] / pi[i] for j in range(n)] for i in range(n)]
Fr_ = [[pi[i] * Pr[i][j] for j in range(n)] for i in range(n)]
check("the reversed passage's flow is the transpose: S stays, J changes sign",
      all(Fr_[i][j] == F[j][i] for i in range(n) for j in range(n)))
beta = {(i, j): J[i][j] / Sm[i][j] for i in range(n) for j in range(n) if i < j}
check("beta = J/S lies strictly inside (-1, 1) on every contact, and (1+beta)/(1-beta) = F_ij/F_ji",
      all(-1 < b < 1 and (1 + b) / (1 - b) == F[i][j] / F[j][i] for (i, j), b in beta.items()))
print(f"   beta on the contacts: {dict((k, str(v)) for k, v in beta.items())}")
tri = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]
cyc = {t: (F[t[0]][t[1]] * F[t[1]][t[2]] * F[t[2]][t[0]]) / (F[t[1]][t[0]] * F[t[2]][t[1]] * F[t[0]][t[2]]) for t in tri}
cycP = {t: (P[t[0]][t[1]] * P[t[1]][t[2]] * P[t[2]][t[0]]) / (P[t[1]][t[0]] * P[t[2]][t[1]] * P[t[0]][t[2]]) for t in tri}
check("a cycle's ratio product is free of the stationary law (the potential cancels around a cycle)", cyc == cycP)
print(f"   cycle ratio products on the four triangles: {dict((k, str(v)) for k, v in cyc.items())}")
check("this flow has circulation: some cycle product differs from 1, so no potential (no reversible law) exists",
      any(v != 1 for v in cyc.values()))
# a flow with a potential: F symmetric
w = [Fr(1), Fr(2), Fr(3), Fr(5)]
K = [[Fr(0), Fr(1), Fr(2), Fr(1)], [Fr(1), Fr(0), Fr(1), Fr(3)], [Fr(2), Fr(1), Fr(0), Fr(1)], [Fr(1), Fr(3), Fr(1), Fr(0)]]
Fs = [[K[i][j] for j in range(n)] for i in range(n)]  # symmetric flows
rate = [[Fs[i][j] / w[i] for j in range(n)] for i in range(n)]
cyc2 = [(rate[a][b] * rate[b][c] * rate[c][a]) / (rate[b][a] * rate[c][b] * rate[a][c]) for a, b, c in tri]
check("a symmetric flow (J = 0) closes every cycle: its rates are a potential's differences", all(v == 1 for v in cyc2))

# ---------------------------------------------------------------------------------------
print("\n5. A field of two points: far comparison that composes is a coboundary")
mul = lambda A, B: ((A[0][0]*B[0][0]+A[0][1]*B[1][0], A[0][0]*B[0][1]+A[0][1]*B[1][1]),
                    (A[1][0]*B[0][0]+A[1][1]*B[1][0], A[1][0]*B[0][1]+A[1][1]*B[1][1]))
inv = lambda A: ((A[1][1], -A[0][1]), (-A[1][0], A[0][0]))  # det 1
I2 = ((1, 0), (0, 1))
h = [((1, 0), (0, 1)), ((1, 2), (0, 1)), ((2, 1), (1, 1)), ((3, 2), (4, 3)), ((1, 0), (5, 1))]
pts = range(len(h))
g = {(a, b): mul(inv(h[a]), h[b]) for a in pts for b in pts}
check("identity at coincidence, and there-and-back restores", all(g[(a, a)] == I2 for a in pts)
      and all(mul(g[(a, b)], g[(b, a)]) == I2 for a in pts for b in pts))
check("g(a,b) = h(a)^-1 h(b) closes every triangle",
      all(mul(mul(g[(a, b)], g[(b, c)]), g[(c, a)]) == I2 for a, b, c in product(pts, repeat=3)))
g2 = dict(g)
shear = ((1, 1), (0, 1))
g2[(1, 3)] = mul(g[(1, 3)], shear)
g2[(3, 1)] = inv(g2[(1, 3)])
open_tri = [t for t in combinations(pts, 3) if mul(mul(g2[(t[0], t[1])], g2[(t[1], t[2])]), g2[(t[2], t[0])]) != I2]
check("one contact slipped by a shear keeps there-and-back and opens exactly the triangles through it",
      all(mul(g2[(a, b)], g2[(b, a)]) == I2 for a in pts for b in pts)
      and sorted(open_tri) == sorted(t for t in combinations(pts, 3) if 1 in t and 3 in t))
print(f"   triangles opened by the slipped contact (1,3): {open_tri}")
hh = [g[(0, a)] for a in pts]
check("when every triangle closes the frames are recovered from one base point: g(a,b) = g(o,a)^-1 g(o,b)",
      all(mul(inv(hh[a]), hh[b]) == g[(a, b)] for a in pts for b in pts))

# ---------------------------------------------------------------------------------------
print("\n6. A source-free field carries a charge only around a hole")


def grid_complex(k, removed=()):
    V = [(i, j) for i in range(k + 1) for j in range(k + 1)]
    vid = {v: n for n, v in enumerate(V)}
    Eh = [((i, j), (i + 1, j)) for i in range(k) for j in range(k + 1)]
    Ev = [((i, j), (i, j + 1)) for i in range(k + 1) for j in range(k)]
    Ed = Eh + Ev
    eid = {e: n for n, e in enumerate(Ed)}
    Fc = [(i, j) for i in range(k) for j in range(k) if (i, j) not in removed]
    d1 = [[0] * len(Ed) for _ in V]
    for e, n in eid.items():
        d1[vid[e[0]]][n] -= 1
        d1[vid[e[1]]][n] += 1
    d2 = [[0] * len(Fc) for _ in Ed]
    for n, (i, j) in enumerate(Fc):
        d2[eid[((i, j), (i + 1, j))]][n] += 1
        d2[eid[((i + 1, j), (i + 1, j + 1))]][n] += 1
        d2[eid[((i, j + 1), (i + 1, j + 1))]][n] -= 1
        d2[eid[((i, j), (i, j + 1))]][n] -= 1
    bb = all(sum(d1[v][e] * d2[e][f] for e in range(len(Ed))) == 0 for v in range(len(V)) for f in range(len(Fc)))
    b1 = len(Ed) - rank(d1) - (rank(d2) if Fc else 0)
    return len(V), len(Ed), len(Fc), bb, b1


for name, rem in [("a 3 x 3 sheet of cells, whole", ()), ("the same sheet with its middle cell removed", ((1, 1),)),
                  ("the same sheet with two cells removed", ((0, 0), (2, 2)))]:
    v, e, f, bb, b1 = grid_complex(3, rem)
    print(f"   {name}: {v} points, {e} contacts, {f} cells; boundary of a boundary zero: {bb}; harmonic classes: {b1}")
    check(f"{name}: harmonic classes = holes ({len(rem)})", bb and b1 == len(rem))

# ---------------------------------------------------------------------------------------
print("\n7. The tower of rings holds each ring's whole windings as the next ring's residue")
rings = [2, 3, 4, 9, 16, 27, 32, 81, 128, 243, 256, 729, 1024, 2187, 4096, 6561]
reach = 3771
dy = [r for r in rings if r % 2 == 0]
tr = [r for r in rings if r % 3 == 0]
lcm = dy[-1] * tr[-1] // gcd(dy[-1], tr[-1])
check(f"the two largest rings ({dy[-1]}, {tr[-1]}) close together only at {lcm} > the reach {reach}: every place has its own residue pair",
      lcm > reach and len({(t % dy[-1], t % tr[-1]) for t in range(reach + 1)}) == reach + 1)
ok = True
for chain in (dy, tr):
    for lo, hi in zip(chain, chain[1:]):
        ok &= all((t // lo) % (hi // lo) == (t % hi) // lo for t in range(reach + 1))
check("along each chain (2, 4, 16, ... and 3, 9, 27, ...) the windings of a ring, counted modulo the step, are the next ring's residue over the ring", ok)
print("   so a ring's face keeps the residue and the next ring keeps the winding: the helix is the circle and its carry.")

# ---------------------------------------------------------------------------------------
print("\n8. An undivided complex pair reads four dimensions, three of one sign and one of the other")
print("   A ratio carried undivided is a pair (xi : eta) of Gaussian integers. Its Hermitian forms are")
print("   X = [[t+z, x-iy], [x+iy, t-z]], det X = t^2 - x^2 - y^2 - z^2, and a move A of determinant one")
print("   acts by X -> A X A^*, keeping det X.")


class G:  # a Gaussian rational
    def __init__(s, re, im=0):
        s.re, s.im = Fr(re), Fr(im)
    def __add__(s, o): return G(s.re + o.re, s.im + o.im)
    def __sub__(s, o): return G(s.re - o.re, s.im - o.im)
    def __mul__(s, o): return G(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)
    def conj(s): return G(s.re, -s.im)
    def __eq__(s, o): return s.re == o.re and s.im == o.im


def mm(A, B):
    return [[A[i][0] * B[0][j] + A[i][1] * B[1][j] for j in range(2)] for i in range(2)]


dag = lambda A: [[A[j][i].conj() for j in range(2)] for i in range(2)]
detG = lambda A: A[0][0] * A[1][1] - A[0][1] * A[1][0]
herm = lambda t, x, y, zz: [[G(t + zz), G(x, -y)], [G(x, y), G(t - zz)]]
moves = [[[G(1), G(2, 1)], [G(0), G(1)]], [[G(1), G(0)], [G(1, -3), G(1)]], [[G(0), G(-1)], [G(1), G(0)]]]
A = mm(mm(moves[0], moves[1]), mm(moves[2], moves[0]))
check("the composed move has determinant one", detG(A) == G(1))
ok = True
for t, x, y, zz in [(5, 1, 2, 3), (3, 0, 0, 3), (7, -2, 6, 3), (1, 1, 1, 1), (9, 4, 4, 7)]:
    X = herm(t, x, y, zz)
    Y = mm(mm(A, X), dag(A))
    d0, d1 = detG(X), detG(Y)
    ok &= (Y == dag(Y)) and d0 == d1 and d0 == G(t * t - x * x - y * y - zz * zz)
check("X -> A X A^* keeps X Hermitian and keeps det X = t^2 - x^2 - y^2 - z^2 on five forms", ok)
psi = (G(2, 1), G(1, -3))
X = [[psi[i] * psi[j].conj() for j in range(2)] for i in range(2)]
t, zz, x, y = (X[0][0].re + X[1][1].re) / 2, (X[0][0].re - X[1][1].re) / 2, X[1][0].re, X[1][0].im
check(f"one pair (xi : eta) = (2+i : 1-3i) is a null direction: (t, x, y, z) = ({t}, {x}, {y}, {zz}), t^2 = x^2 + y^2 + z^2",
      detG(X) == G(0) and t * t == x * x + y * y + zz * zz)
check("a real pair has y = 0: real ratios read three dimensions (two and one), complex ratios four (three and one)",
      all((G(a) * G(b).conj()).im == 0 for a in range(-3, 4) for b in range(-3, 4)))

print(f"\nrulers failed: {len(FAILS)}; wall time {time.time() - T0:.1f} s")
sys.exit(1 if FAILS else 0)
