#!/usr/bin/env python3
"""Host ruler for the record of November 18 (the half is the positivity of the reversal's own form).

A ruler is an instrument: it reads identities and counts on small specimens, on the host, in rational
arithmetic where the claim is an identity and in double floats where it is a spectrum (the floats are
the ruler's, printed as readings). Nothing here
is machinery of the engine. Every claim is an assert; a section that reports that nothing was found
first recovers a planted instance on the same shapes (CLAUDE.md, Method: a ruler's null is held to
a planted law).

Run:  python3 half_ruler.py            (about 40 seconds on one host thread)
Needs: sympy, numpy, scipy.

The predictions were fixed before the reads; they are the constants of PREDICTIONS below and the
asserts beside each read.
"""
import itertools
import math
import random
import sys
from fractions import Fraction
from math import comb

import numpy as np
import sympy as sp
from scipy.linalg import expm

random.seed(20261118)
np.random.seed(20261118)

PREDICTIONS = {
    # section F: the count of Hodge classes of the n-th power of a one-dimensional complex torus
    "hodge_generic_degree_2k": "C(n,k)^2 - C(n,k-1) C(n,k+1)  (a Narayana number), total Catalan(n+1)",
    "hodge_cm_degree_2k": "C(n,k)^2, total C(2n,n)",
    "hodge_generated_by_divisors": "the products of the degree-two classes span every degree, n <= 6",
    # section E
    "neron_severi_rank": "3 without complex multiplication, 4 with it; signature (1, rank-1)",
    # section C
    "toeplitz": "the remainder's Toeplitz form is positive semidefinite iff every nontrivial mode is on the circle",
    # section G
    "laminar": "below the threshold c X(0) < nu the critical reading never rises; a planted start far above it rises",
    "logistic_comb": "at equal weights and a coherent feed the threshold is attained: X(0) > nu blows up at the stated time",
}

u = sp.symbols("u")


def say(*a):
    print(*a)
    sys.stdout.flush()


# ----------------------------------------------------------------------------------------------
# the darts of a finite complex of contacts (multigraph, loops allowed)
# ----------------------------------------------------------------------------------------------
def darts(edges):
    D = [(i, 0) for i in range(len(edges))] + [(i, 1) for i in range(len(edges))]
    s = lambda d: edges[d[0]][0] if d[1] == 0 else edges[d[0]][1]
    t = lambda d: edges[d[0]][1] if d[1] == 0 else edges[d[0]][0]
    sw = lambda d: (d[0], 1 - d[1])
    return D, s, t, sw


def mats(nv, edges, g=None):
    """B (non-backtracking), A, Dg; with dart weights g (g[swap e] = 1/g[e]) the twisted ones."""
    D, s, t, sw = darts(edges)
    N = len(D)
    one = sp.Integer(1)
    w = (lambda d: one) if g is None else (lambda d: g[d])
    B = sp.zeros(N, N)
    for i, e in enumerate(D):
        for j, f in enumerate(D):
            if t(e) == s(f) and f != sw(e):
                B[i, j] = w(f)
    A = sp.zeros(nv, nv)
    Dg = sp.zeros(nv, nv)
    for e in D:
        A[s(e), t(e)] += w(e)
        Dg[s(e), s(e)] += 1
    return B, A, Dg, D, s, t, sw


def random_multigraph():
    nv = random.randint(1, 5)
    m = random.randint(1, 7)
    return nv, [(random.randrange(nv), random.randrange(nv)) for _ in range(m)]


# ----------------------------------------------------------------------------------------------
say("== A. IHARA-BASS, plain and with a connection ==")
# (1-u^2)^|V| det(1 - uB) = det(1 - uA + u^2 (Dg - 1)) (1-u^2)^|E|, polynomial identity in u
for trial in range(12):
    nv, edges = random_multigraph()
    m = len(edges)
    B, A, Dg, D, s, t, sw = mats(nv, edges)
    lhs = sp.expand((sp.eye(2 * m) - u * B).det() * (1 - u**2) ** nv)
    rhs = sp.expand((1 - u**2) ** m * (sp.eye(nv) - u * A + u**2 * (Dg - sp.eye(nv))).det())
    assert sp.expand(lhs - rhs) == 0, (nv, edges)
say("  plain: 12 random multigraphs with loops and repeated contacts, identity holds as polynomials in u")

# planted: the backtracking walk operator (drop the condition f != swap e) must fail the identity
nv, edges = 3, [(0, 1), (1, 2), (2, 0), (0, 1)]
B, A, Dg, D, s, t, sw = mats(nv, edges)
Bbt = sp.zeros(len(D), len(D))
for i, e in enumerate(D):
    for j, f in enumerate(D):
        if t(e) == s(f):
            Bbt[i, j] = 1
m = len(edges)
lhs = sp.expand((sp.eye(2 * m) - u * Bbt).det() * (1 - u**2) ** nv)
rhs = sp.expand((1 - u**2) ** m * (sp.eye(nv) - u * A + u**2 * (Dg - sp.eye(nv))).det())
assert sp.expand(lhs - rhs) != 0
say("  planted: the operator with backtracking allowed fails the identity, as it must")


def random_connection(D, sw, kind):
    g = {}
    for d in D:
        if d in g:
            continue
        if kind == "rational":
            val = sp.Rational(random.randint(1, 5), random.randint(1, 5)) * random.choice([1, -1])
        else:  # a fourth root of unity: a U(1) connection held as its constraint i^2 = -1
            val = sp.I ** random.randint(0, 3)
        g[d] = val
        g[sw(d)] = 1 / val
    return g


for kind in ("rational", "unitary"):
    for trial in range(8):
        nv, edges = random_multigraph()
        m = len(edges)
        D, s, t, sw = darts(edges)
        g = random_connection(D, sw, kind)
        B, A, Dg, D, s, t, sw = mats(nv, edges, g)
        lhs = sp.expand((sp.eye(2 * m) - u * B).det() * (1 - u**2) ** nv)
        rhs = sp.expand((1 - u**2) ** m * (sp.eye(nv) - u * A + u**2 * (Dg - sp.eye(nv))).det())
        assert sp.expand(lhs - rhs) == 0, (kind, nv, edges)
        # gauge change g'_e = h(s e) g_e / h(t e) conjugates B_g by a diagonal matrix
        h = [sp.Rational(random.randint(1, 4), random.randint(1, 4)) for _ in range(nv)]
        g2 = {d: h[s(d)] * g[d] / h[t(d)] for d in D}
        B2 = mats(nv, edges, g2)[0]
        Delta = sp.diag(*[h[t(d)] for d in D])
        assert sp.simplify(Delta * B * Delta.inv() - B2) == sp.zeros(2 * m, 2 * m)
    say(f"  with a connection ({kind} weights, g(reversed) = 1/g): identity holds on 8 multigraphs; "
        "a change of gauge conjugates the dart operator")

# one closed chain of n contacts with holonomy h: det(1 - u B_g) = (1 - h u^n)(1 - u^n / h)
for n in (1, 2, 3, 5):
    edges = [(i, (i + 1) % n) for i in range(n)]
    D, s, t, sw = darts(edges)
    hsym = sp.Rational(3, 2)
    g = {d: sp.Integer(1) for d in D}
    g[(0, 0)] = hsym
    g[(0, 1)] = 1 / hsym
    B = mats(n, edges, g)[0]
    lhs = sp.expand((sp.eye(2 * n) - u * B).det())
    assert sp.expand(lhs - (1 - hsym * u**n) * (1 - u**n / hsym)) == 0
say("  a single closed chain of n contacts with holonomy h: det(1 - u B_g) = (1 - h u^n)(1 - u^n/h), n = 1, 2, 3, 5")


# ----------------------------------------------------------------------------------------------
say("== B. THE REGULAR COMPLEX: lift, area, norm form, index ==")


def petersen():
    E = [(i, (i + 1) % 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)] + [(i, 5 + i) for i in range(5)]
    return 10, E


def complete(n):
    return n, [(i, j) for i in range(n) for j in range(i + 1, n)]


def cube():
    return 8, [(i, i ^ (1 << b)) for i in range(8) for b in range(3) if i < i ^ (1 << b)]


def ladder(n):
    E = [(i, (i + 1) % n) for i in range(n)] + [(n + i, n + (i + 1) % n) for i in range(n)] + [(i, n + i) for i in range(n)]
    return 2 * n, E


def loopy():
    return 2, [(0, 0), (1, 1), (0, 1), (0, 1)]


SPECIMENS = [("petersen", petersen()), ("K4", complete(4)), ("K5", complete(5)), ("cube", cube()),
             ("ladder7", ladder(7)), ("ladder21", ladder(21)), ("loopy", loopy())]

toeplitz_data = {}
for name, (nv, edges) in SPECIMENS:
    B, A, Dg, D, s, t, sw = mats(nv, edges)
    q = Dg[0, 0] - 1
    assert all(Dg[i, i] == q + 1 for i in range(nv))
    N = len(D)
    m = len(edges)
    S = sp.zeros(N, nv)
    T = sp.zeros(N, nv)
    for i, e in enumerate(D):
        S[i, s(e)] = 1
        T[i, t(e)] = 1
    assert B * S == q * T and B * T == T * A - S
    I = sp.eye(nv)
    Z = sp.zeros(nv, nv)
    M = sp.BlockMatrix([[Z, -I], [q * I, A]]).as_explicit()
    Om = sp.BlockMatrix([[Z, I], [-I, Z]]).as_explicit()
    Kf = sp.BlockMatrix([[q * I, A / 2], [A / 2, I]]).as_explicit()
    assert M.T * Om * M == q * Om               # the move scales the area by q
    assert (Om * M + (Om * M).T) / 2 == Kf      # the norm form is the area of x against its image
    assert M.T * Kf * M == q * Kf               # and the move scales it by q, whatever the spectrum
    L = S.row_join(T)
    assert B * L == L * M                       # the lift carries the move to the dart operator
    An = np.array(A.tolist(), dtype=float)
    Bn = np.array(B.tolist(), dtype=float)
    qf = float(q)
    w, V = np.linalg.eigh(An)
    idx = [i for i in range(nv) if abs(abs(w[i]) - (qf + 1)) > 1e-9]
    nontriv = [w[i] for i in idx]
    ram = all(l * l <= 4 * qf + 1e-9 for l in nontriv)
    U = V[:, idx]
    P = np.block([[U, np.zeros_like(U)], [np.zeros_like(U), U]])
    kev = np.linalg.eigvalsh(P.T @ np.array(Kf.tolist(), dtype=float) @ P)
    neg = sum(1 for x in kev if x < -1e-9)
    zero = sum(1 for x in kev if abs(x) <= 1e-9)
    out = sum(1 for l in nontriv if l * l > 4 * qf + 1e-9)
    edge = sum(1 for l in nontriv if abs(l * l - 4 * qf) <= 1e-9)
    assert neg == out and zero == edge, (name, neg, out, zero, edge)   # the index theorem
    # the count of closed walks without backtracking against its smooth part
    bip = sum(1 for x in w if abs(x + (qf + 1)) < 1e-9)
    Bp = np.eye(N)
    worst = 0.0
    c = [2.0 * len(nontriv)]
    for l in range(1, 41):
        Bp = Bp @ Bn
        tr = np.trace(Bp)
        smooth = qf**l + 1 + (m - nv) * (1 + (-1) ** l) + bip * ((-1) ** l) * (qf**l + 1)
        rem = tr - smooth
        c.append(rem / qf ** (l / 2))
        if l <= 24:
            worst = max(worst, abs(rem) / (2 * len(nontriv) * qf ** (l / 2)))
    toeplitz_data[name] = (c, ram)
    assert (worst <= 1 + 1e-6) == ram or not ram, name
    say(f"  {name:9s} q={q} cells={nv} contacts={m} "
        f"{'every nontrivial mode on the circle' if ram else 'modes off the circle'}; "
        f"negative squares of the norm form {neg} = modes with lambda^2 > 4q {out}; "
        f"max |count - smooth| / (2(n-1) q^(l/2)), l <= 24: {worst:.4f}")
say("  the five identities hold on every specimen in rational arithmetic; the index theorem holds on all seven")

# ----------------------------------------------------------------------------------------------
say("== C. THE COUNT'S REMAINDER AS A POSITIVE-DEFINITE SEQUENCE (Toeplitz) ==")
for name, (c, ram) in toeplitz_data.items():
    first_neg = None
    lowest = 0.0
    for size in range(1, 31):
        Tm = np.array([[c[abs(i - j)] for j in range(size)] for i in range(size)])
        lo = np.linalg.eigvalsh(Tm)[0]
        lowest = min(lowest, lo / c[0]) if c[0] else lowest
        if lo < -1e-6 * max(1.0, c[0]) and first_neg is None:
            first_neg = size
    assert (first_neg is None) == ram, (name, first_neg)
    say(f"  {name:9s} lowest eigenvalue over sizes 1..30, over c_0: {lowest:+.2e}; "
        f"{'positive semidefinite at every size' if first_neg is None else 'first negative at size ' + str(first_neg)}")

# ----------------------------------------------------------------------------------------------
say("== D. THE REVERSAL'S OWN FORM (Krein) on symplectic similitudes ==")


def krein(Om, Bm):
    X = Om @ Bm
    return X + X.T


def rot(th):
    return np.array([[math.cos(th), -math.sin(th)], [math.sin(th), math.cos(th)]])


J2 = np.array([[0.0, 1.0], [-1.0, 0.0]])
Om4 = np.block([[J2, np.zeros((2, 2))], [np.zeros((2, 2)), J2]])
for trial in range(20):
    # a random similitude of the area form: sqrt(q) exp(Om^{-1} H), H symmetric
    q = random.uniform(0.5, 4.0)
    H = np.random.randn(4, 4)
    H = (H + H.T) * 0.3
    Ham = np.linalg.inv(Om4) @ H
    Bm = math.sqrt(q) * expm(Ham)
    assert np.allclose(Bm.T @ Om4 @ Bm, q * Om4, atol=1e-8)
    K = krein(Om4, Bm)
    assert np.allclose(K, K.T) and np.allclose(Bm.T @ K @ Bm, q * K, atol=1e-7)
    ev = np.linalg.eigvals(Bm)
    kv = np.linalg.eigvalsh(K)
    if kv[0] > 1e-9 or kv[-1] < -1e-9:
        assert np.allclose(np.abs(ev) ** 2, q, atol=1e-6)   # definite form: every mode on |alpha|^2 = q
say("  20 random similitudes of a 4-dimensional area form: the form is symmetric and scaled by q; "
    "wherever it is definite every mode has |alpha|^2 = q")
# planted: two turns of opposite sense, all modes on the circle, the form indefinite (mixed signature)
Bm = np.block([[rot(0.7), np.zeros((2, 2))], [np.zeros((2, 2)), rot(-1.1)]])
K = krein(Om4, Bm)
kv = np.linalg.eigvalsh(K)
assert kv[0] < -1e-9 and kv[-1] > 1e-9 and np.allclose(np.abs(np.linalg.eigvals(Bm)), 1.0)
# a member of the pencil K_f = krein(Om, f(B)) is definite when the two turns differ ...
found = False
for a1 in np.linspace(-2, 2, 41):
    for a2 in np.linspace(-2, 2, 41):
        kv = np.linalg.eigvalsh(krein(Om4, a1 * Bm + a2 * Bm @ Bm))
        if kv[0] > 1e-6 or kv[-1] < -1e-6:
            found = True
assert found
# ... and none is when they coincide with opposite sense (a Krein collision)
Bc = np.block([[rot(0.7), np.zeros((2, 2))], [np.zeros((2, 2)), rot(-0.7)]])
found = False
for a1 in np.linspace(-2, 2, 21):
    for a2 in np.linspace(-2, 2, 21):
        for a3 in np.linspace(-2, 2, 21):
            kv = np.linalg.eigvalsh(krein(Om4, a1 * Bc + a2 * Bc @ Bc + a3 * Bc @ Bc @ Bc))
            if kv[0] > 1e-6 or kv[-1] < -1e-6:
                found = True
assert not found
say("  turns of opposite sense at different rates: modes on the circle, the first form indefinite, a member of the pencil definite;")
say("  at the same rate (a collision of opposite signatures) no member of the pencil a1 B + a2 B^2 + a3 B^3 is definite (9261 tried)")
# the cell
for (l, q) in [(1.0, 2.0), (2.5, 2.0), (2 * math.sqrt(2.0), 2.0), (3.5, 2.0)]:
    C = np.array([[0.0, -1.0], [q, l]])
    K = np.array([[q, l / 2], [l / 2, 1.0]])
    assert np.allclose(C.T @ J2 @ C, q * J2) and np.allclose(C.T @ K @ C, q * K)
    assert abs(np.linalg.det(K) - (q - l * l / 4)) < 1e-12
say("  the cell [[0,-1],[q,l]]: area and norm form scaled by q for every l; det of the norm form = q - l^2/4 (turn, shear, boost)")

# ----------------------------------------------------------------------------------------------
say("== E. HODGE ON A PRODUCT OF TWO TORI (lattice chart) ==")
# classes c = (c12,c13,c14,c23,c24,c34); period(c) = c13 + c14 tau' + c23 tau + c24 tau tau'
INTER = sp.Matrix([[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0], [0, 0, 0, 1, 0, 0],
                   [0, 0, 1, 0, 0, 0], [0, -1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]])


def neron_severi(tau_sq):
    """tau^2 = a + b tau (a, b rational) for complex multiplication, None for a tau of degree > 2.
    Returns a basis of the integral classes with period zero, for E x E."""
    if tau_sq is None:
        rows = sp.Matrix([[0, 1, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 1, 0]])   # 1, tau, tau^2 free
    else:
        a, b = tau_sq
        rows = sp.Matrix([[0, 1, 0, 0, a, 0], [0, 0, 1, 1, b, 0]])
    return rows.nullspace()


for label, tau_sq, want in [("no complex multiplication (tau of degree 6)", None, 3),
                            ("tau = i", (-1, 0), 4), ("tau = (1+sqrt(-7))/2", (-2, 1), 4)]:
    basis = neron_severi(tau_sq)
    assert len(basis) == want
    G = sp.Matrix(len(basis), len(basis), lambda i, j: (basis[i].T * INTER * basis[j])[0, 0])
    ev = np.linalg.eigvalsh(np.array(G.tolist(), dtype=float))
    sig = (int(sum(ev > 1e-9)), int(sum(ev < -1e-9)))
    assert sig == (1, want - 1), (label, sig)
    say(f"  {label}: rank {want}, the intersection form has signature {sig}")
# det M = |mu|^2 for the lattice maps of tau = i and of tau = (1+sqrt(-7))/2
for trial in range(50):
    p, s_ = random.randint(-9, 9), random.randint(-9, 9)
    # tau = i: M(1) = p + s tau, M(tau) = tau (p + s tau) = -s + p tau
    r, t_ = -s_, p
    assert p * t_ - r * s_ == p * p + s_ * s_
    # tau^2 = tau - 2: M(tau) = p tau + s (tau - 2) = -2 s + (p + s) tau; |p + s tau|^2 = p^2 + p s + 2 s^2
    r, t_ = -2 * s_, p + s_
    assert p * t_ - r * s_ == p * p + p * s_ + 2 * s_ * s_
say("  det of a holomorphic lattice map = the norm of its multiplier (50 draws at two CM points)")

# ----------------------------------------------------------------------------------------------
say("== F. HODGE CLASSES ON THE n-TH POWER: divisors generate, rank over a prime field ==")
PRIME = 1000003


def wedge_masks(m1, m2):
    if m1 & m2:
        return 0, 0
    sign = 1
    a = m1
    while a:
        low = a & -a
        if bin(m2 & (low - 1)).count("1") & 1:   # generators of m2 below this one of m1
            sign = -sign
        a ^= low
    return m1 | m2, sign


def wedge(v1, v2):
    out = {}
    for m1, c1 in v1.items():
        for m2, c2 in v2.items():
            mm, sg = wedge_masks(m1, m2)
            if sg:
                out[mm] = (out.get(mm, 0) + sg * c1 * c2) % PRIME
    return {k: v for k, v in out.items() if v}


def derivation(v, images, nbits):
    """Apply the derivation sending generator b to the vector images[b] (a dict of single-bit masks)."""
    out = {}
    for mask, c in v.items():
        for b in range(nbits):
            if mask >> b & 1:
                below = bin(mask & ((1 << b) - 1)).count("1")
                rest = mask ^ (1 << b)
                for b2, c2 in images.get(b, {}).items():
                    if rest >> b2 & 1:
                        continue
                    below2 = bin(rest & ((1 << b2) - 1)).count("1")
                    sg = -1 if (below + below2) & 1 else 1
                    key = rest | (1 << b2)
                    out[key] = (out.get(key, 0) + sg * c * c2) % PRIME
    return {k: v for k, v in out.items() if v}


def rank_and_basis(vectors, index):
    if not vectors:
        return 0, []
    Mx = np.zeros((len(vectors), len(index)), dtype=np.int64)
    for i, v in enumerate(vectors):
        for mask, c in v.items():
            Mx[i, index[mask]] = c % PRIME
    rank = 0
    rows = Mx.shape[0]
    for col in range(Mx.shape[1]):
        piv = None
        for r in range(rank, rows):
            if Mx[r, col]:
                piv = r
                break
        if piv is None:
            continue
        if piv != rank:
            Mx[[rank, piv]] = Mx[[piv, rank]]
        inv = pow(int(Mx[rank, col]), PRIME - 2, PRIME)
        Mx[rank] = (Mx[rank] * inv) % PRIME
        nz = np.nonzero(Mx[:, col])[0]
        for r in nz:
            if r != rank:
                Mx[r] = (Mx[r] - Mx[r, col] * Mx[rank]) % PRIME
        rank += 1
        if rank == rows:
            break
    masks = sorted(index, key=index.get)
    basis = [{masks[j]: int(Mx[i, j]) for j in np.nonzero(Mx[i])[0]} for i in range(rank)]
    return rank, basis


def hodge_power(n, cm):
    X = lambda i: 1 << i
    Y = lambda i: 1 << (n + i)
    gens = []
    for i in range(n):
        gens.append({X(i) | Y(i): 1})
        for j in range(i + 1, n):
            # x_i ^ y_j + x_j ^ y_i ; as masks with signs: x_i ^ y_j is ordered, x_j ^ y_i is ordered
            gens.append({X(i) | Y(j): 1, X(j) | Y(i): 1})
    if cm:
        for i in range(n):
            for j in range(i + 1, n):
                gens.append({X(i) | X(j): 1, Y(i) | Y(j): 1})   # x_i ^ x_j + y_i ^ y_j
    # the derivations that must kill a class of type (k,k)
    up = {n + i: {i: 1} for i in range(n)}              # y_i -> x_i
    down = {i: {n + i: 1} for i in range(n)}            # x_i -> y_i
    turn = {**{i: {n + i: 1} for i in range(n)}, **{n + i: {i: PRIME - 1} for i in range(n)}}   # x -> y, y -> -x
    killers = [turn] if cm else [up, down]
    for gvec in gens:
        for kill in killers:
            assert derivation(gvec, kill, 2 * n) == {}
    ranks = [1]
    basis = [{0: 1}]
    for k in range(1, n + 1):
        masks = [sum(1 << b for b in comb_) for comb_ in itertools.combinations(range(2 * n), 2 * k)]
        index = {mk: i for i, mk in enumerate(masks)}
        cand = [wedge(gvec, b) for gvec in gens for b in basis]
        cand = [v for v in cand if v]
        rk, basis = rank_and_basis(cand, index)
        for b in basis[: min(len(basis), 5)]:
            for kill in killers:
                assert derivation(b, kill, 2 * n) == {}
        ranks.append(rk)
    return ranks


def narayana_row(n):
    return [comb(n, k) ** 2 - (comb(n, k - 1) * comb(n, k + 1) if k >= 1 else 0) for k in range(n + 1)]


for n in range(1, 7):
    want = narayana_row(n)
    got = hodge_power(n, cm=False)
    assert got == want, (n, got, want)
    assert sum(want) == comb(2 * n + 2, n + 1) // (n + 2)        # Catalan(n+1)
    say(f"  n={n} without complex multiplication: ranks by degree {got} = the count of invariants; total {sum(got)} = Catalan({n + 1})")
for n in range(1, 6):
    want = [comb(n, k) ** 2 for k in range(n + 1)]
    got = hodge_power(n, cm=True)
    assert got == want, (n, got, want)
    say(f"  n={n} at tau = i: ranks by degree {got} = C(n,k)^2; total {sum(got)} = C({2 * n},{n})")
# planted: with one generator removed the span must fall short (the ruler can see a shortfall)
def hodge_power_short(n):
    X = lambda i: 1 << i
    Y = lambda i: 1 << (n + i)
    gens = [{X(i) | Y(i): 1} for i in range(n)]      # only the n fibre classes
    basis = [{0: 1}]
    ranks = [1]
    for k in range(1, n + 1):
        masks = [sum(1 << b for b in comb_) for comb_ in itertools.combinations(range(2 * n), 2 * k)]
        index = {mk: i for i, mk in enumerate(masks)}
        cand = [v for v in (wedge(gvec, b) for gvec in gens for b in basis) if v]
        rk, basis = rank_and_basis(cand, index)
        ranks.append(rk)
    return ranks
short = hodge_power_short(3)
assert short != narayana_row(3) and short == [1, 3, 3, 1]
say(f"  planted: the fibre classes alone span {short} at n=3 against {narayana_row(3)}; the shortfall is seen")

# ----------------------------------------------------------------------------------------------
say("== G. THE LAMINAR CLASS: a critical reading that never rises below Reynolds one ==")


def burgers_rhs(uh, nu, K):
    # modes k = 1..K held (u_{-k} = conj u_k); d u_k/dt = -nu k^2 u_k - (i k / 2) sum_{p+q=k} u_p u_q
    full = np.zeros(2 * K + 1, dtype=complex)        # index k + K
    full[K + 1:] = uh
    full[:K] = np.conj(uh[::-1])
    conv = np.convolve(full, full)                    # index (p+q) + 2K
    out = np.empty(K, dtype=complex)
    for k in range(1, K + 1):
        out[k - 1] = -nu * k * k * uh[k - 1] - 0.5j * k * conv[k + 2 * K]
    return out


def burgers_run(uh0, nu, K, dt, steps):
    uh = uh0.copy()
    ks = np.arange(1, K + 1)
    X = [2 * np.sum(np.abs(uh) / ks)]
    Y = [2 * np.sum(np.abs(uh) * ks)]
    for _ in range(steps):
        k1 = burgers_rhs(uh, nu, K)
        k2 = burgers_rhs(uh + 0.5 * dt * k1, nu, K)
        k3 = burgers_rhs(uh + 0.5 * dt * k2, nu, K)
        k4 = burgers_rhs(uh + dt * k3, nu, K)
        uh = uh + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        X.append(2 * np.sum(np.abs(uh) / ks))
        Y.append(2 * np.sum(np.abs(uh) * ks))
    return np.array(X), np.array(Y)


K, nu, cfeed = 32, 0.05, 0.5       # the specimen's feed bound: |N_k| <= (|k|/2) sum |u_p||u_q|, so c = 1/2
ks = np.arange(1, K + 1)
for trial in range(5):
    uh0 = (np.random.randn(K) + 1j * np.random.randn(K)) * np.exp(-0.3 * ks)
    X0 = 2 * np.sum(np.abs(uh0) / ks)
    uh0 *= 0.9 * nu / (cfeed * X0)                  # c X(0) = 0.9 nu
    dt, steps = 2e-3, 6000
    X, Y = burgers_run(uh0, nu, K, dt, steps)
    assert np.all(np.diff(X) <= 1e-12), "the critical reading rose below the threshold"
    integral = np.cumsum((Y[1:] + Y[:-1]) / 2) * dt
    slack = (X[0] - X[1:]) - (nu - cfeed * X[0]) * integral
    assert np.all(slack >= -1e-9)
    if trial == 0:
        say(f"  a specimen (Burgers' equation on a circle, 32 modes a side, nu = {nu}, c = 1/2): c X(0)/nu = 0.900, "
            f"X(t)/X(0) at t = 12: {X[-1] / X[0]:.4f}, never rising; (nu - cX(0)) * integral of Y = "
            f"{(nu - cfeed * X[0]) * integral[-1]:.5f} <= X(0) - X(t) = {X[0] - X[-1]:.5f}")
say("  5 random starts at c X(0) = 0.9 nu: X(t) nonincreasing at every step and the dissipation integral inside its bound")
uh0 = np.zeros(K, dtype=complex)
uh0[0] = -0.5j * 40 * nu                             # u = 40 nu sin x : c X(0) = 20 nu
X, Y = burgers_run(uh0, nu, K, 2e-4, 4000)
assert X.max() > 1.05 * X[0]
say(f"  planted: one mode at c X(0) = 20 nu: X rises to {X.max() / X[0]:.3f} X(0) before the comb's damping takes it; the ruler sees a rise")
# the logistic comb: equal weights w, coherent feed N_k = w sum_{p+q=k} u_p u_q on Z/m, u >= 0
m_, w_, nu_ = 5, 1.0, 1.0
for U0, blows in [(0.8, False), (1.25, True)]:
    uvec = np.full(m_, U0 * w_ / m_)                 # X = sum u / w = U0
    dt = 1e-4
    tstar = math.log(U0 / (U0 - nu_)) / (nu_ * w_ * w_) if blows else None
    tt = 0.0
    while tt < (0.95 * tstar if blows else 5.0):
        conv = np.array([sum(uvec[p] * uvec[(k - p) % m_] for p in range(m_)) for k in range(m_)])
        uvec = uvec + dt * (-nu_ * w_ * w_ * uvec + w_ * conv)
        tt += dt
    Xn = uvec.sum() / w_
    closed = nu_ / (1 - (1 - nu_ / U0) * math.exp(nu_ * w_ * w_ * tt))
    assert abs(Xn - closed) / closed < 2e-2
    if blows:
        assert Xn > 8 * U0      # the closed form reads 10.3 X(0) at 0.95 t*
        say(f"  the logistic comb at X(0) = {U0} nu: X = {Xn / U0:.1f} X(0) at 0.95 of the blow-up time "
            f"t* = log(X0/(X0 - nu))/(nu w^2) = {tstar:.4f}; the closed form reads {closed / U0:.1f}")
    else:
        assert Xn < U0
        say(f"  the logistic comb at X(0) = {U0} nu: X decays to {Xn:.4f}; the closed form reads {closed:.4f}")

# ----------------------------------------------------------------------------------------------
say("== H. COUPLED LOCKS (Lee-Yang): zeros in the common fugacity ==")


def lock_poly_coeffs(a):
    n = a.shape[0]
    coeffs = np.zeros(n + 1)
    for bits in range(1 << n):
        S = [i for i in range(n) if bits >> i & 1]
        Sc = [i for i in range(n) if not bits >> i & 1]
        wgt = 1.0
        for i in S:
            for j in Sc:
                wgt *= a[i, j]
        coeffs[len(S)] += wgt
    return coeffs


worst = 0.0
for trial in range(30):
    n = random.randint(2, 8)
    a = np.random.uniform(-1, 1, (n, n))
    a = (a + a.T) / 2
    roots = np.roots(lock_poly_coeffs(a)[::-1])
    worst = max(worst, np.max(np.abs(np.abs(roots) - 1)))
assert worst < 1e-5
a = np.ones((4, 4)); a[0, 1] = a[1, 0] = 2.5; a[2, 3] = a[3, 2] = 2.5
roots = np.roots(lock_poly_coeffs(a)[::-1])
assert np.max(np.abs(np.abs(roots) - 1)) > 0.1
say(f"  30 random symmetric couplings in [-1, 1], 2 to 8 locks: every zero within {worst:.1e} of the unit circle; "
    "planted couplings of 2.5 put zeros off it")

# ----------------------------------------------------------------------------------------------
say("== I. A DRIVEN CHAIN (Jarzynski): the mean of exp(-beta W) ==")


def metropolis(E, beta):
    S = len(E)
    Kk = np.zeros((S, S))
    for x in range(S):
        for y in range(S):
            if x != y:
                Kk[x, y] = min(1.0, math.exp(-beta * (E[y] - E[x]))) / (S - 1)
        Kk[x, x] = 1 - Kk[x].sum()
    return Kk


S_, n_, beta = 3, 4, 1.3
E = np.random.randn(n_ + 1, S_)
Ks = [None] + [metropolis(E[t], beta) for t in range(1, n_ + 1)]
Zs = [np.exp(-beta * E[t]).sum() for t in range(n_ + 1)]


def driven_mean(Ks):
    tot, meanW, mass = 0.0, 0.0, 0.0
    for path in itertools.product(range(S_), repeat=n_ + 1):
        pr = math.exp(-beta * E[0][path[0]]) / Zs[0]
        W = 0.0
        for t in range(n_):
            W += E[t + 1][path[t]] - E[t][path[t]]
            pr *= Ks[t + 1][path[t], path[t + 1]]
        tot += pr * math.exp(-beta * W)
        meanW += pr * W
        mass += pr
    return tot, meanW, mass


tot, meanW, mass = driven_mean(Ks)
dF = -(math.log(Zs[n_]) - math.log(Zs[0])) / beta
assert abs(mass - 1) < 1e-12 and abs(tot - Zs[n_] / Zs[0]) < 1e-12 and meanW >= dF - 1e-12
Kbad = [None] + [np.roll(Kk, 1, axis=1) for Kk in Ks[1:]]      # stochastic, the weight no longer stationary
tot_bad = driven_mean(Kbad)[0]
assert abs(tot_bad - Zs[n_] / Zs[0]) > 1e-3
say(f"  3 states, 4 ticks, 243 paths: mean of exp(-beta W) = {tot:.12f} = Z_n/Z_0 = {Zs[n_] / Zs[0]:.12f}; "
    f"mean work {meanW:.4f} >= free energy change {dF:.4f}; planted kernels without the stationary weight read {tot_bad:.4f}")

# ----------------------------------------------------------------------------------------------
say("== J. THE HALF ON THE LINE AND ON THE CIRCLE (Hermite-Biehler, Schur-Cohn) ==")
worst_line, worst_circle = 0.0, 0.0
checked = 0
for trial in range(40):
    n = random.randint(1, 7)
    a = np.random.randn(n) - 1j * np.random.uniform(0.05, 2.0, n)        # roots below the axis
    cc = complex(np.random.randn(), np.random.randn())
    eps = np.exp(1j * random.uniform(0, 2 * math.pi))
    P = cc * np.poly(a)
    Pstar = np.conj(cc) * np.poly(np.conj(a))
    # the mechanism, at random places: above the axis the reversed factor is the smaller, below it the larger
    for _ in range(50):
        z = complex(np.random.randn() * 3, np.random.randn() * 3)
        if abs(z.imag) < 1e-6:
            continue
        gap = abs(np.polyval(P, z)) - abs(np.polyval(Pstar, z))
        assert (gap > 0) == (z.imag > 0)
        checked += 1
    S = P + eps * Pstar
    if abs(S[0]) > 0.3 * abs(cc):                                         # leading coefficient away from a cancellation
        roots = np.roots(S)
        worst_line = max(worst_line, np.max(np.abs(roots.imag) / (1 + np.abs(roots))))
    b = np.random.uniform(0, 0.95, n) * np.exp(1j * np.random.uniform(0, 2 * math.pi, n))   # roots in the disc
    P = np.poly1d(cc * np.poly(b))
    Psharp = np.poly1d([np.conj(cc)])
    for bj in b:
        Psharp = Psharp * np.poly1d([-np.conj(bj), 1.0])
    for _ in range(50):
        z = complex(np.random.randn(), np.random.randn())
        if abs(abs(z) - 1) < 1e-6:
            continue
        gap = abs(P(z)) - abs(Psharp(z))
        assert (gap < 0) == (abs(z) < 1)
        checked += 1
    roots = (P + eps * Psharp).roots
    worst_circle = max(worst_circle, np.max(np.abs(np.abs(roots) - 1)))
assert worst_line < 1e-4 and worst_circle < 1e-4, (worst_line, worst_circle)
P = np.poly([1j, -2j]); Pstar = np.poly([-1j, 2j])
assert np.max(np.abs(np.roots(P + Pstar).imag)) > 0.5
say(f"  40 draws each, degree 1 to 7: the factor inequality holds at {checked} random places; zeros of P + eps P* within "
    f"{worst_line:.1e} of the real line (relative), of P + eps P# within {worst_circle:.1e} of the unit circle; "
    "a planted root on the other side puts zeros off the line")

say("ALL SECTIONS PASSED")
