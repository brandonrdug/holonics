"""A host ruler for the record's second set (November 18 and 19, 2026).

It reads, on small complexes, four statements the Lean modules prove in general, and one planted null for
each reading. Floats are the ruler's own and are printed as readings; the identities of sections C and D
are integer or rational arithmetic.

  A  the one-sided count bound and the Li numbers (Zeta/FiniteLiCriterion, Landmarks/RegularComplexHalf)
  B  the negative squares of the norm form (Holon/InertiaCount)
  C  prime cycles by enumeration, by Moebius inversion of the traces, and the product to a horizon
     (Landmarks/IharaEulerProduct)
  D  the moving metric: a positive form exists for a semisimple imaginary generator and for no Jordan block
     (Coupling/MovingMetricSpectral)

Run: python3 second_ruler.py   (numpy and sympy; one thread; under a minute)
"""
import itertools
import math
import numpy as np
import sympy as sp


def darts(edges):
    D = [(i, 0) for i in range(len(edges))] + [(i, 1) for i in range(len(edges))]
    s = lambda d: edges[d[0]][0] if d[1] == 0 else edges[d[0]][1]
    t = lambda d: edges[d[0]][1] if d[1] == 0 else edges[d[0]][0]
    sw = lambda d: (d[0], 1 - d[1])
    return D, s, t, sw


def mats(nv, edges, backtrack=False):
    D, s, t, sw = darts(edges)
    N = len(D)
    B = np.zeros((N, N), dtype=np.int64)
    for i, e in enumerate(D):
        for j, f in enumerate(D):
            if t(e) == s(f) and (backtrack or f != sw(e)):
                B[i, j] = 1
    A = np.zeros((nv, nv), dtype=np.int64)
    for e in D:
        A[s(e), t(e)] += 1
    return B, A, D, s, t, sw


def petersen():
    E = [(i, (i + 1) % 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)] + [(i, 5 + i) for i in range(5)]
    return 10, E


def K(n):
    return n, [(i, j) for i in range(n) for j in range(i + 1, n)]


def prism(n):
    E = [(i, (i + 1) % n) for i in range(n)] + [(n + i, n + (i + 1) % n) for i in range(n)] + [(i, n + i) for i in range(n)]
    return 2 * n, E


def nontrivial_roots(A, q):
    lam = np.linalg.eigvalsh(A.astype(float))
    roots = []
    for l in lam:
        if abs(l * l - (q + 1) ** 2) < 1e-9:
            continue
        disc = complex(l * l - 4 * q)
        r = np.sqrt(disc)
        roots += [(l + r) / 2, (l - r) / 2]
    return lam, np.array(roots)


print("== A. The one-sided count bound and the Li numbers")
for name, (nv, edges), horizon in [("Petersen", petersen(), 400), ("prism of two rings of 21", prism(21), 60)]:
    B, A, *_ = mats(nv, edges)
    q = int(A.sum(axis=1)[0]) - 1
    assert all(int(x) == q + 1 for x in A.sum(axis=1))
    lam, roots = nontrivial_roots(A, q)
    Nn = len(roots) // 2
    w = roots / math.sqrt(q)
    tempered = bool(np.all(np.abs(np.abs(w) - 1) < 1e-9))
    # the remainder against the trace of B^l, as a check of the root family
    m = len(edges)
    Bp = np.eye(len(B))
    triv = [l for l in lam if abs(l * l - (q + 1) ** 2) < 1e-9]
    worst = 0.0
    first_two = first_one = first_li = None
    min_li = None
    for l in range(1, horizon + 1):
        rem = float(np.real(np.sum(roots ** l)))
        if l <= 24:
            Bp = Bp @ B
            smooth = (m - nv) * (1 + (-1) ** l) + sum((np.sign(x) ** l) * (q ** l + 1) for x in triv)
            worst = max(worst, abs(np.trace(Bp) - smooth - rem) / q ** l)
        bound = 2 * Nn * q ** (l / 2)
        if first_two is None and abs(rem) > bound * (1 + 1e-12):
            first_two = l
        if first_one is None and rem > bound * (1 + 1e-12):
            first_one = l
        li = float(np.real(np.sum(1 - w ** l)))
        min_li = li if min_li is None else min(min_li, li)
        if first_li is None and li < -1e-9:
            first_li = l
    assert worst < 1e-9, worst
    print(f"  {name}: q = {q}, {nv} cells, nontrivial modes {Nn}, on the circle: {tempered}")
    print(f"    remainder against tr(B^l) to length 24, largest difference over q^l {worst:.2e}")
    print(f"    first length outside the two-sided bound: {first_two}; outside the one-sided bound: {first_one}")
    print(f"    first Li number below zero: {first_li}; smallest Li number to n = {horizon}: {min_li:.6f}")
    if tempered:
        assert first_two is None and first_one is None and first_li is None
    else:
        assert first_one is not None and first_li is not None
        assert first_one == first_li, "the one-sided bound and the Li number are one inequality"

print("== B. Negative squares of the norm form")
for name, (nv, edges) in [("Petersen", petersen()), ("K4", K(4)), ("prism of two rings of 21", prism(21))]:
    B, A, *_ = mats(nv, edges)
    q = int(A.sum(axis=1)[0]) - 1
    Af = A.astype(float)
    Kn = np.block([[q * np.eye(nv), Af / 2], [Af / 2, np.eye(nv)]])
    ev = np.linalg.eigvalsh(Kn)
    neg = int(np.sum(ev < -1e-9)); pos = int(np.sum(ev > 1e-9)); nul = len(ev) - neg - pos
    lam = np.linalg.eigvalsh(Af)
    out = int(np.sum(lam ** 2 > 4 * q + 1e-9)); inn = int(np.sum(lam ** 2 < 4 * q - 1e-9)); edge = nv - out - inn
    print(f"  {name}: negative squares {neg} = modes with lambda^2 > 4q {out}; positive {pos} = cells {nv} + modes inside {inn}; null {nul} = modes at the edge {edge}")
    assert neg == out and pos == nv + inn and nul == edge
# planted: a form that is not the norm form (q replaced by q + 3) must not match the count at q
nv, edges = prism(21); B, A, *_ = mats(nv, edges); Af = A.astype(float)
Kp = np.block([[5 * np.eye(nv), Af / 2], [Af / 2, np.eye(nv)]])
negp = int(np.sum(np.linalg.eigvalsh(Kp) < -1e-9)); out = int(np.sum(np.linalg.eigvalsh(Af) ** 2 > 8 + 1e-9))
print(f"  planted (q + 3 in the form, q in the count): negative squares {negp} against {out}")
assert negp != out

print("== C. Prime cycles: enumeration, Moebius inversion and the product to a horizon")


def mobius(n):
    return int(sp.mobius(n))


def prime_cycles_by_moebius(B, n):
    tot = 0
    for d in sp.divisors(n):
        tot += mobius(n // d) * int(np.trace(np.linalg.matrix_power(B, d)))
    assert tot % n == 0
    return tot // n


def prime_cycles_by_enumeration(nv, edges, n, backtrack=False):
    D, s, t, sw = darts(edges)
    nxt = {d: [f for f in D if t(d) == s(f) and (backtrack or f != sw(d))] for d in D}
    count = 0

    def extend(walk):
        nonlocal count
        if len(walk) == n:
            if walk[0] in nxt[walk[-1]]:
                # least period n ?
                if all(walk[k:] + walk[:k] != walk for k in range(1, n)):
                    count += 1
            return
        for f in nxt[walk[-1]]:
            extend(walk + [f])

    for d in D:
        extend([d])
    assert count % n == 0
    return count // n


for name, (nv, edges), top in [("K4", K(4), 8), ("Petersen", petersen(), 9)]:
    B, A, *_ = mats(nv, edges)
    by_m = [prime_cycles_by_moebius(B, n) for n in range(1, top + 1)]
    by_e = [prime_cycles_by_enumeration(nv, edges, n) for n in range(1, top + 1)]
    print(f"  {name}: prime cycles at lengths 1 to {top}: by Moebius {by_m}; by enumeration {by_e}")
    assert by_m == by_e
    u = sp.symbols('u')
    det = sp.expand((sp.eye(len(B)) - u * sp.Matrix(B.tolist())).det())
    prod = sp.Integer(1)
    for d in range(1, top + 1):
        prod *= (1 - u ** d) ** by_m[d - 1]
    diff = sp.Poly(sp.expand(det - prod), u)
    low = [c for (k,), c in diff.terms() if k <= top]
    assert all(c == 0 for c in low)
    high = min([k for (k,), c in diff.terms()], default=None)
    print(f"    det(1 - uB) and the product to horizon {top} agree through u^{top}; the first differing power is u^{high}")
    # the three faces, with no division
    Dg = sp.diag(*[int(x) for x in A.sum(axis=1)])
    rhs = sp.expand((sp.eye(nv) - u * sp.Matrix(A.tolist()) + u ** 2 * (Dg - sp.eye(nv))).det() * (1 - u ** 2) ** len(edges))
    lhs = sp.expand((1 - u ** 2) ** nv * prod)
    d3 = sp.Poly(sp.expand(lhs - rhs), u)
    assert all(c == 0 for (k,), c in d3.terms() if k <= top)
    print(f"    (1 - u^2)^|V| * product and det(1 - uA + u^2(D - 1)) * (1 - u^2)^|E| agree through u^{top}")
# planted: with backtracking allowed the necklace counts are another operator's and the cells' determinant is not met
nv, edges = K(4)
Bb, A, *_ = mats(nv, edges, backtrack=True)
by_b = [prime_cycles_by_moebius(Bb, n) for n in range(1, 7)]
u = sp.symbols('u')
prod = sp.Integer(1)
for d in range(1, 7):
    prod *= (1 - u ** d) ** by_b[d - 1]
Dg = sp.diag(*[int(x) for x in A.sum(axis=1)])
rhs = sp.expand((sp.eye(nv) - u * sp.Matrix(A.tolist()) + u ** 2 * (Dg - sp.eye(nv))).det() * (1 - u ** 2) ** len(edges))
d3 = sp.Poly(sp.expand((1 - u ** 2) ** nv * prod - rhs), u)
bad = min(k for (k,), c in d3.terms())
print(f"  planted (backtracking allowed, K4): necklaces {by_b}; the three faces first differ at u^{bad}")
assert bad <= 6

print("== D. The moving metric: a positive form for a semisimple imaginary generator, none for a Jordan block")
rng = np.random.default_rng(11)
n = 5
S = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
d = 1j * rng.normal(size=n)
Agen = S @ np.diag(d) @ np.linalg.inv(S)
Si = np.linalg.inv(S)
G = Si.conj().T @ Si
rate = Agen.conj().T @ G + G @ Agen
print(f"  semisimple imaginary generator: least eigenvalue of G {np.linalg.eigvalsh(G).min():.4f}, largest entry of A*G + GA {np.abs(rate).max():.2e}")
assert np.linalg.eigvalsh(G).min() > 0 and np.abs(rate).max() < 1e-9
# the converse read numerically: solve A*G + GA = 0 for Hermitian G on a Jordan block at 0 and on i*diag
def conserving_forms(Am):
    k = Am.shape[0]
    # real-linear map on Hermitian matrices; a basis of Hermitian matrices
    basis = []
    for a in range(k):
        for b in range(a, k):
            E = np.zeros((k, k), dtype=complex); E[a, b] = 1; E[b, a] = 1; basis.append(E if a != b else E / 2)
            if a != b:
                F = np.zeros((k, k), dtype=complex); F[a, b] = 1j; F[b, a] = -1j; basis.append(F)
    M = np.array([np.concatenate([(Am.conj().T @ X + X @ Am).real.ravel(), (Am.conj().T @ X + X @ Am).imag.ravel()]) for X in basis]).T
    _, sv, Vt = np.linalg.svd(M)
    null = [Vt[i] for i in range(len(sv)) if sv[i] < 1e-9] + [Vt[i] for i in range(len(sv), Vt.shape[0])]
    return [sum(c * X for c, X in zip(v, basis)) for v in null]
J = np.array([[0, 1], [0, 0]], dtype=complex)
forms = conserving_forms(J)
corner = max(abs(X[0, 0]) for X in forms)
print(f"  Jordan block at zero: the conserved Hermitian forms span {len(forms)} dimensions, and every one vanishes on the block's first vector (largest corner entry {corner:.2e}), so none is positive definite")
assert len(forms) == 2 and corner < 1e-12
T = np.diag([1j, -2j]).astype(complex)
forms = conserving_forms(T)
print(f"  planted (a diagonal imaginary generator): conserved forms span {len(forms)} dimensions, the identity among them")
assert len(forms) == 2
print("all checks pass")
