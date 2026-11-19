"""Host ruler for the fourth set of November 18 (the flat torus's Kahler triple, closed walks by
holonomy class on an abelian cover, the floor from the covering tree's walks).  Every check is an
assert; each null is held to a planted instance in the same run.  Integer arithmetic where the
statement is about counts and the triple; double floats for spectra and norms, printed as the
ruler's readings."""
import itertools, math, time
import numpy as np

T0 = time.time()
rng = np.random.default_rng(20261118)

PREDICTIONS = {
    "A": "on n = 1..4 the letterwise triple obeys [D,U] = H, [H,U] = -2U and adjointness in integers; a "
         "word's weight is n - degree; L^k : degree n-k -> n+k has full rank for every k <= n and its least "
         "singular value is k! exactly; H = degree (the planted sign) breaks [H,U] = -2U",
    "B": "on cyclic covers, sum_k psi(-kg) tr(B_k^n) = m W_n(g) to 1e-9 relative, sum_g W_n(g) = tr B^n, "
         "and |W_n(g) - tr B^n / m| <= (m-1)/m max_(k!=0) |tr B_k^n| on every sample; a wrong character "
         "set misses the identity",
    "C": "on random (q+1)-regular multigraphs (A^(2k))_vv >= C_k q^k at every cell for k <= 8, and the "
         "floor mu^(2k) >= (n C_k q^k - (q+1)^(2k))/(n-1) holds; the Petersen graph has exactly 15 closed "
         "walks of length 4 at each cell (girth 5, the tree's count); the bound with (q+1)^k in place of "
         "q^k fails on Petersen at k = 2",
}

# ---------------- A. The flat torus's triple ----------------
print("A. The Kahler triple of a flat torus")
def torus_ops(n, planted=False):
    words = list(itertools.product(range(4), repeat=n)); idx = {w: i for i, w in enumerate(words)}
    N = len(words)
    U = np.zeros((N, N), dtype=np.int64); D = np.zeros((N, N), dtype=np.int64); H = np.zeros((N, N), dtype=np.int64)
    deg = lambda w: sum(1 for x in w if x in (1, 2)) + 2 * sum(1 for x in w if x == 3)
    for w in words:
        j = idx[w]
        for i in range(n):
            if w[i] == 0:
                w2 = w[:i] + (3,) + w[i + 1:]; U[idx[w2], j] += 1     # L e_w = e_(w with i -> 3)
        H[j, j] = deg(w) if planted else (n - deg(w))
    D = U.T.copy()
    return words, U, D, H, deg
for n in range(1, 5):
    words, U, D, H, deg = torus_ops(n)
    assert np.array_equal(D @ U - U @ D, H)
    assert np.array_equal(H @ U - U @ H, -2 * U)
    worst = []
    for k in range(0, n + 1):
        src = [i for i, w in enumerate(words) if deg(w) == n - k]
        tgt = [i for i, w in enumerate(words) if deg(w) == n + k]
        Lk = np.linalg.matrix_power(U, k)[np.ix_(tgt, src)].astype(float)
        assert len(src) == len(tgt) and np.linalg.matrix_rank(Lk) == len(src)
        s = np.linalg.svd(Lk, compute_uv=False)
        assert abs(s.min() - math.factorial(k)) < 1e-9 * math.factorial(k), (n, k, s.min())
        worst.append(s.min() / math.factorial(k))
    print(f"  n={n}: 4^n = {len(words)} words, triple laws in integers, least singular value of L^k / k! = "
          + ", ".join(f"{x:.6f}" for x in worst))
words, U, D, H, deg = torus_ops(3, planted=True)
assert not np.array_equal(H @ U - U @ H, -2 * U)
print("  planted H = degree: [H, U] = +2U, not -2U (seen)")

# ---------------- B. Closed walks by holonomy class ----------------
print("B. Closed walks of an abelian cover by holonomy class")
def darts(edges):
    D = list(edges) + [(b, a) for (a, b) in edges]; m = len(edges)
    rev = [(i + m) % (2 * m) for i in range(2 * m)]; return D, rev
def hashimoto(D, rev, w=None):
    n = len(D); B = np.zeros((n, n), dtype=complex)
    for i, (s, t) in enumerate(D):
        for j, (s2, t2) in enumerate(D):
            if t == s2 and j != rev[i]:
                B[i, j] = 1 if w is None else w[j]
    return B
def walks_by_class(D, rev, volt, m, L):
    # closed non-backtracking dart walks of length L (cyclic: last dart may not reverse into the first)
    nd = len(D); counts = [0] * m
    succ = [[j for j in range(nd) if D[i][1] == D[j][0] and j != rev[i]] for i in range(nd)]
    def go(start, cur, length, h):
        if length == L:
            if start in succ[cur]: counts[h % m] += 1
            return
        for j in succ[cur]: go(start, j, length + 1, h + volt[j])
    for s in range(nd): go(s, s, 1, volt[s])
    return counts
bases = [([(0, 1), (0, 1), (1, 0), (0, 0)], 2), ([(0, 1), (1, 2), (2, 0), (0, 2), (1, 1)], 3),
         ([(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (1, 3)], 4)]
for edges, nv in bases:
    D, rev = darts(edges); E = len(edges)
    for m in (2, 3, 5):
        v0 = rng.integers(0, m, size=E); volt = list(v0) + list((-v0) % m)
        zeta = np.exp(2j * math.pi / m)
        for L in (3, 4, 5, 6):
            W = walks_by_class(D, rev, volt, m, L)
            trs = [np.trace(np.linalg.matrix_power(hashimoto(D, rev, [zeta ** (k * volt[j]) for j in range(len(D))]), L)) for k in range(m)]
            trB = np.trace(np.linalg.matrix_power(hashimoto(D, rev), L)).real
            assert abs(sum(W) - trB) < 1e-9
            for g in range(m):
                lhs = sum(zeta ** (-k * g) * trs[k] for k in range(m))
                assert abs(lhs - m * W[g]) <= 1e-9 * max(1.0, abs(m * W[g]))
                M = max([abs(t) for t in trs[1:]], default=0.0)
                assert abs(W[g] - trB / m) <= (m - 1) / m * M + 1e-9
    print(f"  base |V|={nv} |E|={E}: identity, total and deviation bound at m = 2, 3, 5, lengths 3 to 6")
edges, nv = bases[1]; D, rev = darts(edges); m = 3; v0 = np.array([1, 0, 2, 1, 0]); volt = list(v0) + list((-v0) % m)
zw = np.exp(2j * math.pi / (m + 1)); gap = 0.0
for L in (4, 5, 6):
    W = walks_by_class(D, rev, volt, m, L)
    trs = [np.trace(np.linalg.matrix_power(hashimoto(D, rev, [zw ** (k * volt[j]) for j in range(len(D))]), L)) for k in range(m)]
    gap = max([gap] + [abs(sum(zw ** (-k * g) * trs[k] for k in range(m)) - m * W[g]) for g in range(m)])
assert gap > 1e-3
print(f"  planted characters of order m + 1 (not characters of Z/m): the identity misses by {gap:.3f} (seen)")

# ---------------- C. The floor from the covering tree ----------------
print("C. The floor from the covering tree's walks")
catalan = lambda k: math.comb(2 * k, k) // (k + 1)
def regular_multigraph(n, k):
    A = np.zeros((n, n), dtype=np.int64)
    for _ in range(k):
        p = rng.permutation(n)
        for v in range(n):
            A[v, p[v]] += 1; A[p[v], v] += 1
    return A
for n, kk in [(30, 2), (50, 3), (64, 2)]:
    A = regular_multigraph(n, kk); d = 2 * kk; q = d - 1
    ev = np.sort(np.linalg.eigvalsh(A.astype(float)))
    assert abs(ev[-1] - d) < 1e-9
    mu = max(abs(ev[0]), abs(ev[-2])) if abs(ev[-2] - d) > 1e-9 else d
    P = np.eye(n, dtype=object); A2 = (A @ A).astype(object); worst = math.inf
    for k in range(1, 9):
        P = P.dot(A2)
        diag = min(P[v, v] for v in range(n))
        assert diag >= catalan(k) * q ** k
        worst = min(worst, diag / (catalan(k) * q ** k))
        assert mu ** (2 * k) >= (n * catalan(k) * q ** k - d ** (2 * k)) / (n - 1) - 1e-6 * d ** (2 * k)
    print(f"  n={n} d={d}: least (A^2k)_vv / (C_k q^k) over k <= 8 is {worst:.3f}; second mode {mu:.3f} against 2 sqrt q = {2*math.sqrt(q):.3f}")
petersen = [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
A = np.zeros((10, 10), dtype=np.int64)
for a, b in petersen: A[a, b] += 1; A[b, a] += 1
A4 = np.linalg.matrix_power(A, 4)
assert all(A4[v, v] == 15 for v in range(10)) and 15 >= catalan(2) * 2 ** 2
assert not all(A4[v, v] >= catalan(2) * 3 ** 2 for v in range(10))
print(f"  Petersen: 15 closed walks of length 4 at every cell, the tree's count; C_2 q^2 = 8; planted C_2 (q+1)^2 = 18 fails (seen)")
print(f"all sections pass; {time.time() - T0:.1f} s")
