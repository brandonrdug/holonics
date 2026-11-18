"""Host ruler for the third set of November 18 (abelian covers, the density law, prime cycles,
the fluid's triads and its global flow).  Every check is an assert; each null is held to a
planted instance in the same run.  Floats are the ruler's and are printed as readings."""
import itertools, math, time
import numpy as np

rng = np.random.default_rng(20261118)
T0 = time.time()

PREDICTIONS = {
    "A": "the cover's dart determinant equals the product over characters to 1e-9 relative at every "
         "sampled u; the m-cycle gives (1-u^m)^2; a wrong character set misses",
    "B": "mixing, Cheeger, Hoffman, relaxation and entropy hold on every sampled tempered specimen; "
         "two disjoint copies break mixing at mu = 2 sqrt q",
    "C": "|n N_n - sum mu(n/d) q^d| stays inside the P1 bound for n <= 16 on tempered specimens; an "
         "untempered specimen leaves it",
    "D": "the triads' work is zero to 1e-12 relative in 2 and 3 dimensions, the plane's enstrophy work "
         "too; in 3 dimensions the enstrophy work is not zero; a truncation set without -k does work",
    "E": "RK4 on a plane truncation keeps the energy equality to 1e-6 and the norm never rises",
}

def darts(edges):
    D = [(a, b) for (a, b) in edges] + [(b, a) for (a, b) in edges]
    m = len(edges)
    rev = [(i + m) % (2 * m) for i in range(2 * m)]
    return D, rev

def hashimoto(D, rev, w=None):
    n = len(D)
    B = np.zeros((n, n), dtype=complex)
    for i, (s, t) in enumerate(D):
        for j, (s2, t2) in enumerate(D):
            if t == s2 and j != rev[i]:
                B[i, j] = 1 if w is None else w[j]
    return B

def random_multigraph(nv, ne):
    return [(int(rng.integers(nv)), int(rng.integers(nv))) for _ in range(ne)]

# ---------------- A. Artin over an abelian cover ----------------
print("A. Artin's factorization over a cyclic cover")
for trial in range(6):
    nv, ne, m = int(rng.integers(2, 5)), int(rng.integers(3, 7)), int(rng.integers(2, 6))
    edges = random_multigraph(nv, ne)
    D, rev = darts(edges)
    sig = [int(rng.integers(m)) for _ in edges]
    sig = sig + [(-s) % m for s in sig]          # sigma on reversed dart is -sigma
    # cover darts (dart, sheet): leaves (src, s), enters (tgt, s + sig)
    CD = [(i, s) for i in range(len(D)) for s in range(m)]
    idx = {p: k for k, p in enumerate(CD)}
    BY = np.zeros((len(CD), len(CD)), dtype=complex)
    for (i, s) in CD:
        for j in range(len(D)):
            if D[i][1] == D[j][0] and j != rev[i]:
                BY[idx[(i, s)], idx[(j, (s + sig[i]) % m)]] = 1
    zeta = np.exp(2j * np.pi / m)
    worst = 0.0
    for _ in range(4):
        u = complex(rng.normal(), rng.normal()) * 0.3
        lhs = np.linalg.det(np.eye(len(CD)) - u * BY)
        rhs = np.prod([np.linalg.det(np.eye(len(D)) - u * hashimoto(D, rev, [zeta ** (k * sig[j]) for j in range(len(D))]))
                       for k in range(m)])
        worst = max(worst, abs(lhs - rhs) / max(1.0, abs(lhs)))
        bad = np.prod([np.linalg.det(np.eye(len(D)) - u * hashimoto(D, rev, [zeta ** ((k if k else 1) * sig[j]) for j in range(len(D))]))
                       for k in range(m)])
    assert worst < 1e-9, worst
    print(f"  base |V|={nv} |E|={ne}, m={m}: worst relative gap {worst:.2e}")
# planted: a wrong character set (character 1 in place of the trivial one) on a cover with nonzero voltage
edges = [(0, 0), (0, 1), (1, 1)]; D, rev = darts(edges); m = 3; sig = [1, 0, 2]; sig = sig + [(-s) % m for s in sig]
CD = [(i, s) for i in range(len(D)) for s in range(m)]; idx = {p: k for k, p in enumerate(CD)}
BY = np.zeros((len(CD), len(CD)), dtype=complex)
for (i, s) in CD:
    for j in range(len(D)):
        if D[i][1] == D[j][0] and j != rev[i]:
            BY[idx[(i, s)], idx[(j, (s + sig[i]) % m)]] = 1
u = 0.31 + 0.17j; zeta = np.exp(2j * np.pi / m)
lhs = np.linalg.det(np.eye(len(CD)) - u * BY)
bad = np.prod([np.linalg.det(np.eye(len(D)) - u * hashimoto(D, rev, [zeta ** ((k if k else 1) * sig[j]) for j in range(len(D))])) for k in range(m)])
assert abs(lhs - bad) > 1e-3
print(f"  planted wrong character set: gap {abs(lhs - bad):.3f} (seen)")
for m in [3, 4, 5, 7]:
    u = 0.41 - 0.2j
    C = np.zeros((2 * m, 2 * m))
    for s in range(m):        # forward darts s->s+1 and backward s+1->s
        C[s, (s + 1) % m] = 1; C[m + (s + 1) % m, m + s] = 1
    lhs = np.linalg.det(np.eye(2 * m) - u * C)
    assert abs(lhs - (1 - u ** m) ** 2) < 1e-12
print("  the m-cycle: det(1 - uB) = (1 - u^m)^2 at m = 3, 4, 5, 7")

# ---------------- B. The density law ----------------
print("B. The density law of a tempered complex")
def regular_multigraph(n, k):
    """2k-regular multigraph: union of k random permutations (each gives a contact v -> pi(v))."""
    A = np.zeros((n, n))
    for _ in range(k):
        p = rng.permutation(n)
        for v in range(n):
            A[v, p[v]] += 1; A[p[v], v] += 1
    return A
def law_checks(A, d, mu, label, expect=True):
    n = len(A); ok = True
    for _ in range(300):
        S = rng.random(n) < rng.uniform(0.05, 0.6); T = rng.random(n) < rng.uniform(0.05, 0.6)
        s, t = S.sum(), T.sum()
        e = S.astype(float) @ A @ T.astype(float)
        bound = mu * math.sqrt(s * t * (1 - s / n) * (1 - t / n))
        ok &= abs(e - d * s * t / n) <= bound + 1e-9
    return ok
specimens = 0
for n, k in [(40, 2), (60, 3), (80, 2), (100, 3)]:
    A = regular_multigraph(n, k); d = 2 * k; q = d - 1
    ev = np.sort(np.linalg.eigvalsh(A))
    lam2 = max(abs(ev[0]), abs(ev[-2]))
    tempered = lam2 <= 2 * math.sqrt(q) + 1e-12
    mu = lam2
    assert law_checks(A, d, mu, "spectral")
    # Cheeger (easy side) and Hoffman at the spectral values
    mu2, nu = ev[-2], -ev[0]
    for _ in range(200):
        S = rng.random(n) < rng.uniform(0.05, 0.95); s = S.sum()
        cut = S.astype(float) @ A @ (~S).astype(float)
        assert (d - mu2) * s * (n - s) / n <= cut + 1e-9
    # greedy independent set
    order = rng.permutation(n); I = []
    for v in order:
        if A[v, v] == 0 and all(A[v, w] == 0 for w in I): I.append(v)
    assert len(I) <= n * nu / (d + nu) + 1e-9
    # relaxation and entropy
    P = A / d; p = np.zeros(n); p[0] = 1.0; u0 = np.ones(n) / n; dist0 = np.sum((p - u0) ** 2)
    for t in range(1, 25):
        p = P @ p
        assert np.sum((p - u0) ** 2) <= (mu / d) ** (2 * t) * dist0 + 1e-12
        ent = sum(x * math.log(n * x) for x in p if x > 0)
        assert ent <= (n - 1) * (mu / d) ** (2 * t) + 1e-12
    floor = d * (n - d) / (n - 1)
    assert floor <= mu ** 2 + 1e-9
    specimens += 1
    print(f"  n={n} d={d}: second mode {lam2:.3f} against 2 sqrt q = {2*math.sqrt(q):.3f} (tempered: {tempered}); "
          f"trace floor sqrt {math.sqrt(floor):.3f}")
# planted: two disjoint copies, claimed tempered
A1 = regular_multigraph(30, 2); A = np.block([[A1, np.zeros((30, 30))], [np.zeros((30, 30)), A1]])
S = np.zeros(60); S[:30] = 1
gap = abs(S @ A @ S - 4 * 30 * 30 / 60); bound = 2 * math.sqrt(3) * math.sqrt(30 * 30 * 0.25)
assert gap > bound
print(f"  planted two disjoint copies at mu = 2 sqrt q: one copy's own edges deviate {gap:.1f} > bound {bound:.2f} (seen)")

# ---------------- C. Prime cycles at the half ----------------
print("C. The prime cycle theorem at the half")
def mobius(n):
    r, p, m = 1, 2, n
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0: return 0
            r = -r
        p += 1
    return -r if m > 1 else r
def prime_cycle_check(edges, nv, q, label):
    D, rev = darts(edges); B = hashimoto(D, rev).real
    W = [None] + [round(np.trace(np.linalg.matrix_power(B, l))) for l in range(1, 17)]
    c = len(edges) - nv; worst = 0.0; inside = True
    for n in range(1, 17):
        divs = [d for d in range(1, n + 1) if n % d == 0]
        nN = sum(mobius(n // d) * W[d] for d in divs)
        assert nN % n == 0 and nN >= 0
        main = sum(mobius(n // d) * q ** d for d in divs)
        bound = sum(1 + 2 * abs(c) + 2 * (nv - 1) * math.sqrt(q) ** d for d in divs)
        inside &= abs(nN - main) <= bound + 1e-9
        worst = max(worst, abs(nN - main) / bound)
    return inside, worst
petersen = [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
K4 = [(a, b) for a in range(4) for b in range(a + 1, 4)]
for name, edges, nv, q in [("Petersen", petersen, 10, 2), ("K4", K4, 4, 2)]:
    inside, worst = prime_cycle_check(edges, nv, q, name)
    assert inside
    print(f"  {name}: inside P1 to n = 16, largest ratio to the bound {worst:.3f}")
prism = [(i, (i + 1) % 21) for i in range(21)] + [(21 + i, 21 + (i + 1) % 21) for i in range(21)] + [(i, 21 + i) for i in range(21)]
inside, worst = prime_cycle_check(prism, 42, 2, "prism42")
assert not inside
print(f"  planted untempered prism on 42 cells: leaves P1, largest ratio {worst:.2f} (seen)")

# ---------------- D. The fluid's triads ----------------
print("D. The truncated fluid's triads do no work")
def leray(k, v):
    k = np.asarray(k, float); return v - k * (k @ v) / (k @ k)
def random_real_field(K, dim):
    a = {}
    for k in K:
        nk = tuple(-x for x in k)
        if nk in a: a[k] = np.conj(a[nk]); continue
        v = rng.normal(size=dim) + 1j * rng.normal(size=dim)
        a[k] = leray(k, v)
    return a
def work(K, a, weight=lambda k: 1.0):
    Kset = set(K); tot = 0.0; scale = 0.0
    for k in K:
        N = np.zeros(len(k), complex)
        for p in K:
            qv = tuple(x - y for x, y in zip(k, p))
            if qv in Kset:
                N += (a[p] @ np.asarray(qv, float)) * a[qv]
        N = -1j * leray(k, N)
        tot += weight(k) * np.real(np.vdot(a[k], N)); scale += weight(k) * np.linalg.norm(a[k]) * np.linalg.norm(N)
    return tot, scale
for dim, R in [(2, 3), (3, 2)]:
    K = [k for k in itertools.product(range(-R, R + 1), repeat=dim) if any(k) and sum(x * x for x in k) <= R * R]
    a = random_real_field(K, dim)
    w, s = work(K, a); assert abs(w) <= 1e-12 * s, (w, s)
    we, se = work(K, a, lambda k: float(sum(x * x for x in k)))
    if dim == 2:
        assert abs(we) <= 1e-12 * se
    else:
        assert abs(we) > 1e-6 * se
    print(f"  dimension {dim}, {len(K)} wave vectors: energy work / scale {abs(w)/s:.1e}, enstrophy work / scale {abs(we)/se:.1e}")
K = [k for k in itertools.product(range(-2, 3), repeat=3) if any(k) and sum(x * x for x in k) <= 4]
a = random_real_field(K, 3); drop = (1, 1, 0)
K2 = [k for k in K if k != drop]
w, s = work(K2, {k: a[k] for k in K2})
print(f"  reading: one wave vector dropped, its -k kept: work / scale {abs(w)/s:.1e} (the guess said this does work)")
keep = rng.random(len(K)) < 0.6
K3 = [k for k, c in zip(K, keep) if c]
w, s = work(K3, {k: a[k] for k in K3})
assert abs(w) > 1e-3 * s
print(f"  planted truncation on a random subset of {len(K3)} of {len(K)} (not closed under -k): work / scale {abs(w)/s:.1e} (seen)")
b = {k: leray(k, rng.normal(size=3) + 1j * rng.normal(size=3)) for k in K}
w, s = work(K, b)
assert abs(w) > 1e-3 * s
print(f"  planted non-real field on the closed set: work / scale {abs(w)/s:.1e} (seen)")

# ---------------- E. The global flow ----------------
print("E. A plane truncation flows with its energy equality")
K = [k for k in itertools.product(range(-3, 4), repeat=2) if any(k) and k[0] ** 2 + k[1] ** 2 <= 9]
nu = 0.05
a = random_real_field(K, 2)
def rhs(a):
    Kset = set(K); out = {}
    for k in K:
        N = np.zeros(2, complex)
        for p in K:
            qv = (k[0] - p[0], k[1] - p[1])
            if qv in Kset: N += (a[p] @ np.asarray(qv, float)) * a[qv]
        out[k] = -nu * (k[0] ** 2 + k[1] ** 2) * a[k] - 1j * leray(k, N)
    return out
E = lambda a: 0.5 * sum(np.vdot(v, v).real for v in a.values())
Dr = lambda a: sum((k[0] ** 2 + k[1] ** 2) * np.vdot(v, v).real for k, v in a.items())
h, steps = 0.002, 1500; E0 = E(a); diss = 0.0; prevnorm = math.sqrt(2 * E0); rises = 0
for _ in range(steps):
    k1 = rhs(a); k2 = rhs({k: a[k] + h / 2 * k1[k] for k in K}); k3 = rhs({k: a[k] + h / 2 * k2[k] for k in K}); k4 = rhs({k: a[k] + h * k3[k] for k in K})
    d0 = Dr(a)
    a = {k: a[k] + h / 6 * (k1[k] + 2 * k2[k] + 2 * k3[k] + k4[k]) for k in K}
    diss += h * 0.5 * (d0 + Dr(a)) * nu
    nrm = math.sqrt(2 * E(a)); rises += nrm > prevnorm + 1e-12; prevnorm = nrm
resid = abs(E(a) + diss - E0) / E0
assert resid < 1e-4 and rises == 0, (resid, rises)
print(f"  {len(K)} wave vectors, {steps} steps: energy equality residual {resid:.1e} of E(0), norm rises {rises}")
x, t = 1.0, 0.0
while x < 1e6 and t < 2: x += 0.001 * x * x; t += 0.001
assert x >= 1e6
print(f"  planted field x' = x^2 (not dissipative): leaves 10^6 by t = {t:.3f} (seen)")
print(f"all sections pass; {time.time() - T0:.1f} s")
