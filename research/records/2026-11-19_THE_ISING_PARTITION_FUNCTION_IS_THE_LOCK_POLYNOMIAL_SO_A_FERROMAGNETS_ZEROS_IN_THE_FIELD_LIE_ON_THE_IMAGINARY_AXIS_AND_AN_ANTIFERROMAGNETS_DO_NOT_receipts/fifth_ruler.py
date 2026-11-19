"""Host ruler for the fifth set of November 19 (the Ising partition function as the lock
polynomial, the Lee-Yang theorem, the antiferromagnet's zeros off the axis).  Every check is an
assert; each null is held to a planted instance in the same run.  Double floats for sums, roots
and angles, printed as the ruler's readings; the statements are the Lean module's
(HolonicsResearch/Coupling/LeeYangIsing.lean)."""
import itertools, math, time, cmath
import numpy as np

T0 = time.time()
rng = np.random.default_rng(20261119)

PREDICTIONS = {
    "A": "on n = 2..7 sites with random symmetric real J (either sign, diagonal included), random beta in "
         "(0.1, 2) and random complex fields h_i, the partition function summed over the 2^n spin "
         "configurations equals exp(beta/2 sum J - beta sum h) * lockPoly(exp(-2 beta J), exp(2 beta h)) to "
         "1e-10 relative on every sample; an asymmetric J (the planted instance) misses the identity",
    "B": "for random ferromagnets (J >= 0) on n = 2..10 sites in one common field, every root of the "
         "partition function in the fugacity z = exp(2 beta h) has |z| = 1 to 1e-7, and the coefficients are "
         "palindromic; random antiferromagnets (J <= 0, the planted instance) have a root off the circle on "
         "most samples; the two-site exchange -K at beta has real roots -y +- sqrt(y^2 - 1), y = exp(2 beta K), "
         "and h = log(zeta)/(2 beta) has nonzero real part",
    "C": "on the Curie-Weiss ferromagnet (J = 1/n off the diagonal), the least angle of a zero from z = 1 at "
         "beta = 2 (ordered) shrinks from n = 4 to n = 14 by more than a factor 2, and at beta = 0.5 "
         "(disordered) it keeps more than half its n = 4 value (the Yang-Lee edge gap)",
}

def spin(S, i):
    return 1.0 if i in S else -1.0

def isingZ(J, beta, h):
    n = len(h); tot = 0j
    for r in range(n + 1):
        for S in itertools.combinations(range(n), r):
            S = set(S)
            s = np.array([spin(S, i) for i in range(n)])
            e = beta / 2 * float(s @ J @ s) + beta * complex(np.dot(h, s))
            tot += cmath.exp(e)
    return tot

def lockPoly(a, z):
    n = len(z); tot = 0j
    for r in range(n + 1):
        for S in itertools.combinations(range(n), r):
            Sc = [j for j in range(n) if j not in S]
            w = 1.0
            for i in S:
                for j in Sc:
                    w *= a[i, j]
            tot += w * np.prod([z[i] for i in S]) if S else w
    return tot

def identity_rhs(J, beta, h):
    pref = cmath.exp(beta / 2 * J.sum() - beta * h.sum())
    return pref * lockPoly(np.exp(-2 * beta * J), np.exp(2 * beta * h))

# ---------------- A. The identity ----------------
print("A. The partition function is the lock polynomial")
worst = 0.0
for n in range(2, 8):
    for _ in range(6):
        M = rng.normal(size=(n, n)); J = (M + M.T) / 2
        beta = rng.uniform(0.1, 2.0)
        h = rng.normal(size=n) * 0.7 + 1j * rng.normal(size=n)
        lhs = isingZ(J, beta, h); rhs = identity_rhs(J, beta, h)
        rel = abs(lhs - rhs) / abs(lhs)
        worst = max(worst, rel)
        assert rel < 1e-10, (n, rel)
    print(f"  n={n}: 6 samples, identity holds")
print(f"  worst relative gap over 36 samples: {worst:.2e}")
n = 4; M = rng.normal(size=(n, n)); Jasym = M  # planted: not symmetric
beta = 0.8; h = rng.normal(size=n) + 1j * rng.normal(size=n)
miss = abs(isingZ(Jasym, beta, h) - identity_rhs(Jasym, beta, h)) / abs(isingZ(Jasym, beta, h))
assert miss > 1e-3, miss
print(f"  planted asymmetric J: the identity misses by {miss:.3f} relative (seen)")

# ---------------- B. The zeros ----------------
print("B. The zeros in one common field")
def fugacity_coeffs(J, beta):
    n = J.shape[0]; a = np.exp(-2 * beta * J); c = np.zeros(n + 1)
    for r in range(n + 1):
        for S in itertools.combinations(range(n), r):
            Sc = [j for j in range(n) if j not in S]
            w = 1.0
            for i in S:
                for j in Sc:
                    w *= a[i, j]
            c[r] += w
    return c  # Z / prefactor = sum_r c_r z^r

worst_dev = 0.0
for n in range(2, 11):
    for _ in range(4):
        M = np.abs(rng.normal(size=(n, n))); J = (M + M.T) / 2 * rng.uniform(0.2, 1.5)
        beta = rng.uniform(0.2, 2.0)
        c = fugacity_coeffs(J, beta)
        assert np.allclose(c, c[::-1], rtol=1e-12), "palindrome"
        roots = np.roots(c[::-1])
        dev = float(np.max(np.abs(np.abs(roots) - 1)))
        worst_dev = max(worst_dev, dev)
        assert dev < 1e-7, (n, dev)
print(f"  ferromagnets n = 2..10, 36 samples: every root on |z| = 1, worst deviation {worst_dev:.2e}; coefficients palindromic")
off = 0; trials = 0; far = 0.0
for n in range(2, 9):
    for _ in range(4):
        M = -np.abs(rng.normal(size=(n, n))); J = (M + M.T) / 2
        beta = rng.uniform(0.5, 2.0)
        roots = np.roots(fugacity_coeffs(J, beta)[::-1])
        d = float(np.max(np.abs(np.abs(roots) - 1)))
        trials += 1
        if d > 1e-3:
            off += 1; far = max(far, d)
assert off > trials / 2, (off, trials)
print(f"  planted antiferromagnets n = 2..8: {off} of {trials} samples have a root off the circle (largest | |z| - 1 | = {far:.3f}) (seen)")
for K, beta in [(0.5, 1.0), (1.0, 0.3), (2.0, 2.0)]:
    y = math.exp(2 * beta * K)
    zeta = -1 / (y + math.sqrt(y * y - 1))  # the root -y + sqrt(y^2 - 1), in the form free of cancellation
    J2 = np.array([[-K, -K], [-K, -K]])
    hz = cmath.log(zeta) / (2 * beta)
    Zv = isingZ(J2, beta, np.array([hz, hz]))
    scale = abs(isingZ(J2, beta, np.array([0j, 0j])))
    assert abs(Zv) / scale < 1e-10 and abs(hz.real) > 1e-6, (K, beta, Zv, hz)
    print(f"  two sites, exchange -{K} at beta {beta}: zeta = {zeta:.6f}, |zeta| != 1, h = {hz.real:.6f} + {hz.imag:.6f} i, Z(h)/Z(0) = {abs(Zv)/scale:.1e}")

# ---------------- C. The Curie-Weiss edge ----------------
print("C. The least zero angle on the Curie-Weiss ferromagnet")
def cw_min_angle(n, beta):
    c = np.array([math.comb(n, k) * math.exp(-2 * beta * k * (n - k) / n) for k in range(n + 1)])
    roots = np.roots(c[::-1])
    assert np.max(np.abs(np.abs(roots) - 1)) < 1e-6
    return float(np.min(np.abs(np.angle(roots))))
res = {}
for beta in (2.0, 0.5):
    row = [(n, cw_min_angle(n, beta)) for n in (4, 6, 8, 10, 12, 14)]
    res[beta] = dict(row)
    print(f"  beta = {beta}: " + ", ".join(f"n={n}: {t:.4f}" for n, t in row))
r_ord = res[2.0][14] / res[2.0][4]; r_dis = res[0.5][14] / res[0.5][4]
print(f"  ratio n=14 / n=4: ordered {r_ord:.3f}, disordered {r_dis:.3f}")
assert r_ord < 0.5 and r_dis > 0.5, (r_ord, r_dis)

print(f"all sections pass; {time.time() - T0:.1f} s")
