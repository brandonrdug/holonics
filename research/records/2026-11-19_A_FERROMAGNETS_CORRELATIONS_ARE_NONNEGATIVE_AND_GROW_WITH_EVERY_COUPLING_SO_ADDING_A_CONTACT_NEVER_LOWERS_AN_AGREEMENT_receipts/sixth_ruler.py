"""Host ruler for the sixth set of November 19 (Griffiths' inequalities for many-body ferromagnets and
the growth of their correlations with every coupling).  Every check is an assert; each null is held
to a planted instance in the same run.  Double floats for weights, sums and averages, printed as the
ruler's readings; the statements are the Lean module's
(HolonicsResearch/Coupling/GriffithsInequalities.lean)."""
import itertools, math, time
import numpy as np

T0 = time.time()
rng = np.random.default_rng(20261119 + 6)

PREDICTIONS = {
    "A": "on n = 3..7 sites with random families of 4 to 10 interactions on sets of 1 to 4 sites and couplings "
         "J >= 0, corr(B) >= 0 for every set B, and corr(B) corr(C) <= Z corr2(B, C) for every pair (B, C) "
         "(all pairs for n <= 5, 400 random pairs above), each to 1e-12 relative; one negative coupling (two "
         "sites at J = -1, the planted instance) makes corr({0, 1}) negative",
    "B": "the spin sum of a monomial equals prod_i (1 + (-1)^k_i) on 50 random exponent vectors; the "
         "derivative of <s^B> along J + t delta equals sum_a delta_a (corr2(B, A_a) Z - corr(B) corr(A_a)) / Z^2 "
         "against a central difference to 1e-6 relative",
    "C": "along a segment 0 <= J <= J' sampled at 21 points, <s^B> never decreases for every B on 20 random "
         "ferromagnets; on the frustrated triangle J12 = J23 = -2 (the planted instance), raising J13 from 0 to "
         "2 lowers <s1 s2>",
}

def configs(n):
    return [frozenset(S) for r in range(n + 1) for S in itertools.combinations(range(n), r)]

def spin(S, i):
    return 1.0 if i in S else -1.0

def sprod(S, A):
    p = 1.0
    for i in A:
        p *= spin(S, i)
    return p

def model(n, A, J):
    Cs = configs(n)
    w = np.array([math.exp(sum(J[a] * sprod(S, A[a]) for a in range(len(A)))) for S in Cs])
    return Cs, w

def corr(Cs, w, B):
    return float(sum(sprod(S, B) * w[k] for k, S in enumerate(Cs)))

def corr2(Cs, w, B, C):
    return float(sum(sprod(S, B) * sprod(S, C) * w[k] for k, S in enumerate(Cs)))

def random_family(n):
    m = int(rng.integers(4, 11))
    A = [tuple(sorted(rng.choice(n, size=int(rng.integers(1, min(4, n) + 1)), replace=False))) for _ in range(m)]
    return A

# ---------------- A. The two inequalities ----------------
print("A. Griffiths' first and second inequalities on many-body ferromagnets")
min_first = math.inf; min_second = math.inf
for n in range(3, 8):
    for _ in range(4):
        A = random_family(n); J = rng.uniform(0, 1.2, size=len(A))
        Cs, w = model(n, A, J); Z = float(w.sum())
        subsets = configs(n)
        for B in subsets:
            c = corr(Cs, w, B)
            assert c >= -1e-12 * Z, (n, B, c)
            min_first = min(min_first, c / Z)
        if n <= 5:
            pairs = [(B, C) for B in subsets for C in subsets]
        else:
            pairs = [(subsets[rng.integers(len(subsets))], subsets[rng.integers(len(subsets))]) for _ in range(400)]
        for B, C in pairs:
            gap = Z * corr2(Cs, w, B, C) - corr(Cs, w, B) * corr(Cs, w, C)
            assert gap >= -1e-12 * Z * Z, (n, B, C, gap)
            min_second = min(min_second, gap / (Z * Z))
    print(f"  n={n}: 4 families, first and second inequalities hold")
print(f"  least <s^B> = {min_first:.3e}; least <s^B s^C> - <s^B><s^C> = {min_second:.3e}")
Cs, w = model(2, [(0, 1)], [-1.0])
c01 = corr(Cs, w, (0, 1)) / float(w.sum())
assert c01 < 0
print(f"  planted antiferromagnet, two sites at J = -1: <s0 s1> = {c01:.6f} < 0 (seen)")

# ---------------- B. The monomial sum and the derivative ----------------
print("B. The monomial's spin sum and the derivative along a segment")
for _ in range(50):
    n = int(rng.integers(1, 7)); k = rng.integers(0, 5, size=n)
    lhs = sum(np.prod([spin(S, i) ** k[i] for i in range(n)]) for S in configs(n))
    rhs = np.prod([1 + (-1.0) ** k[i] for i in range(n)])
    assert abs(lhs - rhs) < 1e-9, (k, lhs, rhs)
print("  50 exponent vectors: sum equals prod_i (1 + (-1)^k_i)")
worst = 0.0
for _ in range(12):
    n = int(rng.integers(3, 7)); A = random_family(n)
    J = rng.uniform(0, 1, size=len(A)); d = rng.uniform(0, 1, size=len(A))
    B = tuple(sorted(rng.choice(n, size=int(rng.integers(1, n + 1)), replace=False)))
    t = float(rng.uniform(0.1, 0.9))
    def avg_at(tt):
        Cs, w = model(n, A, J + tt * d)
        return corr(Cs, w, B) / float(w.sum())
    h = 1e-5
    fd = (avg_at(t + h) - avg_at(t - h)) / (2 * h)
    Cs, w = model(n, A, J + t * d); Z = float(w.sum())
    formula = sum(d[a] * (corr2(Cs, w, B, A[a]) * Z - corr(Cs, w, B) * corr(Cs, w, A[a])) for a in range(len(A))) / Z ** 2
    # where the derivative vanishes by a symmetry the central difference reads roundoff, about 1e-12,
    # so the gap is read against 1e-6 relative with an absolute floor of 1e-8
    gap = abs(fd - formula)
    assert gap < 1e-6 * abs(formula) + 1e-8, (fd, formula)
    if abs(formula) > 1e-8:
        worst = max(worst, gap / abs(formula))
print(f"  12 segments: formula against central difference, worst relative gap {worst:.2e} where the derivative is above 1e-8")

# ---------------- C. Growth with every coupling ----------------
print("C. The correlations grow along a segment of couplings")
least_step = math.inf
for _ in range(20):
    n = int(rng.integers(3, 7)); A = random_family(n)
    J = rng.uniform(0, 1, size=len(A)); Jp = J + rng.uniform(0, 1, size=len(A)) * (rng.random(len(A)) < 0.6)
    for B in configs(n):
        vals = []
        for t in np.linspace(0, 1, 21):
            Cs, w = model(n, A, J + t * (Jp - J))
            vals.append(corr(Cs, w, B) / float(w.sum()))
        steps = np.diff(vals)
        least_step = min(least_step, float(steps.min()))
        assert steps.min() >= -1e-12, (B, steps.min())
print(f"  20 ferromagnets, every B, 21 points: no decrease (least step {least_step:.2e})")
A = [(0, 1), (1, 2), (0, 2)]
vals = []
for j13 in (0.0, 1.0, 2.0):
    Cs, w = model(3, A, [-2.0, -2.0, j13])
    vals.append(corr(Cs, w, (0, 1)) / float(w.sum()))
assert vals[2] < vals[0]
print("  planted frustrated triangle J12 = J23 = -2: <s1 s2> at J13 = 0, 1, 2 reads " + ", ".join(f"{v:.6f}" for v in vals) + " (falls; seen)")

print(f"all sections pass; {time.time() - T0:.1f} s")
