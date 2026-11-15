"""A ruler for the record of November 15 (19:15Z): heating, crystallizing and power that follows news.

Public arithmetic only. Every check is an assert. Run: python3 temper_ruler.py
1. Annealing against quench on a spin glass of 14 spins (every state enumerated for the ground):
   the energy left above the ground falls as the cooling slows, and the quench leaves the most.
2. Deterministic annealing (Rose): one codeword over two clusters splits at T_c = 2 lambda_max of the
   data's covariance (distortion |x - y|^2, association e^(-d/T)).
3. Power that follows the channel: water-filling beats equal power wherever channels differ and ties it
   where they are alike; reverse water-filling gives no bits to a component under the water level.
"""
import math, random
random.seed(20261115)

# ---------- 1. annealing against quench ----------
n = 14
J = [[0.0] * n for _ in range(n)]
for i in range(n):
    for j in range(i + 1, n):
        J[i][j] = J[j][i] = random.gauss(0, 1) / math.sqrt(n)
def energy(s):
    return -sum(J[i][j] * s[i] * s[j] for i in range(n) for j in range(i + 1, n))
# ground by enumeration (the sign of spin 0 fixed by symmetry)
best = math.inf
for code in range(1 << (n - 1)):
    s = [1] + [1 if (code >> k) & 1 else -1 for k in range(n - 1)]
    e = energy(s)
    if e < best: best = e
def field(s, i):
    return sum(J[i][j] * s[j] for j in range(n) if j != i)
def run(sweeps, T0=2.0):
    s = [random.choice((-1, 1)) for _ in range(n)]
    total = sweeps * n
    for step in range(total):
        T = T0 * (1 - step / total)
        i = random.randrange(n)
        dE = 2 * s[i] * field(s, i)
        if dE <= 0 or (T > 0 and random.random() < math.exp(-dE / T)):
            s[i] = -s[i]
    # finish by descent to a local minimum (the quench of whatever is left)
    moved = True
    while moved:
        moved = False
        for i in range(n):
            if 2 * s[i] * field(s, i) < 0:
                s[i] = -s[i]; moved = True
    return energy(s) - best
runs = 60
res = {}
for sweeps in (0, 3, 30, 300):
    res[sweeps] = sum(run(sweeps) for _ in range(runs)) / runs
print("1. spin glass of 14 spins, mean energy above the ground over 60 runs: " +
      ", ".join(f"{'quench' if k == 0 else str(k) + ' sweeps'}: {v:.4f}" for k, v in res.items()))
vals = [res[k] for k in (0, 3, 30, 300)]
assert all(a > b for a, b in zip(vals, vals[1:])), vals

# ---------- 2. deterministic annealing: a codeword splits at 2 lambda_max ----------
pts = [(random.gauss(-1.5, .5), random.gauss(0, .5)) for _ in range(300)] + \
      [(random.gauss(1.5, .5), random.gauss(0, .5)) for _ in range(300)]
mx = sum(p[0] for p in pts) / len(pts); my = sum(p[1] for p in pts) / len(pts)
cxx = sum((p[0] - mx) ** 2 for p in pts) / len(pts); cyy = sum((p[1] - my) ** 2 for p in pts) / len(pts)
cxy = sum((p[0] - mx) * (p[1] - my) for p in pts) / len(pts)
lam = (cxx + cyy) / 2 + math.sqrt(((cxx - cyy) / 2) ** 2 + cxy ** 2)
Tc = 2 * lam
ys = [[mx + 1e-3, my], [mx - 1e-3, my]]
T, split_at = 3 * Tc, None
while T > Tc / 3 and split_at is None:
    for _ in range(400):
        acc = [[0.0, 0.0, 0.0], [0.0, 0.0, 0.0]]
        for x, y in pts:
            d = [(x - c[0]) ** 2 + (y - c[1]) ** 2 for c in ys]
            m = min(d); w = [math.exp(-(dk - m) / T) for dk in d]; z = sum(w)
            for k in range(2):
                acc[k][0] += w[k] / z * x; acc[k][1] += w[k] / z * y; acc[k][2] += w[k] / z
        new = [[a[0] / a[2], a[1] / a[2]] for a in acc]
        delta = max(abs(new[k][q] - ys[k][q]) for k in range(2) for q in range(2))
        ys = new
        if delta < 1e-10: break
    gap = math.dist(ys[0], ys[1])
    if gap > 0.1:
        split_at = T
    else:  # re-seed the pair symmetrically about their centroid, as the method does
        c = [(ys[0][0] + ys[1][0]) / 2, (ys[0][1] + ys[1][1]) / 2]
        ys = [[c[0] + 1e-3, c[1]], [c[0] - 1e-3, c[1]]]
        T *= 0.99
print(f"2. two clusters of 300 points: 2 lambda_max = {Tc:.4f}; the codeword split first at T = {split_at:.4f}"
      f" ({split_at / Tc:.3f} of it), cooling by 1% a step")
assert split_at is not None and 0.93 < split_at / Tc <= 1.0

# ---------- 3. power that follows the channel ----------
def waterfill(gains, P):
    lo, hi = 0.0, P + max(1 / g for g in gains)
    for _ in range(200):
        nu = (lo + hi) / 2
        if sum(max(nu - 1 / g, 0) for g in gains) > P: hi = nu
        else: lo = nu
    return [max(lo - 1 / g, 0) for g in gains]
cap = lambda gains, pw: sum(0.5 * math.log2(1 + g * p) for g, p in zip(gains, pw))
worst_tie, gains_won = 0.0, 0
for trial in range(300):
    K = random.randint(2, 16); P = random.uniform(.1, 20)
    g = [random.lognormvariate(0, 1.2) for _ in range(K)]
    wf, eq = waterfill(g, P), [P / K] * K
    assert cap(g, wf) >= cap(g, eq) - 1e-9
    gains_won += cap(g, wf) > cap(g, eq) + 1e-6
    ga = [random.uniform(.1, 5)] * K
    worst_tie = max(worst_tie, abs(cap(ga, waterfill(ga, P)) - cap(ga, [P / K] * K)))
assert worst_tie < 1e-9
# reverse water-filling: a passage whose news comes in bursts
var = [0.01] * 40 + [4.0] * 5 + [0.01] * 40 + [9.0] * 3 + [0.01] * 40
def reverse(var, D):
    lo, hi = 0.0, max(var)
    for _ in range(200):
        th = (lo + hi) / 2
        if sum(min(th, v) for v in var) > D: hi = th
        else: lo = th
    return lo, [0.5 * math.log2(v / min(lo, v)) for v in var]
th, bits = reverse(var, D=0.5 * len(var) * 0.05)
quiet = [b for v, b in zip(var, bits) if v <= th]
assert all(b == 0 for b in quiet) and sum(bits) > 0
print(f"3. water-filling over 300 draws: never under equal power, above it in {gains_won} (channels unlike), tied within"
      f" {worst_tie:.0e} where channels are alike; reverse water-filling on a passage of 128 ticks with two bursts:"
      f" level {th:.4f}, the {len(quiet)} quiet ticks get 0 bits, the 8 burst ticks {sum(bits):.2f} bits")
