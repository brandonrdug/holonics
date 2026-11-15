"""A ruler for the record of November 15 (19:00Z): where distributing configurations saves time.

Public arithmetic only. Every check is an assert. Run: python3 parallel_ruler.py
1. An affine chain scans in log depth; a section (a rounding) at each step makes the bracketing matter.
2. Two surfaces by Brent's bound, from the machine's measured ratios: the parallelism above which the card wins.
3. Energy per bit on a thermal channel against the breadth a rate is spread over (Shannon's wideband limit).
4. Diversity is subtracted: the ambiguity decompositions for squared loss (Krogh-Vedelsby) and for log loss
   under log-linear pooling (Heskes).
5. A one-dimensional small world is navigable by greedy routing at reach falloff 1/d (Kleinberg), and the
   contact's octave staircase 2^-floor(log2 d) is that falloff.
6. A crowd heard at its mean word: its error in nats of share is bounded by the crowd's spread and radius
   times the receiver's slip against the crowd's mean arriving face.
"""
import math, random
from fractions import Fraction

random.seed(20261115)

# ---------- 1. affine chain: serial, tree, and with a section a step ----------
def compose(f, g):            # apply f then g; affine map x -> a x + b as (a, b)
    a1, b1 = f; a2, b2 = g
    return (a2 * a1, a2 * b1 + b2)

def tree_prefix(maps):        # Hillis-Steele inclusive scan, depth ceil(log2 n)
    out = list(maps); d, depth = 1, 0
    while d < len(out):
        out = [out[i] if i < d else compose(out[i - d], out[i]) for i in range(len(out))]
        d *= 2; depth += 1
    return out, depth

n = 1000
maps = [(random.randint(-3, 3), random.randint(-50, 50)) for _ in range(n)]
x0 = 7
serial, x = [], x0
for a, b in maps:
    x = a * x + b; serial.append(x)
pref, depth = tree_prefix(maps)
assert [a * x0 + b for a, b in pref] == serial, "an affine chain is a prefix product"
assert depth == math.ceil(math.log2(n)) == 10
# a contracting chain whose store is rounded every step (a section inside the chain)
def rnd(q, g=16):             # release to grain 2^-g, a section
    return Fraction(round(q * 2**g), 2**g)
gam = [Fraction(random.choice([4, -4, 9, -9]), 10 if random.random() < .5 else 5) for _ in range(n)]
gam = [g if abs(g) < 1 else g / 2 for g in gam]
drive = [Fraction(random.randint(-2**10, 2**10), 2**12) for _ in range(n)]
q, ser = Fraction(0), []
for g_, k in zip(gam, drive):
    q = rnd(g_ * q) + k; ser.append(q)
pr, _ = tree_prefix([(g_, k) for g_, k in zip(gam, drive)])
unr = [b for a, b in pr]     # the unreleased orbit, released once at the read
diff = sum(1 for s, u in zip(ser, unr) if rnd(u) != s)
gap = max(abs(rnd(u) - s) for s, u in zip(ser, unr)) * 2**16
print(f"1. affine chain of {n}: tree depth {depth} = ceil(log2 n), serial equal; with a section a step,"
      f" {diff} of {n} reads differ from the once-released orbit, the largest by {float(gap):.0f} grains")
assert diff > 0

# ---------- 2. two surfaces by Brent: card against host ----------
card_lanes = 10240           # the card's lanes (published; tower.field-engine-count)
host_lane_over_card = 234    # one host lane's time for a region over the card's (November 7 split, the flock record)
s = card_lanes / host_lane_over_card   # card lanes one host lane matches, at most (the card under full occupancy)
def critical(p_host):        # W/D above which T_card < T_host; terms in a host lane's time
    return (s - 1) / (1 / p_host - s / card_lanes)
for p in (12, 24):
    print(f"2. host of {p} lanes: one host lane = at most {s:.1f} card lanes; the card wins past W/D = {critical(p):.0f}")
assert 500 < critical(12) < 600 and 1100 < critical(24) < 1200
t_launch, t_cross = 23e-6, 94e-6   # least launch, mean transfer (November 11 lap)
print(f"   a chain of launches: each step costs the card at least {t_launch*1e6:.0f} us; a step moved to the host adds"
      f" a crossing of {t_cross*1e6:.0f} us each way, so only a chain whose terms already stand on the host moves")

# ---------- 3. energy per bit against breadth ----------
def eb_over_n0(r):           # Shannon: at r bits a channel use, Eb/N0 >= (2^r - 1)/r
    return math.expm1(r * math.log(2)) / r
R = 8.0                      # bits a tick to carry
prev = math.inf
rows = []
for N in (1, 2, 4, 8, 16, 64, 1024):
    e = eb_over_n0(R / N); rows.append((N, e))
    assert e < prev; prev = e
assert abs(eb_over_n0(1e-9) - math.log(2)) < 1e-8
print("3. Eb/N0 at 8 bits a tick spread over N channels: " +
      ", ".join(f"N={N}: {e:.3f}" for N, e in rows) + f"; the floor ln 2 = {math.log(2):.4f} (with N0 = kT, Landauer's kT ln 2)")
# silicon: energy per op ~ C V^2, V rising with f: per op ~ f^2 at fixed throughput across N lanes
print("   dynamic energy per op ~ f^2 where V follows f: N lanes at f/N do the same work at 1/N^2 of the energy per op")

# ---------- 4. diversity is subtracted ----------
for trial in range(200):
    M = random.randint(2, 9)
    y = Fraction(random.randint(-100, 100), 7)
    f = [Fraction(random.randint(-100, 100), 3) for _ in range(M)]
    fb = sum(f) / M
    lhs = (fb - y) ** 2
    rhs = sum((fi - y) ** 2 for fi in f) / M - sum((fi - fb) ** 2 for fi in f) / M
    assert lhs == rhs
worst = 0.0
for trial in range(300):
    K, M = random.randint(2, 12), random.randint(2, 8)
    P = []
    for _ in range(M):
        w = [random.random() ** 3 + 1e-9 for _ in range(K)]; t = sum(w); P.append([v / t for v in w])
    qv = [random.random() for _ in range(K)]; t = sum(qv); qv = [v / t for v in qv]
    g = [math.exp(sum(math.log(P[i][k]) for i in range(M)) / M) for k in range(K)]
    Z = sum(g); pt = [v / Z for v in g]
    ce = lambda qq, pp: -sum(a * math.log(b) for a, b in zip(qq, pp) if a > 0)
    kl = lambda pp, rr: sum(a * math.log(a / b) for a, b in zip(pp, rr) if a > 0)
    lhs = ce(qv, pt)
    rhs = sum(ce(qv, P[i]) for i in range(M)) / M - sum(kl(pt, P[i]) for i in range(M)) / M
    worst = max(worst, abs(lhs - rhs))
    assert abs(-math.log(Z) - sum(kl(pt, P[i]) for i in range(M)) / M) < 1e-10
assert worst < 1e-10
print(f"4. squared loss: (mean f - y)^2 = mean (f_i - y)^2 - mean (f_i - mean f)^2 on 200 draws, in rationals;"
      f" log loss under log-linear pooling: CE(q, pooled) = mean CE(q, p_i) - mean KL(pooled || p_i) on 300 draws"
      f" (largest gap {worst:.1e}), and the subtracted term is -log Z >= 0")

# ---------- 5. navigability of a ring with one long tie a site ----------
def greedy_steps(Nn, weight, routes=600):
    ds = list(range(2, Nn // 2 + 1))
    w = [weight(d) for d in ds]; tot = sum(w)
    cum, c = [], 0.0
    for v in w:
        c += v / tot; cum.append(c)
    import bisect
    long = []
    for u in range(Nn):
        d = ds[min(bisect.bisect_left(cum, random.random()), len(ds) - 1)]
        long.append((u + d) % Nn if random.random() < .5 else (u - d) % Nn)
    dist = lambda a, b: min((a - b) % Nn, (b - a) % Nn)
    steps = 0
    for _ in range(routes):
        a, b = random.randrange(Nn), random.randrange(Nn)
        while a != b:
            cands = [(a + 1) % Nn, (a - 1) % Nn, long[a]]
            a = min(cands, key=lambda c: dist(c, b)); steps += 1
    return steps / routes
res = {}
for Nn in (2**10, 2**14):
    for name, wt in (("r=0", lambda d: 1.0), ("r=1/2", lambda d: d ** -.5), ("r=1", lambda d: 1 / d),
                     ("octave", lambda d: 2.0 ** -math.floor(math.log2(d))), ("r=3/2", lambda d: d ** -1.5), ("r=2", lambda d: d ** -2.0)):
        res[(Nn, name)] = greedy_steps(Nn, wt)
for Nn in (2**10, 2**14):
    print(f"5. ring of {Nn}, greedy steps: " + ", ".join(f"{k}: {res[(Nn, k)]:.0f}" for k in ("r=0", "r=1/2", "r=1", "octave", "r=3/2", "r=2")))
big = 2**14
assert min(res[(big, k)] for k in ("r=0", "r=1/2", "r=3/2", "r=2")) > max(res[(big, "r=1")], res[(big, "octave")])
grow = {k: res[(2**14, k)] / res[(2**10, k)] for k in ("r=0", "r=1", "octave", "r=2")}
print("   growth from 2^10 to 2^14 places: " + ", ".join(f"{k} x{v:.2f}" for k, v in grow.items()) +
      f"  (log^2 ratio {(14/10)**2:.2f}; n^(1/2) ratio 4.00)")
assert grow["r=1"] < 2.6 and grow["octave"] < 2.6 and grow["r=0"] > 3 and grow["r=2"] > 3

# ---------- 6. a crowd heard at its mean word ----------
def lock(a, b, D):           # 2 D Re<a, b> - D^2 |b|^2, modes complex
    return 2 * D * sum((x.conjugate() * y).real for x, y in zip(a, b)) - D * D * sum(abs(y) ** 2 for y in b)
worst_lo = worst_hi = 0.0
for trial in range(400):
    n_m = random.randint(2, 8); C = random.randint(2, 40)
    T, D = random.uniform(.2, 6), random.uniform(.05, 1)
    a = [complex(random.gauss(0, 1), random.gauss(0, 1)) for _ in range(n_m)]
    ctr = [complex(random.gauss(0, 1), random.gauss(0, 1)) for _ in range(n_m)]
    sp = random.uniform(.001, 1)
    B = [[c + complex(random.gauss(0, sp), random.gauss(0, sp)) for c in ctr] for _ in range(C)]
    bbar = [sum(b[l] for b in B) / C for l in range(n_m)]
    ex = math.log(sum(math.exp(T * lock(a, b, D)) for b in B) / C)
    cr = T * lock(a, bbar, D)
    delta = ex - cr
    s2 = sum(sum(abs(b[l] - bbar[l]) ** 2 for l in range(n_m)) for b in B) / C
    rC = max(math.sqrt(sum(abs(b[l] - bbar[l]) ** 2 for l in range(n_m))) for b in B)
    slip = math.sqrt(sum(abs(a[l] - D * bbar[l]) ** 2 for l in range(n_m)))   # the receiver against the crowd's mean arriving face
    lo, hi = -T * D * D * s2, 2 * T * D * slip * rC
    assert lo - 1e-9 <= delta <= hi + 1e-9
    worst_lo = max(worst_lo, (lo - delta) / max(abs(lo), 1e-12)); worst_hi = max(worst_hi, (delta - hi) / max(hi, 1e-12))
print("6. a crowd at its mean word on 400 draws: -T D^2 s^2 <= log mean_j e^(T lock_j) - T lock(mean b) <= 2 T D |a - D mean b| r_C"
      " (s^2 the members' mean square spread, r_C their largest distance from the mean): held on every draw")
