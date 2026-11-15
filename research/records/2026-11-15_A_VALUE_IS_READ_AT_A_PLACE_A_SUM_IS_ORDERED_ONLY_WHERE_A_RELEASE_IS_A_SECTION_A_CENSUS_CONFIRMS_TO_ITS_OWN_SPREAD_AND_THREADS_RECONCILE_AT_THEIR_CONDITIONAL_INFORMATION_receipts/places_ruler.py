"""Rulers for the record of November 15 on values read at a place (stand-in Python, host arithmetic).

Each section prints its checks; every check is an assert. Integers and Fractions throughout, except where a
platform double is the object being read (section 1). Run: python3 places_ruler.py
"""
from fractions import Fraction as F
import math
import random

rng = random.Random(20261115)
W = 64
MOD = 1 << W


def wrap(x):
    """The two's-complement section of Z/2^64: the 2-adic word read at the real place."""
    x %= MOD
    return x - MOD if x >= 1 << (W - 1) else x


def rel(x, bits):
    """The card's release: x / 2^bits to the nearest, half away from zero (kernels/field.cu, rel)."""
    if bits == 0:
        return x
    half = 1 << (bits - 1)
    return (x + half) >> bits if x >= 0 else -((-x + half) >> bits)


def rel_frac(x):
    """A Fraction released once to the nearest integer, half away from zero."""
    n = abs(x.numerator) * 2 + x.denominator
    v = n // (2 * x.denominator)
    return v if x >= 0 else -v


print("1. A quotient commutes with every bracketing; a section commutes only once")
# 1a. A sum on Z/2^64 whose partial sums leave the section but whose total stands inside it.
terms = [rng.randrange(-(1 << 62), 1 << 62) for _ in range(4096)]
shift = sum(terms) // len(terms)
terms = [t - shift for t in terms]  # total brought inside the section
total = sum(terms)
assert -(1 << 63) <= total < 1 << 63
outs, overflows = set(), 0
for trial in range(200):
    order = terms[:]
    rng.shuffle(order)
    acc = 0
    for t in order:
        s = acc + t
        if not (-(1 << 63) <= s < 1 << 63):
            overflows += 1
        acc = wrap(s)
    outs.add(acc)
assert outs == {total}
print(f"   wrapping sum, 4,096 terms, 200 orders: one result, the total; {overflows} partial sums left the section")

# 1b. A section per term before a free sum commutes; a section after every add does not.
outs = set()
for trial in range(200):
    order = [rel(t, 20) for t in terms]  # every term on the grain first: a section per term, then a free sum
    rng.shuffle(order)
    outs.add(sum(order))
assert len(outs) == 1
outs = set()
for trial in range(200):
    order = terms[:]
    rng.shuffle(order)
    acc = 0
    for t in order:
        acc = rel(acc + t, 1) * 2  # a section after every add: the grain moves the partial
    outs.add(acc)
print(f"   released after every add (grain 2): {len(outs)} distinct results over 200 orders")
assert len(outs) > 1

# 1c. Platform doubles: the plain sum follows its order; the sum with each add's remainder carried (TwoSum) and
# released once gives one result, the rounding of the rational total.
def two_sum(a, b):
    s = a + b
    bb = s - a
    e = (a - (s - bb)) + (b - bb)
    return s, e


xs = [rng.uniform(-1, 1) * 2.0 ** rng.randrange(-20, 20) for _ in range(2000)]
exact = sum(F(x) for x in xs)
plain, carried = set(), set()
for trial in range(100):
    order = xs[:]
    rng.shuffle(order)
    acc = 0.0
    for x in order:  # one rounding after every add (Python's own sum() carries a remainder since 3.12)
        acc = acc + x
    plain.add(acc)
    # Shewchuk's expansion (grow-expansion): the running sum as non-overlapping doubles, nothing dropped
    parts = []
    for x in order:
        q = x
        nxt = []
        for p in parts:
            q, e = two_sum(q, p)
            if e:
                nxt.append(e)
        nxt.append(q)
        parts = nxt
    assert sum(F(p) for p in parts) == exact  # the expansion holds the whole rational total
    carried.add(math.fsum(parts))
assert carried == {float(exact)}
print(f"   doubles, 2,000 terms over 40 binades, 100 orders: plain sum {len(plain)} distinct results;")
print(f"   with every add's remainder carried (TwoSum expansion): the expansion equals the rational total in every")
print(f"   order and its one release is {len(carried)} result, the rational total's nearest double")
assert len(plain) > 1

print("2. Two places reconstruct a total: low digits on Z/2^w, a coarse reading at the real place")
w = 32
for trial in range(20000):
    x = rng.randrange(-(1 << 90), 1 << 90)
    r = x % (1 << w)  # the 2-adic register: order-free, narrow
    a = x + rng.randrange(-(1 << (w - 1)) + 1, 1 << (w - 1))  # a coarse reading, error under half the modulus
    k = (r - a) % (1 << w)
    if k >= 1 << (w - 1):
        k -= 1 << w
    assert a + k == x
print("   20,000 totals of 91 bits: recovered from 32 low bits and a reading off by less than 2^31")

print("3. The carry circle's chain: a section every step holds a charge no leak removes")
MOVE, FACE = 30, 16


def gate(mag, angle):
    g = mag * complex(math.cos(angle), math.sin(angle))
    return (round(g.real * (1 << MOVE)), round(g.imag * (1 << MOVE)))


def step_released(q, g, d):
    qr, qi = q
    yr, yi = g
    return (d[0] + rel(yr * qr - yi * qi, MOVE), d[1] + rel(yr * qi + yi * qr, MOVE))


worst = {}
for mag in (0.25, 0.5, 0.6, 0.8, 0.9):
    held = 0
    for trial in range(400):
        g = gate(mag, rng.uniform(0, 2 * math.pi))
        q = (rng.randrange(-200, 201), rng.randrange(-200, 201))
        for _ in range(400):  # zero drive: the circle should leak to nothing
            q = step_released(q, g, (0, 0))
        held = max(held, math.isqrt(q[0] * q[0] + q[1] * q[1]))
    worst[mag] = held
    bound = 0.5 * math.sqrt(2) / (1 - mag)  # the dead band: half a grain a part, summed over the group 1/(1 - |γ|)
    assert held <= bound + 1, (mag, held, bound)
print("   zero drive, 400 steps, 400 gates each: the largest charge still held (grains of 2^-16)")
print("   " + ", ".join(f"|γ| {m}: {worst[m]}" for m in worst))
assert worst[0.25] == 0 and worst[0.8] >= 1

# The same chain unreleased (Fractions), then released once a site: its bits do not depend on the bracketing.
def affine_compose(f, g):  # apply f then g: x -> g.a (f.a x + f.b) + g.b
    return (g[0] * f[0], g[0] * f[1] + g[1])


diff_max = 0
for trial in range(50):
    mag = 0.8
    n = 64
    gates = [complex(*[c / (1 << MOVE) for c in gate(mag, rng.uniform(0, 2 * math.pi))]) for _ in range(n)]
    gates = [(F(round(g.real * (1 << MOVE)), 1 << MOVE), F(round(g.imag * (1 << MOVE)), 1 << MOVE)) for g in gates]
    drives = [(F(rng.randrange(-3000, 3001)), F(rng.randrange(-3000, 3001))) for _ in range(n)]

    def cmul(a, b):
        return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

    def cadd(a, b):
        return (a[0] + b[0], a[1] + b[1])

    maps = [(gates[t], drives[t]) for t in range(n)]  # Q_t = γ_t Q_(t-1) + d_t

    def comp(f, g):
        return (cmul(g[0], f[0]), cadd(cmul(g[0], f[1]), g[1]))

    # serial prefix and a tree (Hillis-Steele) prefix in Fractions: one orbit
    serial, acc = [], ((F(1), F(0)), (F(0), F(0)))
    for m in maps:
        acc = comp(acc, m)
        serial.append(acc[1])
    tree = maps[:]
    span = 1
    while span < n:
        tree = [tree[i] if i < span else comp(tree[i - span], tree[i]) for i in range(n)]
        span *= 2
    assert [t[1] for t in tree] == serial
    once = [(rel_frac(x[0]), rel_frac(x[1])) for x in serial]
    # the card's chain: a release after every product
    q, chain = (0, 0), []
    for t in range(n):
        g = (int(gates[t][0] * (1 << MOVE)), int(gates[t][1] * (1 << MOVE)))
        q = step_released(q, g, (int(drives[t][0]), int(drives[t][1])))
        chain.append(q)
    for a, b in zip(chain, once):
        diff_max = max(diff_max, abs(a[0] - b[0]), abs(a[1] - b[1]))
bound = 0.5 / (1 - 0.8) + 1
assert diff_max <= bound
print(f"   |γ| 0.8, 64 sites, 50 chains: serial and tree prefixes of the unreleased orbit agree term for term;")
print(f"   the card's released chain stands within {diff_max} grains of the orbit released once (bound {bound:.1f})")

print("4. A census confirms to the grain of its own spread: four charts of one law")
# 4a. Mertens: M(x) = Σ_{n≤x} μ(n) against √x.
N = 2_000_000
mu = [1] * (N + 1)
is_comp = bytearray(N + 1)
primes = []
mu[0] = 0
for i in range(2, N + 1):
    if not is_comp[i]:
        primes.append(i)
        mu[i] = -1
    for p in primes:
        if p * i > N:
            break
        is_comp[p * i] = 1
        if i % p == 0:
            mu[p * i] = 0
            break
        mu[p * i] = -mu[i]
M, worst_ratio, x = 0, 0.0, 1
marks = {}
for n in range(1, N + 1):
    M += mu[n]
    if n >= 100:
        worst_ratio = max(worst_ratio, abs(M) / math.sqrt(n))
    if n in (10**3, 10**4, 10**5, 10**6, 2 * 10**6):
        marks[n] = M
print("   Mertens M(x): " + ", ".join(f"x = {k}: {v}" for k, v in marks.items()))
print(f"   largest |M(x)|/√x for 100 ≤ x ≤ 2·10^6: {worst_ratio:.3f} (a random ±1 walk of the same density stands near 1)")
assert worst_ratio < 1

# 4b. Hasse: the points of y² = x³ − x mod p sit within 2√p of p + 1.
def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


worst_h = 0.0
for p in primes:
    if p > 3000:
        break
    if p == 2:
        continue
    count = p + 1 + sum(legendre(x * x * x - x, p) for x in range(p))  # projective points
    ap = p + 1 - count
    worst_h = max(worst_h, abs(ap) / (2 * math.sqrt(p)))
    assert abs(ap) <= 2 * math.sqrt(p)
print(f"   y² = x³ − x, odd p < 3000: largest |a_p|/(2√p) = {worst_h:.3f} (never above 1: the curve's own Frobenius)")

# 4c. A bias read by a census: a source agreeing with a key with probability (1 + ε)/2 separates from a fair one
# only once N ε² passes a few units (Matsui's count; the refining grain's √N).
eps = 1 / 64
reads = []
for n_samples in (256, 1024, 4096, 16384, 65536):
    z_vals = []
    for trial in range(60):
        agree = sum(1 for _ in range(n_samples) if rng.random() < (1 + eps) / 2)
        z_vals.append((2 * agree - n_samples) / math.sqrt(n_samples))
    reads.append((n_samples, sum(z_vals) / len(z_vals), n_samples * eps * eps))
print("   bias 1/64: mean z of the census by N (and N ε²): " + ", ".join(f"{n}: {z:.2f} ({ne:.2f})" for n, z, ne in reads))
assert reads[0][1] < 1.0 and reads[-1][1] > 3.0

# 4d. A ring's turn against μ (Davenport): Σ μ(n) e(nα) cancels like a census, for any rotation α.
for alpha in (math.sqrt(2) - 1, (math.sqrt(5) - 1) / 2, 1 / 3, 0.1234567):
    s = sum(mu[n] * complex(math.cos(2 * math.pi * n * alpha), math.sin(2 * math.pi * n * alpha)) for n in range(1, N + 1))
    print(f"   |Σ_(n≤2·10^6) μ(n) e(n·{alpha:.6f})| / √N = {abs(s) / math.sqrt(N):.3f}")
    assert abs(s) / math.sqrt(N) < 3

print("5. Reconciling two readings costs their conditional information (Slepian-Wolf), read by a census of parities")


def h2(p):
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def cascade(a, b, p, passes=4):
    """Brassard-Salvail Cascade: parities of blocks; bisect where they differ; earlier passes re-opened."""
    n = len(a)
    b = b[:]
    leaked = 0
    perms, sizes = [], []
    k1 = max(4, int(0.73 / p))
    for i in range(passes):
        perm = list(range(n)) if i == 0 else rng.sample(range(n), n)
        perms.append(perm)
        sizes.append(k1 * (2 ** i))

    def block_of(i, pos):
        inv = invs[i]
        return inv[pos] // sizes[i]

    invs = []
    for perm in perms:
        inv = [0] * n
        for j, pos in enumerate(perm):
            inv[pos] = j
        invs.append(inv)

    def parity(bits, i, blk):
        perm, k = perms[i], sizes[i]
        return sum(bits[perm[j]] for j in range(blk * k, min(n, (blk + 1) * k))) & 1

    def bisect(i, blk):
        nonlocal leaked
        perm, k = perms[i], sizes[i]
        lo, hi = blk * k, min(n, (blk + 1) * k)
        while hi - lo > 1:
            mid = (lo + hi) // 2
            pa = sum(a[perm[j]] for j in range(lo, mid)) & 1
            pb = sum(b[perm[j]] for j in range(lo, mid)) & 1
            leaked += 1
            if pa != pb:
                hi = mid
            else:
                lo = mid
        return perm[lo]

    for i in range(passes):
        blocks = (n + sizes[i] - 1) // sizes[i]
        stack = []
        for blk in range(blocks):
            leaked += 1
            if parity(a, i, blk) != parity(b, i, blk):
                stack.append((i, blk))
        while stack:
            j, blk = stack.pop()
            if parity(a, j, blk) == parity(b, j, blk):
                continue
            pos = bisect(j, blk)
            b[pos] ^= 1
            for jj in range(i + 1):
                if jj != j:
                    stack.append((jj, block_of(jj, pos)))
    return b, leaked


for p in (0.01, 0.03, 0.05):
    n = 20000
    ratios, residual = [], 0
    for trial in range(5):
        a = [rng.getrandbits(1) for _ in range(n)]
        b = [x ^ (1 if rng.random() < p else 0) for x in a]
        b2, leaked = cascade(a, b, p)
        residual += sum(x != y for x, y in zip(a, b2))
        ratios.append(leaked / (n * h2(p)))
    print(f"   error rate {p}: parities sent / (n h(p)) = {min(ratios):.2f} to {max(ratios):.2f}; bits left unequal in 5 x 20,000: {residual}")
    assert min(ratios) >= 1.0

print("all checks pass")
