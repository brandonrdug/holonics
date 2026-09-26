# H1 (R3 D2): the closing-ring moment is lossless only below a capacity, and n* is computed by
# counting, exactly and without sampling.
#
# The persisting source state after n cells is (M_g, C_g(delta) on the source rings, the window win,
# the lift point lambda).  Its number of distinct values is at most
#
#   N(n) = |A|^(max Delta) * prod_g (2n + d_g)
#          * prod_(g in S) [ C(n + d_g|A| - 1, d_g|A| - 1) * prod_(delta in Delta) C(n - delta + d_g|A|^2 - 1, d_g|A|^2 - 1) ]
#
#   - |A|^(max Delta): the window's raw cells (one window, shared by the source rings);
#   - 2n + d_g: ring g ticks at most 2n times in n cells (its own steps plus carries), and a
#     re-keying at an aeon boundary moves only its phase class, so its lift takes at most 2n + d_g values;
#   - C(n + S - 1, S - 1): nonnegative counts on S slots summing to n (first-order counts, S = d_g|A|)
#     or to n - delta (offset counts, S = d_g|A|^2).
#
# n* = the least n with N(n) < |A|^n.  Past n* the map from A^n to the state is not injective
# (pigeonhole), so the moment is lossy by construction.  f(n) = n log2|A| - log2 N(n) is convex with
# f(0) <= 0 (each -log C(n + S - 1, S - 1) and -log(2n + d) is convex), so f > 0 holds at every
# n >= n* once it holds at n*: n* is found by bisection and certified by the exact integer test
# N(n) < |A|^n  <=>  N(n).bit_length() <= n log2|A|   (|A| a power of two).
#
# The moment's exact dense code (each slot self-delimited, max(1, bit length) + 1 bits) is a reading,
# not the capacity: it is longer than log2 N(n), so it crosses later.
import math, random
from fractions import Fraction as F
from field import exact

def log2N_float(n, rings, src, A, deltas):
    """A float bracket only; every n* below is certified by exact integers."""
    lg = lambda m, k: (math.lgamma(m + 1) - math.lgamma(k + 1) - math.lgamma(m - k + 1)) / math.log(2)
    v = (max(deltas) if deltas else 0) * math.log2(A) + sum(math.log2(2 * n + d) for d in rings)
    for g in src:
        d = rings[g]
        v += lg(n + d * A - 1, d * A - 1)
        v += sum(lg(n - dl + d * A * A - 1, d * A * A - 1) for dl in deltas)
    return v

def N_exact(n, rings, src, A, deltas):
    v = A ** (max(deltas) if deltas else 0)
    for d in rings:
        v *= 2 * n + d
    for g in src:
        d = rings[g]
        v *= math.comb(n + d * A - 1, d * A - 1)
        for dl in deltas:
            v *= math.comb(n - dl + d * A * A - 1, d * A * A - 1)
    return v

def lossy(n, rings, src, A, deltas):
    assert A & (A - 1) == 0, "|A| a power of two"
    return N_exact(n, rings, src, A, deltas).bit_length() <= n * (A.bit_length() - 1)

def nstar(rings, src, A, deltas, exact_search=True):
    hi = 1
    f = (lambda n: lossy(n, rings, src, A, deltas)) if exact_search else \
        (lambda n: log2N_float(n, rings, src, A, deltas) < n * math.log2(A))
    while not f(hi):
        hi *= 2
    lo = hi // 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (lo, mid) if f(mid) else (mid, hi)
    # certify exactly: not lossy at n* - 1, lossy at n*
    assert lossy(hi, rings, src, A, deltas) and not lossy(hi - 1, rings, src, A, deltas)
    return hi

def slot_bits(c): return max(1, c.bit_length()) + 1

# 1. The three-ring control: periods 3, 4, 5, |A| = 2, every ring a source ring, no offsets.
rings, A = [3, 4, 5], 2
ns = nstar(rings, [0, 1, 2], A, [])
print(f"three rings of periods 3, 4, 5, |A| = 2 (24 slots): n* = {ns} by counting: "
      f"N(n*) < 2^{ns}, and N(n* - 1) >= 2^{ns - 1}")
for n in (2, 8, 32, 64, 96, 128, 256, 1024, 4096):
    print(f"  n = {n:5d}: log2 N(n) < {N_exact(n, rings, [0, 1, 2], A, []).bit_length():4d}, "
          f"source bits {n:5d}, ratio <= {exact(F(N_exact(n, rings, [0, 1, 2], A, []).bit_length(), n))}")

def moment(src, per, notch, A):
    taus = [0] * len(per); M = [[[0] * A for _ in range(d)] for d in per]
    for x in src:
        carry = 0
        for g, d in enumerate(per):
            new = taus[g] + (1 if x % d in notch[g] else 0) + carry
            carry = 1 if new >= d else 0; taus[g] = new % d
            M[g][taus[g]][x] += 1
    return M

rng = random.Random(1)
print("  the moment's dense code, a reading (max over 50 random sources):")
for n in (8, 32, 64, 96, 128, 144, 256, 1024, 4096):
    worst = max(sum(slot_bits(c) for M in moment([rng.randrange(A) for _ in range(n)], rings, [{1}, {0}, {1}], A)
                    for row in M for c in row) for _ in range(50))
    print(f"    n = {n:5d}: dense code {worst:4d} bits, source bits {n:5d}, ratio {exact(F(worst, n))}")

# 2. Campaign 1's declared field: rings of periods 5, 7, 11, 13; source ring 0; bytes; Delta = {1}.
rings, A = [5, 7, 11, 13], 256
ns = nstar(rings, [0], A, [1])
print(f"campaign 1's field (periods 5, 7, 11, 13; source ring 0 of period 5; |A| = 256; Delta = {{1}}; "
      f"{5 * 256 + 5 * 256 * 256:,} slots): n* = {ns:,} cells")

# 3. One byte ring of period 7 with Delta = {1}: counting against the dense code.
rings = [7]
ns = nstar(rings, [0], A, [1])
first, second = 7 * A, 7 * A * A
dense = next(n for n in range(1000, 10**7, 1000)
             if first * slot_bits(round(F(n, first))) + second * slot_bits(round(F(n, second))) < 8 * n)
print(f"one byte ring of period 7, Delta = {{1}}: n* = {ns:,} by counting; the dense code "
      f"(uniform counts) first falls below the source near {dense:,}")

# 4. A campaign-scale illustration: eight source rings of period 16, bytes, Delta = {1}.
rings = [16] * 8
d, G = 16, 8
first, second = d * A, d * A * A
print(f"campaign-scale illustration (eight source rings of period 16): {G * (first + second):,} slots")
lo = nstar(rings, list(range(8)), A, [1], exact_search=False)   # float bracket, certified exactly
print(f"  n* = {lo:,} cells by counting (certified by exact integers at n* - 1 and n*)")
# the dense code with uniform counts is a step function of n, and its ratio is not monotone:
def mb(n): return G * (first * slot_bits(round(F(n, first))) + second * slot_bits(round(F(n, second))))
def first_below(n, step):
    while mb(n) >= 8 * n:
        n += step
    while mb(n - 1) < 8 * (n - 1):
        n -= 1
    return n
dip = first_below(10**6, 1000)
back = next(n for n in range(dip, 10**8, 1000) if mb(n) >= 8 * n)
last = first_below(back, 1000)
assert all(mb(n) < 8 * n for n in range(last, 16 * 10**6, 997))
print(f"  the dense code (uniform counts), a reading: below the source from n = {dip:,}, above again from "
      f"about {back:,}, and below for good from n = {last:,} "
      f"(ratio {exact(F(mb(4_200_000), 8 * 4_200_000))} at n = 4,200,000, {exact(F(mb(4_300_000), 8 * 4_300_000))} at n = 4,300,000)")
