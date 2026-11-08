#!/usr/bin/env python3
"""Receipts for the 2026-11-08 theory note: a number is a class on a graph of places, the carry is
its boundary, and every method is a chart and a bracketing.

Standalone stand-in checks. No holonics code and no card are run here. Every identity is checked on
integers or Fractions; floats appear only in printed readings (log2 of an error, a mean).
Inputs come from a fixed splitmix64 draw, so the output is reproducible.

Run: python3 -I number_graph.py
"""
import sys
import time
from fractions import Fraction as F
from math import comb, gcd, log, log2

T0 = time.time()
RESULTS = []


def check(name, ok, detail=""):
    RESULTS.append((name, bool(ok)))
    print(("PASS " if ok else "FAIL ") + name + (": " + detail if detail else ""))
    sys.stdout.flush()


def section(title):
    print("\n== " + title + " (t=%.1fs)" % (time.time() - T0))


MASK64 = (1 << 64) - 1


class Draw:
    """splitmix64: a deterministic stream of 64-bit words (inputs for the checks only)."""

    def __init__(self, seed):
        self.s = seed & MASK64

    def u64(self):
        self.s = (self.s + 0x9E3779B97F4A7C15) & MASK64
        z = self.s
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
        return z ^ (z >> 31)

    def bits(self, k):
        v, got = 0, 0
        while got < k:
            v |= self.u64() << got
            got += 64
        return v & ((1 << k) - 1)

    def below(self, n):
        return self.bits(n.bit_length() + 64) % n


D = Draw(20261108)


def bit(v, k):
    return (v >> k) & 1


def s_p(n, p):
    s = 0
    while n:
        s += n % p
        n //= p
    return s


def v_p(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


# ---------------------------------------------------------------------------------------------
section("A. The carry complex: integers are H_0 of Z[x] --(2-x)--> Z[x]; a carry is a boundary")


def normalize(d):
    """Raw place sums d (nonnegative, LSB first) -> canonical binary digits c and carries t."""
    d = list(d) + [0] * (max(d).bit_length() + len(d).bit_length() + 2)
    c, t, carry = [], [], 0
    for dk in d:
        s = dk + carry
        c.append(s & 1)
        carry = s >> 1
        t.append(carry)
    assert carry == 0
    return d, c, t


ok_boundary = ok_value = True
for _ in range(2000):
    n = 1 + D.below(40)
    raw = [D.below(9) for _ in range(n)]  # place sums up to 8: e.g. eight numbers added placewise
    d, c, t = normalize(raw)
    # d - c = (2 - x) t, coefficient by coefficient: d_k - c_k = 2 t_k - t_{k-1}
    for k in range(len(d)):
        if d[k] - c[k] != 2 * t[k] - (t[k - 1] if k else 0):
            ok_boundary = False
    if sum(dk << k for k, dk in enumerate(d)) != sum(ck << k for k, ck in enumerate(c)):
        ok_value = False
check("A1 raw place sums minus canonical digits is the boundary (2-x)*carries", ok_boundary,
      "2000 random raw digit vectors (place sums 0..8)")
check("A1 the boundary evaluates to zero at x=2 (same integer)", ok_value)


def xor_and_loop(a, b):
    it = 0
    while True:
        it += 1
        a, b = a ^ b, (a & b) << 1
        if b == 0:
            return a, it


def longest_chain(a, b, n):
    """Longest carry chain: a generate place followed by consecutive propagate places."""
    best = 0
    for k in range(n):
        if bit(a, k) & bit(b, k):
            length, j = 1, k + 1
            while j < n and (bit(a, j) ^ bit(b, j)):
                length += 1
                j += 1
            best = max(best, length)
    return best


ok_loop, iters = True, []
for _ in range(3000):
    a, b = D.bits(64), D.bits(64)
    s, it = xor_and_loop(a, b)
    iters.append(it)
    if s != a + b or it != 1 + longest_chain(a, b, 64):
        ok_loop = False
check("A2 XOR-and-shift loop: iterations = 1 + longest carry chain (generate, then propagates)",
      ok_loop, "64-bit pairs, mean iterations %.2f (log2 64 = 6)" % (sum(iters) / len(iters)))

# ---------------------------------------------------------------------------------------------
section("B. The modulus is the place graph's closing edge (Smith normal form of the relations)")


def snf(M):
    """Invariant factors of an integer matrix (Smith normal form diagonal), small sizes only."""
    A = [row[:] for row in M]
    m, n = len(A), len(A[0])
    diag = []
    for t in range(min(m, n)):
        while True:
            piv = None
            for i in range(t, m):
                for j in range(t, n):
                    if A[i][j] and (piv is None or abs(A[i][j]) < abs(A[piv[0]][piv[1]])):
                        piv = (i, j)
            if piv is None:
                return diag + [0] * (min(m, n) - t)
            i, j = piv
            A[t], A[i] = A[i], A[t]
            for row in A:
                row[t], row[j] = row[j], row[t]
            p = A[t][t]
            clean = True
            for i in range(t + 1, m):
                q = A[i][t] // p
                if q:
                    for jj in range(t, n):
                        A[i][jj] -= q * A[t][jj]
                if A[i][t]:
                    clean = False
            for j in range(t + 1, n):
                q = A[t][j] // p
                if q:
                    for ii in range(t, m):
                        A[ii][j] -= q * A[ii][t]
                if A[t][j]:
                    clean = False
            if not clean:
                continue
            bad = None
            for i in range(t + 1, m):
                for j in range(t + 1, n):
                    if A[i][j] % p:
                        bad = i
            if bad is None:
                diag.append(abs(p))
                break
            for jj in range(t, n):
                A[t][jj] += A[bad][jj]
    return diag


def relations(n, closing):
    """Columns are relations on n places: 2 e_k - e_(k+1) for k < n-1, then the closing column.
    closing: list of (place, coefficient) added to 2 e_(n-1) for the top carry's return."""
    M = [[0] * n for _ in range(n)]
    for k in range(n - 1):
        M[k][k] = 2
        M[k + 1][k] = -1
    M[n - 1][n - 1] = 2
    for place, coef in closing:
        M[place][n - 1] -= coef
    return M


ok_top = True
rows = []
for n in range(2, 11):
    path = snf(relations(n, []))                      # carry out of the top dropped
    cycle = snf(relations(n, [(0, 1)]))               # end-around carry: 2^n = 1
    twist = snf(relations(n, [(0, -1)]))              # end-around with a sign: 2^n = -1
    xor = snf([[2 if i == j else 0 for j in range(n)] for i in range(n)])  # no carry edges
    pm = snf(relations(n, [(0, 3)]))                  # pseudo-Mersenne 2^n - 3: carry re-enters x3
    ones = [1] * (n - 1)
    ok_top &= path == ones + [2 ** n] and cycle == ones + [2 ** n - 1]
    ok_top &= twist == ones + [2 ** n + 1] and xor == [2] * n and pm == ones + [2 ** n - 3]
    if n in (4, 8):
        rows.append("n=%d path %s cycle %s twist %s xor %s" % (n, path[-1], cycle[-1], twist[-1], xor))
check("B1 path -> Z/2^n, cycle -> Z/(2^n-1), twisted cycle -> Z/(2^n+1), no edges -> (Z/2)^n, "
      "closing weight c -> Z/(2^n-c)", ok_top, "n = 2..10; " + "; ".join(rows))

# Solinas (Goldilocks shape): the top carry re-enters at place 0 and at place m: 2^n - 2^m - 1
ok_sol = True
for n, m_ in ((6, 3), (8, 4), (10, 5), (9, 2)):
    M = relations(n, [(0, 1), (m_, 1)])
    ok_sol &= snf(M) == [1] * (n - 1) + [2 ** n - 2 ** m_ - 1]
check("B1 two closing edges (Solinas shape) -> Z/(2^n - 2^m - 1)", ok_sol, "Goldilocks 2^448-2^224-1 has this shape")

# the ray (no top relation): n relations on n+1 places -> cokernel Z (one free generator)
M = [[0] * 8 for _ in range(9)]
for k in range(8):
    M[k][k], M[k + 1][k] = 2, -1
check("B1 the open ray -> Z (all invariant factors 1, one free place)", snf(M) == [1] * 8)

# ones' complement as a ring: the trace of the carry transfer matrices counts consistent carries
n = 8
ok_trace, doubles = True, 0
for a in range(1 << n):
    for b in range(1 << n):
        # carry transfer matrix at place k: M[cin][cout] = 1 if cout = maj(a_k, b_k, cin)
        P = [[1, 0], [0, 1]]
        for k in range(n):
            ak, bk = bit(a, k), bit(b, k)
            M2 = [[0, 0], [0, 0]]
            for cin in (0, 1):
                M2[cin][(ak & bk) | (ak & cin) | (bk & cin)] = 1
            P = [[P[i][0] * M2[0][j] + P[i][1] * M2[1][j] for j in (0, 1)] for i in (0, 1)]
        tr = P[0][0] + P[1][1]
        if tr == 2:
            doubles += 1
            if a + b != (1 << n) - 1:
                ok_trace = False
        elif tr != 1:
            ok_trace = False
check("B2 ring adder: trace of carry transfer matrices = 1, or 2 exactly when a+b = 2^n-1 "
      "(the two zeros of ones' complement)", ok_trace and doubles == (1 << n),
      "n=8 exhaustive, %d pairs with two consistent end-around carries" % doubles)

# multiplication by the radix is a graph automorphism on the cycle and the twisted cycle
ok_rot = True
for _ in range(2000):
    n = 5 + D.below(40)
    k = D.below(n)
    x = D.bits(n) % ((1 << n) - 1)
    rot = ((x << k) | (x >> (n - k))) & ((1 << n) - 1)
    ok_rot &= (x << k) % ((1 << n) - 1) == rot % ((1 << n) - 1)
    y = D.bits(n)  # y < 2^n
    lo, hi = (y << k) & ((1 << n) - 1), (y << k) >> n
    ok_rot &= (y << k) % ((1 << n) + 1) == (lo - hi) % ((1 << n) + 1)
check("B3 times 2^k: rotation on the cycle (mod 2^n-1); rotation with a sign flip of the wrapped "
      "bits on the twisted cycle (mod 2^n+1)", ok_rot)

# IDEA's three topologies on 16 places: they agree exactly where no carry reaches a closing edge
def idea_mul(x, y):
    r = ((x or 65536) * (y or 65536)) % 65537
    return 0 if r == 65536 else r


agree_free = free = agree_wrap = wrap = 0
for _ in range(20000):
    a, b, c = 1 + D.below(65535), 1 + D.below(65535), 1 + D.below(65535)
    u, v = (a * b) % 65537, (a * c) % 65537              # true residues in 1..65536
    same = idea_mul(a, (b + c) & 0xFFFF) == (idea_mul(a, b) + idea_mul(a, c)) & 0xFFFF
    if b + c < 65536 and u + v <= 65536:                 # no carry reaches either closing edge
        free += 1
        agree_free += same
    else:
        wrap += 1
        agree_wrap += same
check("B4 add mod 2^16 and multiply mod 2^16+1 (IDEA) agree on distributivity exactly where no carry "
      "reaches a closing edge; every failure is a boundary crossing", agree_free == free and agree_wrap <= 3,
      "%d of %d boundary-free triples agree, %d of %d crossing triples agree" % (agree_free, free, agree_wrap, wrap))

# ---------------------------------------------------------------------------------------------
section("C. Addition is an associative product of carry maps; every adder is a bracketing")


def comp(lo, hi):
    """Carry map (p, g): c -> g | (p & c). Lower block then higher block."""
    return (lo[0] & hi[0], hi[1] | (hi[0] & lo[1]))


def leaves(a, b, n):
    return [((bit(a, k) ^ bit(b, k)), (bit(a, k) & bit(b, k))) for k in range(n)]


def ripple(L):
    P, dep, ops = [L[0]], [0], 0
    for k in range(1, len(L)):
        P.append(comp(P[-1], L[k]))
        dep.append(dep[-1] + 1)
        ops += 1
    return P, max(dep), ops


def kogge_stone(L):
    P, dep, ops, d, n = list(L), [0] * len(L), 0, 1, len(L)
    while d < n:
        P2, dep2 = list(P), list(dep)
        for i in range(d, n):
            P2[i] = comp(P[i - d], P[i])
            dep2[i] = max(dep[i - d], dep[i]) + 1
            ops += 1
        P, dep, d = P2, dep2, 2 * d
    return P, max(dep), ops


def sklansky(L):
    P, dep, ops, n = list(L), [0] * len(L), 0, len(L)
    lvl = 0
    while (1 << lvl) < n:
        P2, dep2 = list(P), list(dep)
        for i in range(n):
            if (i >> lvl) & 1:
                j = ((i >> (lvl + 1)) << (lvl + 1)) + (1 << lvl) - 1
                P2[i] = comp(P[j], P[i])
                dep2[i] = max(dep[j], dep[i]) + 1
                ops += 1
        P, dep, lvl = P2, dep2, lvl + 1
    return P, max(dep), ops


def brent_kung(L):
    P, dep, ops, n = list(L), [0] * len(L), 0, len(L)
    d = 1
    while d < n:
        for i in range(2 * d - 1, n, 2 * d):
            P[i] = comp(P[i - d], P[i])
            dep[i] = max(dep[i - d], dep[i]) + 1
            ops += 1
        d *= 2
    d = n // 4
    while d >= 1:
        for i in range(3 * d - 1, n, 2 * d):
            P[i] = comp(P[i - d], P[i])
            dep[i] = max(dep[i - d], dep[i]) + 1
            ops += 1
        d //= 2
    return P, max(dep), ops


def random_bracket(L, lo, hi):
    """Product of L[lo..hi] under a random binary bracketing."""
    if lo == hi:
        return L[lo]
    mid = lo + D.below(hi - lo)
    return comp(random_bracket(L, lo, mid), random_bracket(L, mid + 1, hi))


n = 64
ok_br = True
for _ in range(300):
    a, b = D.bits(n), D.bits(n)
    L = leaves(a, b, n)
    ref, _, _ = ripple(L)
    carries = [ref[k][1] for k in range(n)]  # carry out of place k (carry in 0)
    s = sum(((bit(a, k) ^ bit(b, k) ^ (carries[k - 1] if k else 0)) << k) for k in range(n))
    ok_br &= s + (carries[-1] << n) == a + b
    for f in (kogge_stone, sklansky, brent_kung):
        P, _, _ = f(L)
        ok_br &= [P[k][1] for k in range(n)] == carries
    for k in (5, 17, 40, 63):
        ok_br &= random_bracket(L, 0, k)[1] == carries[k]
shapes = {f.__name__: f(leaves(1, 1, 64))[1:] for f in (ripple, kogge_stone, sklansky, brent_kung)}
check("C1 ripple, Kogge-Stone, Sklansky, Brent-Kung and random bracketings give the same carries",
      ok_br, "64 bits; (depth, products): " + ", ".join("%s %s" % kv for kv in shapes.items()))
check("C1 signatures differ as the theory says", shapes == {
    "ripple": (63, 63), "kogge_stone": (6, 321), "sklansky": (6, 192), "brent_kung": (10, 120)})

# the carry between limbs is one addition of the limbs' generate and propagate masks
ok_mask = True
for code in range(3 ** 8):
    g = p = 0
    x = code
    for i in range(8):
        st = x % 3
        x //= 3
        if st == 1:
            g |= 1 << i
        elif st == 2:
            p |= 1 << i
    c, ripple_in = 0, 0
    for i in range(8):
        ripple_in |= c << i
        c = bit(g, i) | (bit(p, i) & c)
    ok_mask &= (((g | p) + g) ^ p) & 0xFF == ripple_in
check("C2 limb carries = ((g|p) + g) xor p: the carry of a wide sum is a narrow sum (self-similar)",
      ok_mask, "all 3^8 generate/propagate/kill patterns on 8 limbs")

ok_limb = True
for _ in range(3000):
    a, b = D.bits(256), D.bits(256)
    la = [(a >> (32 * i)) & 0xFFFFFFFF for i in range(8)]
    lb = [(b >> (32 * i)) & 0xFFFFFFFF for i in range(8)]
    raw = [la[i] + lb[i] for i in range(8)]
    g = sum(((raw[i] >> 32) & 1) << i for i in range(8))
    p = sum((1 if (raw[i] & 0xFFFFFFFF) == 0xFFFFFFFF else 0) << i for i in range(8))
    cin = ((g | p) + g) ^ p
    out = [((raw[i] + bit(cin, i)) & 0xFFFFFFFF) for i in range(8)]
    total = sum(out[i] << (32 * i) for i in range(8)) + (bit(cin, 8) << 256)
    ok_limb &= total == a + b
check("C2 a 256-bit sum from 8 limbs in parallel plus one 9-bit addition of their carry signals",
      ok_limb, "3000 random pairs")

# signatures of the same count: toggles of a binary counter vs a Gray counter
n = 12
tb = sum(bin(i ^ ((i + 1) % (1 << n))).count("1") for i in range(1 << n))
tg = sum(bin((i ^ (i >> 1)) ^ (((i + 1) % (1 << n)) ^ (((i + 1) % (1 << n)) >> 1))).count("1")
         for i in range(1 << n))
check("C3 same count, two charts: binary counter toggles 2^(n+1)-2 per cycle, Gray counter 2^n",
      tb == 2 ** (n + 1) - 2 and tg == 2 ** n, "n=12: binary %d, Gray %d toggles per 4096 counts" % (tb, tg))

# a ripple adder's settling: glitches on the way to the same sum
n = 32
settle, glitch_total, need_total = [], 0, 0
a0, b0 = D.bits(n), D.bits(n)


def settled(a, b):
    c = [0] * (n + 1)
    for k in range(n):
        c[k + 1] = (bit(a, k) & bit(b, k)) | ((bit(a, k) ^ bit(b, k)) & c[k])
    return c


for _ in range(3000):
    a, b = D.bits(n), D.bits(n)
    c = settled(a0, b0)
    final = settled(a, b)
    s_old = [bit(a0, k) ^ bit(b0, k) ^ c[k] for k in range(n)]
    s_now = [bit(a, k) ^ bit(b, k) ^ c[k] for k in range(n)]
    toggles = sum(x != y for x, y in zip(s_old, s_now))
    steps = 0
    while c != final:
        steps += 1
        c2 = [0] + [(bit(a, k) & bit(b, k)) | ((bit(a, k) ^ bit(b, k)) & c[k]) for k in range(n)]
        s2 = [bit(a, k) ^ bit(b, k) ^ c2[k] for k in range(n)]
        toggles += sum(x != y for x, y in zip(c, c2)) + sum(x != y for x, y in zip(s_now, s2))
        c, s_now = c2, s2
    s_final = [bit(a, k) ^ bit(b, k) ^ final[k] for k in range(n)]
    need = sum(x != y for x, y in zip(s_old, s_final)) + sum(
        x != y for x, y in zip(settled(a0, b0), final))
    settle.append(steps)
    glitch_total += toggles
    need_total += need
    a0, b0 = a, b
check("C3 ripple settling reading (unit gate delay)", True,
      "32 bits: mean settle %.2f steps, max %d; wire toggles %.3f x the necessary changes"
      % (sum(settle) / len(settle), max(settle), glitch_total / need_total))

# ---------------------------------------------------------------------------------------------
section("D. Plural fibres buy locality: redundant digits carry no further than two places")


def sd_value(z):
    return sum(d << k for k, d in enumerate(z))


def sd_add(x, y):
    n = len(x)
    s = [x[k] + y[k] for k in range(n)] + [0, 0]
    t = [0] * (n + 3)
    w = [0] * (n + 2)
    for k in range(n + 2):
        sk, prev = s[k], (s[k - 1] if k else 0)
        if sk == 2:
            t[k + 1], w[k] = 1, 0
        elif sk == -2:
            t[k + 1], w[k] = -1, 0
        elif sk == 1:
            t[k + 1], w[k] = (1, -1) if prev >= 1 else (0, 1)
        elif sk == -1:
            t[k + 1], w[k] = (-1, 1) if prev <= -1 else (0, -1)
    return [w[k] + t[k] for k in range(n + 2)]


ok_sd = ok_local = True
for _ in range(3000):
    n = 4 + D.below(40)
    x = [D.below(3) - 1 for _ in range(n)]
    y = [D.below(3) - 1 for _ in range(n)]
    z = sd_add(x, y)
    ok_sd &= sd_value(z) == sd_value(x) + sd_value(y) and all(d in (-1, 0, 1) for d in z)
    k = 3 + D.below(n - 3)
    x2, y2 = list(x), list(y)
    for j in range(k - 2):  # perturb every digit below the window
        x2[j], y2[j] = D.below(3) - 1, D.below(3) - 1
    ok_local &= sd_add(x2, y2)[k] == z[k]
check("D1 signed-digit sum (digits -1,0,1) is right", ok_sd)
check("D1 each output digit depends only on input places k, k-1, k-2 (perturbing below never moves it)",
      ok_local)
a, b = (1 << 63) - 1, 1
check("D1 contrast: a canonical binary carry crosses all 64 places", bit(a + b, 63) == 1 and bit(a, 63) == 0)

ok_csa = all((x ^ y ^ z) + 2 * ((x & y) | (y & z) | (x & z)) == x + y + z
             for x, y, z in ((D.bits(64), D.bits(64), D.bits(64)) for _ in range(2000)))
dadda = [2]
while dadda[-1] < 4096:
    dadda.append(dadda[-1] * 3 // 2)
stages = {h: next(j for j in range(len(dadda)) if h <= dadda[j]) for h in (3, 16, 64, 256)}
check("D2 3:2 compressor: x+y+z = (x^y^z) + 2*maj(x,y,z), constant depth; Dadda stages",
      ok_csa and stages[64] == 10, "stages to reduce a column of height h to 2: %s" % stages)


def naf(k):
    out = []
    while k:
        if k & 1:
            d = 2 - (k % 4)
            k -= d
        else:
            d = 0
        out.append(d)
        k //= 2
    return out


ok_naf, nz, places = True, 0, 0
for k in range(1, 1 << 16):
    z = naf(k)
    ok_naf &= sd_value(z) == k and all(not (z[i] and z[i + 1]) for i in range(len(z) - 1))
    nz += sum(1 for d in z if d)
    places += len(z)
# uniqueness: count non-adjacent strings of length L by value
from itertools import product as iproduct
L_ = 10
seen = {}
for z in iproduct((-1, 0, 1), repeat=L_):
    if all(not (z[i] and z[i + 1]) for i in range(L_ - 1)):
        v = sd_value(z)
        seen[v] = seen.get(v, 0) + 1
check("D3 non-adjacent form: a unique section of the signed-digit fibre with weight 1/3",
      ok_naf and max(seen.values()) == 1,
      "k < 2^16: %.4f nonzeros per place (binary 1/2); %d strings of length 10, all distinct values"
      % (nz / places, len(seen)))

# ---------------------------------------------------------------------------------------------
section("E. Multiplication: a contraction, then the boundary; fast methods are decompositions")

n = 64
maxcol = maxcarry = 0
ok_conv = True
for _ in range(500):
    a, b = D.bits(n), D.bits(n)
    col = [0] * (2 * n)
    for i in range(n):
        if bit(a, i):
            for j in range(n):
                col[i + j] += bit(b, j)
    d, c, t = normalize(col)
    ok_conv &= sum(ck << k for k, ck in enumerate(c)) == a * b
    maxcol = max(maxcol, max(col))
    maxcarry = max(maxcarry, max(t))
check("E1 product = digit convolution (contraction) then carries; the carry bond's width is the "
      "bits of the count of terms meeting", ok_conv and maxcarry < 2 * n,
      "64-bit: max column %d, max carry %d (%d bits; ceil_log2(64)+1 = 7)" % (maxcol, maxcarry, maxcarry.bit_length()))

leaf = [0]


def karatsuba(x, y, n):
    if n == 1:
        leaf[0] += 1
        return x * y
    h = n // 2
    x0, x1 = x & ((1 << h) - 1), x >> h
    y0, y1 = y & ((1 << h) - 1), y >> h
    z0 = karatsuba(x0, y0, h)
    z2 = karatsuba(x1, y1, h)
    s1, s2 = x0 + x1, y0 + y1
    # (s1)(s2) with s1, s2 < 2^(h+1): split the top bits off so the leaves stay one place wide
    t1, t2 = s1 >> h, s2 >> h
    r1, r2 = s1 & ((1 << h) - 1), s2 & ((1 << h) - 1)
    z1 = karatsuba(r1, r2, h) + ((t1 * r2 + t2 * r1) << h) + ((t1 * t2) << (2 * h))
    return z0 + ((z1 - z0 - z2) << h) + (z2 << (2 * h))


ok_k = True
counts = {}
for k in range(1, 9):
    n = 1 << k
    leaf[0] = 0
    for _ in range(3):
        x, y = D.bits(n), D.bits(n)
        ok_k &= karatsuba(x, y, n) == x * y
    counts[n] = leaf[0] // 3
check("E2 Karatsuba: 3^k one-place products for 2^k places (similarity dimension log2 3 = 1.585)",
      ok_k and all(counts[1 << k] == 3 ** k for k in range(1, 9)), "leaf counts %s" % counts)

mults = [0]


def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][t] * B[t][j] for t in range(n)) for j in range(n)] for i in range(n)]


def strassen(A, B):
    n = len(A)
    if n == 1:
        mults[0] += 1
        return [[A[0][0] * B[0][0]]]
    h = n // 2

    def blk(M, i, j):
        return [row[j * h:(j + 1) * h] for row in M[i * h:(i + 1) * h]]

    def add(X, Y, s=1):
        return [[X[i][j] + s * Y[i][j] for j in range(h)] for i in range(h)]
    A11, A12, A21, A22 = blk(A, 0, 0), blk(A, 0, 1), blk(A, 1, 0), blk(A, 1, 1)
    B11, B12, B21, B22 = blk(B, 0, 0), blk(B, 0, 1), blk(B, 1, 0), blk(B, 1, 1)
    M1 = strassen(add(A11, A22), add(B11, B22))
    M2 = strassen(add(A21, A22), B11)
    M3 = strassen(A11, add(B12, B22, -1))
    M4 = strassen(A22, add(B21, B11, -1))
    M5 = strassen(add(A11, A12), B22)
    M6 = strassen(add(A21, A11, -1), add(B11, B12))
    M7 = strassen(add(A12, A22, -1), add(B21, B22))
    C11 = add(add(M1, M4), add(M7, M5, -1))
    C12 = add(M3, M5)
    C21 = add(M2, M4)
    C22 = add(add(M1, M2, -1), add(M3, M6))
    return [C11[i] + C12[i] for i in range(h)] + [C21[i] + C22[i] for i in range(h)]


ok_s = True
scount = {}
for k in range(1, 5):
    n = 1 << k
    A = [[D.below(17) - 8 for _ in range(n)] for _ in range(n)]
    B = [[D.below(17) - 8 for _ in range(n)] for _ in range(n)]
    mults[0] = 0
    ok_s &= strassen(A, B) == mat_mul(A, B)
    scount[n] = mults[0]
check("E2 Strassen: 7^k products for 2^k x 2^k (similarity dimension log2 7 = 2.807)",
      ok_s and all(scount[1 << k] == 7 ** k for k in range(1, 5)), "counts %s" % scount)


def carries_base(m, n_, p):
    c, cnt = 0, 0
    while m or n_ or c:
        s = m % p + n_ % p + c
        c = 1 if s >= p else 0
        cnt += c
        m //= p
        n_ //= p
    return cnt


ok_kum, free2 = True, 0
for m in range(1 << 9):
    for n_ in range(1 << 9):
        c = carries_base(m, n_, 2)
        free2 += (c == 0)
        if c != s_p(m, 2) + s_p(n_, 2) - s_p(m + n_, 2):
            ok_kum = False
ok_kum3, free3 = True, 0
for m in range(3 ** 5):
    for n_ in range(3 ** 5):
        c = carries_base(m, n_, 3)
        free3 += (c == 0)
        if 2 * c != s_p(m, 3) + s_p(n_, 3) - s_p(m + n_, 3) or c != v_p(comb(m + n_, m), 3):
            ok_kum3 = False
check("E3 Kummer: carries of m+n in base p = v_p(binomial(m+n, m)) (p = 2 and 3)",
      ok_kum and ok_kum3, "all m, n < 2^9 and < 3^5")
check("E3 carry-free pairs: 3^k in base 2 (Sierpinski, dim log2 3), 6^k in base 3 (dim log3 6)",
      free2 == 3 ** 9 and free3 == 6 ** 5, "%d = 3^9, %d = 6^5" % (free2, free3))
ok_leg = all(sum(v_p(i, p) for i in range(1, N + 1)) * (p - 1) == N - s_p(N, p)
             for p in (2, 3, 5, 7) for N in range(1, 1500, 7))
check("E3 Legendre: v_p(N!) = (N - s_p(N))/(p-1): a factorial's valuation counts its carries", ok_leg)
ok_inc = all(s_p(k + 1, 2) == s_p(k, 2) + 1 - v_p(k + 1, 2) for k in range(1, 200000))
check("E3 counting up by one: s_2(k+1) = s_2(k) + 1 - v_2(k+1) (the carry run of an increment)", ok_inc)

# Fermat ring: 2 is a 32nd root of unity mod 2^16+1, so the DFT's twiddles are shifts
q = 65537
ok_f = pow(2, 16, q) == q - 1 and pow(2, 32, q) == 1
Nn = 32
x = [D.below(q) for _ in range(Nn)]
y = [D.below(q) for _ in range(Nn)]
conv = [sum(x[i] * y[(k - i) % Nn] for i in range(Nn)) % q for k in range(Nn)]


def dft(v, w):
    return [sum(v[j] * pow(w, j * k, q) for j in range(Nn)) % q for k in range(Nn)]


X, Y = dft(x, 2), dft(y, 2)
inv2, invN = pow(2, q - 2, q), pow(Nn, q - 2, q)
back = [(c * invN) % q for c in dft([(X[k] * Y[k]) % q for k in range(Nn)], inv2)]
check("E4 cyclic convolution mod 2^16+1 through a DFT whose root of unity is 2 (multiply = shift)",
      ok_f and back == conv)

# ---------------------------------------------------------------------------------------------
section("F. Inversion: one map X -> X(2 - AX); the residual squares in every completion")

ok_h, worst = True, [64] * 6
for _ in range(3000):
    a = D.bits(64) | 1
    x = a
    for k in range(6):
        e = (1 - a * x) % (1 << 64)
        got = 64 if e == 0 else v_p(e, 2)
        worst[k] = min(worst[k], got)
        ok_h &= got >= min(64, 3 * 2 ** k)
        x = (x * (2 - a * x)) % (1 << 64)
ok_m = all(((1 - a * ((3 * a) ^ 2)) % (1 << 20)) % 32 == 0 for a in range(1, 1 << 16, 2))
check("F1 2-adic Newton (bottom end): from x=a, correct low bits 3, 6, 12, 24, 48, 64",
      ok_h and worst[5] == 64, "worst-case correct bits per step %s; (3a) xor 2 gives 5 bits: %s" % (worst, ok_m))

ok_r = True
for _ in range(200):
    a = F(D.below(1 << 20) + (1 << 20), 1 << 20)   # in [1, 2)
    x = F(1, 2) + F(1, 4)
    e = 1 - a * x
    for k in range(5):
        x2 = x * (2 - a * x)
        e2 = 1 - a * x2
        ok_r &= e2 == e * e
        x, e = x2, e2
ok_rel = True
Lg = 40
for _ in range(200):
    a = F(D.below(1 << 20) + (1 << 20), 1 << 20)
    x = F(3, 4)
    for k in range(6):
        e = 1 - a * x
        xt = x * (2 - a * x)
        xr = F(round(xt * (1 << Lg)), 1 << Lg)     # released to the lattice 2^-40
        r = xr - xt
        ok_rel &= (1 - a * xr) == e * e - a * r
        x = xr
check("F2 real Newton (top end): e' = e^2 identically; released to 2^-L it is e^2 - a*r with the "
      "remainder r accounted", ok_r and ok_rel)

ok_sched = all(-(-w // 2 ** k) == ((w - 1) >> k) + 1 for w in range(1, 2000) for k in range(12))


def schedule(w):
    out = [w]
    while out[-1] > 1:
        out.append(-(-out[-1] // 2))
    return out[::-1]


check("F3 Newton's width schedule is ceil(w/2^k) = ((w-1)>>k)+1: the target width's own binary "
      "expansion read from the top", ok_sched,
      "w=11: %s; w=64: %s; w=100: %s" % (schedule(11), schedule(64), schedule(100)))


def mmul(A, B):
    return [[sum(A[i][t] * B[t][j] for t in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def msub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def eye(n):
    return [[F(int(i == j)) for j in range(n)] for i in range(n)]


def mscale(A, s):
    return [[s * v for v in row] for row in A]


def tr(A):
    return [list(r) for r in zip(*A)]


ok_ns = True
for _ in range(50):
    A = [[F(D.below(21) - 10, 1 + D.below(5)) for _ in range(3)] for _ in range(3)]
    X = [[F(D.below(21) - 10, 1 + D.below(5)) for _ in range(3)] for _ in range(3)]
    E = msub(eye(3), mmul(A, X))
    X2 = mmul(X, msub(mscale(eye(3), 2), mmul(A, X)))
    ok_ns &= msub(eye(3), mmul(A, X2)) == mmul(E, E)
check("F4 matrix Newton-Schulz: I - A X(2I - AX) = (I - AX)^2 identically", ok_ns)

A = [[F(v) for v in row] for row in ([2, 0, 1], [0, 2, -1], [1, -1, 1])]  # rank 2, null (1,-1,-2)
Fm = [[F(2), F(0)], [F(0), F(2)], [F(1), F(-1)]]
G = [[F(1), F(0), F(1, 2)], [F(0), F(1), F(-1, 2)]]


def inv2x2(M):
    det = M[0][0] * M[1][1] - M[0][1] * M[1][0]
    return [[M[1][1] / det, -M[0][1] / det], [-M[1][0] / det, M[0][0] / det]]


Aplus = mmul(mmul(tr(G), inv2x2(mmul(G, tr(G)))), mmul(inv2x2(mmul(tr(Fm), Fm)), tr(Fm)))
pen = (mmul(mmul(A, Aplus), A) == A and mmul(mmul(Aplus, A), Aplus) == Aplus
       and tr(mmul(A, Aplus)) == mmul(A, Aplus) and tr(mmul(Aplus, A)) == mmul(Aplus, A))
norm1 = max(sum(abs(A[i][j]) for i in range(3)) for j in range(3))
norminf = max(sum(abs(v) for v in row) for row in A)
X = mscale(tr(A), F(1) / (norm1 * norminf))
u = [[F(1)], [F(-1)], [F(-2)]]
v1, v2 = [[F(1)], [F(1)], [F(0)]], [[F(1)], [F(-1)], [F(1)]]
Aplus2 = [[mmul(v1, tr(v1))[i][j] / 4 + mmul(v2, tr(v2))[i][j] / 9 for j in range(3)] for i in range(3)]
silent, errs = True, []
for k in range(10):
    silent &= mmul(X, u) == [[F(0)]] * 3 and mmul(tr(u), X) == [[F(0)] * 3]
    err = max(abs(v) for row in msub(X, Aplus) for v in row)
    errs.append(round(log2(err.numerator) - log2(err.denominator), 1) if err else None)
    X = mmul(X, msub(mscale(eye(3), 2), mmul(A, X)))
check("F5 Moore-Penrose: the same map from X0 = A^T/(|A|_1 |A|_inf) converges to A^+, and the null "
      "direction stays silent at every step, identically", pen and Aplus == Aplus2 and mmul(Fm, G) == A and silent and errs[-1] is not None and errs[-1] < -60,
      "log2 max|X_k - A^+| for k=0..9: %s" % errs)


def ext_euclid_word(a, m):
    """Quotients of Euclid on (m, a) and the product of [[q,1],[1,0]]."""
    qs, r0, r1 = [], m, a
    while r1:
        q, r = divmod(r0, r1)
        qs.append(q)
        r0, r1 = r1, r
    M = [[1, 0], [0, 1]]
    for q in qs:
        M = [[M[0][0] * q + M[0][1], M[0][0]], [M[1][0] * q + M[1][1], M[1][0]]]
    return qs, M, r0


ok_e, steps = True, []
for _ in range(2000):
    m = D.bits(64) | (1 << 63)
    a = D.below(m)
    if gcd(a, m) != 1:
        continue
    qs, M, g = ext_euclid_word(a, m)
    det = M[0][0] * M[1][1] - M[0][1] * M[1][0]
    ok_e &= det == (-1) ** len(qs) and M[0][0] == m and M[1][0] == a
    # the inverse of a mod m from the convergent: a * M[0][1] - m * M[1][1] = +-1
    inv = (M[0][1] * (-1) ** (len(qs) + 1)) % m
    ok_e &= (a * inv) % m == 1
    steps.append(len(qs))
    # each step [[q,1],[1,0]] = shear [[1,q],[0,1]] times swap [[0,1],[1,0]]
ok_fac = all(mmul([[1, q], [0, 1]], [[0, 1], [1, 0]]) == [[q, 1], [1, 0]] for q in range(1, 50))
check("F6 modular inversion is Euclid's word in SL(2,Z): det = +-1, the convergent is the inverse; "
      "each step is a shear times a swap", ok_e and ok_fac,
      "64-bit moduli: mean %.1f steps (Heilbronn 12 ln2 ln m / pi^2 = %.1f)"
      % (sum(steps) / len(steps), 12 * log(2) * log(2 ** 63.5) / 3.14159265 ** 2))


def det_frac(M):
    A = [[F(v) for v in row] for row in M]
    n, det = len(A), F(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            return F(0)
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = -det
        det *= A[c][c]
        for r in range(c + 1, n):
            f_ = A[r][c] / A[c][c]
            for cc in range(c, n):
                A[r][cc] -= f_ * A[c][cc]
    return det


ok_snf = True
for _ in range(200):
    M = [[D.below(41) - 20 for _ in range(4)] for _ in range(4)]
    dg = snf(M)
    prod = 1
    for v in dg:
        prod *= v
    ok_snf &= prod == abs(det_frac(M)) and all(dg[i + 1] % dg[i] == 0 for i in range(3) if dg[i])
check("F6 Smith normal form: invariant factors divide in a chain and multiply to |det|: the "
      "cokernel (homology) of a Diophantine system AX = B", ok_snf)

ok_rs = True
for _ in range(300):
    a = F(D.below(1000) + 1, D.below(1000) + 1)
    x = F(D.below(1000) + 1, D.below(1000) + 1)
    e = 1 - a * x * x
    x2 = x * (3 - a * x * x) / 2
    ok_rs &= 1 - a * x2 * x2 == F(3, 4) * e ** 2 + F(1, 4) * e ** 3
    r = F(D.below(60) + 1, D.below(60) + 1)  # a = r^2: Heron's step error squares over 2x
    xx = F(D.below(1000) + 1, D.below(100) + 1)
    ok_rs &= (xx + r * r / xx) / 2 - r == (xx - r) ** 2 / (2 * xx)
check("F7 roots are the same family: inverse square root e' = 3/4 e^2 + 1/4 e^3; Heron x' - r = "
      "(x - r)^2 / 2x", ok_rs)

ok_sig = True
for _ in range(500):
    p = F(D.below(999) + 1, 1000)
    k1, k2 = F(D.below(50) + 1, D.below(50) + 1), F(D.below(50) + 1, D.below(50) + 1)

    def upd(p, k):
        return k * p / (k * p + 1 - p)          # Moebius [[k,0],[k-1,1]] on p
    o = p / (1 - p)
    ok_sig &= upd(p, k1) / (1 - upd(p, k1)) == k1 * o           # odds are multiplied: a boost
    ok_sig &= upd(upd(p, k1), k2) == upd(p, k1 * k2)
    t = (o - 1) / (o + 1)                                      # Cayley transform of the odds
    ok_sig &= p == (1 + t) / 2                                 # sigmoid = (1 + tanh(x/2))/2
    t1, t2 = F(D.below(99) - 49, 50), F(D.below(99) - 49, 50)
    Bm = mmul([[1, t1], [t1, 1]], [[1, t2], [t2, 1]])
    tt = (t1 + t2) / (1 + t1 * t2)
    ok_sig &= Bm[0][0] == Bm[1][1] and Bm[0][1] == Bm[1][0] and Bm[0][1] / Bm[0][0] == tt
    v = F(D.below(99) - 49, 50)
    act = lambda M, z: (M[0][0] * z + M[0][1]) / (M[1][0] * z + M[1][1])
    ok_sig &= act(Bm, v) == act([[1, t1], [t1, 1]], act([[1, t2], [t2, 1]], v))
check("F8 the sigmoid is a Moebius map: an update multiplies the odds (a boost), composes by "
      "product, and tanh addition is the boost matrices' product", ok_sig)

# ---------------------------------------------------------------------------------------------
section("G. Reversibility: shears are the reversible primitive; merges are where bits leave")

S1 = [[1, -1], [0, 1]]
S2 = [[1, 0], [1, 1]]
check("G1 the quarter-turn is three integer shears", mmul(mmul(S1, S2), S1) == [[0, -1], [1, 0]])

ok_sh = True
for _ in range(5000):
    x, y = D.below(1 << 40) - (1 << 39), D.below(1 << 40) - (1 << 39)
    f = (x * x) // 7 + (x >> 3)          # nonlinear and rounded
    ok_sh &= ((y + f) - f) == y
ok_lift = True
for a in range(-64, 64):
    for b in range(-64, 64):
        d = a - b
        s = b + (d >> 1)                    # floor((a+b)/2)
        b2 = s - (d >> 1)
        ok_lift &= (b2 == b and d + b2 == a and s == (a + b) // 2)
ok_fei = True
for _ in range(3000):
    Lh, Rh = D.bits(32), D.bits(32)
    keys = [D.bits(32) for _ in range(4)]
    def Ff(r, k):
        return ((r * r + k) >> 7) & 0xFFFFFFFF   # not invertible on its own
    l, r = Lh, Rh
    for k in keys:
        l, r = r, l ^ Ff(r, k)
    for k in reversed(keys):
        l, r = r ^ Ff(l, k), l
    ok_fei &= (l, r) == (Lh, Rh)
check("G1 a shear (x, y + f(x)) inverts for any f, rounded or not: integer lifting, Feistel",
      ok_sh and ok_lift and ok_fei)


def cuccaro(a, b, n):
    """Reversible ripple adder (Cuccaro et al. 2004): wires c0, b_i, a_i, z."""
    w = {"c": 0, "z": 0}
    for i in range(n):
        w["a%d" % i], w["b%d" % i] = bit(a, i), bit(b, i)
    gates = [0, 0]

    def cnot(c_, t_):
        w[t_] ^= w[c_]
        gates[0] += 1

    def tof(c1, c2, t_):
        w[t_] ^= w[c1] & w[c2]
        gates[1] += 1

    def maj(c_, b_, a_):
        cnot(a_, b_)
        cnot(a_, c_)
        tof(c_, b_, a_)

    def uma(c_, b_, a_):
        tof(c_, b_, a_)
        cnot(a_, c_)
        cnot(c_, b_)
    maj("c", "b0", "a0")
    for i in range(1, n):
        maj("a%d" % (i - 1), "b%d" % i, "a%d" % i)
    cnot("a%d" % (n - 1), "z")
    for i in range(n - 1, 0, -1):
        uma("a%d" % (i - 1), "b%d" % i, "a%d" % i)
    uma("c", "b0", "a0")
    A_ = sum(w["a%d" % i] << i for i in range(n))
    B_ = sum(w["b%d" % i] << i for i in range(n))
    return A_, B_, w["c"], w["z"], gates


ok_cu = True
for a in range(32):
    for b in range(32):
        A_, B_, c, z, g = cuccaro(a, b, 5)
        ok_cu &= (A_, B_ + (z << 5), c) == (a, a + b, 0)
for _ in range(500):
    a, b = D.bits(32), D.bits(32)
    A_, B_, c, z, g = cuccaro(a, b, 32)
    ok_cu &= (A_, B_ + (z << 32), c) == (a, a + b, 0)
check("G2 reversible adder: (a, b) -> (a, a+b), every carry computed and uncomputed in place, "
      "the ancilla returns to 0, only the top carry (the winding) is written out",
      ok_cu, "n=5 exhaustive, n=32 sampled; gates for n=32: %d CNOT, %d Toffoli" % (g[0], g[1]))


def fibre_bits(outputs, total):
    """H(input | output) in bits when inputs are uniform: sum_y P(y) log2 |fibre(y)|."""
    h = 0.0
    for cnt in outputs.values():
        h += cnt / total * log2(cnt)
    return h


n = 8
add_f, mul_f, xor_f, csa_f = {}, {}, {}, {}
for a in range(1 << n):
    for b in range(1 << n):
        add_f[a + b] = add_f.get(a + b, 0) + 1
        mul_f[a * b] = mul_f.get(a * b, 0) + 1
        xor_f[a ^ b] = xor_f.get(a ^ b, 0) + 1
        v = a + 2 * b                                 # carry-save pair (s, c) collapsed
        csa_f[v] = csa_f.get(v, 0) + 1
tot = 1 << (2 * n)
check("G3 Landauer cost = log2 of the fibre: bits merged per operation on two 8-bit inputs", True,
      "a+b %.2f, a*b %.2f, a^b %.2f, carry-save collapse s+2c %.2f, in-place (a, a+b) 0.00"
      % (fibre_bits(add_f, tot), fibre_bits(mul_f, tot), fibre_bits(xor_f, tot), fibre_bits(csa_f, tot)))

# ---------------------------------------------------------------------------------------------
section("H. Analysis: the carry's one-way cone, its Walsh face, and recovering a register")

ok_cone = True
for _ in range(3000):
    a, b = D.bits(16), D.bits(16)
    j = D.below(16)
    s1 = (a + b) & 0xFFFF
    s2 = ((a ^ (1 << j)) + b) & 0xFFFF
    changed = s1 ^ s2
    ok_cone &= (changed & ((1 << j) - 1)) == 0      # nothing below the flipped place moves
check("H1 the carry cone is one-way: an input bit only reaches its own and higher places", ok_cone)


def arx_dependence(rounds, r):
    dep = [[0] * 32 for _ in range(32)]
    for trial in range(48):
        x0, y0 = D.bits(16), D.bits(16)

        def run(x, y):
            for _ in range(rounds):
                x = (x + y) & 0xFFFF
                y = (((y << r) | (y >> (16 - r))) & 0xFFFF if r else y) ^ x
            return x | (y << 16)
        base = run(x0, y0)
        for i in range(32):
            xi, yi = (x0 ^ (1 << i), y0) if i < 16 else (x0, y0 ^ (1 << (i - 16)))
            diff = base ^ run(xi, yi)
            for o in range(32):
                if bit(diff, o):
                    dep[i][o] = 1
    return sum(map(sum, dep))


full = {}
for r in (0, 3, 7):
    full[r] = next((R for R in range(1, 13) if arx_dependence(R, r) == 1024), None)
check("H1 rotation closes the cone into a cycle: with rotation every output bit depends on every "
      "input bit after a few rounds, without it never", full[0] is None and full[3] and full[7],
      "rounds to full dependence (16-bit ARX toy): rotate 0 -> %s, rotate 3 -> %s, rotate 7 -> %s"
      % (full[0], full[3], full[7]))

n = 4
best = []
for k in range(n):
    f = [bit((x & 15) + (x >> 4), k) for x in range(256)]
    corr = 0
    for mask in range(1, 256):
        c = sum(1 if f[x] == (bin(x & mask).count("1") & 1) else -1 for x in range(256))
        corr = max(corr, abs(c))
    best.append(F(corr, 256))
n6 = 6
degs = []
for k in range(n6):
    t = [bit((x & 63) + (x >> 6), k) for x in range(1 << 12)]
    for i in range(12):                       # Moebius transform to the algebraic normal form
        for x in range(1 << 12):
            if x >> i & 1:
                t[x] ^= t[x ^ (1 << i)]
    degs.append(max(bin(x).count("1") for x in range(1 << 12) if t[x]))
check("H2 the carry is the only nonlinearity: sum bit k has algebraic degree k+1 over F_2 and best "
      "linear correlation 1 (k=0) then 1/2", degs == [1, 2, 3, 4, 5, 6] and best == [1] + [F(1, 2)] * 3,
      "degrees (6-bit) %s; best |correlation| (4-bit) %s" % (degs, [str(b) for b in best]))


def berlekamp_massey(s):
    C, B = [1], [1]
    L, m, b = 0, 1, 1
    for n_ in range(len(s)):
        d = s[n_]
        for i in range(1, L + 1):
            d ^= C[i] & s[n_ - i]
        if d == 0:
            m += 1
        elif 2 * L <= n_:
            T = list(C)
            C = C + [0] * (len(B) + m - len(C))
            for i, bb in enumerate(B):
                C[i + m] ^= bb
            L, B, m = n_ + 1 - L, T, 1
        else:
            C = C + [0] * (len(B) + m - len(C))
            for i, bb in enumerate(B):
                C[i + m] ^= bb
            m += 1
    return L, C[:L + 1]


ok_bm = True
for trial in range(40):
    Lr = 8 + D.below(24)
    taps = [1] + [D.below(2) for _ in range(Lr - 1)] + [1]
    state = [D.below(2) for _ in range(Lr)]
    if not any(state):
        state[0] = 1
    seq = list(state)
    while len(seq) < 2 * Lr + 400:
        nxt = 0
        for i in range(1, Lr + 1):
            nxt ^= taps[i] & seq[-i]
        seq.append(nxt)
    Lf, C = berlekamp_massey(seq[:2 * Lr])
    regen = seq[:Lf]
    while len(regen) < len(seq):
        nxt = 0
        for i in range(1, Lf + 1):
            nxt ^= C[i] & regen[-i]
        regen.append(nxt)
    ok_bm &= Lf <= Lr and regen == seq
check("H3 Berlekamp-Massey: 2L output bits recover a register's feedback (its closing edges) and "
      "regenerate the rest", ok_bm, "40 random registers of length 8..31")

ok_rr = True
for _ in range(300):
    qn = D.bits(20) | 1 | (1 << 19)
    pn = D.below(1 << 19) - (1 << 18)
    if gcd(pn, qn) != 1:
        continue
    N = 2 * 21 + 2
    alpha = (pn * pow(qn, -1, 1 << N)) % (1 << N)
    r0, r1, t0, t1 = 1 << N, alpha, 0, 1
    while r1 >= (1 << (N // 2)):
        qq = r0 // r1
        r0, r1 = r1, r0 - qq * r1
        t0, t1 = t1, t0 - qq * t1
    ok_rr &= F(r1, t1) == F(pn, qn)
bits19 = [(((-1) * pow(19, -1, 1 << 120)) % (1 << 120) >> k) & 1 for k in range(120)]
per = next(p for p in range(1, 60) if all(bits19[k] == bits19[k + p] for k in range(100 - p)))
check("H4 with the carry (2-adic): 2*log2(q)+2 low bits recover p/q by Euclid (rational "
      "reconstruction); -1/19 repeats with period ord_19(2)", ok_rr and per == 18,
      "period of -1/19 in Z_2: %d" % per)

# ---------------------------------------------------------------------------------------------
section("I. The carry is Witt addition: binary for p=2, balanced ternary for p=3")


def teich_digits(x, p, n):
    out = []
    for i in range(n):
        mod = p ** (n - i)
        a = x % p
        w = pow(a, p ** (n - i), mod)            # Teichmueller lift of a in Z/p^(n-i)
        out.append(a)
        x = ((x - w) % mod) // p
    return out


def witt_sum(X, Y, p):
    S = []
    for n_ in range(len(X)):
        ghost = sum(p ** i * (X[i] ** (p ** (n_ - i)) + Y[i] ** (p ** (n_ - i))) for i in range(n_ + 1))
        known = sum(p ** i * S[i] ** (p ** (n_ - i)) for i in range(n_))
        num = ghost - known
        assert num % (p ** n_) == 0
        S.append(num // p ** n_)
    return S


ok_w = True
for p in (2, 3):
    mod = p ** 3
    for _ in range(3000):
        a, b = D.below(mod), D.below(mod)
        A_, B_ = teich_digits(a, p, 3), teich_digits(b, p, 3)
        S = [s % p for s in witt_sum(A_, B_, p)]
        ok_w &= S == teich_digits((a + b) % mod, p, 3)
ok_bt = teich_digits(2, 3, 1) == [2] and pow(2, 9, 27) == 26
check("I1 Witt addition polynomials reproduce the carries: p=2 gives bit addition (S_1 = a1+b1+a0*b0 "
      "mod 2, the AND), p=3 gives balanced ternary (the Teichmueller lift of 2 is -1)", ok_w and ok_bt,
      "3 places, 3000 random pairs each")

Nmax = 10 ** 6
mu = [1] * (Nmax + 1)
is_c = bytearray(Nmax + 1)
for p in range(2, Nmax + 1):
    if not is_c[p]:
        for m_ in range(p, Nmax + 1, p):
            if m_ > p:
                is_c[m_] = 1
            mu[m_] = -mu[m_]
        pp = p * p
        for m_ in range(pp, Nmax + 1, pp):
            mu[m_] = 0
mert = sum(mu[1:])
tm, pop = 0, 0
for k in range(1, Nmax + 1):
    pop = bin(k).count("1")
    tm += mu[k] * (1 if pop % 2 == 0 else -1)
check("I2 reading: the Moebius function against the carry parity (-1)^s_2(n) (Mauduit-Rivat: o(N))",
      True, "N=10^6: sum mu*(-1)^s2 = %d (%.3f sqrt N); Mertens M(N) = %d (%.3f sqrt N)"
      % (tm, tm / Nmax ** 0.5, mert, mert / Nmax ** 0.5))

ok_shell = True
lam = 2
for _ in range(200):
    u = [F(0)] + [F(D.below(41) - 20, 1 + D.below(9)) for _ in range(12)] + [F(0)]
    du = [F(0)] * 14
    for k in range(1, 13):
        du[k] = lam ** (k - 1) * u[k - 1] ** 2 - lam ** k * u[k] * u[k + 1]
    flux = [F(0)] * 15
    for k in range(1, 14):
        flux[k] = lam ** (k - 1) * u[k - 1] ** 2 * u[k]
    ok_shell &= sum(u[k] * du[k] for k in range(1, 13)) == 0
    ok_shell &= all(u[k] * du[k] == flux[k] - flux[k + 1] for k in range(1, 13))
check("I3 dyadic shell model of fluids: energy passes shell to shell as a carry (flux telescopes, "
      "total conserved)", ok_shell, "12 shells, 200 random states, Fractions")

# ---------------------------------------------------------------------------------------------
section("J. Elliptic curves: scalar multiplication is the scalar's register; NAF is its signed section")

P_ = (1 << 61) - 1
a_c, b_c = 2, 3


def ec_add(P, Q):
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2 and (y1 + y2) % P_ == 0:
        return None
    if P == Q:
        lam_ = (3 * x1 * x1 + a_c) * pow(2 * y1, -1, P_) % P_
    else:
        lam_ = (y2 - y1) * pow(x2 - x1, -1, P_) % P_
    x3 = (lam_ * lam_ - x1 - x2) % P_
    return (x3, (lam_ * (x1 - x3) - y1) % P_)


def ec_neg(P):
    return None if P is None else (P[0], (-P[1]) % P_)


x0 = 5
while True:
    rhs = (x0 ** 3 + a_c * x0 + b_c) % P_
    if pow(rhs, (P_ - 1) // 2, P_) == 1:
        break
    x0 += 1
y0 = pow(rhs, (P_ + 1) // 4, P_) if P_ % 4 == 3 else None
if y0 is None or (y0 * y0) % P_ != rhs:
    # P_ = 2^61-1 is 3 mod 4, so the root above is valid; this branch is unreachable
    y0 = 0
Pt = (x0, y0)
ok_ec, adds_bin, adds_naf, nk = True, 0, 0, 0
for _ in range(200):
    k = D.bits(64) | 1
    R = None
    for i in range(k.bit_length() - 1, -1, -1):
        R = ec_add(R, R)
        if bit(k, i):
            R = ec_add(R, Pt)
            adds_bin += 1
    z = naf(k)
    R2 = None
    for d in reversed(z):
        R2 = ec_add(R2, R2)
        if d == 1:
            R2 = ec_add(R2, Pt)
            adds_naf += 1
        elif d == -1:
            R2 = ec_add(R2, ec_neg(Pt))
            adds_naf += 1
    ok_ec &= R == R2
    nk += 1
check("J1 [k]P by the binary register and by its non-adjacent form agree on y^2 = x^3+2x+3 over "
      "F_(2^61-1)", ok_ec, "mean additions per 64-bit scalar: binary %.1f, NAF %.1f"
      % (adds_bin / nk, adds_naf / nk))

# ---------------------------------------------------------------------------------------------
section("K. Coprime rings carry nothing between them: residues on rings, the CRT as the one carry")

ok_g = all(gcd(2 ** a - 1, 2 ** b - 1) == 2 ** gcd(a, b) - 1 for a in range(1, 41) for b in range(1, 41))
check("K1 two rings are coprime exactly when their lengths are: gcd(2^a-1, 2^b-1) = 2^gcd(a,b) - 1", ok_g,
      "a, b <= 40")
mods = [2 ** 19 - 1, 2 ** 31 - 1, 2 ** 61 - 1]
Mprod = mods[0] * mods[1] * mods[2]


def garner(res):
    """Mixed-radix digits (the carries between rings), then the integer below the product."""
    x, base = 0, 1
    for r, m in zip(res, mods):
        d = ((r - x) * pow(base, -1, m)) % m
        x += base * d
        base *= m
    return x


def ring_reduce(v, n):
    """Reduction mod 2^n - 1 by end-around carry only: fold the top places back onto place 0."""
    m = (1 << n) - 1
    while v > m:
        v = (v & m) + (v >> n)
    return 0 if v == m else v


ok_rns = True
for _ in range(3000):
    a, b = D.below(Mprod), D.below(Mprod)
    ra, rb = [a % m for m in mods], [b % m for m in mods]
    s = [ring_reduce(x + y, n) for x, y, n in zip(ra, rb, (19, 31, 61))]
    p = [ring_reduce(x * y, n) for x, y, n in zip(ra, rb, (19, 31, 61))]
    ok_rns &= garner(s) == (a + b) % Mprod and garner(p) == (a * b) % Mprod
check("K2 residues on rings of 19, 31 and 61 places add and multiply lane by lane, each lane closing "
      "its own carry end-around; the mixed-radix reconstruction is the only carry between lanes", ok_rns,
      "3000 random pairs below (2^19-1)(2^31-1)(2^61-1)")

# ---------------------------------------------------------------------------------------------
section("L. A data type is a register: its places, carry cuts, closing edge, section and fields")


def signed(v, n):
    """The two's complement section of Z/2^n: the top place read with weight -2^(n-1)."""
    return v - ((v >> (n - 1)) & 1) * (1 << n)


ok_ring = ok_val = ok_ext = ok_order = True
for _ in range(20000):
    a, b = D.u64(), D.u64()
    sa, sb = signed(a, 64), signed(b, 64)
    M = 1 << 64
    ok_ring &= ((sa + sb) % M == (a + b) & MASK64 and (sa - sb) % M == (a - b) & MASK64
                and (sa * sb) % M == (a * b) & MASK64)
    ok_val &= sa == sum(bit(a, k) << k for k in range(63)) - bit(a, 63) * (1 << 63)
    ext = a | ((MASK64 << 64) if bit(a, 63) else 0)
    ok_ext &= signed(ext, 128) == sa
    ok_order &= ((a < b) != (sa < sb)) == (bit(a, 63) != bit(b, 63))
check("L1 u64 and i64 are one ring Z/2^64 with two sections: wrapping +, -, * give the same bits; the "
      "signed value weights the top place -2^63; sign extension writes the top place out as the tail; "
      "the two orders differ exactly when the top places differ", ok_ring and ok_val and ok_ext and ok_order,
      "20000 random pairs")
ok_tail = all((sum(1 << k for k in range(63, 64 + K)) + (1 << 63)) % (1 << (64 + K)) == 0 for K in range(65))
check("L1 the top place's weight -2^63 is the 2-adic tail of ones summed into one place: "
      "2^63 + 2^64 + ... + 2^(63+K) = -2^63 mod 2^(64+K)", ok_tail, "K = 0..64")


def oc_value(v, n):
    return v if not bit(v, n - 1) else -((~v) & ((1 << n) - 1))


def sm_value(v, n):
    m = v & ((1 << (n - 1)) - 1)
    return -m if bit(v, n - 1) else m


n8 = 8
vals_tc = {signed(v, n8) for v in range(256)}
vals_oc = {oc_value(v, n8) for v in range(256)}
vals_sm = {sm_value(v, n8) for v in range(256)}
ok_oc = True
for x in range(256):
    for y in range(256):
        s = x + y
        if s > 255:
            s = (s & 255) + 1
        ok_oc &= (oc_value(s, n8) - oc_value(x, n8) - oc_value(y, n8)) % 255 == 0
check("L2 three sections of 8 places: two's complement holds 256 values; ones' complement and "
      "sign-magnitude hold 255 (two zeros); ones' complement addition is the ring Z/(2^8-1), its sign a "
      "place, while sign-magnitude's sign is a separate half-turn state",
      len(vals_tc) == 256 and len(vals_oc) == 255 and len(vals_sm) == 255 and ok_oc,
      "exhaustive at 8 places")


def lane_add(x, y, H):
    """One native add with the carry edges cut above each field's top place (H marks those places)."""
    return ((x & ~H & MASK64) + (y & ~H & MASK64) ^ ((x ^ y) & H)) & MASK64


ok_lanes = True
examples = []
for trial in range(2000):
    widths, total = [], 0
    while total < 64:
        w = min(1 + D.below(16), 64 - total)
        widths.append(w)
        total += w
    H, lo, fields = 0, 0, []
    for w in widths:
        H |= 1 << (lo + w - 1)
        fields.append((lo, w))
        lo += w
    x, y = D.u64(), D.u64()
    z = lane_add(x, y, H)
    for lo_, w in fields:
        m = (1 << w) - 1
        ok_lanes &= (z >> lo_) & m == (((x >> lo_) & m) + ((y >> lo_) & m)) & m
    if trial < 2:
        examples.append(widths)
xa, ya = D.u64(), D.u64()
ok_ends = lane_add(xa, ya, MASK64) == xa ^ ya and lane_add(xa, ya, 1 << 63) == (xa + ya) & MASK64
check("L3 lanes and bitfields are the register with carry edges cut at the field boundaries: one native "
      "add, masking each field's top place and restoring it by XOR, adds every field on its own; all "
      "edges cut is XOR, none cut is the 64-place add", ok_lanes and ok_ends,
      "2000 random partitions of 64 places, e.g. widths %s" % examples[0])

import struct


def f32_value(bits):
    """binary32 fields read as integers: sign (a half-turn), level (exponent) and phase (mantissa)."""
    s, e, m = bits >> 31, (bits >> 23) & 0xFF, bits & ((1 << 23) - 1)
    assert 0 < e < 255
    v = F(2) ** (e - 127) * (1 + F(m, 1 << 23))
    return -v if s else v


ok_layout = True
for _ in range(3000):
    bits = (D.below(2) << 31) | ((1 + D.below(254)) << 23) | D.below(1 << 23)
    ok_layout &= F(struct.unpack('>f', struct.pack('>I', bits))[0]) == f32_value(bits)
check("L4 a float's register is three fields: a half-turn, a level and a phase "
      "(value = (-1)^s 2^(e-127) (1 + m/2^23)); matches the platform's binary32", ok_layout,
      "3000 random normal patterns (the platform float read only at this boundary)")

ok_mitchell, worst, gap = True, F(1), 0.0
for _ in range(5000):
    e1, e2 = 64 + D.below(126), 64 + D.below(126)
    m1, m2 = D.below(1 << 23), D.below(1 << 23)
    i1, i2 = (e1 << 23) | m1, (e2 << 23) | m2
    x, y = f32_value(i1), f32_value(i2)
    approx = f32_value(i1 + i2 - (127 << 23))
    f1, f2 = F(m1, 1 << 23), F(m2, 1 << 23)
    mitchell = F(2) ** (e1 + e2 - 254) * ((1 + f1 + f2) if f1 + f2 < 1 else 2 * (f1 + f2))
    ok_mitchell &= approx == mitchell and F(8, 9) <= approx / (x * y) <= 1
    worst = min(worst, approx / (x * y))
    gap = max(gap, log2(float(1 + f1)) - float(f1))
check("L4 adding two floats' bit patterns as integers multiplies their values in the log chart "
      "(Mitchell): the mantissa's carry into the exponent field is the helix's winding carry, and the "
      "product is within 8/9 of the true one", ok_mitchell,
      "5000 pairs; smallest ratio %.4f; the bits read as an integer are log2 to within %.4f "
      "(log2(1+f) - f <= 0.0861)" % (float(worst), gap))

# ---------------------------------------------------------------------------------------------
section("M. The digit face's calculus: the increment's carries are the derivative's defect")

ok_inc = all(s_p(n + 1, b) - s_p(n, b) == 1 - (b - 1) * v_p(n + 1, b)
             for b in range(2, 17) for n in range(5000))
check("M1 an increment moves the digit sum by s_b(n+1) - s_b(n) = 1 - (b-1) v_b(n+1): the carry run "
      "is the defect of the derivative", ok_inc, "b = 2..16, n < 5000")
ok_sum, ok_leg = True, True
for b in range(2, 17):
    acc = 0
    for N in range(1, 3001):
        acc += v_p(N, b)
        ok_sum &= acc * (b - 1) == N - s_p(N, b)
        if b in (2, 3, 5, 7, 11, 13) and N % 97 == 0:
            leg, q = 0, b
            while q <= N:
                leg += N // q
                q *= b
            ok_leg &= acc == leg
comp10 = sum(v_p(k, 10) for k in range(1, 6))
check("M2 summing the increments: sum_(k<=N) v_b(k) = (N - s_b(N))/(b-1), the carries of counting to N; "
      "at a prime radix it is v_p(N!) (Legendre), at a composite one it is not", ok_sum and ok_leg
      and comp10 == 0, "b = 2..16, N <= 3000; b = 10, N = 5: %d carries, v_10(5!) = 1" % comp10)


def digits(n, b):
    out = []
    while n:
        out.append(n % b)
        n //= b
    return out


def lucas_holds(b, nmax):
    bad = 0
    for n in range(nmax):
        dn = digits(n, b)
        for k in range(n + 1):
            dk = digits(k, b)
            prod = 1
            for i in range(len(dn)):
                prod *= comb(dn[i], dk[i] if i < len(dk) else 0)
            bad += (comb(n, k) - prod) % b != 0
    return bad


bad_p = {p: lucas_holds(p, 200) for p in (2, 3, 5, 7)}
bad_c = {b: lucas_holds(b, 200) for b in (4, 6, 10)}
check("M3 at a prime radix the difference calculus's basis C(n,k) factors place by place (Lucas); at a "
      "composite radix it does not", all(v == 0 for v in bad_p.values()) and all(v > 0 for v in bad_c.values()),
      "n < 200, all k: failures %s at primes, %s at composites" % (bad_p, bad_c))


def newton_coeffs(seq):
    out, row = [], list(seq)
    while row:
        out.append(row[0])
        row = [row[i + 1] - row[i] for i in range(len(row) - 1)]
    return out


ok_mahler = all(newton_coeffs([(1 + p) ** x for x in range(25)]) == [p ** k for k in range(25)]
                for p in (2, 3, 5))
check("M3 Mahler's basis: (1+p)^x = sum_k C(x,k) p^k, coefficients of valuation k, so the series "
      "converges at every p-adic x", ok_mahler, "p = 2, 3, 5, 25 coefficients")

lead16 = [int(hex(2 ** k)[2], 16) for k in range(2000)]
ok_hex = all(lead16[k] == (1, 2, 4, 8)[k % 4] for k in range(2000))
cnt = [0] * 10
K10 = 3000
for k in range(K10):
    cnt[int(str(2 ** k)[0])] += 1
dev = max(abs(cnt[d] / K10 - log(1 + 1 / d, 10)) / log(1 + 1 / d, 10) for d in range(1, 10))
check("M4 how digits disperse depends on the radix: the leading digit of 2^k cycles 1, 2, 4, 8 in base "
      "16 (log_16 2 = 1/4 closes the phase) and spreads in base 10 as the phase k log10 2 fills its circle "
      "(Benford)", ok_hex and dev < 0.02,
      "k < 2000 in base 16; k < 3000 in base 10, largest relative deviation from log10(1+1/d): %.4f" % dev)

# ---------------------------------------------------------------------------------------------
section("S. Sections meet before they add; inversion carries its residual (the owner's property tests)")


def signed_width(lo, hi):
    """The fewest signed places [-2^(s-1), 2^(s-1)) holding every value of [lo, hi]."""
    s = 1
    while not (-(1 << (s - 1)) <= lo and hi < (1 << (s - 1))):
        s += 1
    return s


ok_mix, over = True, []
for wa in range(1, 7):
    for wb in range(1, 7):
        sums = [a + b for a in range(1 << wa) for b in range(-(1 << (wb - 1)), 1 << (wb - 1))]
        tight = signed_width(min(sums), max(sums))
        rule = max(wa + 1, wb) + 1
        ok_mix &= tight == rule - (1 if wb == 1 else 0)
        over += [(wa, wb)] if tight < rule else []
ok_mix &= all(signed_width(-(1 << (wb - 1)), (1 << wa) - 1 + (1 << (wb - 1)) - 1)
              == max(wa + 1, wb) + 1 - (1 if wb == 1 else 0) for wa in range(1, 33) for wb in range(1, 33))
check("S1 a low operand of w places and a signed one meet in the signed section, where the low one takes "
      "w+1 places: the sum needs max(w_a+1, w_b)+1 signed places, one fewer only when the signed operand has "
      "one place (3+1 at two places each needs four)", ok_mix,
      "every value pair to 6 places, the bounds to 32; the rule is one too many at %d of 36 small "
      "pairs, those whose signed operand has one place" % len(over))

ok_diff = all(signed_width(min(a - b for a in range(1 << wa) for b in range(1 << wb)),
                           max(a - b for a in range(1 << wa) for b in range(1 << wb))) == max(wa, wb) + 1
              for wa in range(1, 7) for wb in range(1, 7))
check("S2 a difference of two low operands is signed at the wider plus one (not the wider plus two that "
      "converting both and adding gives)", ok_diff, "every value pair to 6 places")

ok_carried, vals = True, [64] * 5
for _ in range(10000):
    a = D.bits(64) | 1
    x = (3 * a) ^ 2
    e = (1 - a * x) % (1 << 64)
    for k in range(5):
        vals[k] = min(vals[k], 64 if e == 0 else v_p(e, 2))
        ok_carried &= e == (1 - a * x) % (1 << 64)
        x, e = (x * (1 + e)) % (1 << 64), (e * e) % (1 << 64)
    ok_carried &= (a * x) % (1 << 64) == 1 and e == 0
check("S3 the bottom end with its residual carried, X' = X(1+E) and E' = E^2 (since 1 - A X(1+E) = E^2), "
      "keeps a step's two products independent: from (3a) xor 2 the residual's valuation runs 5, 10, 20, "
      "40 and four steps reach 64 places", ok_carried and vals[:4] == [5, 10, 20, 40],
      "10,000 odd 64-bit a; least valuation per step %s (64 = zero mod 2^64)" % vals)

# ---------------------------------------------------------------------------------------------
print("\n%d checks, %d failed, %.1f s" % (len(RESULTS), sum(1 for _, ok in RESULTS if not ok), time.time() - T0))
sys.exit(0 if all(ok for _, ok in RESULTS) else 1)
