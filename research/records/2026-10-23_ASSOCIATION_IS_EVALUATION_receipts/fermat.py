# Exact checks for the record's combinatorial and thermodynamic joins (integers and rationals only).
# usage: python3 -I fermat.py
from fractions import Fraction
import itertools, random
def mat_mul(a, b):
    n = len(a); return [[sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def mat_pow(a, e):
    n = len(a); r = [[int(i == j) for j in range(n)] for i in range(n)]
    for _ in range(e): r = mat_mul(r, a)
    return r
tr = lambda a: sum(a[i][i] for i in range(len(a)))
def mobius(n):
    m, p, r = n, 2, 1
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0: return 0
            r = -r
        p += 1
    return -r if m > 1 else r
rng = random.Random(20261023)
# 1. a ring of p sites: tr(A^p) = tr(A) (mod p); primitive closed walks P_n = (1/n) sum_{d|n} mu(d) tr(A^(n/d)) are integers
bad = 0; checked = 0
for _ in range(200):
    k = rng.randint(1, 4); A = [[rng.randint(-5, 5) for _ in range(k)] for _ in range(k)]
    for p in (2, 3, 5, 7, 11, 13):
        checked += 1; bad += (tr(mat_pow(A, p)) - tr(A)) % p != 0
    for n in range(1, 13):
        s = sum(mobius(d) * tr(mat_pow(A, n // d)) for d in range(1, n + 1) if n % d == 0)
        checked += 1; bad += s % n != 0
print("ring of p sites and primitive walks:", checked, "checks,", bad, "failures")
# necklaces: a colours on a p-ring
print("primitive necklaces (a^p - a)/p, a = 2,3,10; p = 5,7:", [((a ** p - a) // p, (a ** p - a) % p) for a in (2, 3, 10) for p in (5, 7)])
# binary potentials: (x + y)^p over the 2^p binary words; the mixed words come in full rotation orbits
p = 7; orbits = {}
for w in itertools.product((0, 1), repeat=p):
    rep = min(w[i:] + w[:i] for i in range(p)); orbits.setdefault(rep, set()).add(w)
sizes = sorted({len(o) for o in orbits.values()})
print("binary words of length 7:", 2 ** p, "orbits", len(orbits), "orbit sizes", sizes)
# 2. Fermat composed over the base's atoms: n^5 = n (mod 10); 9 x = -x (mod 10)
print("n^5 = n (mod 10) for n < 1000:", all(pow(n, 5, 10) == n % 10 for n in range(1000)),
      "| 9x = -x (mod 10):", all((9 * x) % 10 == (-x) % 10 for x in range(1000)))
# 3. the trailing digit law of a product factors over the base's prime atoms (CRT)
def law(b):
    c = [0] * b
    for x in range(b):
        for y in range(b): c[x * y % b] += 1
    return c
def prime_law(p):  # absorbed with (2p-1)/p^2, each unit (p-1)/p^2
    return [2 * p - 1] + [p - 1] * (p - 1)
L10 = law(10); L2, L5 = prime_law(2), prime_law(5)
crt = [L2[d % 2] * L5[d % 5] for d in range(10)]
print("base 10 product digit counts", L10, "= parity x five-ring", crt, L10 == crt)
L12 = law(12); L4 = law(4); L3 = prime_law(3)
print("base 12 counts", L12, "= Z/4 law x Z/3 law", [L4[d % 4] * L3[d % 3] for d in range(12)] == L12)
# unit ring <3> = Z/4: discrete logs add
dl = {1: 0, 3: 1, 9: 2, 7: 3}
print("units of Z/10 multiply by adding discrete logs:", all(dl[(u * v) % 10] == (dl[u] + dl[v]) % 4 for u in dl for v in dl))
# 4. the leading face under the integer gas at sigma = 1 (weights 1/n over whole decades) against Benford
for K in (3, 5):
    w = [Fraction(0)] * 10
    for n in range(10 ** (K - 1), 10 ** K): w[int(str(n)[0])] += Fraction(1, n)
    tot = sum(w); print("leading digit under 1/n weights, n in [10^%d, 10^%d):" % (K - 1, K), [round(float(w[d] / tot), 5) for d in range(1, 10)])
import math; print("Benford                                          :", [round(math.log10(1 + 1 / d), 5) for d in range(1, 10)])
