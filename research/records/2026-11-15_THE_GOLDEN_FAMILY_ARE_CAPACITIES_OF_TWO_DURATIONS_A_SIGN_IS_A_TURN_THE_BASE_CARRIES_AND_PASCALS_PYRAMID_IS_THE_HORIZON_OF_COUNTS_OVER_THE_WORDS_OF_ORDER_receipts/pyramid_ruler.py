"""Ruler for the record of November 15 (the supergolden ratio, turned bases, Pascal's pyramid): public arithmetic.

1. The golden family as capacities: tilings by pieces of two lengths grow at the root of sum X^(-t) = 1.
2. Signs carried by a turned base: base -1+i over the Gaussian integers, base w-1 over the Eisenstein integers.
3. Pascal's pyramid as the type simplex: the Laplace code is the cell's address plus the cell's width.
Every check is an assert.
"""
from fractions import Fraction
from itertools import product
from math import comb, factorial, log2
from decimal import Decimal, getcontext

getcontext().prec = 60

# 1. Tilings by two piece lengths, the root of their capacity polynomial, Pisot conjugates, Hankel rank.
def tilings(parts, n_max):
    N = [1] + [0] * n_max
    for n in range(1, n_max + 1):
        N[n] = sum(N[n - t] for t in parts if n - t >= 0)
    return N


def brute(parts, n):
    """Compositions of n into the given parts, by enumeration."""
    count = 0
    def go(rest):
        nonlocal count
        if rest == 0:
            count += 1
            return
        for t in parts:
            if t <= rest:
                go(rest - t)
    go(n)
    return count


def root(poly, lo, hi, steps=200):
    """Largest real root of poly (coefficients high to low) in [lo, hi] by bisection on Decimals (a reading)."""
    f = lambda x: sum(c * x ** (len(poly) - 1 - i) for i, c in enumerate(poly))
    lo, hi = Decimal(lo), Decimal(hi)
    for _ in range(steps):
        mid = (lo + hi) / 2
        if (f(mid) > 0) == (f(hi) > 0):
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2


def rank(m):
    m = [[Fraction(x) for x in row] for row in m]
    r = 0
    rows, cols = len(m), len(m[0])
    for c in range(cols):
        piv = next((i for i in range(r, rows) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        for i in range(rows):
            if i != r and m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [x - f * y for x, y in zip(m[i], m[r])]
        r += 1
    return r


def det(m):
    m = [[Fraction(x) for x in row] for row in m]
    d, size = Fraction(1), len(m)
    for c in range(size):
        piv = next((r for r in range(c, size) if m[r][c] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != c:
            m[c], m[piv] = m[piv], m[c]
            d = -d
        d *= m[c][c]
        for r in range(c + 1, size):
            f = m[r][c] / m[c][c]
            for cc in range(c, size):
                m[r][cc] -= f * m[c][cc]
    return d


family = [("golden (Fibonacci)", (1, 2), [1, -1, -1]),
          ("supergolden (Narayana)", (1, 3), [1, -1, 0, -1]),
          ("plastic (Padovan)", (2, 3), [1, 0, -1, -1])]
print("1. tilings by pieces of two lengths: the count's growth is the root of sum X^(-t) = 1")
for name, parts, poly in family:
    N = tilings(parts, 60)
    assert all(N[n] == brute(parts, n) for n in range(0, 25))
    r = root(poly, 1, 2)
    cap = sum(r ** (-t) for t in parts)
    assert abs(cap - 1) < Decimal(10) ** -40
    ratio = Decimal(N[60]) / Decimal(N[59])
    deg = len(poly) - 1
    hank = rank([[N[i + j] for j in range(8)] for i in range(8)])
    assert hank == deg
    # conjugates: product of the roots is (-1)^deg * constant term; for these units it is +-1, so the conjugates'
    # modulus squared (cubic) or modulus (quadratic) is 1/r: Pisot
    conj = (1 / r) if deg == 2 else (1 / r).sqrt()
    # power sums s_n = r^n + conjugates^n are integers by Newton's recurrence; r^n's distance to s_n shrinks
    s = {2: [2, 1], 3: [3, 1 if poly[1] == -1 else 0, None]}[deg]
    if deg == 3:
        e1, e2 = -poly[1], poly[2]  # x^3 - e1 x^2 + e2 x - e3
        e3 = -poly[3]
        s = [3, e1, e1 * e1 - 2 * e2]
        for n in range(3, 41):
            s.append(e1 * s[-1] - e2 * s[-2] + e3 * s[-3])
    else:
        s = [2, 1]
        for n in range(2, 41):
            s.append(s[-1] + s[-2])
    gaps = [abs(r ** n - s[n]) for n in (10, 20, 40)]
    assert gaps[0] > gaps[1] > gaps[2]
    print(f"  {name:<24} parts {parts}: N_1..N_12 = {N[1:13]}; N_60/N_59 = {ratio:.12f}; root {r:.12f}"
          f" = {r.ln():.6f} nats a tick; conjugate modulus {conj:.6f}; |root^n - s_n| at n = 10, 20, 40:"
          f" {gaps[0]:.2e}, {gaps[1]:.2e}, {gaps[2]:.2e}; Hankel rank {hank} (8 by 8)")
    assert abs(ratio - r) < Decimal(10) ** -6

# a complete prefix code's lengths, read as durations, have capacity root 2 (Kraft equality); nats give e.
for lengths in ([1, 2, 3, 3], [2, 2, 2, 3, 3], [1, 3, 3, 3, 3]):
    assert sum(Fraction(1, 2 ** l) for l in lengths) == 1
print("  complete prefix codes [1,2,3,3], [2,2,2,3,3], [1,3,3,3,3]: sum 2^(-l) = 1, so their lengths as durations"
      " have capacity root 2, one bit a tick; lengths in nats give root e, one nat a tick")

# 2. Turned bases: every Gaussian integer in base -1+i with digits {0, 1}; every Eisenstein integer in base w-1
# with digits {0, 1, 2}. Elements are pairs (a, b): a + b i, or a + b w with w^2 = -1 - w.
def expand(z, digit_of, step, mul_base, add, zero, limit=200):
    digits = []
    while z != zero:
        d = digit_of(z)
        digits.append(d)
        z = step(z, d)
        assert len(digits) < limit, "no termination"
    return digits


def value(digits, mul_base, add, zero):
    v = zero
    for d in reversed(digits):
        v = add(mul_base(v), (d, 0))
    return v


# Gaussian, base beta = -1 + i, norm 2: z = a + b i is divisible by beta iff a + b is even.
g_add = lambda u, v: (u[0] + v[0], u[1] + v[1])
g_mul = lambda u: (-u[0] - u[1], u[0] - u[1])  # (a + b i)(-1 + i) = (-a - b) + (a - b) i
def g_step(z, d):
    a, b = z[0] - d, z[1]
    # (a + b i)/(-1 + i) = (a + b i)(-1 - i)/2 = ((-a + b) + (-a - b) i)/2
    assert (b - a) % 2 == 0
    return ((b - a) // 2, (-a - b) // 2)
g_lengths = []
for a in range(-40, 41):
    for b in range(-40, 41):
        ds = expand((a, b), lambda z: (z[0] + z[1]) % 2, g_step, g_mul, g_add, (0, 0))
        assert value(ds, g_mul, g_add, (0, 0)) == (a, b)
        g_lengths.append(len(ds))

# Eisenstein, base beta = w - 1, norm 3, minimal polynomial x^2 + 3x + 3; w = 1 mod beta, so a + b w = a + b mod beta.
def e_mul(u):  # (a + b w)(w - 1) = a w - a + b w^2 - b w = (-a - b) + (a - 2b) w   [w^2 = -1 - w]
    a, b = u
    return (-a - b, a - 2 * b)
def e_step(z, d):
    a, b = z[0] - d, z[1]
    # 1/(w - 1) = (w^2 - 1)/3 = (-2 - w)/3; (a + b w)(-2 - w) = -2a - a w - 2b w - b w^2 = (-2a + b) + (-a - b) w
    x, y = -2 * a + b, -a - b
    assert x % 3 == 0 and y % 3 == 0
    return (x // 3, y // 3)
e_lengths = []
for a in range(-40, 41):
    for b in range(-40, 41):
        ds = expand((a, b), lambda z: (z[0] + z[1]) % 3, e_step, e_mul, g_add, (0, 0))
        assert value(ds, e_mul, g_add, (0, 0)) == (a, b)
        e_lengths.append(len(ds))
print(f"\n2. turned bases: base -1+i, digits {{0,1}}: all {len(g_lengths)} Gaussian integers with |a|,|b| <= 40 written"
      f" once, longest {max(g_lengths)} places; base w-1 (w a cube root of one), digits {{0,1,2}}: all {len(e_lengths)}"
      f" Eisenstein integers with |a|,|b| <= 40 written once, longest {max(e_lengths)} places; no sign and no axis label")
# the six units of the hexagon in base w - 1:
units = {"1": (1, 0), "-1": (-1, 0), "w": (0, 1), "-w": (0, -1), "w^2": (-1, -1), "-w^2": (1, 1)}
print("  the hexagon's six units in base w-1 (lowest place first):",
      {k: expand(v, lambda z: (z[0] + z[1]) % 3, e_step, e_mul, g_add, (0, 0)) for k, v in units.items()})

# 3. Pascal's pyramid: cells per layer, the Laplace code as address plus width, and the integers 2^a 3^b 5^c.
print("\n3. Pascal's pyramid as the type simplex")
layers = [comb(n + 2, 2) for n in range(5)]
cum = [comb(n + 3, 3) for n in range(5)]
assert layers == [1, 3, 6, 10, 15] and cum == [1, 4, 10, 20, 35]
print(f"  cells a layer {layers}, cumulative {cum} (the attached figure)")
checked = 0
for n in range(1, 9):
    for word in product(range(3), repeat=n):
        counts = [0, 0, 0]
        p = Fraction(1)
        for t, x in enumerate(word):
            p *= Fraction(counts[x] + 1, t + 3)
            counts[x] += 1
        multinomial = factorial(n) // (factorial(counts[0]) * factorial(counts[1]) * factorial(counts[2]))
        assert p == Fraction(1, comb(n + 2, 2) * multinomial)
        checked += 1
print(f"  every word over three letters to length 8 ({checked} words): the Laplace probability is 1/(cells x width),"
      " so its code is the cell's address log2 C(n+2,2) plus the cell's width log2 n!/(a!b!c!)")
# step: -log P(next letter x | counts) = log((n+3)/(a+1)) = log((n+1)/(a+1)) [width grows] + log((n+3)/(n+1)) [cells grow]
for n, a in [(0, 0), (5, 2), (5, 5), (40, 13)]:
    assert Fraction(n + 3, a + 1) == Fraction(n + 1, a + 1) * Fraction(n + 3, n + 1)
    assert comb(n + 3, 2) * (n + 1) == comb(n + 2, 2) * (n + 3)
corner = log2(comb(100 + 2, 2))
centre = log2(factorial(99) // (factorial(33) ** 3)) + log2(comb(99 + 2, 2))
print(f"  a word of 100 letters held at a corner (all x) costs only its address, {corner:.2f} bits; one at the centre"
      f" (33 of each, 99 letters) {centre:.2f} bits, against 99 log2 3 = {99 * log2(3):.2f}")

def ordered_prime_factorizations(limit, primes=(2, 3, 5)):
    f = {1: 1}
    smooth = sorted(2 ** a * 3 ** b * 5 ** c for a in range(15) for b in range(10) for c in range(7)
                    if 2 ** a * 3 ** b * 5 ** c <= limit)
    for m in smooth[1:]:
        f[m] = sum(f[m // p] for p in primes if m % p == 0)
    return f

f = ordered_prime_factorizations(10 ** 5)
for m, ways in f.items():
    a = b = c = 0
    x = m
    while x % 2 == 0: x //= 2; a += 1
    while x % 3 == 0: x //= 3; b += 1
    while x % 5 == 0: x //= 5; c += 1
    assert ways == factorial(a + b + c) // (factorial(a) * factorial(b) * factorial(c))
print(f"  with x, y, z = 2, 3, 5: every 5-smooth integer up to 10^5 ({len(f)} of them) is a cell, its layer Omega,"
      f" and its count of ordered prime factorizations is the cell's multinomial (360 = 2^3 3^2 5: {f[360]} orderings)")
print("\nevery check passed")
