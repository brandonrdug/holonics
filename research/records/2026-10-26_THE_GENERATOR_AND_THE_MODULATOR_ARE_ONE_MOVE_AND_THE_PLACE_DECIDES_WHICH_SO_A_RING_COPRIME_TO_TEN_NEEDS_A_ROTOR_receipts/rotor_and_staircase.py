"""The rotor at the tower, and why only the base's neighbours are one-plane turns: exact checks.

The follow-up to generator_modulator.py (parts A to G). Every check is in integers and
fractions.Fraction; phases are held as exponents of a root of unity. No float is built.

Parts:
  H. The rotor at the tower: a ring of K modes stepped once a digit and turned by 10^j d holds n
     mod every divisor of 10^K - 1; one register read on past an operator holds the concatenation,
     which is the sum only mod 9; a k-digit class acts on ring 11 as x -> (-1)^k x + D; a mode that
     reads another mode's state keeps the passivity bound.
  I. One plane in any base b: the digit maps on Z/m are a turn, a mirror or a flattening exactly
     when m divides b - 1, b + 1 or b, the base's three neighbours.
  J. The grain staircase: read k digits at once and the one-plane rings are the divisors of
     10^k - 1, 10^k + 1 and 10^k; every ring coprime to 10, or made of 2s and 5s, arrives at some
     grain, and a ring mixing both kinds never does; prime powers climb by lifting the exponent.
  K. The rotor's planes are the Galois orbit of 10 on the ring's roots of unity, up to the mirror;
     whether the half-way grain (p - 1)/2 is a turn or a mirror is (10/p), which depends on p mod 40.
  L. The base's coprime factors nest: in base b = r s the endings divisible by r are a copy of ring s.
  M. Music: a step on twelve notes is gcd(step, 12) strokes; 3^a never meets 2^b.
  N. The pair contact's bilinear block reads the sum and the difference of two phases at once.
"""
import sys
import time
from fractions import Fraction
from math import gcd

T0 = time.monotonic()
CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", what)
        sys.exit(1)


def digits_of(n, b=10):
    if n == 0:
        return [0]
    out = []
    while n:
        out.append(n % b)
        n //= b
    return out[::-1]


def ord_walk(a, m):
    k, x = 1, a % m
    while x != 1 % m:
        x = x * a % m
        k += 1
    return k


def primes_below(n):
    sieve = bytearray([1]) * n
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i < n:
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
        i += 1
    return [i for i in range(n) if sieve[i]]


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def vp(n, p):
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


# ---------------------------------------------------------------- H. the rotor at the tower
print("H. The rotor at the tower")


def ring_read(m, K, n):
    """K modes, mode j holding the exponent of chi_(10^j)(n) mod m; the restart state is chi(0) = 1.
    Each digit steps the ring once (mode j takes old mode j + 1) and turns mode j by 10^j d."""
    h = [0] * K
    for d in digits_of(n):
        h = [(h[(j + 1) % K] + pow(10, j, m) * d) % m for j in range(K)]
    return h


for K in (1, 2, 3, 4, 6):
    M = 10**K - 1
    for m in divisors(M)[1:]:
        for n in range(0, 20000, 7):
            h = ring_read(m, K, n)
            check(all(h[j] == pow(10, j, m) * n % m for j in range(K)), f"ring K={K} m={m} n={n}")
print("   a ring of K modes (step once a digit, mode j turned by 10^j d) holds n mod every divisor")
print("   of 10^K - 1, K = 1, 2, 3, 4, 6 (9, 99, 999, 9999 = 3^2 11 101, 999999 = 3^3 7 11 13 37)")

for a in range(0, 400, 3):
    for b in range(0, 400, 7):
        k = len(str(b))
        c = a * 10**k + b
        check(c % 9 == (a + b) % 9, "concatenation mod 9")
        check(c % 10 == b % 10, "concatenation mod 10")
        check(c % 11 == ((-1) ** k * a + b) % 11, "concatenation mod 11")
print("   read on past '+', one register holds the concatenation 10^len(b) a + b: a + b mod 9,")
print("   (-1)^len(b) a + b mod 11, b mod 10; ring 9 is the one ring where it is the sum")

for D in range(100000):
    k = len(str(D))
    for x in range(11):
        y = x
        for d in digits_of(D):
            y = (-y + d) % 11
        check(y == ((-1) ** k * x + D) % 11, "k-digit class on ring 11")
    if k % 2:
        check((D - 6 * D) % 11 == 6 * D % 11, "mirror about 6D")  # x -> D - x fixes x = 6D
print("   a k-digit class acts on ring 11 as x -> (-1)^k x + D: a turn for even k, the mirror")
print("   about 6D for odd k (every D < 10^5): 22 actions, the dihedral group of 11")

# Passivity: rho K + sqrt(1 - rho^2) <= K(rho_max) for rho <= rho_max, K(r) = sqrt((1+r)/(1-r)),
# checked squared: 1 - rho^2 <= K(rho_max)^2 (1 - rho)^2.
for num in range(1, 4096):
    rmax = Fraction(num, 4096)
    K2 = (1 + rmax) / (1 - rmax)
    for rn in range(0, num + 1, 37):
        r = Fraction(rn, 4096)
        check(1 - r * r <= K2 * (1 - r) ** 2, "passivity under a permutation")
print("   a mode that reads another mode's state keeps |h| <= sqrt((1+rho_max)/(1-rho_max)) max|Bx|")


# ---------------------------------------------------------------- I. one plane in any base
print("I. One plane in any base: the base's three neighbours")


def one_plane_kind(b, m):
    """Classify the digit maps k -> b k + d on Z/m (d < b): 'flat' if every map is constant,
    'turn' or 'mirror' if every map is k -> k + c or k -> c - k, else None."""
    maps = [[(b * k + d) % m for k in range(m)] for d in range(b)]
    if all(len(set(f)) == 1 for f in maps):
        return "flat"
    if all(all((f[k] - f[0]) % m == k % m for k in range(m)) for f in maps):
        return "turn"
    if all(all((f[k] - f[0]) % m == (-k) % m for k in range(m)) for f in maps):
        return "mirror"
    return None


for b in range(2, 61):
    rings = {}
    for m in range(2, 2 * b + 3):
        kind = one_plane_kind(b, m)
        if kind:
            rings[m] = kind
    want = set(divisors(b - 1)[1:] if b > 2 else []) | set(divisors(b)[1:]) | set(divisors(b + 1)[1:])
    check(set(rings) == want, f"one-plane rings of base {b}")
    for m, kind in rings.items():
        if b % m == 0:
            check(kind == "flat", f"flat {b} {m}")
        elif (b - 1) % m == 0:
            check(kind == "turn", f"turn {b} {m}")
        else:
            check(kind == "mirror", f"mirror {b} {m}")
r10 = sorted(m for m in range(2, 40) if one_plane_kind(10, m))
r9 = sorted(m for m in range(2, 40) if one_plane_kind(9, m))
check(r10 == [2, 3, 5, 9, 10, 11] and r9 == [2, 3, 4, 5, 8, 9, 10], "bases 10 and 9")
check(one_plane_kind(9, 2) == "turn", "in base 9, 2 is a turn (9 = 1 = -1 mod 2)")
print("   bases 2..60: the one-plane rings are exactly the divisors of b - 1 (turns), b + 1 (mirrors)")
print("   and b (flattenings); base 10:", r10, " base 9:", r9)


# ---------------------------------------------------------------- J. the grain staircase
print("J. The grain staircase")


def least_grain(m, b=10, kmax=None):
    kmax = kmax or m  # a ring that arrives does so by k <= m: the order divides phi(m), max(v_2, v_5) < m
    for k in range(1, kmax + 1):
        r = pow(b, k, m)
        if r in (0, 1, m - 1):
            return k
    return None


table = {}
for m in range(2, 2000):
    k = least_grain(m)
    two_five = m
    while two_five % 2 == 0:
        two_five //= 2
    while two_five % 5 == 0:
        two_five //= 5
    core = two_five  # the part of m coprime to 10
    if core == 1:
        want = max(vp(m, 2), vp(m, 5))
        check(k == want, f"grain of {m}")
    elif core == m:
        o = ord_walk(10, m)
        want = o // 2 if (o % 2 == 0 and pow(10, o // 2, m) == m - 1) else o
        check(k == want, f"grain of {m}")
    else:
        check(k is None, f"mixed ring {m} never fits one plane")
    table[m] = k
for k in range(1, 5):
    # Read k digits at once: the base is 10^k, so by part I the one-plane rings are its neighbours'.
    rings = sorted(m for m in range(2, 2000) if pow(10, k, m) in (0, 1, m - 1))
    want = sorted((set(divisors(10**k - 1)) | set(divisors(10**k)) | set(divisors(10**k + 1))) - {1})
    check(rings == [m for m in want if m < 2000], f"one-plane rings at grain {k}")
    for m in rings:
        check(table[m] is not None and table[m] <= k, f"grain {k} ring {m} has arrived")
check(table[101] == 2 and pow(10, 3, 101) not in (0, 1, 100), "101 at two digits, not at three")
check(table[4] == 2 and table[25] == 2 and table[7] == 3 and table[13] == 3 and table[37] == 3,
      "4 and 25 at two digits, 7, 13 and 37 at three")
check(1001 == 7 * 11 * 13, "1001")
mixed = [m for m in range(2, 60) if table[m] is None]
check(mixed[:6] == [6, 12, 14, 15, 18, 22], "the first mixed rings")
# Lifting the exponent: v_3(10^k - 1) = 2 + v_3(k), v_11(10^k + 1) = 1 + v_11(k) for odd k,
# v_11(10^k - 1) = 1 + v_11(k) for even k.
for k in range(1, 301):
    check(vp(10**k - 1, 3) == 2 + vp(k, 3), f"LTE 3 at {k}")
    if k % 2:
        check(vp(10**k + 1, 11) == 1 + vp(k, 11), f"LTE 11 at {k}")
    else:
        check(vp(10**k - 1, 11) == 1 + vp(k, 11), f"LTE 11 at {k}")
pp = {p: [least_grain(p**a) for a in range(1, 5)] for p in (2, 3, 5, 7, 11)}
check(pp[3] == [1, 1, 3, 9] and pp[11] == [1, 11, 121, 1331] and pp[2] == [1, 2, 3, 4], "staircases")
print("   least grain at which ring m is one plane (10^k = 0, 1 or -1 mod m), m < 2000: ord/2 or ord")
print("   for m coprime to 10, max(v_2, v_5) for m made of 2s and 5s, never for a ring mixing both")
print("   (first: 6, 12, 14, 15, 18, 22); the grain-k rings are the divisors of 10^k - 1, 10^k, 10^k + 1")
print("   prime-power staircases (grain of p, p^2, p^3, p^4):", pp)


# ---------------------------------------------------------------- K. the Galois orbit
print("K. The rotor's planes are the Galois orbit of 10, up to the mirror")


def legendre_by_reciprocity(a, p):
    """The Jacobi symbol (a/p) by quadratic reciprocity (no powering)."""
    a %= p
    s = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if p % 8 in (3, 5):
                s = -s
        a, p = p, a
        if a % 4 == 3 and p % 4 == 3:
            s = -s
        a %= p
    return s if p == 1 else 0


by40 = {}
planes_seen = {}
for p in primes_below(100000):
    if p in (2, 3, 5):
        continue
    o = ord_walk(10, p) if p < 1000 else None
    if o is not None:
        orbit = {pow(10, j, p) for j in range(o)}
        with_mirror = orbit | {(-x) % p for x in orbit}
        planes = len(with_mirror) // 2
        check(planes == (o // 2 if o % 2 == 0 else o), f"planes at {p}")
        planes_seen[p] = planes
    leg = legendre_by_reciprocity(10, p)
    check(pow(10, (p - 1) // 2, p) == leg % p, f"Euler's criterion at {p}")
    if p % 40 in by40:
        check(by40[p % 40] == leg, f"(10/p) by p mod 40 at {p}")
    by40[p % 40] = leg
check([planes_seen[p] for p in (7, 13, 37, 101, 41, 73, 17)] == [3, 3, 3, 2, 5, 4, 8], "plane counts")
mirrors = sorted(r for r, s in by40.items() if s == -1)
print("   for primes p < 1000: planes = |<10, -1>|/2 (ring 7: 3, 13: 3, 37: 3, 101: 2, 41: 5, 73: 4,")
print("   17: 8); for primes p < 10^5: 10^((p-1)/2) = (10/p) (Euler), and (10/p) depends only on")
print("   p mod 40 (quadratic reciprocity); the half-way grain is a mirror for p mod 40 in", mirrors)


# ---------------------------------------------------------------- L. the base's factors nest
print("L. The base's coprime factors nest")
for b in range(2, 61):
    for r in divisors(b):
        s = b // r
        if gcd(r, s) != 1 or r == 1 or s == 1:
            continue
        copy = [r * j % b for j in range(s)]
        check(sorted(copy) == [x for x in range(b) if x % r == 0], f"r Z/b in base {b}")
        for i in range(s):
            for j in range(s):
                check((copy[i] + copy[j]) % b == copy[(i + j) % s], f"copy adds, base {b}")
        check(sorted(x % s for x in copy) == list(range(s)), f"the copy reads every residue mod s, {b}")
check([2 * j % 10 for j in range(5)] == [0, 2, 4, 6, 8] and [5 * j % 10 for j in range(2)] == [0, 5],
      "base 10: the even endings are ring 5, the endings 0 and 5 are ring 2")
print("   in base b = r s (r, s coprime) the endings divisible by r add as ring s and read every")
print("   residue mod s once (bases 2..60):")
print("   in base 10 the even endings 0, 2, 4, 6, 8 are ring 5 and the endings 0, 5 are ring 2")


# ---------------------------------------------------------------- M. music
print("M. Music: steps on twelve notes")
for step in range(1, 12):
    seen, strokes = set(), 0
    for start in range(12):
        if start in seen:
            continue
        strokes += 1
        x = start
        while x not in seen:
            seen.add(x)
            x = (x + step) % 12
    check(strokes == gcd(step, 12), f"strokes of step {step}")
check(gcd(7, 12) == 1 and gcd(3, 12) == 3 and gcd(4, 12) == 4, "fifths, diminished, augmented")
for a in range(1, 61):
    for bb in range(1, 101):
        check(3**a != 2**bb, "3^a never meets 2^b")
comma = Fraction(3**12, 2**19)
check(comma == Fraction(531441, 524288), "the Pythagorean comma")
print("   a step s on twelve notes is gcd(s, 12) strokes: fifths (7) one stroke, minor thirds (3)")
print("   three diminished sevenths, major thirds (4) four augmented triads; 3^a never meets 2^b,")
print("   and twelve fifths overshoot seven octaves by 3^12/2^19 = 531441/524288")


# ---------------------------------------------------------------- N. the bilinear block
print("N. The pair contact's bilinear block reads the sum and the difference")


def gm(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def gc(a):
    return (a[0], -a[1])


R = range(-3, 4)
for c1 in ((x, y) for x in R for y in R):
    for c2 in ((x, y) for x in (-2, 1, 3) for y in (-1, 2)):
        for h1 in ((x, y) for x in (-2, 0, 3) for y in (-3, 1)):
            for h2 in ((x, y) for x in (-1, 2) for y in (-2, 0, 3)):
                lhs = 2 * gm(c1, h1)[0] * gm(c2, h2)[0]
                rhs = gm(gm(c1, c2), gm(h1, h2))[0] + gm(gm(c1, gc(c2)), gm(h1, gc(h2)))[0]
                check(lhs == rhs, "bilinear sum and difference")
for m in (9, 10, 11, 7, 13, 101):
    for a in range(0, 300, 7):
        for b in range(0, 300, 11):
            check((a % m + b % m) % m == (a + b) % m and (a % m - b % m) % m == (a - b) % m, "phases")
print("   2 Re(c1 h1) Re(c2 h2) = Re(c1 c2 h1 h2) + Re(c1 conj(c2) h1 conj(h2)) in Gaussian integers:")
print("   h1 h2 carries the phase of a + b and h1 conj(h2) that of a - b, on every ring at once")

ms = int((time.monotonic() - T0) * 1000)
print(f"all {CHECKS} checks hold ({ms} ms)")
