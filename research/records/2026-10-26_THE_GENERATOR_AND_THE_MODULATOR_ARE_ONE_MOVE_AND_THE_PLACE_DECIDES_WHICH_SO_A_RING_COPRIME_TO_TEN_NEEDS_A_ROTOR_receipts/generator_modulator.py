"""The generator and the modulator are one move: exact checks.

Every check is in integers and fractions.Fraction. Decimals in the output are readings printed by
integer division beside fractions and enter no check. No float is built.

Parts:
  A. One move, one pivot: x -> 10x + d is the dilation by 10 about -d/9, the repdigit ...ddd.
  B. The place decides the kind: the same multiplier is a boost, a contraction, a shear, a
     half-turn or a turn of order ord_p(10), and the product formula ties the places.
  C. Unicursal or a link: the remainder orbit of long division is one stroke iff 10 generates.
  D. What one plane carries: a ring coprime to 10 fits one plane (any chart) iff 10 = 1 or -1 mod m;
     in the phase chart, iff 10 = 0, 1 or -1; the suffix fits one contracting coordinate.
  E. The rotor: every other coprime ring needs a ring of coupled modes, ord_p(10) or half of it
     planes, and in the phase chart the last k digits need a chain of k planes (the cascade).
  F. Fourier exchanges the generator and the modulator; their commutator is a phase; a ring's
     stepping is a turn in its dual chart; the quadratic Gauss sum squares to +-q.
  G. The torus: two shears (Dehn twists) compose into a boost, a turn of order 6 and the quarter
     turn; two boosts compose into a shear; fixed points are Lucas numbers; coprime windings are
     one stroke.
"""
import sys
import time
from fractions import Fraction
from math import gcd, isqrt

T0 = time.monotonic()
CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", what)
        sys.exit(1)


def primes_below(n):
    sieve = bytearray([1]) * n
    sieve[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n - 1) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(n) if sieve[i]]


def ord_walk(a, m):
    """Multiplicative order of a mod m (gcd(a, m) = 1), by walking the orbit."""
    k, x = 1, a % m
    while x != 1 % m:
        x = x * a % m
        k += 1
    return k


def ord_mod(a, p):
    """Multiplicative order of a mod a prime p, by reducing p - 1 over its prime factors."""
    k, t, f = p - 1, p - 1, 2
    factors = []
    while f * f <= t:
        if t % f == 0:
            factors.append(f)
            while t % f == 0:
                t //= f
        f += 1
    if t > 1:
        factors.append(t)
    for f in factors:
        while k % f == 0 and pow(a, k // f, p) == 1:
            k //= f
    return k


def reading(fr, places=6):
    """A decimal reading of a nonnegative Fraction by integer division (printing only)."""
    whole = fr.numerator // fr.denominator
    rest = fr - whole
    digits = (rest * 10 ** places).numerator // (rest * 10 ** places).denominator
    return f"{whole}.{digits:0{places}d}"


def digits_of(n):
    return [int(c) for c in str(n)]


# ---------------------------------------------------------------- A. one move, one pivot
print("A. One move, one pivot")
pivot = {d: Fraction(-d, 9) for d in range(10)}
for d in range(10):
    check(10 * pivot[d] + d == pivot[d], f"pivot of digit {d}")
# Horner as a word of dilations about the digits' pivots, over every numeral below 10^5.
for n in range(100000):
    x = Fraction(0)
    for d in digits_of(n):
        x = 10 * (x - pivot[d]) + pivot[d]
    check(x == n, f"Horner as pivot word at {n}")
# The pivot -d/9 is the repdigit ...ddd in the 10-adic integers: mod 10^k it is d repeated k times.
for k in range(1, 13):
    m = 10 ** k
    inv9 = pow(9, -1, m)
    for d in range(10):
        check((-d * inv9) % m == int(str(d) * k) % m, f"repdigit pivot d={d} k={k}")
print("   x -> 10x + d is the dilation by 10 about -d/9 (checked for d = 0..9);")
print("   every numeral below 10^5 is the word of those dilations (100,000 numerals);")
print("   mod 10^k, k = 1..12, the pivot -d/9 is the repdigit dd...d (e.g. -1 = ...999).")

# ---------------------------------------------------------------- B. the place decides the kind
print("B. The place decides the kind")
# Product formula for the multiplier 10, and for every a in 2..2000.
abs_inf = Fraction(10)
abs_2 = Fraction(1, 2)
abs_5 = Fraction(1, 5)
check(abs_inf * abs_2 * abs_5 == 1, "product formula for 10")
for a in range(2, 2001):
    prod = Fraction(a)
    t = a
    p = 2
    while t > 1:
        while t % p == 0:
            prod /= p
            t //= p
        p += 1
    check(prod == 1, f"product formula for {a}")
print("   |10| = 10 at the real place (a boost: digits grow), 1/2 at 2 and 1/5 at 5 (a contraction")
print("   toward the pivot: the units-first, suffix geometry); the product is 1 (and for a = 2..2000).")
rows = []
for p in primes_below(110):
    if p in (2, 5):
        continue
    k = ord_mod(10, p)
    # The decimal period of 1/p by long division: the remainder orbit r -> 10r from r = 1.
    r, period = 1, 0
    while True:
        r = r * 10 % p
        period += 1
        if r == 1:
            break
    check(period == k, f"decimal period of 1/{p} is ord_p(10)")
    if k == 1:
        kind = "shear: a translation, x -> x + d"
    elif k == 2:
        kind = "half-turn: x -> d - x"
    else:
        kind = f"turn of order {k}"
    rows.append((p, k, kind))
for p, k, kind in rows:
    print(f"   p = {p:3d}: ord_p(10) = {k:3d} = the period of 1/{p}; at this place the move is a {kind}")

# ---------------------------------------------------------------- C. unicursal or a link
print("C. One stroke or a link")
counts = {}
ps = [p for p in primes_below(100000) if p not in (2, 5)]
full = 0
strokes_hist = {}
idx = 0
for N in (1000, 10000, 100000):
    while idx < len(ps) and ps[idx] < N:
        p = ps[idx]
        k = ord_mod(10, p)
        strokes = (p - 1) // k
        check((p - 1) % k == 0, f"ord divides p-1 at {p}")
        if strokes == 1:
            full += 1
        strokes_hist[strokes] = strokes_hist.get(strokes, 0) + 1
        idx += 1
    counts[N] = (full, idx)
# Direct check of the stroke count on small primes: orbits of r -> 10r on (Z/p)^*.
for p in primes_below(400):
    if p in (2, 5):
        continue
    seen, orbits = set(), 0
    for r0 in range(1, p):
        if r0 in seen:
            continue
        orbits += 1
        r = r0
        while r not in seen:
            seen.add(r)
            r = r * 10 % p
    check(orbits == (p - 1) // ord_mod(10, p) == (p - 1) // ord_walk(10, p), f"orbit count at {p}")
artin = Fraction(1)
for q in primes_below(1000):
    artin *= Fraction(q * (q - 1) - 1, q * (q - 1))
for N, (f, t) in counts.items():
    print(f"   primes below {N:6d} (2 and 5 left out): {t}; the long division of 1/p is one stroke")
    print(f"     through every nonzero remainder (10 generates) at {f}, share {reading(Fraction(f, t))}")
print(f"   Artin's product over primes below 1000: {reading(artin)} (a reading; the density of")
print("   primes where 10 generates is Artin's constant if GRH holds, Hooley 1967)")
top = sorted(strokes_hist.items())[:6]
print("   strokes per prime below 10^5 (strokes: primes):", ", ".join(f"{s}: {c}" for s, c in top), "...")

# ---------------------------------------------------------------- D. what one plane carries
print("D. What one plane carries")
# For m coprime to 10 the digit maps x -> 10x + d generate the whole affine group of Z/m, every
# translation included (BFS over pairs (a, b) meaning x -> a x + b).
for m in range(3, 120):
    if gcd(m, 10) != 1:
        continue
    gens = [(10 % m, d % m) for d in range(10)]
    seen = {(1, 0)}
    frontier = [(1, 0)]
    while frontier:
        nxt = []
        for (a, b) in frontier:
            for (c, e) in gens:
                g = (c * a % m, (c * b + e) % m)  # apply (a, b) then (c, e)
                if g not in seen:
                    seen.add(g)
                    nxt.append(g)
        frontier = nxt
    k = ord_walk(10, m)
    check(len(seen) == m * k, f"affine group of Z/{m} has m * ord elements")
    check(all((1, b) in seen for b in range(m)), f"every translation of Z/{m}")
coprime_one_plane = [m for m in range(3, 301) if gcd(m, 10) == 1 and 10 % m in (1, m - 1)]
check(coprime_one_plane == [3, 9, 11], f"coprime one-plane rings {coprime_one_plane}")
phase_one_plane = [m for m in range(2, 301) if 10 % m in (0, 1, m - 1)]
check(phase_one_plane == [2, 3, 5, 9, 10, 11], f"phase-chart one-plane rings {phase_one_plane}")
print("   for every m < 120 coprime to 10 the digit maps generate the whole affine group of Z/m,")
print("   m * ord_m(10) moves with every translation; so any one-plane realization is a finite group")
print("   of turns, and the digit move can only send a turn to itself or its inverse:")
print("   rings coprime to 10 that one plane carries (m <= 300):", coprime_one_plane)
print("   in the phase chart (the residue held as a turn, where a sum is one crossing) one plane")
print("   carries exactly the rings", phase_one_plane, "(10 = 0, 1 or -1 mod m)")


def grain(m):
    for k in range(1, 61):
        if pow(10, k, m) in (0, 1, m - 1):
            return k
    return None


print("   least digit grain k at which one plane carries ring m (10^k = 0, 1 or -1 mod m):")
line = []
for m in (2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 16, 20, 25, 27, 33, 37, 41, 73, 99, 100, 101):
    line.append(f"{m}:{grain(m)}")
print("     " + "  ".join(line))
check(grain(7) == 3 and grain(13) == 3 and grain(101) == 2 and grain(37) == 3, "1001 and 101 grains")
check(1001 == 7 * 11 * 13 and 999 == 27 * 37 and 101 * 99 == 9999, "factorizations")
# Explicit realizations over every numeral below 10^5.
for n in range(100000):
    ds = digits_of(n)
    e9 = 0
    e11 = 0
    x = Fraction(0)
    s_, t_ = 0, 0
    for d in ds:
        e9 = (e9 + d) % 9  # phase chart, ring 9: a turn by d (translation)
        e11 = (d - e11) % 11  # phase chart, ring 11: conjugate, then turn by d (half-turn)
        x = (x + d) / 10  # coordinate chart: a contraction by 1/10, the suffix address
        s_, t_ = d, s_  # one real plane, nilpotent move (s, t) -> (d, s): units and tens
    check(e9 == n % 9 and e11 == n % 11, f"one-plane phase reads at {n}")
    check(ds[-1] % 10 == n % 10, f"reset read at {n}")
    for j in range(1, len(ds) + 1):
        y = x * 10 ** j
        check((y.numerator // y.denominator) % 10 == (n // 10 ** (j - 1)) % 10, f"suffix digit {j} of {n}")
    check((s_, t_) == (n % 10, (n // 10) % 10), f"nilpotent plane at {n}")
print("   checked on every numeral below 10^5: ring 9 is a turn by each digit, ring 11 a conjugation")
print("   then a turn, ring 10 a reset; one contracting coordinate x -> (x + d)/10 holds every digit")
print("   of the suffix (the j-th from the end is the j-th place of x: the chaos-game address);")
print("   one real plane holds units and tens as two coordinates by the nilpotent move (s, t) -> (d, s)")

# ---------------------------------------------------------------- E. the rotor and the cascade
print("E. The rotor and the cascade")


def rotor_read(m, n):
    """Complex modes for the characters a in the orbit of 1 under x10 (mod m), as exponents of
    omega_m. Mode a holds a*x; the digit d moves it to old mode 10a times omega^(a d). A mode
    whose character is 0 is the constant. Returns the exponent of mode 1 after reading n."""
    orbit, a = [], 1 % m
    while a not in orbit:
        orbit.append(a)
        a = a * 10 % m
    state = {a: 0 for a in orbit}
    state[0] = 0
    for d in digits_of(n):
        new = {}
        for a in orbit:
            new[a] = (state.get(a * 10 % m, 0) + a * d) % m
        new[0] = 0
        state = new
    return state[1 % m], orbit


def planes(m):
    _, orbit = rotor_read(m, 0)
    chars = set(a for a in orbit if a != 0)
    both = chars | set((-a) % m for a in chars)
    return len(both) // 2 + (len(both) % 2), sorted(chars)


table = []
for m in (3, 7, 9, 11, 13, 17, 37, 41, 73, 101, 1001, 4, 8, 20, 40, 100, 1000):
    for n in range(3000):
        got, _ = rotor_read(m, n)
        check(got == n % m, f"rotor reads {n} mod {m}")
    pl, chars = planes(m)
    table.append((m, pl, len(chars)))
for m, pl, nc in table:
    kind = "cycle" if gcd(m, 10) == 1 else "chain into the constant"
    print(f"   ring {m:4d}: {nc} characters in the orbit of 1 under x10 ({kind}); real planes {pl}")
for p in primes_below(200):
    if p in (2, 5):
        continue
    k = ord_mod(10, p)
    pl, _ = planes(p)
    check(pl == (k // 2 if k % 2 == 0 else k), f"plane count at {p}")
    check(k == ord_walk(10, p), f"order by walk at {p}")
    if k % 2 == 0:
        check(pow(10, k // 2, p) == p - 1, f"even order puts -1 in <10> at {p}")
print("   for every prime p < 200 (not 2, 5): planes = ord_p(10)/2 when the order is even, else ord_p(10);")
print("   every ring above reads every numeral below 3000 exactly.")

# ---------------------------------------------------------------- F. Fourier exchange
print("F. Fourier exchanges the generator and the modulator")
for n in range(2, 41):
    # Exponent forms: X e_k = e_(k+1) (shift), Z e_k = w^k e_k (clock), F_jk = w^(jk).
    for j in range(n):
        for k in range(n):
            fx = (j * ((k + 1) % n)) % n  # (F X)_jk = F_(j, k+1)
            zf = (j + j * k) % n  # (Z F)_jk = w^j F_jk
            check(fx == zf, f"F X = Z F at n={n}")
            fz = (j * k + k) % n  # (F Z)_jk = F_jk w^k
            xinvf = (((j + 1) % n) * k) % n  # (X^-1 F)_jk = F_(j+1, k)
            check(fz == xinvf, f"F Z = X^-1 F at n={n}")
    for k in range(n):
        zx = (k + 1) % n  # Z X e_k = w^(k+1) e_(k+1)
        xz = k % n  # X Z e_k = w^k e_(k+1)
        check((zx - xz) % n == 1, f"Z X = w X Z at n={n}")
print("   n = 2..40: F X = Z F and F Z = X^-1 F (the shift and the clock exchange), Z X = w X Z")


# Ring of four: the 4-point Fourier chart is exact in Gaussian integers; a turn of the dual
# chart by i^(k s) is the cyclic shift by s of the ring (F X F^-1 = Z, part F).
def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def gpow_i(e):
    return [(1, 0), (0, 1), (-1, 0), (0, -1)][e % 4]


for s in range(4):
    for col in range(4):
        # Apply F^-1 diag(i^(k s)) F to the basis vector e_col; F_jk = i^(jk), F^-1 = conj(F)/4.
        v = [(1 if r == col else 0, 0) for r in range(4)]
        g = [(0, 0)] * 4
        for k in range(4):
            acc = (0, 0)
            for r in range(4):
                t = gmul(gpow_i(k * r), v[r])
                acc = (acc[0] + t[0], acc[1] + t[1])
            g[k] = gmul(acc, gpow_i(k * s))
        out = []
        for r in range(4):
            acc = (0, 0)
            for k in range(4):
                t = gmul(gpow_i(-r * k), g[k])
                acc = (acc[0] + t[0], acc[1] + t[1])
            check(acc[0] % 4 == 0 and acc[1] % 4 == 0, "dyadic quarter")
            out.append((acc[0] // 4, acc[1] // 4))
        want = [(1 if r == (col + s) % 4 else 0, 0) for r in range(4)]
        check(out == want, f"dual turn is the shift by {s}")
print("   ring of four: F^-1 diag(i^(ks)) F e_c = e_(c+s), exactly in Gaussian integers over 4")
gauss_rows = []
for q in primes_below(60):
    if q == 2:
        continue
    tau = [0] * q
    for a in range(1, q):
        tau[a] = 1 if pow(a, (q - 1) // 2, q) == 1 else -1
    sq = [0] * q
    for a in range(q):
        if tau[a]:
            for b in range(q):
                if tau[b]:
                    sq[(a + b) % q] += tau[a] * tau[b]
    sign = 1 if q % 4 == 1 else -1
    sq[0] -= sign * q
    check(len(set(sq)) == 1, f"tau^2 = (-1/q) q at q={q}")  # a multiple of 1 + x + ... + x^(q-1)
    gauss_rows.append(f"{q}:{'+' if sign > 0 else '-'}{q}")
print("   the quadratic character (the +-1 sheet) against the additive turn: tau^2 = (-1/q) q for")
print("   every odd prime q < 60 (" + ", ".join(gauss_rows[:6]) + ", ...): |tau| = q^(1/2)")

# ---------------------------------------------------------------- G. the torus
print("G. The torus: twists compose into every kind")


def mm(a, b):
    return [[a[0][0] * b[0][0] + a[0][1] * b[1][0], a[0][0] * b[0][1] + a[0][1] * b[1][1]],
            [a[1][0] * b[0][0] + a[1][1] * b[1][0], a[1][0] * b[0][1] + a[1][1] * b[1][1]]]


def inv(a):
    return [[a[1][1], -a[0][1]], [-a[1][0], a[0][0]]]  # det 1


def tr(a):
    return a[0][0] + a[1][1]


def kind(a):
    t = abs(tr(a))
    return "turn" if t < 2 else ("shear" if t == 2 else "boost")


I = [[1, 0], [0, 1]]
NEG = [[-1, 0], [0, -1]]
T = [[1, 1], [0, 1]]  # sigma_1: the Dehn twist about one cycle
L = [[1, 0], [-1, 1]]  # sigma_2: the twist about the other
check(mm(mm(T, L), T) == mm(mm(L, T), L), "braid relation")
cat = mm(T, inv(L))
check(cat == [[2, 1], [1, 1]] and tr(cat) == 3 and kind(cat) == "boost", "cat map")
six = mm(T, L)
check(tr(six) == 1 and mm(mm(six, six), six) == NEG, "order-6 turn")
S = mm(mm(T, L), T)
check(S == [[0, 1], [-1, 0]] and mm(S, S) == NEG, "quarter turn")
A = [[2, 1], [1, 1]]
B = [[1, 1], [1, 2]]
comm = mm(mm(A, B), mm(inv(A), inv(B)))
check(tr(comm) == -2 and kind(comm) == "shear" and kind(A) == "boost" and kind(B) == "boost",
      "commutator of two boosts is a shear")
print(f"   T = sigma_1, L = sigma_2: T L T = L T L; T L^-1 = {cat} (boost, trace 3: the cat map);")
print(f"   T L has trace 1 and (T L)^3 = -I (a turn of order 6); T L T = {S}, the quarter turn")
print(f"   (the Fourier chart, S^2 = -I); [A, B] = {comm} for the boosts A, B: trace -2, a shear")
lucas = [2, 1]
for _ in range(60):
    lucas.append(lucas[-1] + lucas[-2])
Ak = I
for k in range(1, 21):
    Ak = mm(Ak, A)
    det = (Ak[0][0] - 1) * (Ak[1][1] - 1) - Ak[0][1] * Ak[1][0]
    check(abs(det) == lucas[2 * k] - 2 == abs(tr(Ak) - 2), f"fixed points of A^{k}")
    if k <= 5:
        D = abs(det)
        cnt = 0
        for i in range(D):
            for j in range(D):
                u = ((Ak[0][0] - 1) * i + Ak[0][1] * j) % D
                v = (Ak[1][0] * i + (Ak[1][1] - 1) * j) % D
                if u == 0 and v == 0:
                    cnt += 1
        check(cnt == D, f"brute fixed-point count of A^{k}")
print("   the cat map's fixed points on the torus: |det(A^k - I)| = L_2k - 2 (Lucas), k = 1..20,")
print("   counted point by point for k = 1..5: 1, 5, 16, 45, 121")
for p in range(1, 41):
    for q in range(1, 41):
        seen, cycles = set(), 0
        for i0 in range(p):
            if i0 in seen:
                continue
            cycles += 1
            i = i0
            while i not in seen:
                seen.add(i)
                i = (i + q) % p
        check(cycles == gcd(p, q), f"torus curve ({p},{q}) components")
        # (1,1) generates Z/p x Z/q iff gcd = 1 (CRT): its order is lcm(p, q).
        check((p * q // gcd(p, q) == p * q) == (gcd(p, q) == 1), "CRT")
print("   the (p, q) curve on the torus has gcd(p, q) strokes, p, q = 1..40: coprime windings are one")
print("   stroke (a knot), the rest a link of gcd strokes")

elapsed_ms = int((time.monotonic() - T0) * 1000)
print(f"all {CHECKS} checks hold ({elapsed_ms} ms)")
