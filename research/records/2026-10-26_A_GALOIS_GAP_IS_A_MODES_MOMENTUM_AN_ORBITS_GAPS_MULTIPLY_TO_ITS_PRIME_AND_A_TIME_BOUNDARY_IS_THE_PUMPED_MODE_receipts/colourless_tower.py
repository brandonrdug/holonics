"""Colourless is compressible: the trace, the tower of colours and the quasicrystal. Exact checks.

The second receipt of the record on Galois gaps (October 26, §16). Integers and fractions.Fraction
only; elements of Q(zeta_n) are integer polynomials reduced modulo Phi_n, and numbers of Q(sqrt 5)
are pairs (p, q) meaning p + q sqrt 5, compared by exact sign tests. No float is built.

Parts:
  P. The colourless shadow of a colour. The trace of zeta_n^j to Q is the Ramanujan sum
     c_n(j) = sum_{d | gcd(n, j)} mu(n/d) d; a primitive colour compresses to mu(n), and the sum of
     every primitive colour of order <= N is the Mertens function M(N). The norm of 1 - zeta_n is
     Phi_n(1) = prod_{d | n} d^(-mu(d)) = exp(Lambda(n)).
  Q. The tower of colours. From Q(zeta_(p^(k+1))) down to Q(zeta_(p^k)) the trace of omega^j is
     p omega^j when p | j and 0 otherwise: each layer adds p colours above every colour, and the
     trace keeps the old colours and erases the new ones. Base 10 climbs the 3-tower as
     ord_(3^k)(10) = 3^(k-2).
  R. The Fibonacci quasicrystal is a model set: the points m + n tau whose conjugate colour
     m + n tau' falls in the window [-1, tau - 1) have gaps tau and 1 in the order of the
     substitution a -> ab, b -> a; tau^n = (L_n + F_n sqrt 5)/2 and the hidden colour
     tau'^n = (L_n - F_n sqrt 5)/2 shrinks at every inflation.
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


def factor(n):
    out, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def divisors(n):
    ds = [1]
    for p, e in factor(n).items():
        ds = [d * p ** k for d in ds for k in range(e + 1)]
    return sorted(ds)


def mobius(n):
    f = factor(n)
    if any(e > 1 for e in f.values()):
        return 0
    return -1 if len(f) % 2 else 1


def phi(n):
    r = n
    for p in factor(n):
        r = r // p * (p - 1)
    return r


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def pdiv_exact(a, b):
    a = a[:]
    q = [0] * (len(a) - len(b) + 1)
    for i in range(len(q) - 1, -1, -1):
        c = a[i + len(b) - 1]
        q[i] = c
        for j, y in enumerate(b):
            a[i + j] -= c * y
    assert all(x == 0 for x in a[: len(b) - 1])
    return q


def preduce(a, m):
    # remainder of a modulo the monic polynomial m
    a = a[:]
    for i in range(len(a) - 1, len(m) - 2, -1):
        c = a[i]
        if c:
            for j, y in enumerate(m):
                a[i - len(m) + 1 + j] -= c * y
    out = a[: len(m) - 1]
    while out and out[-1] == 0:
        out.pop()
    return out


CYC = {1: [-1, 1]}
for d in range(2, 401):
    den = [1]
    for e in divisors(d)[:-1]:
        den = pmul(den, CYC[e])
    CYC[d] = pdiv_exact([-1] + [0] * (d - 1) + [1], den)


def root_sum(n, exps):
    # sum of zeta_n^e over the list, reduced modulo Phi_n
    v = [0] * n
    for e in exps:
        v[e % n] += 1
    return preduce(v, CYC[n])


# ---------- P. the colourless shadow ----------
print("P. the trace of a colour is the Ramanujan sum; a primitive colour compresses to mu(n)")
for n in range(2, 201):
    units = [u for u in range(1, n) if gcd(u, n) == 1]
    for j in range(n):
        tr = root_sum(n, [u * j for u in units])
        c = sum(mobius(n // d) * d for d in divisors(gcd(n, j) if j else n))
        check(tr == ([c] if c else []), f"Ramanujan sum c_{n}({j})")
    check(root_sum(n, units) == ([mobius(n)] if mobius(n) else []), f"Tr zeta_{n} = mu({n})")
M = 1   # n = 1: the colour 1 is its own trace
for N in range(2, 201):
    units = [u for u in range(1, N) if gcd(u, N) == 1]
    tr = root_sum(N, units)
    M += tr[0] if tr else 0
    check(M == sum(mobius(k) for k in range(1, N + 1)), f"M({N}) as the sum of compressed colours")
for n in range(2, 5001):
    val = Fraction(1)
    for d in divisors(n):
        if mobius(d):
            val *= Fraction(d) ** (-mobius(d))
    f = factor(n)
    check(val == (next(iter(f)) if len(f) == 1 else 1), f"prod d^(-mu(d)) = exp(Lambda({n}))")
print("   n <= 200 for the traces and M(N); n <= 5000 for the norm; M(200) =", M)


# ---------- Q. the tower of colours ----------
print("Q. each layer of a prime's tower adds p colours above every colour; the trace erases them")
for p in (2, 3, 5, 7, 11, 13, 17, 19):
    k = 1
    while p ** (k + 1) <= 400:
        n, lower = p ** (k + 1), p ** k
        layer = [1 + i * lower for i in range(p)]           # Gal(Q(zeta_n)/Q(zeta_lower))
        check(all(gcd(u, n) == 1 for u in layer), "the layer's automorphisms are units")
        check(phi(n) // phi(lower) == p, f"layer degree {p}")
        for j in range(n):
            tr = root_sum(n, [j * u for u in layer])
            expect = root_sum(n, [j]) if j % p == 0 else []
            expect = [p * c for c in expect]
            check(tr == expect, f"layer trace of omega^{j}, n = {n}")
        k += 1


def ord_mod(a, m):
    k, x = 1, a % m
    while x != 1:
        x = x * a % m
        k += 1
    return k


for k in range(2, 13):
    check(ord_mod(10, 3 ** k) == 3 ** (k - 2), f"ord_(3^{k})(10)")
print("   layers checked for p^(k+1) <= 400; ord_(3^k)(10) = 3^(k-2) for k = 2..12")


# ---------- R. the Fibonacci quasicrystal ----------
print("R. the Fibonacci chain is the model set of the window [-1, tau - 1) in the conjugate colour")


def sign5(p, q):
    # sign of p + q sqrt 5, p and q rational
    if p == 0 and q == 0:
        return 0
    if p >= 0 and q >= 0:
        return 1
    if p <= 0 and q <= 0:
        return -1
    return (1 if p > 0 else -1) if p * p > 5 * q * q else (1 if q > 0 else -1)


def tau_point(m, n):
    # x = m + n tau and its conjugate x' = m + n tau', each as (p, q)
    half = Fraction(1, 2)
    return (m + n * half, n * half), (m + n * half, -n * half)


def less(a, b):
    return sign5(b[0] - a[0], b[1] - a[1]) > 0


LO = (Fraction(-1), Fraction(0))                 # -1
HI = (Fraction(-1, 2), Fraction(1, 2))           # tau - 1 = (-1 + sqrt 5)/2
TAU = (Fraction(1, 2), Fraction(1, 2))
ONE = (Fraction(1), Fraction(0))
pts = []
X = 1500
for n in range(-2 * X, 2 * X + 1):
    # x' in [-1, tau - 1) bounds m within about two integers of -n tau'
    approx = -n * Fraction(-618034, 1000000)
    for m in range(int(approx) - 3, int(approx) + 4):
        x, xs = tau_point(m, n)
        if not less(xs, LO) and less(xs, HI) and sign5(*x) >= 0 and sign5(X - x[0], -x[1]) >= 0:
            pts.append(x)
pts.sort(key=lambda a: (a[0] + a[1] * Fraction(2236067977, 1000000000)))
for i in range(len(pts) - 1):
    check(less(pts[i], pts[i + 1]), "exact order of the model set")
gaps = []
for i in range(len(pts) - 1):
    g = (pts[i + 1][0] - pts[i][0], pts[i + 1][1] - pts[i][1])
    check(g in (TAU, ONE), "every gap is tau or 1")
    gaps.append("a" if g == TAU else "b")
word = "a"
while len(word) < len(gaps):
    word = "".join("ab" if c == "a" else "a" for c in word)
check("".join(gaps) == word[: len(gaps)], "the gaps follow a -> ab, b -> a")
check(pts[0] == (0, 0), "the chain starts at 0")
F = [0, 1]
L = [2, 1]
for n in range(2, 61):
    F.append(F[-1] + F[-2])
    L.append(L[-1] + L[-2])
tp_pow = (Fraction(1), Fraction(0))
t_pow = (Fraction(1), Fraction(0))
prev_abs = None
for n in range(1, 61):
    t_pow = (t_pow[0] * TAU[0] + 5 * t_pow[1] * TAU[1], t_pow[0] * TAU[1] + t_pow[1] * TAU[0])
    tp = (Fraction(1, 2), Fraction(-1, 2))
    tp_pow = (tp_pow[0] * tp[0] + 5 * tp_pow[1] * tp[1], tp_pow[0] * tp[1] + tp_pow[1] * tp[0])
    check(t_pow == (Fraction(L[n], 2), Fraction(F[n], 2)), f"tau^{n} = (L + F sqrt 5)/2")
    check(tp_pow == (Fraction(L[n], 2), Fraction(-F[n], 2)), f"tau'^{n} = (L - F sqrt 5)/2")
    absv = tp_pow if sign5(*tp_pow) > 0 else (-tp_pow[0], -tp_pow[1])
    if prev_abs is not None:
        check(less(absv, prev_abs), f"the hidden colour shrinks at inflation {n}")
    prev_abs = absv
# the substitution matrix [[1, 1], [1, 0]] has characteristic polynomial x^2 - x - 1, roots tau, tau'
for r in (TAU, (Fraction(1, 2), Fraction(-1, 2))):
    sq = (r[0] * r[0] + 5 * r[1] * r[1], 2 * r[0] * r[1])
    check((sq[0] - r[0] - 1, sq[1] - r[1]) == (0, 0), "tau and tau' are the substitution's colours")
print("   points in [0,", X, "]:", len(pts), " first gaps:", "".join(gaps[:21]))

ms = int((time.monotonic() - T0) * 1000)
print(f"all {CHECKS} checks hold ({ms} ms)")
