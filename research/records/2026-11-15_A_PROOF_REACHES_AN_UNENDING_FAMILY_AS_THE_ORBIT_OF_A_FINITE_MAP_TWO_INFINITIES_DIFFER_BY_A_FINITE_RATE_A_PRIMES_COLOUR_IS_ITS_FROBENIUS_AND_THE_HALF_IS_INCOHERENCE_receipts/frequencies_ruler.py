"""Ruler for the record of November 15 (proof, infinities, counts): public arithmetic only.

1. Chebotarev: the frequencies of a cubic's root counts at the primes are the class sizes of its Galois group.
2. The root counts of x^3 - x - 1 are the coefficients of one wave, eta(z) eta(23z).
3. A curve's counts over every extension are held by four numbers: a finite Hankel rank.
"""
from fractions import Fraction
from math import isqrt, log, sqrt


def primes_below(n):
    s = bytearray([1]) * n
    s[0] = s[1] = 0
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n) if s[i]]


def roots_mod_p(coeffs, p):
    """Distinct roots in F_p of the monic cubic x^3 + a x^2 + b x + c: deg gcd(x^p - x, f)."""
    a, b, c = (x % p for x in coeffs)

    def mul(u, v):  # u, v of degree < 3, reduced by x^3 = -a x^2 - b x - c
        w = [0] * 5
        for i in range(3):
            if u[i]:
                for j in range(3):
                    w[i + j] += u[i] * v[j]
        for k in (4, 3):
            t = w[k] % p
            if t:
                w[k] = 0
                w[k - 1] -= a * t
                w[k - 2] -= b * t
                w[k - 3] -= c * t
        return [w[0] % p, w[1] % p, w[2] % p]

    r, base, e = [1, 0, 0], [0, 1, 0], p
    while e:
        if e & 1:
            r = mul(r, base)
        base = mul(base, base)
        e >>= 1
    g = [r[0], (r[1] - 1) % p, r[2]]  # x^p - x mod f
    f = [c, b, a, 1]

    def trim(u):
        while u and u[-1] % p == 0:
            u.pop()
        return u

    u, v = trim(f[:]), trim(g[:])
    while v:
        inv = pow(v[-1], p - 2, p)
        while len(u) >= len(v):
            t = u[-1] * inv % p
            s = len(u) - len(v)
            for i in range(len(v)):
                u[s + i] = (u[s + i] - t * v[i]) % p
            trim(u)
            if not u:
                break
        u, v = v, u
    return len(u) - 1


def census(coeffs, ramified, bound):
    ps = [p for p in primes_below(bound) if p not in ramified]
    rows, counts, marks = [], {}, [10**3, 10**4, 10**5, 10**6]
    mi = 0
    for idx, p in enumerate(ps):
        k = roots_mod_p(coeffs, p)
        counts[k] = counts.get(k, 0) + 1
        nxt = ps[idx + 1] if idx + 1 < len(ps) else None
        while mi < len(marks) and (nxt is None or nxt >= marks[mi]) and p < marks[mi]:
            rows.append((marks[mi], idx + 1, dict(counts)))
            mi += 1
    return rows


def show(name, coeffs, ramified, classes):
    print(f"\n{name}  (f = x^3 {coeffs[0]:+d} x^2 {coeffs[1]:+d} x {coeffs[2]:+d}; ramified primes {sorted(ramified)} left out)")
    print("  class of Frobenius -> roots mod p, its share of the group")
    for roots, (label, share) in sorted(classes.items(), reverse=True):
        print(f"    {label:<14} {roots} roots  {share}")
    for x, n, counts in census(coeffs, ramified, 10**6 + 1):
        parts = []
        for roots, (label, share) in sorted(classes.items(), reverse=True):
            c = counts.get(roots, 0)
            expect = n * share
            spread = sqrt(n * share * (1 - share))
            parts.append(f"{roots} roots: {c} (share {c / n:.4f}, against {float(share):.4f}: {(c - expect) / spread:+.2f} spreads)")
            assert abs(c - expect) < 3 * spread, (name, x, roots)
        other = {k: v for k, v in counts.items() if k not in classes}
        assert not other, (name, other)
        print(f"  primes below {x:>7}: {n:>6}  " + "; ".join(parts) + (f"; other {other}" if other else ""))


show("S3 (disc -23)", (0, -1, -1), {23},
     {3: ("identity", Fraction(1, 6)), 1: ("transposition", Fraction(1, 2)), 0: ("3-cycle", Fraction(1, 3))})
show("C3 (disc 81 = 3^4)", (0, -3, 1), {3},
     {3: ("identity", Fraction(1, 3)), 0: ("3-cycle", Fraction(2, 3))})

# 2. eta(z) eta(23z) = q prod (1 - q^n)(1 - q^(23 n)); a_p against (roots of x^3 - x - 1 mod p) - 1.
N = 10**5


def euler_product(step, limit):
    """prod_(n>=1) (1 - q^(step n)) up to q^limit, by Euler's pentagonal theorem: sparse."""
    out = {}
    k = 0
    while True:
        done = True
        for kk in ([0] if k == 0 else [k, -k]):
            e = step * kk * (3 * kk - 1) // 2
            if e <= limit:
                out[e] = out.get(e, 0) + (-1) ** abs(kk)
                done = False
        if done and k > 0:
            break
        k += 1
    return out


A, B = euler_product(1, N), euler_product(23, N)
coef = [0] * (N + 1)
for i, u in A.items():
    for j, v in B.items():
        if i + j <= N:
            coef[i + j] += u * v
# coefficient of q^m in eta(z)eta(23z) is coef[m - 1]
agree = total = 0
first_miss = None
for p in primes_below(N + 1):
    if p == 23:
        continue
    total += 1
    ap = coef[p - 1]
    if ap == roots_mod_p((0, -1, -1), p) - 1:
        agree += 1
    elif first_miss is None:
        first_miss = (p, ap)
print(f"\neta(z) eta(23z): sparse factors {len(A)} and {len(B)} terms to q^{N}")
print(f"  a_p = (roots of x^3 - x - 1 mod p) - 1 at {agree} of {total} primes p < {N}, p != 23; first miss {first_miss}")
assert agree == total
print("  first coefficients a_1..a_30:", [coef[m - 1] for m in range(1, 31)])

# 3. y^2 = x^3 + x^2 + 1 over F_3: N_n over F_(3^n), n = 1..10, and the Hankel rank of (N_n).
q = 3


def poly_mod_mul_x(v, modpoly):
    # v: coefficient list of degree < n; multiply by x and reduce by the monic modpoly (coeffs low..high, length n+1)
    n = len(v)
    top = v[-1]
    w = [0] + v[:-1]
    if top:
        w = [(w[i] - top * modpoly[i]) % q for i in range(n)]
    return w


def primitive_table(n):
    from itertools import product
    for tail in product(range(q), repeat=n):
        if tail[0] == 0:
            continue
        modpoly = list(tail) + [1]
        one = [1] + [0] * (n - 1)
        v = one
        table = []
        for k in range(q**n - 1):
            table.append(tuple(v))
            v = poly_mod_mul_x(v, modpoly)
            if v == one and k + 1 < q**n - 1:
                break
        else:
            if v == one:
                return table
    raise RuntimeError("no primitive polynomial")


def count_points(n):
    exp = primitive_table(n)
    size = q**n - 1
    log = {e: k for k, e in enumerate(exp)}
    zero = tuple([0] * n)
    total = 1  # the point at infinity
    def chi(vec):
        if vec == zero:
            return 0
        return 1 if log[vec] % 2 == 0 else -1
    # x = 0: f(0) = 1
    one = tuple([1] + [0] * (n - 1))
    total += 1 + chi(one)
    for k in range(size):
        x2, x3 = exp[(2 * k) % size], exp[(3 * k) % size]
        fx = tuple((x3[i] + x2[i] + (1 if i == 0 else 0)) % q for i in range(n))
        total += 1 + chi(fx)
    return total


counts = [count_points(n) for n in range(1, 11)]
a = q + 1 - counts[0]
s = [2, a]
for n in range(2, 11):
    s.append(a * s[-1] - q * s[-2])
print(f"\ny^2 = x^3 + x^2 + 1 over F_3: N_n for n = 1..10: {counts}")
print(f"  a = q + 1 - N_1 = {a}; alpha + conj(alpha) = {a}, alpha conj(alpha) = {q}; |alpha|^2 = 3 (Hasse: a^2 = {a*a} <= 4q = {4*q})")
assert all(counts[n - 1] == q**n + 1 - s[n] for n in range(1, 11))
assert a * a <= 4 * q
print(f"  N_n = q^n + 1 - (alpha^n + conj(alpha)^n) at every n: {all(counts[n-1] == q**n + 1 - s[n] for n in range(1, 11))}")


def det(m):
    m = [[Fraction(x) for x in row] for row in m]
    d = Fraction(1)
    size = len(m)
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


dets = []
for k in range(1, 6):
    H = [[counts[i + j] for j in range(k)] for i in range(k)]
    dets.append(det(H))
    print(f"  Hankel determinant of order {k} on N_1..N_{2*k-1}: {dets[-1]}")
assert all(d != 0 for d in dets[:4]) and dets[4] == 0
print("\nevery check passed")
