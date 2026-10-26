"""Galois gaps as energy, momentum, stress and impedance: exact checks.

The receipt of the record on Galois gaps (October 26). Every check is in integers and
fractions.Fraction, with Gaussian rationals held as pairs. No float is built.

Parts:
  A. Orbit energies. The product of the gaps 1 - zeta over the primitive d-th roots is Phi_d(1):
     p when d = p^k, 1 otherwise, so its logarithm is the von Mangoldt weight Lambda(d), and the
     orbits of a ring m multiply to m.
  B. The ring's spectrum is its Galois orbits. The cycle Laplacian's characteristic polynomial is
     x (x - 4)^[m even] prod_{d | m, d >= 3} psi_d(x)^2, psi_d the minimal polynomial of the squared
     gap 2 - zeta_d - zeta_d^-1; psi_d(0) = Phi_d(1); the nonzero eigenvalues multiply to m^2 and the
     ring has m spanning trees.
  C. The base's dilation x -> u x is a symmetry of the ring's adjacency exactly when u = +-1 mod m.
  D. The colourless faces: the characters of Z/m fixed by the digit move are those of
     Z/gcd(m, b - 1); those it sends to their mirror are those of Z/gcd(m, b + 1).
  E. Space and time boundaries for one mode of an LC line: a step in space keeps the frequency and
     the power; a step in time keeps the wavenumber and the action, and turns the state by
     A -> alpha A + beta conj(A) with alpha = (1 + r)/2, beta = (1 - r)/2, r = Z/Z': the pumped mode.
  F. The dilation current: d_mu(x_nu T^{mu nu}) = T^mu_mu + x_nu d_mu T^{mu nu}.
  G. The zero gas: at a simple root, P''/P' = 2 sum 1/(x_k - x_j) (Stieltjes), so a root under the
     heat flow moves by the field of the others; a Foster tank's L = -2/rho'^2 is positive exactly on
     the line; |Res(x^n - 1, n x^(n-1))| = n^n.
  H. Elliptic curves over F_p: a_p^2 < 4p, so the two Frobenius colours are a conjugate pair on the
     circle of radius sqrt(p) and never merge (Hasse).
  K. The passivity factor of the relaxed Fourier step.
"""
import random
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


def primes_below(n):
    sieve = bytearray([1]) * n
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i < n:
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, n, i)))
        i += 1
    return [i for i in range(n) if sieve[i]]


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


def divisors(n):
    ds = [1]
    for p, e in factor(n).items():
        ds = [d * p ** k for d in ds for k in range(e + 1)]
    return sorted(ds)


def prime_power_base(d):
    f = factor(d)
    return next(iter(f)) if len(f) == 1 else None


# ---------- integer polynomials, lowest degree first ----------

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
        assert c % b[-1] == 0
        c //= b[-1]
        q[i] = c
        for j, y in enumerate(b):
            a[i + j] -= c * y
    assert all(x == 0 for x in a[: len(b) - 1])
    return q


def peval(a, x):
    s = 0
    for c in reversed(a):
        s = s * x + c
    return s


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pscale(a, k):
    return [k * x for x in a]


# ---------- A. orbit energies ----------
print("A. orbit energies: the product of a Galois orbit's gaps is Phi_d(1) = exp(Lambda(d))")
CYC = {1: [-1, 1]}
DMAX = 400
for d in range(2, DMAX + 1):
    num = [-1] + [0] * (d - 1) + [1]
    den = [1]
    for e in divisors(d)[:-1]:
        den = pmul(den, CYC[e])
    CYC[d] = pdiv_exact(num, den)
    check(len(CYC[d]) - 1 == phi(d), f"deg Phi_{d}")
    p = prime_power_base(d)
    check(peval(CYC[d], 1) == (p if p else 1), f"Phi_{d}(1)")
# the Mobius product prod_{e | d} e^{mu(d/e)} for larger d
ORBIT = {}
for d in range(2, 20001):
    val = Fraction(1)
    for e in divisors(d):
        mu = mobius(d // e)
        if mu:
            val *= Fraction(e) ** mu
    p = prime_power_base(d)
    check(val == (p if p else 1), f"Mobius product at {d}")
    if d <= 400:
        check(val == peval(CYC[d], 1), f"Mobius product = Phi_{d}(1)")
    ORBIT[d] = val
for m in range(2, 20001):
    prod = Fraction(1)
    for d in divisors(m)[1:]:
        prod *= ORBIT[d]
    check(prod == m, f"orbits of ring {m} multiply to m")
for m in range(2, DMAX + 1):
    # (x^m - 1)/(x - 1) = prod_{d | m, d > 1} Phi_d(x), at x = 1 equal to m
    q = [1]
    for d in divisors(m)[1:]:
        q = pmul(q, CYC[d])
    check(q == [1] * m and peval(q, 1) == m, f"the gaps of ring {m} multiply to m")
for p in primes_below(60):
    for k in range(1, 8 if p < 10 else 3):
        if p ** k <= DMAX:
            check(peval(CYC[p ** k], 1) == p, f"repetition {p}^{k} keeps the primitive weight")
print("   Phi_d(1) = p for d = p^k and 1 otherwise, d <= 20000; rings multiply to m")
print("   Phi_9(1) =", peval(CYC[9], 1), " Phi_10(1) =", peval(CYC[10], 1),
      " Phi_7(1) =", peval(CYC[7], 1), " Phi_12(1) =", peval(CYC[12], 1))


# ---------- B. the ring's spectrum is its Galois orbits ----------
print("B. the cycle Laplacian's characteristic polynomial factors over the Galois orbits")


def P_cheb(k):
    # z^k + z^-k as a polynomial in y = z + 1/z
    a, b = [2], [0, 1]
    if k == 0:
        return a
    for _ in range(k - 1):
        a, b = b, padd(pmul([0, 1], b), pscale(a, -1))
    return b


def psi(d):
    c = CYC[d]
    n = (len(c) - 1) // 2
    check(c == c[::-1], f"Phi_{d} palindromic")
    R = [c[n]]
    for k in range(1, n + 1):
        R = padd(R, pscale(P_cheb(k), c[n + k]))
    # psi_d(x) = R(2 - x)
    out = [0]
    powx = [1]
    lin = [2, -1]
    for coeff in R:
        out = padd(out, pscale(powx, coeff))
        powx = pmul(powx, lin)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


PSI = {d: psi(d) for d in range(3, 61)}
for d, ps in PSI.items():
    check(len(ps) - 1 == phi(d) // 2, f"deg psi_{d}")
    check(peval(ps, 0) == peval(CYC[d], 1), f"psi_{d}(0) = Phi_{d}(1)")


def det_bareiss(M):
    M = [row[:] for row in M]
    n = len(M)
    sign, prev = 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for i in range(k + 1, n):
                if M[i][k] != 0:
                    M[k], M[i] = M[i], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]


for m in range(3, 61):
    L = [[0] * m for _ in range(m)]
    for i in range(m):
        L[i][i] = 2
        L[i][(i + 1) % m] -= 1
        L[i][(i - 1) % m] -= 1
    prodpoly = [0, 1]
    if m % 2 == 0:
        prodpoly = pmul(prodpoly, [-4, 1])
    for d in divisors(m):
        if d >= 3:
            prodpoly = pmul(prodpoly, pmul(PSI[d], PSI[d]))
    check(len(prodpoly) - 1 == m and prodpoly[-1] == 1, f"degree and monic at m = {m}")
    for x in range(-1, m + 1):
        M = [[(x if i == j else 0) - L[i][j] for j in range(m)] for i in range(m)]
        check(det_bareiss(M) == peval(prodpoly, x), f"char poly at m = {m}, x = {x}")
    check(prodpoly[1] == (-1) ** (m - 1) * m * m, f"nonzero eigenvalues multiply to m^2, m = {m}")
    reduced = [row[1:] for row in L[1:]]
    check(det_bareiss(reduced) == m, f"m spanning trees, m = {m}")
print("   m = 3..60: char poly = x (x-4)^[2|m] prod psi_d^2; psi_7 =", PSI[7], " psi_9 =", PSI[9])


# ---------- C. dilation symmetry ----------
print("C. x -> u x keeps the ring's adjacency exactly when u = +-1 (mod m)")
for m in range(3, 301):
    for u in range(1, m):
        if gcd(u, m) != 1:
            continue
        keeps = all((u * (x + 1) - u * x) % m in (1, m - 1) for x in range(m))
        check(keeps == (u % m in (1, m - 1)), f"dilation {u} on ring {m}")
for m in (3, 9, 11, 7, 13, 101):
    print(f"   ring {m}: 10 is {'a symmetry' if 10 % m in (1, m - 1) else 'a strain'}")


# ---------- D. colourless faces ----------
print("D. the characters fixed by the digit move are those of Z/gcd(m, b-1); mirrored, Z/gcd(m, b+1)")
for b in range(2, 41):
    for m in range(2, 301):
        fixed = [a for a in range(m) if (b * a - a) % m == 0]
        mirrored = [a for a in range(m) if (b * a + a) % m == 0]
        g1, g2 = gcd(m, b - 1), gcd(m, b + 1)
        check(fixed == list(range(0, m, m // g1)), f"fixed b={b} m={m}")
        check(mirrored == list(range(0, m, m // g2)), f"mirrored b={b} m={m}")
for m in range(2, 2001):
    fixed = sum(1 for a in range(m) if (9 * a) % m == 0)
    check(fixed == gcd(m, 9), f"base 10 fixed count on ring {m}")
print("   base 10, ring 63: fixed", gcd(63, 9), "characters (the digit sum mod 9);",
      "ring 77: mirrored", gcd(77, 11), "(the alternating sum mod 11)")


# ---------- E. space and time boundaries ----------
print("E. a step in space keeps frequency and power; a step in time keeps wavenumber and action")


def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def gconj(a):
    return (a[0], -a[1])


def gabs2(a):
    return a[0] * a[0] + a[1] * a[1]


vals = [Fraction(n, d) for n in range(1, 7) for d in range(1, 5)]
for l1 in vals[::3]:
    for c1 in vals[::4]:
        for l2 in vals[1::3]:
            for c2 in vals[2::4]:
                Z1, Z2 = l1 / c1, l2 / c2
                w1, w2 = 1 / (l1 * c1), 1 / (l2 * c2)
                # space: V and I continuous, the same frequency on both sides
                G = (Z2 - Z1) / (Z2 + Z1)
                tau = 2 * Z2 / (Z1 + Z2)
                check(1 + G == tau and (1 - G) / Z1 == tau / Z2, "space continuity")
                check((1 - G * G) / Z1 == tau * tau / Z2, "space keeps power")
                # time: charge q and flux phi continuous, the same wavenumber before and after
                r = Z1 / Z2
                alpha, beta = (1 + r) / 2, (1 - r) / 2
                check(alpha * alpha - beta * beta == r, "time: det = r")
                for A in [(Fraction(3), Fraction(-2)), (Fraction(1, 2), Fraction(5, 3))]:
                    Ap = (alpha * A[0] + beta * A[0], alpha * A[1] - beta * A[1])
                    check(Ap[0] == A[0] and Z2 * Ap[1] == Z1 * A[1], "time: q and phi continuous")
                    Af, Ab = (alpha * A[0], alpha * A[1]), (beta * A[0], beta * A[1])
                    check(Z2 * (gabs2(Af) - gabs2(Ab)) == Z1 * gabs2(A), "time keeps action")
                    E1 = gabs2(A) / (c1 * c1)
                    E2 = (gabs2(Af) + gabs2(Ab)) / (c2 * c2)
                    check(E1 == w1 * Z1 * gabs2(A), "energy = frequency * quanta before")
                    check(E2 == w2 * Z2 * (gabs2(Af) + gabs2(Ab)), "energy = frequency * quanta after")
                    work = E2 - E1
                    check(work == w2 * Z2 * (gabs2(Af) + gabs2(Ab)) - w1 * Z1 * gabs2(A), "work")
for N in range(1, 200):
    r = Fraction(1, N)
    check(((1 - r) / 2) / ((1 + r) / 2) == Fraction(N - 1, N + 1), "time mirror limit")
print("   r = Z/Z' = 1/9: alpha, beta =", (1 + Fraction(1, 9)) / 2, (1 - Fraction(1, 9)) / 2,
      "(backward over forward 4/5)")


# ---------- F. the dilation current ----------
print("F. d_mu(x_nu T^{mu nu}) = T^mu_mu + x_nu d_mu T^{mu nu}, signature (-,+,+,+)")
ETA = [-1, 1, 1, 1]
rng = random.Random(20261026)


def rpoly():
    p = {}
    for _ in range(4):
        e = tuple(rng.randrange(3) for _ in range(4))
        p[e] = p.get(e, 0) + Fraction(rng.randrange(-5, 6), rng.randrange(1, 4))
    return p


def dpoly(p, i):
    out = {}
    for e, c in p.items():
        if e[i]:
            e2 = list(e)
            e2[i] -= 1
            out[tuple(e2)] = out.get(tuple(e2), 0) + c * e[i]
    return out


def mulx(p, i, s=1):
    out = {}
    for e, c in p.items():
        e2 = list(e)
        e2[i] += 1
        out[tuple(e2)] = out.get(tuple(e2), 0) + s * c
    return out


def add(p, q, s=1):
    out = dict(p)
    for e, c in q.items():
        out[e] = out.get(e, 0) + s * c
    return {e: c for e, c in out.items() if c != 0}


for trial in range(300):
    T = [[rpoly() for _ in range(4)] for _ in range(4)]
    D = [{} for _ in range(4)]
    for mu in range(4):
        for nu in range(4):
            D[mu] = add(D[mu], mulx(T[mu][nu], nu, ETA[nu]))
    lhs = {}
    for mu in range(4):
        lhs = add(lhs, dpoly(D[mu], mu))
    rhs = {}
    for mu in range(4):
        rhs = add(rhs, T[mu][mu], ETA[mu])
        for nu in range(4):
            rhs = add(rhs, mulx(dpoly(T[mu][nu], mu), nu, ETA[nu]))
    check(lhs == rhs, "dilation current divergence")
for lam in vals[:12]:
    for dd in vals[:12]:
        x = Fraction(7, 3)
        check(lam * (x / lam + dd) == x + lam * dd, "a dilation conjugates a translation to a scaled one")
print("   300 random polynomial tensors; the trace is the source of the dilation current")


# ---------- G. the zero gas ----------
print("G. the zero gas: Stieltjes, the Foster tank's sign, the roots of unity's resultant")
for trial in range(400):
    roots = set()
    size = rng.randrange(2, 9)
    while len(roots) < size:
        roots.add(Fraction(rng.randrange(-30, 31), rng.randrange(1, 6)))
    roots = sorted(roots)
    # P(x) = prod (x - x_j), lowest degree first
    P = [Fraction(1)]
    for x0 in roots:
        newP = [Fraction(0)] * (len(P) + 1)
        for i, c in enumerate(P):
            newP[i + 1] += c
            newP[i] -= x0 * c
        P = newP
    d1 = [i * c for i, c in enumerate(P)][1:]
    d2 = [i * c for i, c in enumerate(d1)][1:]
    for k, xk in enumerate(roots):
        field = sum(Fraction(1) / (xk - xj) for j, xj in enumerate(roots) if j != k)
        check(peval(d2, xk) == 2 * field * peval(d1, xk), "Stieltjes at a root")
for dn in range(-6, 7):
    for gn in range(-6, 7):
        if dn == 0 and gn == 0:
            continue
        rp = (Fraction(dn, 2), Fraction(gn, 3))
        sq = gmul(rp, rp)
        n2 = gabs2(sq)
        Lval = (-2 * sq[0] / n2, 2 * sq[1] / n2)          # -2 / rho'^2
        positive_real = Lval[1] == 0 and Lval[0] > 0
        check(positive_real == (dn == 0 and gn != 0), "tank L > 0 exactly on the line")
        if dn != 0 and gn != 0:
            sqc = gmul(gconj(rp), gconj(rp))
            Lc = (-2 * sqc[0] / gabs2(sqc), 2 * sqc[1] / gabs2(sqc))
            check(Lc == gconj(Lval), "an off-line quartet makes a conjugate pair of tanks")


def resultant(f, g):
    # Sylvester determinant; f, g lowest degree first
    m, n = len(f) - 1, len(g) - 1
    size = m + n
    S = []
    for i in range(n):
        row = [0] * size
        for j, c in enumerate(reversed(f)):
            row[i + j] = c
        S.append(row)
    for i in range(m):
        row = [0] * size
        for j, c in enumerate(reversed(g)):
            row[i + j] = c
        S.append(row)
    return det_bareiss(S)


for n in range(2, 11):
    f = [-1] + [0] * (n - 1) + [1]
    fp = [0] * (n - 1) + [n]
    check(abs(resultant(f, fp)) == n ** n, f"|Res(x^{n}-1, f')| = n^n")
print("   Res(x^7 - 1, 7x^6) =", resultant([-1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 7]))


# ---------- H. elliptic curves over F_p ----------
print("H. Hasse: a_p^2 < 4p for every elliptic curve over F_p, 5 <= p < 70")
curves = 0
for p in primes_below(70):
    if p < 5:
        continue
    chi = [0] * p
    for x in range(1, p):
        chi[x * x % p] = 1
    leg = [0] + [1 if chi[x] else -1 for x in range(1, p)]
    for a in range(p):
        for b in range(p):
            if (4 * a ** 3 + 27 * b * b) % p == 0:
                continue
            count = p + 1 + sum(leg[(x ** 3 + a * x + b) % p] for x in range(p))
            ap = p + 1 - count
            check(ap * ap < 4 * p, f"Hasse p={p} a={a} b={b}")
            curves += 1
print("   curves checked:", curves)


# ---------- K. the passivity factor ----------
print("K. the relaxed Fourier step: the triangle inequality certifies 2^13, the per-mode bound sqrt(2^13 - 1)")
rho = 1 - Fraction(1, 2 ** 12)
K2 = (1 + rho) / (1 - rho)
check(K2 == 2 ** 13 - 1, "per-mode bound squared")
l2 = 2 / (1 - rho)                       # ||h||_2 <= ||Bx||_2/(1 - rho), ||Bx||_2 <= 2 max|Bx| on four modes
check(l2 == 2 ** 13, "l2 bound on a ring of four")
ratio2 = l2 * l2 / K2
check(2 ** 13 < ratio2 < 2 ** 13 * (1 + Fraction(1, 2 ** 12)), "factor between 2^6.5 and 2^6.5 (1 + 2^-13)")
print("   ratio^2 = 2^26/(2^13 - 1), just above 2^13")

ms = int((time.monotonic() - T0) * 1000)
print(f"all {CHECKS} checks hold ({ms} ms)")
