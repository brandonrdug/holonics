"""Exact receipt: neutral is a ratio of one, and the scope decides what a colour reads.

Elements of Q(zeta_n) are integer polynomials reduced modulo the cyclotomic polynomial Phi_n.
Only integers are used; no float is built.

Parts:
  S  every subgroup H of (Z/n)^x for n <= N_S: the reading Tr_H(zeta_n) = sum_{h in H} zeta^h,
     its fixedness under H, compression in stages (H inside H'), and which readings are neutral,
     against the fibre criterion; the twelfth-turn table.
  F  fibres: for p^2 | n every fibre {j + k n/p} of a primitive colour is primitive and cancels;
     for p || n the fibre holds exactly one non-unit.
  M  the sign of a new prime: mu(p n) = -mu(n) when p does not divide n.
"""
import sys
import time
from math import gcd, isqrt

T0 = time.perf_counter_ns()
CHECKS = 0


def check(cond, what):
    global CHECKS
    if not cond:
        raise SystemExit("FAILED: " + what)
    CHECKS += 1


def poly_divmod_monic(a, b):
    """Divide integer poly a by monic integer poly b (lowest degree first)."""
    a = a[:]
    db = len(b) - 1
    q = [0] * max(len(a) - db, 1)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i]
        if c:
            q[i - db] = c
            for k in range(db + 1):
                a[i - db + k] -= c * b[k]
    r = a[:db] if db > 0 else []
    while r and r[-1] == 0:
        r.pop()
    return q, r


PHI = {}


def phi_poly(n):
    if n in PHI:
        return PHI[n]
    num = [-1] + [0] * (n - 1) + [1]  # x^n - 1
    for d in range(1, n):
        if n % d == 0:
            q, r = poly_divmod_monic(num, phi_poly(d))
            assert not r
            num = q
            while num and num[-1] == 0:
                num.pop()
    PHI[n] = num
    return num


def reduce(f, n):
    _, r = poly_divmod_monic(f, phi_poly(n))
    return tuple(r)


def monomials(exps, n):
    f = [0] * n
    for e in exps:
        f[e % n] += 1
    return reduce(f, n)


def sigma(g, elem, n):
    f = [0] * n
    for i, c in enumerate(elem):
        if c:
            f[(g * i) % n] += c
    return reduce(f, n)


def units(n):
    return [u for u in range(1, n + 1) if gcd(u, n) == 1] if n > 1 else [0]


def subgroups(n):
    G = [u % n for u in units(n)]
    cyc = set()
    for g in G:
        H, x = {1 % n}, g
        while x not in H:
            H.add(x)
            x = (x * g) % n
        cyc.add(frozenset(H))
    subs = set(cyc)
    frontier = set(cyc)
    while frontier:
        new = set()
        for A in frontier:
            for B in cyc:
                C = frozenset((a * b) % n for a in A for b in B)
                if C not in subs:
                    new.add(C)
        subs |= new
        frontier = new
    return subs


def factor(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def mu(n):
    f = factor(n)
    if any(e > 1 for e in f.values()):
        return 0
    return -1 if len(f) % 2 else 1


# ---- S: the scope decides the reading -------------------------------------------------------
N_S = int(sys.argv[1]) if len(sys.argv) > 1 else 200
pairs = neutral = criterion_hits = 0
by_kind = {"turn": 0, "real": 0, "neutral": 0}
for n in range(3, N_S + 1):
    subs = subgroups(n)
    G = frozenset(u % n for u in units(n))
    check(G in subs and frozenset({1}) in subs, f"S trivial and whole group n={n}")
    fac = factor(n)
    sq_primes = [p for p, e in fac.items() if e >= 2]
    kernels = [frozenset(u for u in G if (u - 1) % (n // p) == 0) for p in sq_primes]
    readings = {}
    for H in subs:
        r = monomials(H, n)
        readings[H] = r
        pairs += 1
        # the reading lives in the scope: every h in H fixes it
        for h in H:
            check(sigma(h, r, n) == r, f"S fixed n={n}")
        zero = (len(r) == 0)
        crit = any(K <= H for K in kernels)
        check(zero == crit, f"S neutral iff the scope holds a repeated prime's fibre n={n} H={sorted(H)}")
        if zero:
            neutral += 1
        if crit:
            criterion_hits += 1
        real = sigma(n - 1, r, n) == r  # fixed by conjugation
        by_kind["neutral" if zero else ("real" if real else "turn")] += 1
    # compression in stages: for H inside H2, Tr_H2 = sum over coset reps of sigma_g(Tr_H)
    sl = sorted(subs, key=len)
    for H in sl:
        for H2 in sl:
            if len(H2) > len(H) and H <= H2:
                reps, seen = [], set()
                for g in sorted(H2):
                    if g not in seen:
                        reps.append(g)
                        seen |= {(g * h) % n for h in H}
                acc = [0] * n
                for g in reps:
                    for i, c in enumerate(sigma(g, readings[H], n)):
                        acc[i] += c
                check(reduce(acc, n) == readings[H2], f"S stages n={n}")
    # to Q the reading is mu(n)
    check(readings[G] == ((mu(n),) if mu(n) else ()), f"S to Q is mu n={n}")

# the twelfth-turn table
n = 12
z3 = monomials([3], 12)  # i = zeta^3
check(monomials([1, 5], 12) == z3, "S12 quarter-turn scope reads i")
r11 = monomials([1, 11], 12)
sq = [0] * 24
for a, ca in enumerate(r11):
    for b, cb in enumerate(r11):
        sq[a + b] += ca * cb
check(reduce(sq, 12) == (3,), "S12 real scope reads sqrt 3 (its square is 3)")
check(sigma(11, r11, 12) == r11, "S12 real scope reading is real")
check(monomials([1, 7], 12) == (), "S12 cube-root scope reads 0")
check(monomials([1, 5, 7, 11], 12) == (), "S12 rational scope reads mu(12) = 0")
print(f"S: n <= {N_S}: {pairs} (n, scope) pairs; neutral {neutral} "
      f"({by_kind['real']} real, {by_kind['turn']} turning, {by_kind['neutral']} neutral); "
      f"neutral exactly when the scope holds a repeated prime's fibre: {criterion_hits} = {neutral}")
print("S: twelfth turn: Q(i) reads i, Q(sqrt3) reads sqrt3, Q(zeta3) reads 0, Q reads 0")

# ---- F: fibres -----------------------------------------------------------------------------
N_F = 400
fibres = 0
for n in range(2, N_F + 1):
    for p, e in factor(n).items():
        step = n // p
        for j in range(1, n):
            if gcd(j, n) != 1:
                continue
            fib = [j + k * step for k in range(p)]
            nonunits = sum(1 for x in fib if gcd(x, n) != 1)
            if e >= 2:
                check(nonunits == 0, f"F primitive fibre n={n} p={p}")
                check(monomials(fib, n) == (), f"F fibre cancels n={n} p={p}")
                fibres += 1
            else:
                check(nonunits == 1, f"F p||n one non-unit n={n} p={p}")
print(f"F: n <= {N_F}: {fibres} fibres over repeated primes, each primitive and cancelling; "
      f"a single prime's fibre always holds one non-unit")

# ---- M: a new prime flips the sign -----------------------------------------------------------
N_M, P_M = 5000, 100
primes = [p for p in range(2, P_M + 1) if all(p % q for q in range(2, isqrt(p) + 1))]
flips = 0
for nn in range(1, N_M + 1):
    m = mu(nn)
    for p in primes:
        if nn % p:
            check(mu(p * nn) == -m, f"M flip n={nn} p={p}")
            flips += 1
print(f"M: mu(p n) = -mu(n) for {flips} pairs, n <= {N_M}, p <= {P_M}, p not dividing n")

ms = (time.perf_counter_ns() - T0) // 1_000_000
print(f"all {CHECKS} checks hold ({ms} ms)")
