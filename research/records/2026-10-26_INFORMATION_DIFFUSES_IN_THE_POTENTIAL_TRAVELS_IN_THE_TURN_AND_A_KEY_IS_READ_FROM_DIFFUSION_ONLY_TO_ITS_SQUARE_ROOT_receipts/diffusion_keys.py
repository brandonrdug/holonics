#!/usr/bin/env python3
"""Exact receipt for the record 2026-10-26 "INFORMATION DIFFUSES IN THE POTENTIAL, TRAVELS IN THE
TURN, AND A KEY IS READ FROM DIFFUSION ONLY TO ITS SQUARE ROOT".

Everything stored or compared is exact: Fractions, integers, and the cyclotomic fields
Q(zeta_N) = Q[x]/(x^(N/2) + 1) for N a power of two. Decimal figures are printed only as readings
beside the exact values they read (marked "reading").

Parts
  A  a Z_k connection on the n-cycle with one twisted edge: every eigenvector of the connection
     Laplacian exactly; the least labelling energy by brute force; the spread section's energy against
     a labelling's, which differ by the Fejer factor |1 + z + ... + z^(n-1)|^2 / n (the square root)
  B  relaxation on a path, H = aI + B^T B with kappa = m^2: plain passes against critically tuned
     momentum passes to the same exact tolerance; both reach one hop per pass
  C  a unique game on the Petersen graph over S_3: loop closure (the Bombe) at value 1, the same
     game with one constraint corrupted, the defect located by its cycle syndrome, brute force over 3^10
  D  two flat blocks joined by two conflicting contacts: the slow mode, the optimal labellings, and
     what one landmark per slow mode pins
  E  gradient play on a pure turn, with and without friction
  F  the founding charge (S/(S - drop))^N > N|P|^2: the least certifiable relative drop as N grows
"""
from fractions import Fraction as Q
from itertools import product
import hashlib
import time

T0 = time.time()
CHECKS = []


def check(name, ok):
    CHECKS.append((name, ok))
    if not ok:
        raise SystemExit(f"FAILED: {name}")


def stamp(label):
    print(f"[{label}] elapsed_ms={int((time.time() - T0) * 1000)}")


# ---------------- Q(zeta_N), N a power of two ----------------
class Cyc:
    def __init__(self, N):
        self.N, self.D = N, N // 2

    def zero(self):
        return [Q(0)] * self.D

    def const(self, c):
        z = self.zero()
        z[0] = Q(c)
        return z

    def zpow(self, k):
        k %= self.N
        z = self.zero()
        if k < self.D:
            z[k] = Q(1)
        else:
            z[k - self.D] = Q(-1)
        return z

    def add(self, a, b):
        return [x + y for x, y in zip(a, b)]

    def sub(self, a, b):
        return [x - y for x, y in zip(a, b)]

    def mul(self, a, b):
        out = [Q(0)] * self.D
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        k = i + j
                        if k < self.D:
                            out[k] += x * y
                        else:
                            out[k - self.D] -= x * y
        return out

    def conj(self, a):
        out = self.zero()
        for k, x in enumerate(a):
            if x:
                out = self.add(out, [c * x for c in self.zpow(-k)])
        return out

    def is_rational(self, a):
        return all(c == 0 for c in a[1:])

    def reading(self, a):
        import cmath
        z = cmath.exp(2j * cmath.pi / self.N)
        return sum(complex(c) * z ** k for k, c in enumerate(a))


# ---------------- A: the twisted cycle ----------------
def part_a():
    print("A  the twisted cycle: Z_k connection on C_n, one edge carrying the turn c")
    k, c = 4, 1
    for n in (2, 4, 8, 16):
        N = n * k
        F = Cyc(N)
        omega_c = F.zpow(n * c)                 # omega = zeta_N^n is a primitive k-th root
        # edges x -> x+1 (transport 1) and n-1 -> 0 (transport omega^c); flat section: u(y) = rho u(x)
        edges = [(x, x + 1, F.const(1)) for x in range(n - 1)] + [(n - 1, 0, omega_c)]
        # L = d^H d, (d u)_e = u(y) - rho_e u(x)
        L = [[F.zero() for _ in range(n)] for _ in range(n)]
        for (x, y, rho) in edges:
            L[x][x] = F.add(L[x][x], F.const(1))
            L[y][y] = F.add(L[y][y], F.const(1))
            L[x][y] = F.sub(L[x][y], F.conj(rho))
            L[y][x] = F.sub(L[y][x], rho)
        best = None
        for j in range(n):
            a = j * k - c                       # u_a(x) = zeta^(a x), closing needs a + c = 0 mod k
            u = [F.zpow(a * x) for x in range(n)]
            lam = F.sub(F.const(2), F.add(F.zpow(a), F.zpow(-a)))
            for x in range(n):
                lu = F.zero()
                for y in range(n):
                    lu = F.add(lu, F.mul(L[x][y], u[y]))
                check(f"A n={n} a={a}: L u = lambda u", lu == F.mul(lam, u[x]))
            dist = min(a % N, (-a) % N)       # 2 - 2cos(2 pi a / N) increases with this distance
            if best is None or dist < best[0]:
                best = (dist, a, lam)
        _, a_min, lam_min = best
        # a labelling's section u = omega^l: one violated edge of defect c is the least energy
        lab_energy = F.mul(F.sub(F.const(1), omega_c), F.conj(F.sub(F.const(1), omega_c)))
        z = F.zpow(c)
        dsum = F.zero()
        for j in range(n):
            dsum = F.add(dsum, F.zpow(c * j))
        fejer_n = F.mul(dsum, F.conj(dsum))  # |1 + z + ... + z^(n-1)|^2
        # |1 - z^n|^2 = |1 - z|^2 |sum z^j|^2, with |1 - z|^2 = lambda_min
        spread = F.mul(F.sub(F.const(1), z), F.conj(F.sub(F.const(1), z)))
        check(f"A n={n}: lambda_min = |1 - zeta^c|^2", spread == lam_min)
        check(f"A n={n}: |1 - omega^c|^2 = lambda_min * |sum z^j|^2", lab_energy == F.mul(lam_min, fejer_n))
        check(f"A n={n}: labelling energy is rational", F.is_rational(lab_energy))
        if n <= 8:
            # brute force: least violated edges and least labelling energy over all k^n labellings
            best_viol, best_count, best_e = n + 1, 0, None
            for lab in product(range(k), repeat=n):
                viol, energy = 0, Q(0)
                for (x, y, rho) in edges:
                    shift = c if (x, y) == (n - 1, 0) else 0
                    d = (lab[y] - lab[x] - shift) % k
                    if d:
                        viol += 1
                        energy += Q({1: 2, 2: 4, 3: 2}[d])      # |1 - i^d|^2 for k = 4, exact
                if viol < best_viol:
                    best_viol, best_count = viol, 1
                elif viol == best_viol:
                    best_count += 1
                best_e = energy if best_e is None or energy < best_e else best_e
            check(f"A n={n}: least violations 1", best_viol == 1)
            check(f"A n={n}: least labelling energy = |1 - omega^c|^2", Q(best_e) == lab_energy[0])
            check(f"A n={n}: n*k optimal labellings (which edge carries the turn, global shift)", best_count == n * k)
            brute = f"brute force over {k}^{n}: least violations 1, optimal labellings {best_count}"
        else:
            brute = "brute force skipped (4^16); one violation is forced: sum of defects round the cycle = c != 0 mod k"
        ratio = F.reading(fejer_n).real / n
        print(f"  n={n:2d} N={N:2d}: lambda_min = 2 - zeta^{a_min} - zeta^{-a_min} (a={a_min}); "
              f"labelling energy |1-omega|^2 = {lab_energy[0]}; |sum z^j|^2 = exact element of Q(zeta_{N}); {brute}")
        print(f"     reading: lambda_min = {F.reading(lam_min).real:.6f}, n^2 lambda_min = {n * n * F.reading(lam_min).real:.4f} "
              f"(-> (2 pi c/k)^2 = 2.4674), violated fraction 1/n = {1 / n:.4f}, "
              f"labelling Rayleigh / lambda_min = |sum z^j|^2 / n = {ratio:.4f}, diffusion passes to feel the turn ~ 1/lambda_min = {1 / F.reading(lam_min).real:.1f}")
    stamp("A")


# ---------------- B: plain against momentum relaxation ----------------
def thomas(n, diag, off, rhs):
    """solve a symmetric tridiagonal system exactly."""
    cp, dp = [Q(0)] * n, [Q(0)] * n
    cp[0] = off / diag[0]
    dp[0] = rhs[0] / diag[0]
    for i in range(1, n):
        den = diag[i] - off * cp[i - 1]
        cp[i] = off / den if i < n - 1 else Q(0)
        dp[i] = (rhs[i] - off * dp[i - 1]) / den
    x = [Q(0)] * n
    x[-1] = dp[-1]
    for i in range(n - 2, -1, -1):
        x[i] = dp[i] - cp[i] * x[i + 1]
    return x


def part_b():
    print("B  a pass is a hop: plain relaxation against momentum on a path, kappa = m^2")
    n = 33
    rows = []
    for m in (3, 5, 9, 17):
        a = Q(4, m * m - 1)                      # spectrum of H inside [a, a + 4], so kappa <= m^2
        deg = [Q(1)] + [Q(2)] * (n - 2) + [Q(1)]
        diag = [a + d for d in deg]
        off = Q(-1)
        b = [Q(1)] + [Q(0)] * (n - 1)

        def Hx(x):
            return [diag[i] * x[i] + (off * x[i - 1] if i else 0) + (off * x[i + 1] if i < n - 1 else 0) for i in range(n)]

        xs = thomas(n, diag, off, b)

        def energy(x):
            e = [x[i] - xs[i] for i in range(n)]
            he = Hx(e)
            return sum(e[i] * he[i] for i in range(n))

        e0 = energy([Q(0)] * n)
        tol = e0 / 2 ** 20
        # plain: x <- x + alpha (b - Hx), alpha = 2 / (lambda_min + lambda_max) on [a, a + 4]
        alpha = Q(2) / (2 * a + 4)
        x = [Q(0)] * n
        plain, cone_ok = 0, True
        while energy(x) > tol:
            r = [b[i] - v for i, v in enumerate(Hx(x))]
            x = [x[i] + alpha * r[i] for i in range(n)]
            plain += 1
            if plain < n:
                cone_ok &= all(v == 0 for v in x[plain:]) and x[plain - 1] != 0
        check(f"B m={m}: plain pass t reaches exactly t hops", cone_ok)
        # momentum (heavy ball), critically tuned: alpha = 4/(sqrt(L)+sqrt(mu))^2, beta = q^2, q = (m-1)/(m+1)
        # sqrt(a + 4) = m sqrt(a), so alpha = 4 / (a (m + 1)^2) is rational
        alpha_h = Q(4) / (a * (m + 1) ** 2)
        beta = Q(m - 1, m + 1) ** 2
        x_prev = [Q(0)] * n
        x = [Q(0)] * n
        mom, cone_ok = 0, True
        while energy(x) > tol:
            r = [b[i] - v for i, v in enumerate(Hx(x))]
            x, x_prev = [x[i] + alpha_h * r[i] + beta * (x[i] - x_prev[i]) for i in range(n)], x
            mom += 1
            if mom < n:
                cone_ok &= all(v == 0 for v in x[mom:]) and x[mom - 1] != 0
        check(f"B m={m}: momentum pass t reaches exactly t hops", cone_ok)
        rows.append((m, plain, mom))
        print(f"  m={m:2d} kappa<=m^2={m * m:3d}: a = {a}; to energy below 2^-20 of the start: plain {plain} passes "
              f"(rate per pass (k-1)/(k+1) = {Q(m * m - 1, m * m + 1)}), momentum {mom} passes "
              f"(rate q = (m-1)/(m+1) = {Q(m - 1, m + 1)})")
    # the scaling: plain grows like kappa, momentum like sqrt(kappa)
    check("B plain passes grow faster than momentum passes at every kappa", all(p > q for _, p, q in rows))
    check("B plain/momentum ratio grows with kappa", all(rows[i][1] * rows[i + 1][2] < rows[i + 1][1] * rows[i][2] for i in range(len(rows) - 1)))
    print("  reading: plain/momentum = " + ", ".join(f"{p / q:.2f} at kappa {m * m}" for m, p, q in rows))
    stamp("B")


# ---------------- C: a unique game on the Petersen graph ----------------
PETERSEN = [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
PERMS3 = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]


def sha_int(tag):
    return int.from_bytes(hashlib.sha256(tag.encode()).digest(), "big")


def propagate(edges, perms, n, k, root=0, skip=None):
    """loop closure: for each hypothesis at the root, propagate along a BFS tree and keep the
    hypotheses that close every other edge (the Bombe's stops)."""
    adj = {v: [] for v in range(n)}
    for idx, (u, v) in enumerate(edges):
        if idx == skip:
            continue
        adj[u].append((v, idx, True))
        adj[v].append((u, idx, False))
    stops = []
    for h in range(k):
        lab = {root: h}
        queue = [root]
        while queue:
            u = queue.pop(0)
            for (v, idx, fwd) in adj[u]:
                p = perms[idx]
                val = p[lab[u]] if fwd else p.index(lab[u])
                if v not in lab:
                    lab[v] = val
                    queue.append(v)
        ok = all(perms[idx][lab[u]] == lab[v] for idx, (u, v) in enumerate(edges) if idx != skip)
        if ok and len(lab) == n:
            stops.append(tuple(lab[v] for v in range(n)))
    return stops


def part_c():
    print("C  a unique game on the Petersen graph over S_3: loop closure at value 1 and at 1 - 1/15")
    n, k, E = 10, 3, PETERSEN
    key = [sha_int(f"ug-key-2026-10-26:{v}") % k for v in range(n)]
    perms = []
    for idx, (u, v) in enumerate(E):
        cands = [p for p in PERMS3 if p[key[u]] == key[v]]
        perms.append(cands[sha_int(f"ug-perm-2026-10-26:{idx}") % len(cands)])

    def value(lab, ps):
        return sum(ps[idx][lab[u]] == lab[v] for idx, (u, v) in enumerate(E))

    stops = propagate(E, perms, n, k)
    check("C value 1: loop closure keeps the key", tuple(key) in stops)
    hist = {}
    for lab in product(range(k), repeat=n):
        val = value(lab, perms)
        hist[val] = hist.get(val, 0) + 1
    check("C value 1: the key is the only labelling closing all 15", hist.get(15, 0) == 1 and len(stops) == 1)
    print(f"  key {key}; loop closure from one vertex: {k} hypotheses x {len(E)} edges, stops {len(stops)} (the key)")
    print(f"  brute force over 3^10 = {3 ** 10}: labellings by edges satisfied {dict(sorted(hist.items(), reverse=True)[:4])} ...")
    # corrupt one constraint
    bad = sha_int("ug-bad-2026-10-26") % len(E)
    u, v = E[bad]
    perms_bad = list(perms)
    perms_bad[bad] = [p for p in PERMS3 if p[key[u]] != key[v]][0]
    stops_bad = propagate(E, perms_bad, n, k)
    check("C value 1 - 1/15: loop closure returns no key", stops_bad == [])
    best = max(value(lab, perms_bad) for lab in product(range(k), repeat=n))
    opt = [lab for lab in product(range(k), repeat=n) if value(lab, perms_bad) == best]
    check("C value 1 - 1/15: the optimum satisfies 14, and the key is optimal", best == 14 and tuple(key) in opt)
    # the cycle syndrome locates one defect: Petersen is 3-edge-connected and 3 > 2*1
    located = [idx for idx in range(len(E)) if propagate(E, perms_bad, n, k, skip=idx)]
    check("C one defect is located by dropping each edge in turn", located == [bad])
    recovered = propagate(E, perms_bad, n, k, skip=bad)
    check("C dropping the located edge recovers the key", recovered == [tuple(key)])
    print(f"  corrupted edge {bad} {E[bad]}: loop closure stops 0; optimum 14 of 15 with {len(opt)} optimal labellings; "
          f"dropping each edge in turn locates only edge {located} ({len(E)} x {k} propagations), and the key returns")
    stamp("C")


# ---------------- D: slow modes and landmarks ----------------
def part_d():
    print("D  two flat blocks (K4, Z_3 differences) joined by two conflicting contacts")
    k = 3
    blk = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    E = blk + [(u + 4, v + 4) for (u, v) in blk] + [(0, 4), (1, 5)]
    # differences l(v) - l(u) = c_e: each block flat (c from a potential), the joins disagree on the shift
    pot = [0, 1, 2, 1, 0, 2, 2, 1]
    c = {}
    for (u, v) in E[:12]:
        c[(u, v)] = (pot[v] - pot[u]) % k
    c[(0, 4)] = (pot[4] - pot[0]) % k            # honours shift 0 between the blocks
    c[(1, 5)] = (pot[5] - pot[1] + 1) % k        # demands shift 1

    def viol(lab):
        return sum((lab[v] - lab[u] - c[(u, v)]) % k != 0 for (u, v) in E)

    labs = list(product(range(k), repeat=8))
    best = min(viol(l) for l in labs)
    opt = [l for l in labs if viol(l) == best]
    check("D the optimum violates exactly one contact", best == 1)
    check("D optimal labellings: 2 honoured joins x 3 global shifts", len(opt) == 6)
    g = [l for l in opt if l[0] == pot[0]]                     # the global shift is gauge: fix it
    check("D with the global gauge fixed, 2 optimal labellings remain (the slow mode's gauge)", len(g) == 2)
    lm = [l for l in g if l[4] == pot[4]]                       # one landmark in the second block
    check("D one landmark in the second block leaves one", len(lm) == 1)
    # the slow mode: block-sign vector s has Rayleigh (joins * 4) / 8 = 1 on L = D - A; L0 (blocks) has
    # spectrum 0,0,4,...: L >= L0 gives lambda_3(L) >= 4; s is orthogonal to the constant, so lambda_2(L) <= 1
    n = 8
    A = [[0] * n for _ in range(n)]
    for (u, v) in E:
        A[u][v] = A[v][u] = 1
    L = [[(sum(A[i]) if i == j else 0) - A[i][j] for j in range(n)] for i in range(n)]
    s = [1] * 4 + [-1] * 4
    Ls = [sum(L[i][j] * s[j] for j in range(n)) for i in range(n)]
    rq = Q(sum(s[i] * Ls[i] for i in range(n)), sum(x * x for x in s))
    check("D the block-sign Rayleigh quotient is 1", rq == 1)
    L0 = [[L[i][j] if (i < 4) == (j < 4) else 0 for j in range(n)] for i in range(n)]
    for i in range(n):
        L0[i][i] = 3
    L0sq = [[sum(L0[i][t] * L0[t][j] for t in range(n)) for j in range(n)] for i in range(n)]
    check("D each K4 block satisfies L0^2 = 4 L0 (spectrum 0, 4, 4, 4)", L0sq == [[4 * x for x in row] for row in L0])
    print(f"  least violations {best}; optimal labellings {len(opt)}; gauge fixed {len(g)}; after one landmark {len(lm)}")
    print("  spectrum: lambda_2(L) <= 1 (block sign, Rayleigh 1), lambda_3(L) >= 4 (L >= L0 = two K4 blocks): "
          "two slow modes, the constant (gauge) and the block sign (the undetermined relative shift)")
    stamp("D")


# ---------------- E: gradient play on a pure turn ----------------
def part_e():
    print("E  gradient play on f(x, y) = x y (x descends, y ascends): the turn alone, and with friction")
    eta = Q(1, 2)
    x0, y0 = Q(3), Q(4)
    x, y = x0, y0
    for _ in range(8):
        x, y = x - eta * y, y + eta * x
    check("E simultaneous steps multiply |xi|^2 by 1 + eta^2 each", x * x + y * y == (x0 * x0 + y0 * y0) * (1 + eta * eta) ** 8)
    x, y = x0, y0
    inv0 = x * x + y * y - eta * x * y
    alt = True
    for _ in range(8):
        x = x - eta * y
        y = y + eta * x
        alt &= (x * x + y * y - eta * x * y) == inv0
    check("E alternating steps conserve x^2 + y^2 - eta x y (recurrent, no settling)", alt)
    for gamma in (Q(1, 2), Q(2)):
        x, y = x0, y0
        for _ in range(8):
            x, y = x - eta * (y + gamma * x), y + eta * (x - gamma * y)
        f = (1 - eta * gamma) ** 2 + eta * eta
        check(f"E friction gamma={gamma}: |xi|^2 multiplied by (1 - eta gamma)^2 + eta^2 = {f}", x * x + y * y == (x0 * x0 + y0 * y0) * f ** 8)
    print(f"  eta = 1/2: simultaneous x{1 + eta * eta} per step (the turn pumps); alternating conserves a quadratic; "
          f"friction 1/2: x{(1 - eta / 2) ** 2 + eta * eta}; friction 2: x{eta * eta}")
    stamp("E")


# ---------------- F: the founding charge and the volume of evidence ----------------
def part_f():
    print("F  the least certifiable relative drop delta = 1/m: (m/(m-1))^N > N |P|^2, |P| = 2^10")
    P2 = (2 ** 10) ** 2

    def passes(m, N):
        return m ** N > N * P2 * (m - 1) ** N

    out = []
    for N in (10 ** 3, 10 ** 4, 10 ** 5):
        lo, hi = 2, N
        check(f"F N={N}: delta = 1/2 passes", passes(2, N))
        while lo < hi:                                   # largest m that passes
            mid = (lo + hi + 1) // 2
            if passes(mid, N):
                lo = mid
            else:
                hi = mid - 1
        check(f"F N={N}: m={lo} passes and m={lo + 1} does not", passes(lo, N) and not passes(lo + 1, N))
        out.append((N, lo))
        import math
        print(f"  N={N:6d}: smallest certifiable drop 1/{lo} of the tension (reading {1 / lo:.5f}; "
              f"(ln N + 2 ln|P|)/N = {(math.log(N) + 2 * math.log(2 ** 10)) / N:.5f})")
    check("F the threshold falls as N grows", all(out[i][1] < out[i + 1][1] for i in range(len(out) - 1)))
    stamp("F")


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
    part_e()
    part_f()
    print(f"all {len(CHECKS)} checks hold")
