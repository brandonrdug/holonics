#!/usr/bin/env python3
"""Rulers for the record of November 12, 2026 on the friction a region sets.

Host arithmetic on public material: integers and rationals (fractions.Fraction) in every check.
A decimal appears only where a figure is printed for reading, and in rulers 7 and 10, which do
arithmetic on readings already printed in receipts on main (g108_reach_reads.txt, g110_te6_reads.txt).
A ruler measures; nothing here is machinery, and no state, passage or card is read.

The built circle (holonics::hnn::tower::field, FieldDeclaration::carry), a left scan:
    Q(t) = (u_t Q(t-1) + d_t N0 b_t) / (1 + d_t),   |u_t| = 1,   d_t = d0 2^l(t),  N0 = 5, d0 = 1/4.
The derived circle carries its count beside its charge. Three equal forms (rulers 1 to 6 state the site's mass
as j; ruler 9 reads it from the built chart, m = d^^2/(1 + d^) with d^ = d0 2^l):
    pair   arriving (eta, n):  eta <- u_t eta + j_t N0 b_t,  n <- n + j_t,  Q = eta/n,
           then to the next site (eta, n) <- (eta, n) / (1 + q0 n),   q0 = 1/20
    gate   d_t = m_t R_t,  m_t = q0 j_t,  R_(t+1) = 1 + R_t/(1 + d_t),  R = N0 at the edge
    chain  the minimizer, at site t, of the half strand's quadratic energy (ruler 3)
"""
from fractions import Fraction as F
import random
import sys

FAILED = 0


def check(ok, text):
    global FAILED
    if not ok:
        FAILED += 1
    print(("  [ok] " if ok else "  [FAILED] ") + text)


class C:
    """A complex number with rational parts."""
    __slots__ = ("re", "im")

    def __init__(self, re, im=0):
        self.re, self.im = F(re), F(im)

    def __add__(self, o):
        o = o if isinstance(o, C) else C(o)
        return C(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __sub__(self, o):
        o = o if isinstance(o, C) else C(o)
        return C(self.re - o.re, self.im - o.im)

    def __neg__(self):
        return C(-self.re, -self.im)

    def __mul__(self, o):
        if not isinstance(o, C):
            return C(self.re * o, self.im * o)
        return C(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def conj(self):
        return C(self.re, -self.im)

    def abs2(self):
        return self.re * self.re + self.im * self.im

    def __truediv__(self, o):
        if not isinstance(o, C):
            return C(self.re / o, self.im / o)
        return self * o.conj() / o.abs2()

    def __eq__(self, o):
        o = o if isinstance(o, C) else C(o)
        return self.re == o.re and self.im == o.im

    def iszero(self):
        return self.re == 0 and self.im == 0


N0 = F(5)
D0 = F(1, 4)
Q0 = F(1, 20)
# Unit turns with rational parts (Pythagorean triples) and their conjugates.
TURNS = [C(1), C(F(3, 5), F(4, 5)), C(F(5, 13), F(12, 13)), C(0, 1), C(F(-3, 5), F(4, 5)), C(F(8, 17), F(-15, 17)), C(F(7, 25), F(24, 25)), C(-1)]
MASSES = [F(0), F(0), F(0), F(1, 8), F(1, 2), F(1), F(1), F(2), F(5)]


def strand(rng, sites, masses=MASSES):
    js = [rng.choice(masses) for _ in range(sites)]
    us = [rng.choice(TURNS) for _ in range(sites)]
    bs = [C(rng.randint(-9, 9), rng.randint(-9, 9)) for _ in range(sites)]
    return js, us, bs


def scan_pair(js, us, bs, n_edge=N0 - 1):
    """The pair form. Returns each site's (arriving turned charge, arriving count, charge after, count after)."""
    eta, n = C(0), n_edge
    out = []
    for j, u, b in zip(js, us, bs):
        eta = u * eta
        arriving = (eta / n, n)
        eta, n = eta + j * N0 * b, n + j
        out.append((arriving[0], arriving[1], eta / n, n))
        shrink = 1 / (1 + Q0 * n)
        eta, n = eta * shrink, n * shrink
    return out


def scan_gate(js, us, bs, r_edge=N0):
    """The gate form. Returns each site's (charge after, friction, back range arriving)."""
    q, r = C(0), r_edge
    out = []
    for j, u, b in zip(js, us, bs):
        d = Q0 * j * r
        q = (u * q + d * N0 * b) / (1 + d)
        out.append((q, d, r))
        r = 1 + r / (1 + d)
    return out


def solve(a, rhs):
    """Dense Gauss-Jordan elimination over complex rationals, pivoting on the first nonzero entry."""
    n = len(a)
    a = [[a[i][k] for k in range(n)] + [rhs[i]] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if not a[r][col].iszero())
        a[col], a[piv] = a[piv], a[col]
        p = a[col][col]
        a[col] = [x / p for x in a[col]]
        for r in range(n):
            if r != col and not a[r][col].iszero():
                f = a[r][col]
                a[r] = [x - f * y for x, y in zip(a[r], a[col])]
    return [a[i][n] for i in range(n)]


def chain_system(js, us, bs, n_left, n_right):
    """Stationarity of  n_left |f_1|^2 + n_right |f_T|^2 + c sum |f_(s+1) - u_(s+1) f_s|^2 + sum j_s |f_s - N0 b_s|^2."""
    t, c = len(js), 1 / Q0
    a = [[C(0)] * t for _ in range(t)]
    rhs = [js[s] * N0 * bs[s] for s in range(t)]
    for s in range(t):
        diag = js[s]
        if s == 0:
            diag += n_left
        else:
            diag += c
            a[s][s - 1] = -(c * us[s])
        if s == t - 1:
            diag += n_right
        else:
            diag += c
            a[s][s + 1] = -(c * us[s + 1].conj())
        a[s][s] = C(diag)
    return a, rhs


def ruler_1():
    print("Ruler 1. A uniform strand: the back range rests at the group, and the mass formula is its rest.")
    check(Q0 * N0 == D0 and (1 + D0) / D0 == N0 and D0 * D0 / (1 + D0) == Q0, "the founding: q0 N0 = d0, (1 + d0)/d0 = N0 = 5, d0^2/(1 + d0) = q0 = 1/20")
    for d in (F(1, 16), F(1, 4), F(1, 2), F(1), F(2)):
        m = d * d / (1 + d)
        rest = (1 + d) / d
        fixed = rest == 1 + rest / (1 + m * rest) and m * rest == d
        gaps = []
        for start in (F(1), F(1000)):
            r, last, falls = start, None, True
            for _ in range(400):
                r = 1 + r / (1 + m * r)
                gap = abs(r - rest)
                falls = falls and (last is None or gap < last or gap == 0)
                last = gap
            gaps.append(last)
            fixed = fixed and falls
        check(fixed and max(gaps) < F(1, 10**6), f"d = {d}: mass {m}, the rest R = (1 + d)/d = {rest}, with d = m R; from R = 1 and R = 1000 the gap falls at every step, under 10^-6 after 400")
    # The back range's move at a site is the Mobius move of [[1 + m, 1], [m, 1]]: a shear by one place after the mass's shear of the inverse.
    ok_swing = True
    for d in (F(1, 16), F(1, 4), F(1, 2), F(1), F(2), F(7, 3)):
        m = d * d / (1 + d)
        a, b, c, e = 1 + m, F(1), m, F(1)
        shear_place, shear_mass = ((F(1), F(1)), (F(0), F(1))), ((F(1), F(0)), (m, F(1)))
        prod = tuple(tuple(sum(shear_place[i][k] * shear_mass[k][j] for k in range(2)) for j in range(2)) for i in range(2))
        k_mult = (1 + d) ** 2
        r = F(9, 2)
        ok_swing = ok_swing and prod == ((a, b), (c, e)) and a * e - b * c == 1 and (a + e) ** 2 == k_mult + 1 / k_mult + 2
        ok_swing = ok_swing and (a * r + b) / (c * r + e) == 1 + r / (1 + m * r) and m * ((1 + d) / d) ** 2 - m * (1 + d) / d - 1 == 0
    check(ok_swing, "the back range's move is the Mobius move of [[1 + m, 1], [m, 1]] = [[1, 1], [0, 1]] [[1, 0], [m, 1]], two shears of determinant one; its trace gives (2 + m)^2 = K + 1/K + 2 at K = (1 + d)^2, which is m = d^2/(1 + d), and its fixed range solves m R^2 - m R - 1 = 0")


def ruler_2():
    print("Ruler 2. The pair form and the gate form are one scan.")
    rng = random.Random(20261112)
    ok_q = ok_n = ok_passive = ok_bound = True
    sites = 0
    for _ in range(40):
        js, us, bs = strand(rng, 48)
        pair, gate = scan_pair(js, us, bs), scan_gate(js, us, bs)
        peak = max(b.abs2() for b in bs)
        for (_, n_in, q_pair, _), (q_gate, d, r), j in zip(pair, gate, js):
            sites += 1
            ok_q = ok_q and q_pair == q_gate
            ok_n = ok_n and n_in == 1 / (Q0 * r) and d == j / n_in
            mod, kappa = 1 / (1 + d), N0 * d / (1 + d)
            ok_passive = ok_passive and mod + kappa / N0 == 1 and d >= 0
            ok_bound = ok_bound and q_gate.abs2() <= N0 * N0 * peak
    check(ok_q, f"{sites} sites of 40 random strands (masses 0 to 5, eight turns): the charge eta/n of the pair form equals the gate form's Q at every site")
    check(ok_n, "at every site the arriving count is n = 1/(q0 R) and the friction is d = j/n = m R: what the site brings over what the circle holds")
    check(ok_passive and ok_bound, "the move stays the built one: |gamma| + kappa/N0 = 1 at every site, and |Q| <= N0 max|b| on every strand")


def ruler_3():
    print("Ruler 3. The scan is the one-way factor of the two-way chain, and the two arrivals with the site make the two-way field.")
    rng = random.Random(410)
    ok_left = ok_two = ok_slope = True
    strands = sites = 0
    for _ in range(12):
        t = 14
        js, us, bs = strand(rng, t)
        left = scan_pair(js, us, bs)
        # The half strand's minimizer at its last site, for every length.
        for upto in range(1, t + 1):
            a, rhs = chain_system(js[:upto], us[:upto], bs[:upto], N0 - 1, F(0))
            if upto == 1 and js[0] == 0:
                # One site with no mass: the energy is the edge's alone, its minimizer zero.
                ok_left = ok_left and left[0][2] == C(0)
                continue
            f = solve(a, rhs)
            ok_left = ok_left and f[-1] == left[upto - 1][2]
            # The slope: the energy's second difference in the last site's value is the count after it.
            a2, rhs2 = chain_system(js[:upto], us[:upto], bs[:upto], N0 - 1, F(1))
            g = solve(a2, rhs2)
            # With one more unit of mass at the last site pulling toward zero: g_last = n f_last / (n + 1).
            n_after = left[upto - 1][3]
            ok_slope = ok_slope and g[-1] == f[-1] * n_after / (n_after + 1)
        # The right scan: the same strand read from its other end, each arrival turned back.
        rj, rb = js[::-1], bs[::-1]
        ru = [us[s + 1].conj() if s + 1 < t else C(1) for s in range(t)][::-1]
        right = scan_pair(rj, ru, rb)[::-1]
        a, rhs = chain_system(js, us, bs, N0 - 1, N0 - 1)
        f = solve(a, rhs)
        for s in range(t):
            ql, nl = left[s][0], left[s][1]
            qr, nr = right[s][0], right[s][1]
            joint = (ql * nl + qr * nr + js[s] * N0 * bs[s]) / (nl + nr + js[s])
            ok_two = ok_two and joint == f[s]
            sites += 1
        strands += 1
    check(ok_left, f"{strands} strands of 14 sites: for every length the dense solve of the half strand's energy gives the scan's charge at its last site")
    check(ok_slope, "and that energy's stiffness in the last site's value is the scan's count there (a unit of mass added at the site moves the minimizer by n/(n + 1))")
    check(ok_two, f"{sites} sites: the two-way solve equals (n_L Q_L + n_R Q_R + j N0 b)/(n_L + n_R + j), the two arrivals and the site weighed by their counts")


def ruler_4():
    print("Ruler 4. Across sites that bring nothing the ratio holds and the pair leaks.")
    ok_hold = ok_range = ok_share = True
    shares = []
    for gap in (0, 1, 5, 15, 35, 75):
        # A long written stretch at the founding, a letter, then `gap` massless sites, then a letter.
        js = [F(1)] * 60 + [F(0)] * gap + [F(1)]
        us = [TURNS[1]] * len(js)
        bs = [C(1 + (s % 3), s % 2) for s in range(len(js))]
        # Start the back range at its rest so the written stretch stands at the founding.
        pair, gate = scan_pair(js, us, bs), scan_gate(js, us, bs)
        held = gate[59][0]
        for s in range(60, 60 + gap):
            ok_hold = ok_hold and gate[s][0].abs2() == held.abs2() and gate[s][1] == 0
            ok_range = ok_range and gate[s][2] == N0 + (s - 60) and pair[s][3] < pair[s - 1][3]
        d = gate[-1][1]
        share = d / (1 + d)
        ok_share = ok_share and d == F(gap + 5, 20) and share == F(gap + 5, gap + 25)
        shares.append(f"{gap}: {share}")
    check(ok_hold, "a site of no mass turns the charge and keeps its modulus (d = 0 there), for gaps of 0 to 75 sites")
    check(ok_range, "the back range grows one place a site across the gap, and the count falls at every site of it")
    check(ok_share, "the letter after a gap of g such sites has d = (g + 5)/20 and takes (g + 5)/(g + 25) of the charge; by gap " + ", ".join(shares))


def bracket(target):
    """Rational d_lo < d < d_hi with d^2/(1 + d) = target between them, 10^-9 apart."""
    lo, hi = F(0), F(64)
    while hi - lo > F(1, 10**9):
        mid = (lo + hi) / 2
        if mid * mid / (1 + mid) < target:
            lo = mid
        else:
            hi = mid
    return lo, hi


def ruler_5():
    print("Ruler 5. A region sets its friction by how thinly it is written: letters one site in g, the sites between bringing nothing.")
    ok_root = ok_iter = True
    rows = []
    for g in (1, 2, 4, 8, 10, 16):
        target = F(g) * Q0
        lo, hi = bracket(target)
        if g == 1:
            ok_root = ok_root and D0 * D0 / (1 + D0) == target
        if g == 10:
            ok_root = ok_root and F(1) * F(1) / (1 + F(1)) == target
        # Iterate the gate form over 400 periods and read the friction at the last letter.
        r = N0
        d = None
        for _ in range(400):
            d = Q0 * r
            r = 1 + r / (1 + d)
            r += g - 1
        ok_iter = ok_iter and lo - F(1, 10**6) < d < hi + F(1, 10**6)
        letters = (1 + lo) / lo
        # The built law at the founding: every site leaks at d0, written or not.
        w = D0 / (1 + D0)
        built = w / (1 - (1 - w) ** g)
        rows.append((g, float(lo), float(letters), float(g * letters), built))
    check(ok_root, "the rest at the letters solves d^2/(1 + d) = g q0: d = 1/4 at g = 1 (five letters, five sites) and d = 1 at g = 10 (two letters, twenty sites)")
    check(ok_iter, "400 periods of the gate form land on that rest for g = 1, 2, 4, 8, 10 and 16 (within 10^-6)")
    print("     g   friction at a letter   letters heard   sites heard   built law: letters' share of the charge")
    for g, d, letters, sites, built in rows:
        print(f"    {g:2d}   {d:.4f}                 {letters:.2f}            {sites:.1f}          {built} = {float(built):.3f}")
    check(rows[-2][4] == F(5**9, 5**10 - 4**10) and rows[0][4] == 1, "the built law's share of the charge at the letters is w/(1 - (1 - w)^g) at w = 1/5 (one at g = 1, 5^9/(5^10 - 4^10) at g = 10): the rest is the drive of the sites between")


def ruler_6():
    print("Ruler 6. The back range is bounded and forgets.")
    rng = random.Random(6)
    ok_bounds = ok_slope = True
    for _ in range(40):
        js, us, bs = strand(rng, 64)
        for s, (_, d, r) in enumerate(scan_gate(js, us, bs)):
            ok_bounds = ok_bounds and 1 <= r <= N0 + s
    for _ in range(200):
        m, r, h = F(rng.randint(0, 40), rng.randint(1, 40)), F(rng.randint(1, 400), rng.randint(1, 9)), F(1, rng.randint(1, 50))
        step = lambda x: 1 + x / (1 + m * x)
        ok_slope = ok_slope and (step(r + h) - step(r)) / h == 1 / ((1 + m * r) * (1 + m * (r + h))) and (m == 0 or (step(r + h) - step(r)) < h)
    check(ok_bounds, "on 40 random strands 1 <= R <= N0 + (sites passed) at every site")
    check(ok_slope, "R' = 1 + R/(1 + m R) has difference quotient 1/((1 + m R)(1 + m (R + h))): its slope is |gamma|^2 at a site of mass, one at a site of none")


def ruler_7():
    print("Ruler 7. Arithmetic on G108's receipt (g108_reach_reads.txt on main): what one friction chart costs its regions at te5's mean.")
    places = [10818, 10881, 10853, 10918]
    total = 43470
    read = {
        "control": ([0.609122, 1.197870, 1.973933, 2.957331], 1.687019),
        "P-8": ([0.613285, 1.202510, 1.975659, 2.950416], 1.687911),
        "P-4": ([0.610789, 1.199730, 1.974410, 2.954189], 1.687230),
        "P+4": ([0.607741, 1.196834, 1.974927, 2.960737], 1.687520),
    }
    ok = sum(places) == total
    for name, (q, joint) in read.items():
        ok = ok and abs(sum(p * x for p, x in zip(places, q)) / total - joint) < 2e-6
    check(ok, "each read's quarters, weighed by their places, sum to its joint (within 2 millionths)")
    base = read["control"][0]
    shift = {"P-8": -0.5, "P-4": -0.25, "control": 0.0, "P+4": 0.25}
    print("     quarter   slope per unit of l   curvature   own zero from te5's (units of l)   gain at it   best shift read   gain there")
    best_joint = quad_joint = 0.0
    for k in range(4):
        slope = (read["P+4"][0][k] - read["P-4"][0][k]) / 0.5
        curve = (read["P+4"][0][k] + read["P-4"][0][k] - 2 * base[k]) / 0.0625
        zero = -slope / curve
        gain = slope * slope / (2 * curve)
        name = min(read, key=lambda n: read[n][0][k])
        got = base[k] - read[name][0][k]
        best_joint += places[k] * got / total
        quad_joint += places[k] * gain / total
        print(f"     {k + 1}         {slope:+.4f}               {curve:.4f}      {zero:+.2f}                              {gain:.4f}       {name} ({shift[name]:+.2f})     {got:.4f}")
    slope_joint = (read["P+4"][1] - read["P-4"][1]) / 0.5
    print(f"     the joint's slope {slope_joint:+.5f} nats a place a unit of l; a friction of its own for each quarter, among the four shifts read: {best_joint:.4f} nats a place; at each quarter's quadratic zero: {quad_joint:.4f}")
    check(abs(slope_joint) < 0.001 and best_joint > 0.002, "the joint stands near its own zero in the shared chart (slope under 0.001) while its quarters do not: one chart costs the joint at least 0.002 nats a place among the shifts read")
    # The lap means before te5's, from the differences G108's premise prints (te5 less te4, te4 less te3, by quarter).
    te4 = [b - x for b, x in zip(base, (-0.010464, -0.006748, -0.002191, +0.019074))]
    te3 = [b - x for b, x in zip(te4, (-0.015858, -0.016616, -0.008399, +0.026566))]
    joint_of = lambda q: sum(pl * x for pl, x in zip(places, q)) / total
    check(abs(joint_of(te4) - 1.687069) < 3e-6 and abs(joint_of(te3) - 1.690599) < 3e-6, "te4's and te3's quarters, rebuilt from the differences G108's premise prints, sum to their printed joints (within 3 millionths): te3 " + ", ".join(f"{x:.6f}" for x in te3) + "; te4 " + ", ".join(f"{x:.6f}" for x in te4))
    # The lever rule: a shared entry rests where its regions' weighed slopes cancel, at sum(w h z)/sum(w h).
    slopes = [(read["P+4"][0][k] - read["P-4"][0][k]) / 0.5 for k in range(4)]
    curves = [(read["P+4"][0][k] + read["P-4"][0][k] - 2 * base[k]) / 0.0625 for k in range(4)]
    lever = lambda w: -sum(x * s for x, s in zip(w, slopes)) / sum(x * c for x, c in zip(w, curves))
    held = lever(places)
    by_state = lever([0.5000, 0.2071, 0.1589, 0.1340])
    print(f"     the lever point of the four quarters, from te5's mean in units of l: weighed by their places (the held joint) {held:+.3f}; weighed by the masks' counts of states (ruler 8) {by_state:+.3f}")
    stiff = max(range(4), key=lambda k: curves[k])
    check(abs(held) < 0.1 and stiff == 2 and curves[2] > 5 * curves[3], "te5's chart stands within a tenth of a unit of l of its held quarters' lever point, and quarter 3, the stiffest (over five times quarter 4's curvature), holds it")
    # te6's own lap (g110_te6_reads.txt): the chart travelled on, and the quarters turned.
    te6 = [0.605245, 1.189710, 1.972207, 2.974266]
    turn = [a - b for a, b in zip(te6, base)]
    p4 = [read["P+4"][0][k] - base[k] for k in range(4)]
    print("     te6's mean less te5's by quarter: " + ", ".join(f"{x:+.4f}" for x in turn) + "; the shift P+4 less te5's: " + ", ".join(f"{x:+.4f}" for x in p4))
    check(turn[3] > 0.015 and turn[0] < 0 and turn[1] < 0 and sum(pl * x for pl, x in zip(places, turn)) / total > 0.0005, "over te6's lap quarter 4 rose 0.017 nats a place, quarters 1 to 3 fell, and the joint rose 0.0008: the lap's rest stands past the held joint's")


def ruler_8():
    print("Ruler 8. How a lap weighs its states, from the draw's own laws (field_train.rs: shape, weighed_domain, writer_region).")
    # A mask state: u uniform on 1..2^16, tau = u^2 >> 16 on 2^-16, each site of the domain open with chance tau.
    # Its weight a site is 2 sqrt(m/K), so its summed weight is 2 sqrt(m K), read at K = m tau as 2 m u / 2^16.
    cuts = [0, 16384, 32768, 49152, 65536]
    count = [0] * 4
    first = [0] * 4
    second = [0] * 4
    for u in range(1, 65537):
        tau = max(1, (u * u) >> 16)
        k = next(s for s in range(4) if tau <= cuts[s + 1])
        count[k] += 1
        first[k] += u
        second[k] += u * u
    share = lambda xs: [F(x, sum(xs)) for x in xs]
    c, f1, f2 = share(count), share(first), share(second)
    fmt = lambda xs: ", ".join(f"{float(x):.4f}" for x in xs)
    print(f"     mask states by quarter of tau (1 the fewest open): states {fmt(c)}; summed weight {fmt(f1)}; summed square weight {fmt(f2)}")
    check(all(abs(x - F(1, 4)) < F(1, 1000) for x in f1), "the masks weigh the four quarters alike, a quarter of the weight each (the importance weight 2 sqrt(tau) against the draw tau = u^2)")
    check(c[0] > F(499, 1000) and c[3] < F(135, 1000) and f2[3] > F(35, 100) and f2[0] < F(126, 1000), "half of the mask states stand in quarter 1 and 0.134 in quarter 4, each quarter 4 state at 3.7 times a quarter 1 state's weight, so quarter 4 holds 0.35 of the summed square weight and quarter 1 0.125")
    # A writer state: an octave o of 0..bits(len - 1) uniform, k = 0 at o = 0, else k uniform in [2^(o-1), min(2^o - 1, len - 1)];
    # the first k places in octave order written, the other len - k open, each compared at weight one.
    print("     the writer's state, weight one an open place: its summed weight over the answer's length, and its share in states at least 3/4 open")
    ok = True
    for length in (64, 128, 340, 1024):
        most = length - 1
        octaves = most.bit_length() + 1
        weight = F(0)
        open34 = F(0)
        for o in range(octaves):
            ks = [0] if o == 0 else list(range(1 << (o - 1), min((1 << o) - 1, most) + 1))
            for k in ks:
                p = F(1, octaves * len(ks))
                weight += p * (length - k)
                if 4 * (length - k) >= 3 * length:
                    open34 += p * (length - k)
        ok = ok and weight / length > F(3, 4) and open34 / weight > F(4, 5)
        print(f"       answer of {length:4d} places: {float(weight / length):.3f} of its length a state, {float(open34 / weight):.3f} of that in states at least 3/4 open; beside the masks' quarter 4, {float(open34 / length):.3f} against 0.250")
    check(ok, "a writer state weighs over 3/4 of its answer's length, over 4/5 of it in states at least 3/4 open: more than twice the masks' quarter 4, on states of another kind (a written front, the rest open)")


def scan_built(ds, us, bs):
    """The built circle: the friction read from the site's chart alone."""
    q = C(0)
    out = []
    for d, u, b in zip(ds, us, bs):
        q = (u * q + d * N0 * b) / (1 + d)
        out.append(q)
    return out


def scan_charted(ds, us, bs):
    """The derived circle on the built chart: the site's chart reads its own rest friction d^, its mass is d^^2/(1 + d^),
    and the edge's back range is the first site's rest. Returns each site's (charge after, friction, back range arriving)."""
    q, r = C(0), (1 + ds[0]) / ds[0]
    out = []
    for dh, u, b in zip(ds, us, bs):
        d = dh * dh / (1 + dh) * r
        q = (u * q + d * N0 * b) / (1 + d)
        out.append((q, d, r))
        r = 1 + r / (1 + d)
    return out


def ruler_9():
    print("Ruler 9. On the built chart: a strand of one friction is the built circle at every site, and the two differ only where the friction varies along a strand.")
    rng = random.Random(9)
    ok_same = True
    sites = 0
    for dh in (F(1, 65536), F(1, 16), F(1, 4), F(37, 100), F(1), F(3)):
        _, us, bs = strand(rng, 40)
        ds = [dh] * 40
        built, charted = scan_built(ds, us, bs), scan_charted(ds, us, bs)
        for qb, (qc, d, r) in zip(built, charted):
            sites += 1
            ok_same = ok_same and qb == qc and d == dh and r == (1 + dh) / dh
    check(ok_same, f"{sites} sites of six uniform strands (frictions from one grain, 2^-16, to 3): the charge, the friction and the back range equal the built circle's at every site, the first included")
    # Where the friction varies: written sites at the founding, the sites between at a low friction.
    low = F(1, 1024)
    rows = []
    ok_fresh = True
    for gap in (1, 5, 15, 35, 75):
        ds = [D0] * 60 + [low] * gap + [D0]
        us = [TURNS[1]] * len(ds)
        bs = [C(1 + (s % 3), s % 2) for s in range(len(ds))]
        charted = scan_charted(ds, us, bs)
        d = charted[-1][1]
        share = d / (1 + d)
        built_share = D0 / (1 + D0)
        # Between the massless limit of ruler 4 and the built share.
        ok_fresh = ok_fresh and built_share < share < F(gap + 5, gap + 25)
        rows.append(f"{gap}: {float(share):.3f} (massless {float(F(gap + 5, gap + 25)):.3f})")
    check(ok_fresh, "a letter after a gap of sites charted at d^ = 2^-10 takes more of the charge the longer the gap, where the built circle gives it 1/5 at every gap; by gap " + ", ".join(rows))


def ruler_10():
    print("Ruler 10. The ladder is standing: the 32 circles' mean moduli over open sites at te6's and te5's lap means (g110_te6_reads.txt, g108_reach_reads.txt; on 2^-30).")
    te6 = [924294530, 880513016, 760072461, 925979033, 750287021, 959476774, 914417094, 876382942, 875451143, 965661315, 783388433, 882888859, 856214497, 864543880, 814836200, 823735366, 800371294, 807832395, 901084531, 876156623, 893679202, 792498072, 825707543, 936048516, 870862677, 939220072, 788411428, 790782344, 771105373, 905470834, 893717936, 842663262]
    te5 = [940791125, 906710412, 789699221, 945297146, 786426162, 974015212, 930065663, 915814966, 900754775, 976602827, 817102167, 901254564, 881384004, 881544858, 839629227, 870593778, 840159563, 828873370, 928717697, 907863432, 921322583, 837187417, 852541040, 951475968, 897680656, 960220089, 813710984, 816222270, 816703159, 928712427, 913546751, 878539051]
    one = 1 << 30
    group = lambda g: F(one, one - g)  # (1 + d)/d at |gamma| = 1/(1 + d)
    for name, gs in (("te6", te6), ("te5", te5)):
        lo, hi = min(gs), max(gs)
        mean = F(sum(gs), 32 * one)
        print(f"     {name}: mean |gamma| {float(mean):.4f}; the circles from {lo / one:.4f} to {hi / one:.4f}, groups of {float(group(lo)):.2f} to {float(group(hi)):.2f} places")
    fell = sum(1 for a, b in zip(te6, te5) if a < b)
    check(len(te6) == 32 and group(max(te6)) > 2 * group(min(te6)) and group(max(te6)) > 9 and group(min(te6)) < 4, "at te6's mean the circles' groups run from 3.3 to 9.9 places, a ladder of over an octave and a half, and G108's trade was read with it standing")
    check(fell == 32, "from te5's mean to te6's every one of the 32 circles' moduli fell: the whole ladder travelled toward the near letters")


def main():
    for ruler in (ruler_1, ruler_2, ruler_3, ruler_4, ruler_5, ruler_6, ruler_7, ruler_8, ruler_9, ruler_10):
        ruler()
    print(f"rulers failed: {FAILED}")
    return 1 if FAILED else 0


if __name__ == "__main__":
    sys.exit(main())
