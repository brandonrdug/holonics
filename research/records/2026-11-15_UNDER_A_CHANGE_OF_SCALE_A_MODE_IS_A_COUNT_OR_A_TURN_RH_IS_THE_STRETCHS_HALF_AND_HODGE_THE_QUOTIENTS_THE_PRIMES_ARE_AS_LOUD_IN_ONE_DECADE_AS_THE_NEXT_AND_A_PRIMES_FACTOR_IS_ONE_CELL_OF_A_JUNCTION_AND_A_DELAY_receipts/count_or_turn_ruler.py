#!/usr/bin/env python3
"""count_or_turn_ruler.py: arithmetic for the record of 2026-11-15 that reads the Riemann
hypothesis and the Hodge conjecture through the lens of a change of scale.

Pure Python, no input, no state.  Run:  python3 -I count_or_turn_ruler.py
A ruler: it measures identities and counts on public arithmetic.  It decides neither
statement, and no reading here is evidence for either.

Sections
  BAND   a tower of equal junctions of step b with one delay between: its pass band
  TREE   closed walks from the root of the tree with b + 1 branches: its radius
  HASSE  one curve's counts over small prime fields, read as cells of that tower
  ZEROS  the first zeros of zeta from the Riemann-Siegel sum, against an area in cells
  LOUD   the primes' fluctuation in the half chart, its power in each decade of scale
  CM     the places where the square of a torus gains a fourth class of its own type
"""
import cmath
import math

TWO_PI = 2.0 * math.pi


# ---------------------------------------------------------------- BAND
def cell(eta, phi):
    """One junction of rapidity eta followed by one delay phi, on (forward, backward)."""
    ch, sh = math.cosh(eta), math.sinh(eta)
    e = cmath.exp(1j * phi)
    return (ch * e, sh / e, sh * e, ch / e)


def mul(m, n):
    a, b, c, d = m
    e, f, g, h = n
    return (a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h)


def tower_pass(b, phi, k):
    m = (1, 0, 0, 1)
    c = cell(0.5 * math.log(b), phi)
    for _ in range(k):
        m = mul(m, c)
    return 1.0 / abs(m[0]) ** 2


def band():
    for b in (2, 3, 5, 7, 16, 256):
        eta = 0.5 * math.log(b)
        edge = 2.0 * math.sqrt(b) / (b + 1)
        junction = 4.0 * b / (b + 1) ** 2
        phi_edge = math.acos(edge)
        share = 2.0 * math.asin(edge) / math.pi
        inside = min(tower_pass(b, phi_edge + 0.1, k) for k in range(1, 201))
        phi_out = max(phi_edge - 0.1, 0.0)
        kappa = math.acosh(math.cosh(eta) * math.cos(phi_out))
        outside = -math.log(tower_pass(b, phi_out, 60)) / 120.0
        print(
            f"BAND b={b} sech(eta)={1 / math.cosh(eta):.6f} 2sqrt(b)/(b+1)={edge:.6f} "
            f"edge^2={edge * edge:.6f} junction_pass={junction:.6f} "
            f"share_of_turns_passed={share:.4f} "
            f"inside(+0.1 rad): least_pass_over_200_cells={inside:.4f} "
            f"outside(-0.1 rad): decay_a_cell={outside:.4f} acosh(cosh(eta)cos(phi))={kappa:.4f}"
        )


# ---------------------------------------------------------------- TREE
def tree_closed_walks(b, half_length):
    """m_2k: walks of 2k steps from the root back to it on the tree with b + 1 branches."""
    v = [1]
    out = []
    for step in range(1, 2 * half_length + 1):
        w = [0] * (len(v) + 1)
        for n, c in enumerate(v):
            if not c:
                continue
            if n == 0:
                w[1] += (b + 1) * c
            else:
                w[n + 1] += b * c
                w[n - 1] += c
        v = w
        if step % 2 == 0:
            out.append(v[0])
    return out


def tree():
    k = 300
    for b in (2, 3, 5, 7):
        m = tree_closed_walks(b, k)
        ratio = m[-1] / m[-2]
        print(
            f"TREE branches={b + 1} m_2,m_4,m_6={m[0]},{m[1]},{m[2]} "
            f"m_{2 * k}/m_{2 * k - 2}={ratio:.5f} over_4b={ratio / (4 * b):.5f} "
            f"(1-3/(2k)={1 - 1.5 / k:.5f}) radius^2=4b={4 * b} "
            f"=(b+1)^2*junction_pass={(b + 1) ** 2 * 4.0 * b / (b + 1) ** 2:.1f}"
        )


# ---------------------------------------------------------------- HASSE
def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = bytearray(len(range(i * i, n + 1, i)))
    return [i for i in range(n + 1) if s[i]]


def trace_of_frobenius(p):
    """a_p = p + 1 - #E(F_p) for y^2 = x^3 + x + 1 (discriminant -2^4 * 31)."""
    half = (p - 1) // 2
    s = 0
    for x in range(p):
        v = (x * x * x + x + 1) % p
        if v:
            s += 1 if pow(v, half, p) == 1 else -1
    return -s


def hasse():
    ps = [p for p in primes_upto(2000) if p not in (2, 31)]
    inside = 0
    cos2 = 0.0
    worst = 0.0
    shown = []
    for p in ps:
        a = trace_of_frobenius(p)
        ct = a / (2.0 * math.sqrt(p))
        cphi = a / (p + 1.0)
        if abs(ct) < 1.0:
            inside += 1
        cos2 += ct * ct
        worst = max(worst, abs(ct))
        if p in (3, 5, 7, 11, 101, 1009):
            shown.append(
                f"p={p}:a={a},theta={math.acos(ct) / TWO_PI:.4f}turn,"
                f"delay={math.acos(cphi) / TWO_PI:.4f}turn"
            )
    print(
        f"HASSE y^2=x^3+x+1 primes={len(ps)} (to 2000, without 2 and 31) "
        f"cells_that_are_turns={inside} largest|a_p|/(2sqrt(p))={worst:.4f} "
        f"mean_cos^2(theta)={cos2 / len(ps):.4f} (even on the half-circle of sin^2: 0.2500)"
    )
    print("HASSE " + " ".join(shown))


# ---------------------------------------------------------------- ZEROS
def rs_theta(t):
    return 0.5 * t * math.log(t / TWO_PI) - 0.5 * t - math.pi / 8 + 1 / (48 * t) + 7 / (5760 * t ** 3)


LOGS = [0.0] + [math.log(n) for n in range(1, 64)]
ROOTS = [0.0] + [1.0 / math.sqrt(n) for n in range(1, 64)]


def rs_z(t):
    a = math.sqrt(t / TWO_PI)
    n_top = int(a)
    p = a - n_top
    th = rs_theta(t)
    s = 0.0
    for n in range(1, n_top + 1):
        s += ROOTS[n] * math.cos(th - t * LOGS[n])
    den = math.cos(TWO_PI * p)
    if abs(den) < 1e-9:
        p += 1e-7
        den = math.cos(TWO_PI * p)
    c0 = math.cos(TWO_PI * (p * p - p - 1.0 / 16.0)) / den
    return 2.0 * s + (-1) ** (n_top - 1) * (t / TWO_PI) ** -0.25 * c0


def zeros_to(height, step=0.02):
    out = []
    t = 10.0
    z = rs_z(t)
    while t < height:
        u = t + step
        w = rs_z(u)
        if (z < 0) != (w < 0):
            lo, hi, zl = t, u, z
            for _ in range(40):
                mid = 0.5 * (lo + hi)
                zm = rs_z(mid)
                if (zm < 0) == (zl < 0):
                    lo, zl = mid, zm
                else:
                    hi = mid
            out.append(0.5 * (lo + hi))
        t, z = u, w
    return out


def area_count(t):
    """Cells of 2 pi under x p = t, each of x and p cut at its grain, and 7/8."""
    return (t / TWO_PI) * (math.log(t / TWO_PI) - 1.0) + 7.0 / 8.0


def zeros():
    g = zeros_to(1000.0)
    print(f"ZEROS first three heights {g[0]:.4f} {g[1]:.4f} {g[2]:.4f}")
    for height in (100, 200, 500, 1000):
        n = sum(1 for x in g if x <= height)
        print(
            f"ZEROS height={height} counted={n} area_in_cells+7/8={area_count(height):.2f} "
            f"difference={n - area_count(height):+.2f}"
        )
    s = sum(2.0 / (0.25 + x * x) for x in g)
    tail = (math.log(1000.0 / TWO_PI) + 1.0) / (math.pi * 1000.0)
    euler = 0.5772156649015329
    whole = 2.0 + euler - math.log(4.0 * math.pi)
    print(
        f"ZEROS sum over the {len(g)} zeros to 1000 of 2/(1/4+g^2)={s:.5f} "
        f"tail_from_the_area_count={tail:.5f} together={s + tail:.5f} "
        f"2+gamma-ln(4pi)={whole:.5f} first_pair_share={2.0 / (0.25 + g[0] ** 2) / whole:.3f}"
    )
    return whole


# ---------------------------------------------------------------- LOUD
def loud(whole):
    top = 7
    n_max = 10 ** top
    sieve = bytearray([1]) * (n_max + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n_max ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(range(i * i, n_max + 1, i)))
    powers = {}
    for p in range(2, int(n_max ** 0.5) + 1):
        if sieve[p]:
            q = p * p
            lp = math.log(p)
            while q <= n_max:
                powers[q] = lp
                q *= p
    log = math.log
    c = log(TWO_PI)
    psi = sum(log(p) for p in (2, 3, 5, 7)) + log(2) * 2 + log(3)  # psi(9)
    readings = []
    for k in range(1, top):
        acc = 0.0
        for n in range(10 ** k, 10 ** (k + 1)):
            if sieve[n]:
                psi += log(n)
            elif n in powers:
                psi += powers[n]
            x = n + 0.5
            e = psi - x + c - 0.5 / (x * x)
            acc += e * e / (x * x)
        readings.append(acc / log(10.0))
        print(
            f"LOUD decade 10^{k}..10^{k + 1} power_in_the_half_chart_per_e-fold={readings[-1]:.5f} "
            f"over_the_zeros'_sum={readings[-1] / whole:.3f} psi(10^{k + 1})-10^{k + 1}={psi - 10 ** (k + 1):+.2f}"
        )
    # the rate: slope of ln(power) against ln(scale) over the decades from 10^2
    ys = [math.log(r) for r in readings[1:]]
    xs = [(k + 0.5) * log(10.0) for k in range(2, top)]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    mean = sum(readings[1:]) / len(readings[1:])
    print(
        f"LOUD decades from 10^2: mean={mean:.5f} over_the_zeros'_sum={mean / whole:.3f} "
        f"slope_of_ln(power)_in_ln(scale)={slope:+.4f} rate=1/2+slope/2={0.5 + slope / 2:.4f}"
    )
    print(
        "LOUD a zero at real part 0.6 would add slope +0.2: "
        f"x{10 ** 0.2:.3f} a decade, x{10 ** (0.2 * 5):.1f} over these five"
    )


# ---------------------------------------------------------------- CM
def reduced_forms(bound):
    """Primitive reduced forms a x^2 + b x y + c y^2 with -bound <= b^2 - 4ac < 0, by discriminant."""
    h = {}
    a = 1
    while 3 * a * a <= bound:
        for b in range(-a + 1, a + 1):
            c = a
            while 4 * a * c - b * b <= bound:
                if (a != c or b >= 0) and math.gcd(a, math.gcd(abs(b), c)) == 1:
                    d = b * b - 4 * a * c
                    h[d] = h.get(d, 0) + 1
                c += 1
        a += 1
    return h


def cm():
    zeta3 = sum(1.0 / n ** 3 for n in range(1, 200000))
    h = reduced_forms(10000)
    first = " ".join(f"{d}:{h[d]}" for d in sorted(h, reverse=True)[:12])
    print(f"CM discriminant:places  {first}")
    for bound in (100, 1000, 10000):
        n = sum(v for d, v in h.items() if -d <= bound)
        kinds = sum(1 for d in h if -d <= bound)
        print(
            f"CM to |D|={bound}: discriminants={kinds} places={n} places/|D|^(3/2)={n / bound ** 1.5:.4f} "
            f"(pi/(18 zeta(3))={math.pi / (18 * zeta3):.4f})"
        )
    print("CM classes of the torus's own type on E x E: 3 at a place with no relation, 4 at each place counted")


if __name__ == "__main__":
    band()
    tree()
    hasse()
    whole = zeros()
    loud(whole)
    cm()
