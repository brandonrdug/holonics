#!/usr/bin/env python3
"""A host ruler for the record of November 23 on the handed cycle, implicit units and the comma.

It reads no state of the machine and no private file: every number is drawn from a fixed seed or is a constant of the literature,
recomputed here. `python3 handed_cycle.py > handed_cycle.txt`. Sections:

  A  a helix of fifths addressed by its own remainders (Euclid on two ratios, in factored integers)
  B  what a quotient of that address costs to write and what it fixes of the ratio
  C  a layout against a count: cells at one separation, and the rounding cost, on five lattices
  D  a common stretch as a shift of the logarithmic axis, and a loop of two stretches that leaves a turn
  E  mutual loss on a drawn pair of shares: two directed parts, one symmetric sum
  F  a unit read as the difference tone of its partials, which no linear read holds
  G  a chain of relative moves with one link unread, and the loop that returns it
  H  a triad under a second invariant of one sign
"""
import cmath
import math
import random
from fractions import Fraction

random.seed(20261123)


def factored(fr):
    """A ratio of powers of 2 and 3 as its two valuations."""
    n, d, v2, v3 = fr.numerator, fr.denominator, 0, 0
    for p in (2, 3):
        while n % p == 0:
            n //= p
            if p == 2:
                v2 += 1
            else:
                v3 += 1
        while d % p == 0:
            d //= p
            if p == 2:
                v2 -= 1
            else:
                v3 -= 1
    assert n == 1 and d == 1
    return v2, v3


def section_a():
    print("A. A helix of fifths addressed by its own remainders")
    print("   Euclid on the octave 2:1 and the fifth 3:2, multiplicatively: how many times the smaller fits the larger, and the")
    print("   remainder becomes the next unit. Integers only.")
    print("   step  fits  remainder (2^a 3^b)        nats      cents   unit (fifths)  laps to one own step")
    big, small = Fraction(2), Fraction(3, 2)
    h0, h1, k0, k1 = 1, 0, 0, 1  # convergents h/k of log 2 / log(3/2): h fifths against k octaves
    quotients = []
    for step in range(1, 10):
        a = 0
        rest = big
        while rest >= small:
            rest /= small
            a += 1
        quotients.append(a)
        h0, h1 = a * h0 + h1, h0
        k0, k1 = a * k0 + k1, k0
        v2, v3 = factored(rest)
        nats = math.log(rest.numerator) - math.log(rest.denominator)
        cents = 1200 * nats / math.log(2)
        # the quotients are those of log 2 / log(3/2): the unit of h0 fifths misses k0 octaves by |h0 log2(3/2) - k0| octaves,
        # which is the remainder of this step; its own step is 1/h0 of an octave
        miss = abs(h0 * math.log2(1.5) - k0)
        laps = (1 / h0) / miss if miss > 0 else float("inf")
        print(f"   {step:>4}  {a:>4}  2^{v2:<5} 3^{v3:<6}         {nats:9.6f} {cents:9.3f}   {h0:>6}        {laps:9.2f}")
        big, small = small, rest
    print(f"   the address of the fifth in the octave: {quotients}")
    print("   remainders: the fourth 4:3, the tone 9:8, the leimma 256:243, the comma 531441:524288, then finer commas;")
    print("   each level's remainder is the next level's gap, and a unit's laps before its comma amounts to one of its own steps")
    print("   is its quality, which lies between the next quotient and the next quotient and one: 4.26 for twelve, 6.26 for fifty-three, 23.88 for 665.")
    print()


def section_b():
    print("B. What a quotient costs to write and what it fixes")
    ln2 = math.log(2)
    # the quotients' law for a ratio drawn at large (Gauss, Kuzmin): P(k) = log2(1 + 1/(k(k+2)))
    H = 0.0
    gamma = 0.0
    top = 2_000_000
    mass = 0.0
    for k in range(1, top + 1):
        p = math.log2(1 + 1 / (k * (k + 2)))
        mass += p
        H -= p * math.log2(p)
        gamma += p * (2 * (k.bit_length() - 1) + 1)
    # the tail past `top`: P(k) ~ 1/(k^2 ln 2), length ~ 2 log2 k + 1, by the integral
    tail = (2 * math.log2(top) + 1 + 2 / ln2) / (top * ln2)
    tail_h = (math.log2(top * top * ln2) + 1 / ln2) / (top * ln2)
    print(f"   entropy of a quotient (its law at large, Gauss and Kuzmin): {H + tail_h:.4f} bits = {(H + tail_h) * ln2:.4f} nats")
    print(f"   written with its own length (Elias gamma, 2 floor(log2 k) + 1 bits): {gamma + tail:.4f} bits a quotient")
    print(f"   fixed of the ratio by a quotient, pi^2 / (6 ln 2): {math.pi ** 2 / (6 * ln2):.4f} nats = {math.pi ** 2 / (6 * ln2 * ln2):.4f} bits")
    # measured: Euclid on drawn pairs of 4096-bit integers
    counts = {}
    total_q = 0
    total_ln = 0.0
    pairs = 200
    for _ in range(pairs):
        b = random.getrandbits(4096) | (1 << 4095)
        a = random.randrange(1, b)
        total_ln += 2 * math.log(b)
        while a:
            q, r = divmod(b, a)
            counts[q] = counts.get(q, 0) + 1
            total_q += 1
            b, a = a, r
    Hm = -sum(c / total_q * math.log2(c / total_q) for c in counts.values())
    gm = sum(c * (2 * (q.bit_length() - 1) + 1) for q, c in counts.items()) / total_q
    print(f"   measured on {pairs} drawn pairs of 4,096-bit integers, {total_q} quotients:")
    print(f"     nats of the ratio fixed a quotient {total_ln / total_q:.4f}; the quotients' entropy {Hm:.4f} bits; written with")
    print(f"     their own length {gm:.4f} bits; share of quotients equal to 1, 2, 3: "
          f"{counts[1] / total_q:.3f}, {counts[2] / total_q:.3f}, {counts[3] / total_q:.3f}")
    print("   a radix digit of base b costs log b and fixes log b, with the base, the width and the point's place held beside it.")
    print()


def ball(n, r):
    return math.pi ** (n / 2) * r ** n / math.gamma(n / 2 + 1)


def section_c():
    print("C. A layout against a count")
    print("   cells at one least separation in one volume (the packing's share of space), and the mean squared rounding distance")
    print("   at one cell volume (the normalized second moment G), each against the cubic lattice of scalar digits.")
    print("   lattice            dim  share      against cube   bits/coordinate   G          bits/coordinate (rounding)")
    rows = [
        ("cube Z^n (n = 1)", 1, 0.5, 1.0, Fraction(1, 12)),
        ("hexagonal A2", 2, 0.5, math.sqrt(3) / 2, 5 / (36 * math.sqrt(3))),
        ("face-centred D3", 3, math.sqrt(2) / 2, 2.0, 0.078745),
        ("E8", 8, 1 / math.sqrt(2), 1.0, Fraction(929, 12960)),
        ("Leech", 24, 1.0, 1.0, 0.065771),
    ]
    for name, n, radius, covolume, G in rows:
        share = ball(n, radius) / covolume
        cube = ball(n, 0.5)
        ratio = share / cube
        gain = 0.5 * math.log2((1 / 12) / float(G))
        print(f"   {name:<18} {n:>3}  {share:9.6f}  {ratio:13.4f}  {math.log2(ratio) / n:12.4f}      {float(G):.6f}   {gain:8.4f}")
    limit = 1 / (2 * math.pi * math.e)
    print(f"   the rounding cost's floor in any dimension, 1/(2 pi e) = {limit:.6f}: {0.5 * math.log2((1 / 12) / limit):.4f} bits a coordinate")
    print("   (G of D3 and of the Leech lattice are Conway and Sloane's values, from training; the rest is computed here.)")
    print()


def mat(a, b, c, d):
    return [[a, b], [c, d]]


def mul(m, n):
    return [[sum(m[i][k] * n[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def dagger(m):
    return [[m[j][i].conjugate() for j in range(2)] for i in range(2)]


def section_d():
    print("D. A common stretch, and a loop of stretches")
    for beta in (0.1, 0.5):
        D = math.sqrt((1 + beta) / (1 - beta))
        both = (2 * beta) / (1 + beta * beta)
        D2 = math.sqrt((1 + both) / (1 - both))
        print(f"   speed {beta}: the stretch of every rate {D:.5f}, on the logarithmic axis {math.log(D):.5f};"
              f" two in a chain: speed {both:.5f}, log stretch {math.log(D2):.5f} = twice")
    print("   a spectrum of partials 2:3:5 under the stretch 1.73205: 3.4641 : 5.1962 : 8.6603, ratios 2:3:5 as before")
    print("   two equal stretches at a right angle (2 x 2 complex, a half-angle each), then the turn the product holds:")
    for beta in (0.1, 0.5, 0.9):
        eta = math.atanh(beta)
        c, s = math.cosh(eta / 2), math.sinh(eta / 2)
        bx = mat(c, s, s, c)
        by = mat(c, -1j * s, 1j * s, c)
        m = mul(bx, by)
        a = mul(dagger(m), m)  # positive, determinant one
        tr = (a[0][0] + a[1][1]).real
        root = [[(a[i][j] + (1 if i == j else 0)) / math.sqrt(tr + 2) for j in range(2)] for i in range(2)]
        det = root[0][0] * root[1][1] - root[0][1] * root[1][0]
        inv = [[root[1][1] / det, -root[0][1] / det], [-root[1][0] / det, root[0][0] / det]]
        u = mul(m, inv)
        half = math.acos(max(-1.0, min(1.0, ((u[0][0] + u[1][1]) / 2).real)))
        closed = 2 * math.atan(math.tanh(eta / 2) ** 2)
        print(f"     speed {beta}: turn {math.degrees(2 * half):8.4f} degrees; 2 atan(tanh^2(eta/2)) = {math.degrees(closed):8.4f}")
    print()


def section_e():
    print("E. Mutual loss on a drawn pair of shares over 16 symbols")
    w = [random.random() for _ in range(16)]
    v = [x * math.exp(0.6 * (random.random() - 0.5)) for x in w]
    p = [x / sum(w) for x in w]
    q = [x / sum(v) for x in v]
    dpq = sum(a * math.log(a / b) for a, b in zip(p, q))
    dqp = sum(b * math.log(b / a) for a, b in zip(p, q))
    both = sum((a - b) * (math.log(a) - math.log(b)) for a, b in zip(p, q))
    chi = sum((a - b) ** 2 / a for a, b in zip(p, q))
    least = min((a - b) * (math.log(a) - math.log(b)) for a, b in zip(p, q))
    print(f"   p's reader paying to read with q's shares {dpq:.6f} nats; q's with p's {dqp:.6f}; their sum {dpq + dqp:.6f}")
    print(f"   the sum over symbols of (p - q)(log p - log q) = {both:.6f}; the least symbol's term {least:.2e}, none negative")
    print(f"   its second order, the sum of (p - q)^2 / p: {chi:.6f}")
    print()


def section_f():
    print("F. A unit as the difference tone of its partials")
    n = 240
    for phase in (0.0, 0.7):
        x = [sum(math.cos(2 * math.pi * k * t / n + phase) for k in (3, 4, 5)) for t in range(n)]
        lin = sum(x[t] * cmath.exp(-2j * math.pi * t / n) for t in range(n)) * 2 / n
        quad = sum(x[t] ** 2 * cmath.exp(-2j * math.pi * t / n) for t in range(n)) * 2 / n
        third = sum(x[t] * cmath.exp(-2j * math.pi * 3 * t / n) for t in range(n)) * 2 / n
        print(f"   partials 3, 4, 5 of a unit, each turned by {phase:.1f}: the unit in a linear read {abs(lin):.6f};"
              f" in the square {abs(quad):.6f} at phase {cmath.phase(quad):+.4f}; partial 3 at phase {cmath.phase(third):+.4f}")
    print("   the common turn moves every partial's phase and leaves the difference tone where it was.")
    print()


def compose(g, h):
    (a, x, y), (b, u, v) = g, h
    return (a + b, x + math.cos(a) * u - math.sin(a) * v, y + math.sin(a) * u + math.cos(a) * v)


def inverse(g):
    a, x, y = g
    return (-a, -(math.cos(a) * x + math.sin(a) * y), -(-math.sin(a) * x + math.cos(a) * y))


def section_g():
    print("G. A chain of relative moves with one link unread")
    draw = lambda: (random.uniform(-2, 2), random.uniform(-1, 1), random.uniform(-1, 1))
    worst_far, worst_link = 0.0, 0.0
    for _ in range(1000):
        a, x, b, c = draw(), draw(), draw(), draw()
        place = compose(compose(a, x), b)
        far = compose(inverse(place), compose(place, c))
        worst_far = max(worst_far, max(abs(far[i] - c[i]) for i in range(3)))
        back = compose(compose(inverse(a), place), inverse(b))
        worst_link = max(worst_link, max(abs(back[i] - x[i]) for i in range(3)))
    print(f"   1,000 drawn chains trunk . a . x . b . c of planar moves (a turn and a shift each), x unread:")
    print(f"   the far part read against the part before it returns c, worst difference {worst_far:.1e};")
    print(f"   one touch of the far part's place returns the link, worst difference {worst_link:.1e}.")
    print()


def section_h():
    print("H. A triad under a second invariant")
    w = [Fraction(1), Fraction(4), Fraction(9)]
    d2 = Fraction(-1)
    d1 = -(w[2] - w[1]) / (w[2] - w[0]) * d2
    d3 = -(w[1] - w[0]) / (w[2] - w[0]) * d2
    print(f"   weights 1, 4, 9 (a squared rate at rates 1, 2, 3), the middle gives 1: the coarse end takes {d1}, the fine end {d3};")
    print(f"   of the weighted total the coarse end takes {w[0] * d1} and the fine end {w[2] * d3} of {-w[1] * d2}")
    print("   weights 1, -1 (two hands): members 1 and 1 hold the weighted total 0 at any size, so it bounds neither.")
    print()


if __name__ == "__main__":
    section_a()
    section_b()
    section_c()
    section_d()
    section_e()
    section_f()
    section_g()
    section_h()
