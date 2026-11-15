#!/usr/bin/env python3
"""scale_ruler: eight pieces of arithmetic behind the record's readings (a host ruler; numbers only, no input)

usage: python3 -I scale_ruler.py

1. A junction between two levels whose clock and impedance step by b (atlas wave.wound-ladder-radix) reflects
   (b - 1)/(b + 1) and passes 4b/(b + 1)^2. With the step written as a logarithm, e = ln b, these are tanh(e/2) and
   sech(e/2)^2: on the pair (forward wave, backward wave) the junction is the boost [[cosh, sinh], [sinh, cosh]] of
   e/2, and a delay between two junctions is the turn diag(exp(i phi), exp(-i phi)). A chain of k equal steps across
   a whole ratio rho is a word of k boosts with k - 1 turns between them, and it passes 1/|M_11|^2. Printed:
   no delay (the word is one boost of ln rho / 2); a quarter turn at every delay (k = 2: all of it); the mean of
   the logarithm over every delay on an even grid, beside the product sech(ln rho/(2k))^(2k) it equals; that
   product beside its floor exp(-(ln rho)^2/(4k)); and the sum of powers with every re-reflection and no phase
   kept, 1/(1 + k sinh(ln rho/(2k))^2).
2. The store's floor 2 pi E R/(hbar c) for a mass m at the length hbar/(m c) with its rest energy, in nats.
3. The count of nucleons at which gravity's summed pull meets the pressure of matter held up by the exclusion of
   like particles, in order of magnitude: (hbar c/(G m_p^2))^(3/2), beside the Sun's count. Constants are the
   2018 CODATA values to five digits, typed in.
4. The distance "p^(-k), k the deepest level at which two residues share a cell" on Z/p^n: over every triple the
   two longest sides are equal, and from one cell of the first level every residue of another cell is at one
   distance.
5. The same towers read as paths: from a residue up to the first level it shares with another and back down is
   2(n - k) steps. Printed: the greatest count over every pair (it is finite for all), how many pairs stand at
   each count, and that the count obeys the triangle inequality.
6. A rider and its ground: the fourth root of a light mass over a heavy one, k = (m_e/m_p)^(1/4), with k^2 and
   k^4, the orders of a molecule's vibrational and rotational steps against its electronic step (Born and
   Oppenheimer 1927).
7. A drive between two baths: quanta sent out per quantum taken in at equal power, the ratio of the two
   temperatures, for 5772 K against 255 K and against 288 K.
8. Euclid's construction: the product of the first n primes plus one, and its least prime factor, which is none
   of the n.
"""
import itertools
import math


def word(eta, phis):
    c, sh = math.cosh(eta), math.sinh(eta)
    a, b = complex(c), complex(sh)
    for phi in phis:
        r = complex(math.cos(phi), math.sin(phi))
        a, b = a * r, b * r.conjugate()
        a, b = a * c + b * sh, a * sh + b * c
    return 1 / abs(a) ** 2


def delays():
    print("DELAYS a word of k boosts of eta = ln(rho)/(2k) with k - 1 turns between")
    for rho, k, grid in ((16.0, 2, 720), (16.0, 3, 180), (1024.0, 3, 180), (1024.0, 4, 60)):
        eta = math.log(rho) / (2 * k)
        none = word(eta, [0.0] * (k - 1))
        quarter = word(eta, [math.pi / 2] * (k - 1))
        total, count = 0.0, 0
        for idx in itertools.product(range(grid), repeat=k - 1):
            total += math.log(word(eta, [2 * math.pi * (i + 0.5) / grid for i in idx]))
            count += 1
        product = 1 / math.cosh(eta) ** (2 * k)
        print("  rho=%g k=%d no_delay=%.6f one_boost=%.6f quarter_turns=%.6f log_mean_over_delays=%.6f log_product=%.6f" % (rho, k, none, 1 / math.cosh(math.log(rho) / 2) ** 2, quarter, total / count, math.log(product)))


def junction():
    print("JUNCTION step b: reflects, passes, tanh(ln b/2), sech(ln b/2)^2")
    for b in (2, 3, 10):
        e = math.log(b)
        print("  b=%d reflects=%.6f passes=%.6f tanh=%.6f sech2=%.6f" % (b, (b - 1) / (b + 1), 4 * b / (b + 1) ** 2, math.tanh(e / 2), 1 / math.cosh(e / 2) ** 2))
    for rho, name in ((2.0 ** 30, "2^30"), (1e9, "10^9"), (1e46, "10^46")):
        lr = math.log(rho)
        print("CHAIN ratio=%s ln=%.3f one_step=%.3e four_over_ratio=%.3e" % (name, lr, 1 / math.cosh(lr / 2) ** 2, 4 / rho))
        for k in (1, 9, 30, 100, 300, 1000, 10000):
            passes = math.exp(-2 * k * math.log(math.cosh(lr / (2 * k))))
            mixed = 1 / (1 + k * math.sinh(lr / (2 * k)) ** 2)
            print("  steps=%d step_ratio=%.4f product=%.6f floor_exp=%.6f powers_summed=%.6f" % (k, rho ** (1 / k), passes, math.exp(-lr * lr / (4 * k)), mixed))
        print("  steps for a half passed: floor form %.1f, powers summed %.1f" % (lr * lr / (4 * math.log(2)), lr * lr / 4))


def compton():
    print("COMPTON 2 pi E R/(hbar c) at R = hbar/(m c), E = m c^2: %.6f nats (2 pi = %.6f)" % (2 * math.pi, 2 * math.pi))


def star():
    g, mp, hbar, c, msun = 6.6743e-11, 1.6726e-27, 1.0546e-34, 2.9979e8, 1.9884e30
    ag = g * mp * mp / (hbar * c)
    print("STAR G m_p^2/(hbar c)=%.4e its power -3/2=%.3e Sun's nucleons=%.3e ratio=%.2f" % (ag, ag ** -1.5, msun / mp, ag ** -1.5 / (msun / mp)))


def depth(p, n, x, y):
    d, k = (x - y) % p ** n, 0
    if d == 0:
        return n
    while d % p == 0:
        d //= p
        k += 1
    return k


def towers():
    for p, n in ((2, 6), (3, 4), (5, 3)):
        size, bad, triples = p ** n, 0, 0
        for x, y, z in itertools.product(range(size), repeat=3):
            if x < y < z:
                triples += 1
                a, b, c = sorted((depth(p, n, x, y), depth(p, n, y, z), depth(p, n, x, z)))
                bad += a != b
        seen = {depth(p, n, 0, y) for y in range(size) if y % p == 1}
        print("TOWER p=%d levels=%d residues=%d triples=%d two_longest_sides_unequal=%d depths_from_0_to_the_cell_of_1=%s" % (p, n, size, triples, bad, sorted(seen)))


def steps():
    for p, n in ((2, 6), (3, 4), (5, 3)):
        size = p ** n
        d = [[2 * (n - depth(p, n, x, y)) for y in range(size)] for x in range(size)]
        counts = {}
        for x in range(size):
            for y in range(x + 1, size):
                counts[d[x][y]] = counts.get(d[x][y], 0) + 1
        bad = 0
        for x, y, z in itertools.product(range(size), repeat=3):
            bad += d[x][z] > d[x][y] + d[y][z]
        print("STEPS p=%d levels=%d greatest=%d pairs_at_each_count=%s triangle_fails=%d" % (p, n, max(counts), sorted(counts.items()), bad))


def ground():
    me, mp = 9.1094e-31, 1.6726e-27
    k = (me / mp) ** 0.25
    print("GROUND m_p/m_e=%.2f k=(m_e/m_p)^(1/4)=%.4f k^2=%.5f k^4=%.3e" % (mp / me, k, k * k, k ** 4))


def baths():
    for cold in (255, 288):
        print("BATHS hot=5772 K cold=%d K quanta_out_per_quantum_in=%.1f" % (cold, 5772 / cold))


def least_factor(n):
    f = 2
    while f * f <= n:
        if n % f == 0:
            return f
        f += 1
    return n


def euclid():
    primes, product = [], 1
    for q in (2, 3, 5, 7, 11, 13, 17, 19):
        primes.append(q)
        product *= q
        f = least_factor(product + 1)
        print("EUCLID primes=%d product_plus_one=%d least_factor=%d among_the_present=%s" % (len(primes), product + 1, f, f in primes))


if __name__ == "__main__":
    junction()
    delays()
    compton()
    star()
    towers()
    steps()
    ground()
    baths()
    euclid()
