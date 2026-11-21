#!/usr/bin/env python3
"""grain_relation.py FAMILIES_TSV: a host ruler (floats are a ruler's; nothing here is the machine's).

Reads the lead's published table of the line's material by family (W80t: receipts/2026-11-21_widths/families_W80t.tsv; magnitudes in
units of 2^-24) and the published held reads (grains_W80t.txt, end_W80t.txt, copied below with their sources), and prints:

  A  each family's top, median and standing spread (rms of the lap's end less its mean), and each over the spread, in places;
  B  the price of a place as a ratio: rent(u) = R * mean_i (u / sigma_i)^2 / 12, R the spread's own rent (the lap's end over its mean),
     against the five masks the lead read (G-W1), with no fitted number;
  C  the same price for a read part at each family's own spread, and the bits such a read part needs;
  D  the frozen error of a count read on a lattice u from a store that jitters by sigma: the closed form
     (u/pi) * sum_k ((-1)^k / k) exp(-2 pi^2 k^2 sigma^2 / u^2) sin(2 pi k m / u), beside a drawn check;
  E  a flux of a thousandth of a grain a tick, released plainly and with its rest carried.
"""
import csv, math, random, sys

rows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t'))
U = 2.0 ** 24
fam = []
for r in rows:
    n, s, mx, p50 = int(r['entries']), float(r['rms_end_less_mean']) / U, float(r['max']) / U, float(r['p50']) / U
    if s > 0 and mx > 0:
        fam.append((r['name'], n, int(r['grain']), p50, mx, s))
N = sum(f[1] for f in fam)
lg = math.log2
print('A  families with a spread: %d of %d, entries %d' % (len(fam), len(rows), N))
w = lambda g: sum(g(f) * f[1] for f in fam) / N
print('A  lg sigma: least %.2f greatest %.2f entry mean %.2f' % (min(lg(f[5]) for f in fam), max(lg(f[5]) for f in fam), w(lambda f: lg(f[5]))))
print('A  top over sigma, places: least %.2f greatest %.2f entry mean %.2f' % (min(lg(f[4] / f[5]) for f in fam), max(lg(f[4] / f[5]) for f in fam), w(lambda f: lg(f[4] / f[5]))))
med = [f for f in fam if f[3] > 0]
Nm = sum(f[1] for f in med)
print('A  median over sigma, places: least %.2f greatest %.2f entry mean %.2f' % (min(lg(f[3] / f[5]) for f in med), max(lg(f[3] / f[5]) for f in med), sum(lg(f[3] / f[5]) * f[1] for f in med) / Nm))
print('A  places of the declared word under sigma: entry mean %.2f (grain 24: %.2f, grain 16: %.2f)' % (
    w(lambda f: f[2] + lg(f[5])),
    sum((f[2] + lg(f[5])) * f[1] for f in fam if f[2] == 24) / sum(f[1] for f in fam if f[2] == 24),
    sum((f[2] + lg(f[5])) * f[1] for f in fam if f[2] == 16) / sum(f[1] for f in fam if f[2] == 16)))

# B: the lead's reads (millionths of a nat a place, 139,998 places): grains_W80t.txt (the lap's mean) and end_W80t.txt (the lap's end).
MEAN, END = 1309612, 1350068
MASK = {12: 1309799, 10: 1309979, 9: 1310299, 8: 1312076, 6: 1340059}
R = (END - MEAN) / 1e6
print('B  the spread\'s rent R = end - mean = %.6f nats a place' % R)
print('B  g   read rise   equal rent an entry   one stiffness')
ms = sum(f[1] * f[5] ** 2 for f in fam) / N
for g in (12, 10, 9, 8, 6):
    u = 2.0 ** -g
    eq = R * sum(f[1] * (u / f[5]) ** 2 for f in fam) / N / 12
    one = R * u * u / (12 * ms)
    print('B  %2d  %.6f   %.6f              %.6f' % (g, (MASK[g] - MEAN) / 1e6, eq, one))

# C: a read part at each family's own spread: u_f the power of two at or under sigma_f, and j places under it.
for j in (0, 1, 2):
    cost = R * sum(f[1] * (2.0 ** (math.floor(lg(f[5])) - j) / f[5]) ** 2 for f in fam) / N / 12
    bits = [math.ceil(lg(f[4]) - (math.floor(lg(f[5])) - j)) + 1 for f in fam]   # places from the top to the lattice, and a sign
    hist = {}
    for f, b in zip(fam, bits):
        hist[b] = hist.get(b, 0) + f[1]
    print('C  lattice %d under the spread\'s place: rent %.6f nats a place; read part bits (with sign): greatest %d, entry mean %.2f, entries over 16 bits %d'
          % (j, cost, max(bits), sum(b * f[1] for f, b in zip(fam, bits)) / N, sum(n for b, n in hist.items() if b > 16)))
places = sorted(set((-math.floor(lg(f[5]))) for f in fam))
print('C  the spread\'s place by family, places under the point: %s' % ' '.join('%d:%d' % (p, sum(1 for f in fam if -math.floor(lg(f[5])) == p)) for p in places))

# D: the frozen error of the mean of counts read on a lattice u = 1 from m + sigma Z.
def frozen(m, s, terms=40):
    return sum(((-1) ** k / k) * math.exp(-2 * math.pi ** 2 * k * k * s * s) * math.sin(2 * math.pi * k * m) for k in range(1, terms)) / math.pi
random.seed(20261121)
print('D  sigma/u   greatest frozen error over the cell (closed form)   drawn at m = 0.25 (200,000 reads)   closed form at 0.25')
for s in (0.0, 0.125, 0.25, 0.5, 0.75, 1.0):
    worst = max(abs(frozen(i / 400, s)) for i in range(400)) if s > 0 else 0.5
    K = 200000
    drawn = sum(math.floor(0.25 + s * random.gauss(0, 1) + 0.5) for _ in range(K)) / K - 0.25
    print('D  %.3f     %.3e                                          %+.5f                            %+.5f' % (s, worst, drawn, frozen(0.25, s) if s > 0 else -0.25))

# E: a flux of a thousandth of a grain a tick over 10,000 ticks: the count that crossed, plain and carried (integers).
GRAIN, FLUX, TICKS = 1000, 1, 10000          # a grain is 1000 fine units, the flux one fine unit a tick
plain = sum((FLUX + GRAIN // 2) // GRAIN for _ in range(TICKS))
rest, carried = 0, 0
for _ in range(TICKS):
    t = FLUX + rest
    c = (t + GRAIN // 2) // GRAIN
    carried += c
    rest = t - c * GRAIN
print('E  true crossings %d; plain release %d; rest carried %d (rest %d of a grain of %d)' % (FLUX * TICKS // GRAIN, plain, carried, rest, GRAIN))
