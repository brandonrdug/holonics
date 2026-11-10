#!/usr/bin/env python3
"""reach_bias.py REACH.<set>.tsv RUNLOG: per offset d, the census's U a place (FIELD_REACH line in RUNLOG) beside its plug-in
bias estimate (Miller-Madow: df = nonzero (far, letter) cells - far cells - letter cells + 1, over 2 x places) and their difference."""
import csv, sys, re
from collections import defaultdict
rows = defaultdict(list)
r = csv.reader(open(sys.argv[1]), delimiter="\t"); next(r)
for x in r:
    rows[int(x[1])].append((x[2], x[3], int(x[4])))
u = {}
for line in open(sys.argv[2]):
    m = re.match(r"FIELD_REACH set=(\S+) d=(-?\d+) places=\d+ u_nats_a_place=([\d.]+)", line)
    if m:
        u[int(m.group(2))] = float(m.group(3))
print("d places U bias U-bias")
for d in sorted(rows, key=lambda v: (abs(v), v)):
    R = rows[d]; P = sum(n for a, b, n in R)
    ab = sum(1 for a, b, n in R if n > 0); A = len({a for a, b, n in R if n > 0}); B = len({b for a, b, n in R if n > 0})
    bias = (ab - A - B + 1) / (2 * P)
    print(d, P, "%.4f" % u.get(d, float("nan")), "%.4f" % bias, "%+.4f" % (u.get(d, float("nan")) - bias))
