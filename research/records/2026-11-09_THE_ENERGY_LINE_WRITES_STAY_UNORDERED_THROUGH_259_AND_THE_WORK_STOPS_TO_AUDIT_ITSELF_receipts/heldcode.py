#!/usr/bin/env python3
"""A held read's code (the claim's held G): the mean over held places of -ln p(truth) under the full G at the read's T, with its SE over
places (as 14:08) and the jackknife over problems; with a second read, the paired difference. Args: ENUMERATED:lap [ENUMERATED:lap]."""
import csv, math, sys, statistics
def plain(spec):
    path, lap = spec.rsplit(':', 1); o = {}
    for r in csv.DictReader(open(path), delimiter='\t'):
        if r['lap'] != lap: continue
        T = 2.0 ** (int(r['log2_t']) / 2 ** 24); g = [int(v) / 2 ** 32 for v in r['energies'].split(',')]; lo = min(g)
        w = [2.0 ** (-(x - lo) / T) for x in g]; o[(r['problem'], r['place'])] = -math.log(w[int(r['truth'])] / sum(w))
    return o
def jk(vals):
    per = {}
    for (p, _), v in vals.items(): per.setdefault(p, []).append(v)
    n = len(vals); s = sum(vals.values()); loo = [(s - sum(per[p])) / (n - len(per[p])) for p in per]; m = sum(loo) / len(loo)
    return math.sqrt((len(loo) - 1) / len(loo) * sum((x - m) ** 2 for x in loo))
A = plain(sys.argv[1])
print(f"{sys.argv[1]}: {len(A)} places, held G {statistics.mean(A.values()):.4f} (SE {statistics.stdev(A.values()) / len(A) ** 0.5:.4f} over places, {jk(A):.4f} over problems)")
if len(sys.argv) > 2:
    B = plain(sys.argv[2]); d = {k: B[k] - A[k] for k in A if k in B}
    print(f"{sys.argv[2]}: held G {statistics.mean(B.values()):.4f}; second less first {statistics.mean(d.values()):+.4f} (SE {statistics.stdev(d.values()) / len(d) ** 0.5:.4f} over places, {jk(d):.4f} over problems), n {len(d)}")
