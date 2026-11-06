#!/usr/bin/env python3
"""Each refine pass's drive (the unified-theory reading of November 6, 17:38): PASSES.tsv summed over the answers.

Usage: passes.py SAMPLE_DIR [SAMPLE_DIR ...]

Per pass: the answers redrawn, the places, and a place's mean standing code S, face entropy H, drive D = S - H and spread
sqrt(C / n) (bits), the changes a place against K a place (the changes a walk at equilibrium keeps), and how many answers
had D <= sqrt C. Then each answer's first pass with D <= sqrt C or a fall of D within sqrt C (the rest law). A reading only.
"""
import csv, collections, math, sys

B = 1 << 20
for d in sys.argv[1:]:
    rows = list(csv.DictReader(open(f"{d}/PASSES.tsv"), delimiter="\t"))
    by = collections.defaultdict(list)
    for r in rows:
        by[int(r["pass"])].append(r)
    print(f"PASSES {d.rstrip('/').split('/')[-1]}")
    print("pass\tanswers\tplaces\tS\tH\tD\tsqrtC/n\tchanges\tK\twithin")
    for p, rs in sorted(by.items()):
        n = sum(int(r["redrawn"]) for r in rs)
        S = sum(int(r["standing"]) for r in rs) / B
        H = sum(int(r["entropy"]) for r in rs) / B
        C = sum(int(r["varentropy"]) for r in rs) / B / B
        ch = sum(int(r["changes"]) for r in rs)
        K = sum(int(r["equilibrium"]) for r in rs) / B
        within = sum(1 for r in rs if int(r["drive"]) <= 0 or int(r["drive"]) ** 2 <= int(r["varentropy"]))
        print(f"{p}\t{len(rs)}\t{n}\t{S/n:.3f}\t{H/n:.3f}\t{(S-H)/n:+.3f}\t{math.sqrt(C)/n:.3f}\t{ch/n:.3f}\t{K/n:.3f}\t{within}")
    per = collections.defaultdict(dict)
    for r in rows:
        per[int(r["problem"])][int(r["pass"])] = (int(r["drive"]), int(r["varentropy"]))
    stops = collections.Counter()
    for k, t in per.items():
        stop = None
        for p in sorted(t):
            dd, c = t[p]
            ok = lambda x: x <= 0 or x * x <= c
            if ok(dd) or (p - 1 in t and ok(t[p - 1][0] - dd)):
                stop = p
                break
        stops[stop] += 1
    print("rest pass (None: never)", sorted(stops.items(), key=lambda x: (x[0] is None, x[0] or 0)))
