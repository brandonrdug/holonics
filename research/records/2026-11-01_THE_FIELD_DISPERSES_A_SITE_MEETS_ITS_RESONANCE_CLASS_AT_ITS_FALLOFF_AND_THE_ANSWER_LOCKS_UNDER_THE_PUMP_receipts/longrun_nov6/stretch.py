#!/usr/bin/env python3
"""The stretch's rate against the far void (the unified-theory reading of November 6, 09:56): from stretch-field's STRETCH.tsv
(each held question's kappa_1 a paced head and tick, on 2^-24) and opening-field's OPENING.tsv of the same state, for each
paced head at the last tick read: kappa_1's mean and spread over the questions, and its correlation across them with each
question's conditioned overrun past 1,200 (sum over places 1,200 past the held end to the room's end of 1 - M(t)/M(R)).

Usage: stretch.py NAME STRETCH_DIR OPENING_DIR [NAME STRETCH_DIR OPENING_DIR ...]
"""
import csv
import statistics
import sys

ONE = 1 << 24
args = sys.argv[1:]
for i in range(0, len(args), 3):
    name, sd, od = args[i : i + 3]
    rows = list(csv.DictReader(open(f"{sd}/STRETCH.tsv"), delimiter="\t"))
    last = max(int(r["tick"]) for r in rows)
    kappa = {}
    for r in rows:
        if int(r["tick"]) == last:
            kappa.setdefault(int(r["head"]), {})[int(r["problem"])] = int(r["kappa"]) / ONE
    problems = {}
    for r in csv.DictReader(open(f"{od}/OPENING.tsv"), delimiter="\t"):
        p = problems.setdefault(int(r["problem"]), {"held": int(r["held"]), "void": []})
        p["void"].append(int(r["void"]))
    over = {}
    for k, p in problems.items():
        run, m = [], 0
        for v in p["void"]:
            m = max(m, v)
            run.append(m)
        top = run[-1] or 1
        lo = p["held"] + 1200
        over[k] = sum(1 - run[t] / top for t in range(lo, len(run))) if lo < len(run) else 0.0
    for head, ks in sorted(kappa.items()):
        common = sorted(set(ks) & set(over))
        xs = [ks[k] for k in common]
        ys = [over[k] for k in common]
        corr = statistics.correlation(xs, ys) if len(xs) > 2 and statistics.pstdev(xs) > 0 and statistics.pstdev(ys) > 0 else float("nan")
        print(f"STRETCH {name} paced={head} tick={last} questions={len(xs)} kappa_mean={statistics.mean(xs):.4f} kappa_sd={statistics.pstdev(xs):.4f} overrun_1200_mean={statistics.mean(ys):.1f} corr={corr:+.3f}")
