#!/usr/bin/env python3
"""The one-end draw conditioned on the room (the unified-theory reading of November 6, 07:21): P(L <= t | L <= R) = M(t)/M(R),
M the running maximum of the opening's void mass and R the room's last place. From opening-field's OPENING.tsv, the band split
of the expected overrun past each answer's end, sum over places d = t - held >= 0 of (1 - M(t)/M(R)), beside the plain
profile's sum of (1 - void(t)), over 0-127, 128-511, 512-1199 and 1200 to the room's end. Means over answers, in places.

Usage: conditioned.py OPENING_DIR [OPENING_DIR ...]
"""
import csv
import statistics
import sys

BANDS = ((0, 127), (128, 511), (512, 1199), (1200, None))

for o in sys.argv[1:]:
    problems = {}
    with open(f"{o}/OPENING.tsv") as f:
        for r in csv.DictReader(f, delimiter="\t"):
            p = problems.setdefault(int(r["problem"]), {"held": int(r["held"]), "void": []})
            p["void"].append(int(r["void"]))
    room = len(next(iter(problems.values()))["void"])
    cond = {b: [] for b in BANDS}
    plain = {b: [] for b in BANDS}
    unit = 1 << 20
    for p in problems.values():
        run, m = [], 0
        for v in p["void"]:
            m = max(m, v)
            run.append(m)
        top = run[-1] or 1
        h = p["held"]
        for b in BANDS:
            lo, hi = h + b[0], room - 1 if b[1] is None else min(h + b[1], room - 1)
            cond[b].append(sum(1 - run[t] / top for t in range(lo, hi + 1)) if lo < room else 0.0)
            plain[b].append(sum(1 - p["void"][t] / unit for t in range(lo, hi + 1)) if lo < room else 0.0)
    total = sum(statistics.mean(v) for v in cond.values())
    print(f"CONDITIONED {o.rstrip('/').split('/')[-1]} answers={len(problems)} mean_past_end={total:.1f} plain={sum(statistics.mean(v) for v in plain.values()):.1f}")
    for b in BANDS:
        print(f"  {b[0]}-{b[1] if b[1] is not None else 'end'}\tconditioned {statistics.mean(cond[b]):.1f}\tplain {statistics.mean(plain[b]):.1f}")
