#!/usr/bin/env python3
"""The opening's lean against the question-blind length law (§16.47), from opening-field's OPENING.tsv and LENGTHS.tsv.

Usage: lean.py OPENING_DIR

The opening's expected length is the sum of (1 - void mass) over its places; the law's is the training answers' mean
length. Printed: each one's mean less the held length, and the same by thirds of the held length, with the correlation of
the opening's length with held. Masses on 2^-20. Reading only; nothing here is a text.
"""
import csv, statistics, sys
U = 1 << 20
o = sys.argv[1]
lengths = {}
for r in csv.DictReader(open(f"{o}/LENGTHS.tsv"), delimiter="\t"):
    lengths[int(r["length"])] = int(r["answers"])
tot = sum(lengths.values())
probs = {}
for r in csv.DictReader(open(f"{o}/OPENING.tsv"), delimiter="\t"):
    p = probs.setdefault(int(r["problem"]), {"held": int(r["held"]), "v": []})
    p["v"].append(int(r["void"]) / U)
el = sum(l * n for l, n in lengths.items()) / tot
rows = sorted((p["held"], sum(1 - v for v in p["v"]) - p["held"]) for p in probs.values())
print(f"law E[L] {el:.1f}; mean held {statistics.mean(h for h,_ in rows):.1f}; law lead {el - statistics.mean(h for h,_ in rows):+.1f}; opening lead {statistics.mean(x for _,x in rows):+.1f}")
n = len(rows)
for i, name in enumerate(("short", "middle", "long")):
    part = rows[i * n // 3:(i + 1) * n // 3]
    hs = [h for h, _ in part]; xs = [x for _, x in part]
    print(f"{name} third: held {min(hs)}-{max(hs)} mean {statistics.mean(hs):.0f}; opening lead {statistics.mean(xs):+.1f}; law lead {el - statistics.mean(hs):+.1f}; opening length {statistics.mean(h + x for h, x in part):.0f}")
print(f"correlation of opening length with held: {statistics.correlation([h for h,_ in rows], [h + x for h, x in rows]):+.3f}")
