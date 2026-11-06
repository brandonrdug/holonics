#!/usr/bin/env python3
"""The opening's overrun past each answer's end, split by distance (the unified-theory reading of November 6, 06:50, F).

Usage: overrun.py OPENING_DIR [OPENING_DIR ...]

From opening-field's OPENING.tsv and LENGTHS.tsv: for each answer, its letter mass (1 - void mass) at the places at distance
d = place - held from its end (d = 0 the first void place), summed over the bands 0-127, 128-511, 512-1199 and 1200 to the
room's end, beside the question-blind length law's mass in the same band (the share of training answers longer than the
place). Means over the set's answers, in places, and the share of the total in each band. Masses on 2^-20. A reading only.
"""
import csv
import statistics
import sys

UNIT = 1 << 20
BANDS = ((0, 127), (128, 511), (512, 1199), (1200, None))


def read(o):
    lengths = {}
    with open(f"{o}/LENGTHS.tsv") as f:
        for r in csv.DictReader(f, delimiter="\t"):
            lengths[int(r["length"])] = int(r["answers"])
    problems = {}
    with open(f"{o}/OPENING.tsv") as f:
        for r in csv.DictReader(f, delimiter="\t"):
            p = problems.setdefault(int(r["problem"]), {"held": int(r["held"]), "void": []})
            p["void"].append(int(r["void"]) / UNIT)
    return lengths, problems


def main():
    for o in sys.argv[1:]:
        lengths, problems = read(o)
        total = sum(lengths.values())
        room = len(next(iter(problems.values()))["void"])
        share, run = [], 0
        for j in range(room):
            run += lengths.get(j, 0)
            share.append(run / total)
        sums = {b: [] for b in BANDS}
        laws = {b: [] for b in BANDS}
        for p in problems.values():
            h = p["held"]
            for b in BANDS:
                lo, hi = h + b[0], room - 1 if b[1] is None else min(h + b[1], room - 1)
                sums[b].append(sum(1 - v for v in p["void"][lo : hi + 1]) if lo < room else 0.0)
                laws[b].append(sum(1 - s for s in share[lo : hi + 1]) if lo < room else 0.0)
        whole = sum(statistics.mean(v) for v in sums.values())
        print(f"OVERRUN {o.rstrip('/').split('/')[-1]} answers={len(problems)} room={room} mean_past_end={whole:.1f}")
        for b in BANDS:
            name = f"{b[0]}-{b[1] if b[1] is not None else 'end'}"
            m = statistics.mean(sums[b])
            print(f"  {name}\tmean {m:.1f}\tshare {m / whole if whole else 0:.3f}\tmedian {statistics.median(sums[b]):.1f}\tlength_law {statistics.mean(laws[b]):.1f}")


if __name__ == "__main__":
    main()
