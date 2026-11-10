#!/usr/bin/env python3
"""energy133: central squares at one base (theory, November 7 03:22): per band and step (a letter's weight over 16, 8, 4),
the curl/readings (sum |ri - rj| over sum (|ri| + |rj|), times two) and the per-square median, and the readings' growth per
doubling of the step. Pass: curl/readings <= 0.1 at a step whose readings double per doubling within 10%. A reading only."""
import csv, statistics, sys
rows = list(csv.DictReader(open(f"{sys.argv[1]}/CURL.tsv"), delimiter="\t"))
NAMES = ["1", "2-3", "4-7", "8-15", "16+"]
print("band\tsquares\t/16: curl/readings median\t/8: curl/readings median\t/4: curl/readings median\treadings /8 over /16\t/4 over /8")
for b, name in enumerate(NAMES):
    r = [x for x in rows if int(x["band"]) == b]
    if len(r) < 3:
        continue
    cells = []
    sizes = []
    for s in ("16", "8", "4"):
        pairs = [(int(x[f"c{s}_i"]), int(x[f"c{s}_j"])) for x in r]
        c = sum(abs(i - j) for i, j in pairs); z = sum(abs(i) + abs(j) for i, j in pairs)
        per = sorted(2 * abs(i - j) / (abs(i) + abs(j)) for i, j in pairs if abs(i) + abs(j) > 0)
        cells.append(f"{2 * c / z if z else float('nan'):.3f} {per[len(per) // 2]:.3f}")
        sizes.append(z)
    print(f"{name}\t{len(r)}\t" + "\t".join(cells) + f"\t{sizes[1] / sizes[0]:.2f}\t{sizes[2] / sizes[1]:.2f}")
