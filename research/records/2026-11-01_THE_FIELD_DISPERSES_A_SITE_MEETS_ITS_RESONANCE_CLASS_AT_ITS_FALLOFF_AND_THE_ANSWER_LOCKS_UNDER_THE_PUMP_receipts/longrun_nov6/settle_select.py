#!/usr/bin/env python3
"""settle135: theory's settling read (November 7, 04:20). From energy133's central squares, the 55 that are bad at /16 and /8
(per-square curl/readings 2|ri - rj|/(|ri| + |rj|) > 0.5), grow at least 3x from /16 to /4 and stay above 0.5 at /4; of
those, the ones whose linear end (the end that grows more from /16 to /4) reads >= 20 bits raw at /16. Writes their
problem, band, i, j (answer places) and which end is linear. A reading only."""
import csv, sys
rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
B = 1 << 20
def ratio(i, j): return 2 * abs(i - j) / (abs(i) + abs(j)) if abs(i) + abs(j) else 0.0
out = []
for x in rows:
    c = {s: (int(x[f"c{s}_i"]) / B, int(x[f"c{s}_j"]) / B) for s in ("16", "8", "4")}
    if not (ratio(*c["16"]) > 0.5 and ratio(*c["8"]) > 0.5): continue
    size = {s: (abs(c[s][0]) + abs(c[s][1])) / 2 for s in c}
    if not (size["16"] > 0 and size["4"] >= 3 * size["16"] and ratio(*c["4"]) > 0.5): continue
    gi = abs(c["4"][0]) / max(abs(c["16"][0]), 1e-9); gj = abs(c["4"][1]) / max(abs(c["16"][1]), 1e-9)
    end = "i" if gi >= gj else "j"
    lin = c["16"][0] if end == "i" else c["16"][1]
    if abs(lin) >= 20: out.append((x["problem"], x["band"], x["i"], x["j"], end, c))
print("problem\tband\ti\tj\tlinear_end")
for p, b, i, j, e, c in out: print(f"{p}\t{b}\t{i}\t{j}\t{e}")
sys.stderr.write(f"{len(out)} squares\n")
for p, b, i, j, e, c in out:
    sys.stderr.write(f"{p} {b} {i} {j} {e}: i " + " ".join(f"{c[s][0]:.1f}" for s in ("16", "8", "4")) + " | j " + " ".join(f"{c[s][1]:.1f}" for s in ("16", "8", "4")) + "\n")
