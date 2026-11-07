#!/usr/bin/env python3
"""The held code at T·2^(j/4), j = −8…8 (theory, November 7, 16:56): from a contrast-field run's ENUMERATED.tsv, the enumerated
conditional P(c | rest) ∝ 2^(−G_c / T′) renormalized at each T′ = T·2^(j/4) from the same G reads, its code −ln P(truth | rest)
a place in nats (each codec letter is one byte), with the paired change against j = 0 and its standard error. A reading only."""
import csv, math, statistics, sys
rows = [r for r in csv.DictReader(open(sys.argv[1]), delimiter="\t") if int(r["lap"]) == int(sys.argv[2])]
def code(r, j):
    t = 2.0 ** (int(r["log2_t"]) / 2 ** 24 + j / 4)
    g = [int(v) / 2 ** 32 for v in r["energies"].split(",")]
    lo = min(g)
    w = [2.0 ** (-(x - lo) / t) for x in g]
    return -math.log(w[int(r["truth"])] / sum(w))
base = [code(r, 0) for r in rows]
print(f"# {sys.argv[1].split('/run/')[-1]} lap {sys.argv[2]}: {len(rows)} places, log2 T = {int(rows[0]['log2_t']) / 2 ** 24:.3f}")
print("j\tlog2_T\tcode_nats_a_byte\tchange\tse")
best = None
for j in range(-8, 9):
    c = [code(r, j) for r in rows]
    d = [a - b for a, b in zip(c, base)]
    m = statistics.mean(c)
    se = statistics.stdev(d) / len(d) ** 0.5 if j else 0.0
    best = min(best or (m, j), (m, j))
    print(f"{j}\t{int(rows[0]['log2_t']) / 2 ** 24 + j / 4:.3f}\t{m:.4f}\t{statistics.mean(d):+.4f}\t{se:.4f}")
print(f"# best {best[0]:.4f} at j = {best[1]} ({best[1] / 4:+.2f} bits of T)")
