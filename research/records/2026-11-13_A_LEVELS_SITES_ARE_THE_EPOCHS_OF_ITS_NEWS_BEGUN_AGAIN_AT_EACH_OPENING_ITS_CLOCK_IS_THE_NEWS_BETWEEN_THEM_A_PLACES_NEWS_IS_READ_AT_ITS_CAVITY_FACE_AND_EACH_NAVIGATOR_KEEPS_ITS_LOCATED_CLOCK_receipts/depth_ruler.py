"""depth_ruler: G149's reading of read-depth's rows (a host ruler; numbers only).

usage: python3 -I depth_ruler.py WIDTH DIR [DIR ...]   (each a read-depth output directory: depth.tsv, charts.bin; WIDTH the chart's words)

By stage k (the chart before tick k, the last after the last tick), over every place and by slice: the mean code of the place's class and the
mean expected code of its face, in nats a place; the mean length of each tick's change of chart, |r_k - r_(k-1)|, and the mean cosine of two
successive changes, cos(r_k - r_(k-1), r_(k-1) - r_(k-2)): near +1 a settling that keeps its direction, near -1 a reversal (two loops in
anti-phase), near 0 a turn.
"""
import math
import sys
from collections import defaultdict

import numpy as np

LN2 = math.log(2.0)
NATS = LN2 / float(1 << 20)
width = int(sys.argv[1])
for d in sys.argv[2:]:
    slices, codes, ents = [], [], []
    with open(d + "/depth.tsv") as f:
        head = f.readline().rstrip("\n").split("\t")
        stages = (len(head) - 2) // 2
        for line in f:
            w = line.rstrip("\n").split("\t")
            slices.append(w[0])
            vals = [int(x) for x in w[2:]]
            codes.append(vals[0::2])
            ents.append(vals[1::2])
    codes = np.array(codes, dtype=float) * NATS
    ents = np.array(ents, dtype=float) * NATS
    charts = np.fromfile(d + "/charts.bin", dtype="<i4").astype(float).reshape(len(slices), stages, width)
    delta = np.diff(charts, axis=1)
    norm = np.linalg.norm(delta, axis=2)
    dots = (delta[:, 1:, :] * delta[:, :-1, :]).sum(axis=2)
    denom = norm[:, 1:] * norm[:, :-1]
    cos = np.where(denom > 0, dots / np.where(denom > 0, denom, 1.0), 0.0)
    name = d.rstrip("/").split("/")[-1]
    print("DEPTH %s places=%d stages=%d" % (name, len(slices), stages))
    print("  code_nats " + " ".join("s%d=%.4f" % (k, codes[:, k].mean()) for k in range(stages)))
    print("  entropy_nats " + " ".join("s%d=%.4f" % (k, ents[:, k].mean()) for k in range(stages)))
    print("  change_norm " + " ".join("t%d=%.1f" % (k + 1, norm[:, k].mean()) for k in range(stages - 1)))
    print("  successive_cos " + " ".join("t%d=%.3f" % (k + 2, cos[:, k].mean()) for k in range(stages - 2)))
    best = int(np.argmin(codes.mean(axis=0)))
    print("  minimum stage=%d code=%.4f entropy=%.4f | last stage code over the minimum %.4f, entropy over its own at the minimum %.4f" % (best, codes[:, best].mean(), ents[:, best].mean(), codes[:, -1].mean() - codes[:, best].mean(), ents[:, -1].mean() - ents[:, best].mean()))
    by = defaultdict(list)
    for i, s in enumerate(slices):
        by[s].append(i)
    for s, ix in by.items():
        c = codes[ix].mean(axis=0)
        print("  slice %s places=%d code_by_stage %s" % (s, len(ix), " ".join("%.3f" % v for v in c)))
