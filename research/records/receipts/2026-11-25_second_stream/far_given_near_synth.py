#!/usr/bin/env -S python3 -I
"""A planted control for `far_given_near_ruler.py envelope2`: a slice of twenty synthetic documents of 60,000 samples each, a
two-pole resonance driven by noise and charted in thirteen levels, in the slice's own files (CHART_t.tsv, HELD_t.tsv, HELD_t.bin).

    far_given_near_synth.py OUT slow|steady

`slow` scales the drive by a gain that holds for 200 to 600 samples and then jumps among 0.15, 0.4 and 1.0, so the loudness some
samples back tells of the spread of the next sample beyond what the last few samples tell; `steady` holds the gain at 0.4, so it
tells nothing more. The ruler should read a far loudness's gain over a near one on `slow` and none on `steady`.
"""
import os
import sys

import numpy as np

out, slow = sys.argv[1], sys.argv[2] == "slow"
os.makedirs(out, exist_ok=True)
rng = np.random.default_rng(7)
k, docs, n = 13, 20, 60000
a1, a2 = 1.6, -0.8
with open(f"{out}/CHART_t.tsv", "w") as f:
    f.write("level\toctet\tlow\thigh\tcount\n")
    for l in range(k):
        f.write(f"{l}\t{192 + l}\t0\t0\t0\n")
with open(f"{out}/HELD_t.tsv", "w") as f, open(f"{out}/HELD_t.bin", "wb") as b:
    f.write("document\ttitle_octets\ttext_octets\topens\tcloses\n")
    for d in range(docs):
        x = np.zeros(n)
        e = rng.standard_normal(n)
        if slow:
            seg = rng.integers(200, 600, size=n // 200 + 2)
            g = np.repeat(rng.choice([0.15, 0.4, 1.0], size=len(seg)), seg)[:n]
        else:
            g = np.full(n, 0.4)
        for t in range(2, n):
            x[t] = a1 * x[t - 1] + a2 * x[t - 2] + g[t] * e[t]
        q = np.clip(np.round(x / 0.6) + 6, 0, k - 1).astype(np.uint8)
        b.write((192 + q).astype(np.uint8).tobytes())
        f.write(f"{d}\t0\t{n}\t1\t1\n")
