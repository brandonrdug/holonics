#!/usr/bin/env -S python3 -I
"""lap_travel.py PREV_RUN RUN [NAME]: a ruler (the lead, November 23): whether the pull a lap's deposit follows comes back, read over the
lap's thousand-section windows. From the whole-word means `WHOLE.k` (the material summed whole at every section of a window), the
displacements d0 = W1000 - PREV's W3000, d1 = W2000 - W1000 and d2 = W3000 - W2000, by block (the constitution's material, the level's,
the third), and their cosines cos(d0, d1), cos(d1, d2), with the persistence |d0 + d1 + d2| / sqrt(|d0|^2 + |d1|^2 + |d2|^2): 1 for a
walk whose steps are unrelated, sqrt(3) = 1.732 for a pull that holds its direction, under 1 for one that turns back. A reading of saved
states on the host (floats at the exterior); the states are read, never written."""
import sys
import numpy as np


def blocks(path):
    L = open(path).read().split('\n')
    return [np.array(L[i].split(), dtype=np.float64) for i in (2, 5, 6)]


prev, run = sys.argv[1], sys.argv[2]
name = sys.argv[3] if len(sys.argv) > 3 else run.rstrip('/').split('/')[-1]
w = [blocks(f"{prev}/WHOLE.3000")] + [blocks(f"{run}/WHOLE.{k}") for k in (1000, 2000, 3000)]
out = []
for b, label in enumerate(("material", "level", "third")):
    d = [w[i + 1][b] - w[i][b] for i in range(3)]
    n = [np.linalg.norm(x) for x in d]
    cos = lambda x, y: float(x @ y / (np.linalg.norm(x) * np.linalg.norm(y) + 1e-300))
    pers = float(np.linalg.norm(d[0] + d[1] + d[2]) / np.sqrt(sum(v * v for v in n)))
    out.append(f"{label}: |d|={n[0]:.4g},{n[1]:.4g},{n[2]:.4g} cos01={cos(d[0], d[1]):+.3f} cos12={cos(d[1], d[2]):+.3f} persistence={pers:.3f}")
print(f"LAP_TRAVEL {name} " + " | ".join(out))
