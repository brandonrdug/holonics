#!/usr/bin/env -S python3 -I
"""moment_coherence.py STATE [STATE ...]: a ruler (the lead, November 23): the deposit's moments' coherence, mean |m| / (isqrt(v) + 1) over entries with a second moment, by the
state's three material lines (the constitution's material, the level's, the third block), against the no-direction floor sqrt(2/pi)/sqrt(15)."""
import sys, math
import numpy as np
for path in sys.argv[1:]:
    L = open(path).read().split('\n')
    sizes = [len(L[2].split()), len(L[5].split()), len(L[6].split())]
    m = np.array([float(x) for x in L[7].split()])
    v = np.array([float(x) for x in L[8].split()])
    r = np.abs(m) / (np.floor(np.sqrt(v)) + 1)
    at = 0
    out = []
    for name, n in zip(("material", "level", "third"), sizes):
        sel = slice(at, at + n); at += n
        live = v[sel] > 0
        out.append(f"{name}: n={int(live.sum())} mean={r[sel][live].mean():.4f} rms={np.sqrt((r[sel][live]**2).mean()):.4f} share_over_0.5={(r[sel][live] > 0.5).mean():.4f}")
    live = v > 0
    print(path.split('/')[-2], f"all n={int(live.sum())} mean={r[live].mean():.4f}", " | ".join(out), f"(floor {math.sqrt(2/math.pi)/math.sqrt(15):.4f})")
