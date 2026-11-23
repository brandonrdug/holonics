#!/usr/bin/env -S python3 -I
"""moment_sign.py RUN: a ruler (the lead, November 23): whether an entry's pull keeps its direction over a thousand sections: the first moment m at a lap's saves 1000, 2000, 3000, by block:
the correlation of m between saves, the share of entries whose sign is kept, and that share among the entries whose |m|/(isqrt v + 1)
stands over 0.5 at both."""
import sys, numpy as np
def read(p):
    L = open(p).read().split('\n'); sizes = [len(L[i].split()) for i in (2, 5, 6)]
    return sizes, np.array(L[7].split(), dtype=np.float64), np.array(L[8].split(), dtype=np.float64)
run = sys.argv[1]
s, m1, v1 = read(f'{run}/STATE.1000'); _, m2, v2 = read(f'{run}/STATE.2000'); _, m3, v3 = read(f'{run}/STATE.3000')
out = []; at = 0
for name, n in zip(('material', 'level', 'third'), s):
    sl = slice(at, at + n); at += n
    a, b, c = m1[sl], m2[sl], m3[sl]
    live = (a != 0) & (b != 0) & (c != 0)
    r = lambda x, y: float(np.corrcoef(x[live], y[live])[0, 1])
    keep = lambda x, y: float((np.sign(x[live]) == np.sign(y[live])).mean())
    z1 = np.abs(a) / (np.floor(np.sqrt(v1[sl])) + 1); z2 = np.abs(b) / (np.floor(np.sqrt(v2[sl])) + 1)
    loud = live & (z1 > 0.5) & (z2 > 0.5)
    kl = float((np.sign(a[loud]) == np.sign(b[loud])).mean()) if loud.any() else float('nan')
    out.append(f"{name}: corr12={r(a, b):+.3f} corr23={r(b, c):+.3f} corr13={r(a, c):+.3f} kept12={keep(a, b):.3f} kept23={keep(b, c):.3f} kept_loud12={kl:.3f} (n_loud={int(loud.sum())})")
print('M_SIGN', run.rstrip('/').split('/')[-1], ' | '.join(out))
