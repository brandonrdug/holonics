#!/usr/bin/env python3
"""The word tree's floor against the per-receiver floor at each head's, tick's and octave's own jitter (the theory thread, 19:20Z).

tree_at_jitter.py TREE_LOG JITTER_LOG: from OPEN_CROWDS_GRAINS (pairs, cover and tree terms at grains 2^-6..2^2 bits by octave, by slice, head
and tick) and FAR_JITTER (the median |z_end - z_mean| by head, tick and octave, a bin's upper edge), the sums over slices and octaves of the
terms at the octave's own grain, read at the jitter bin's lower edge and at its upper edge, and the shared tree's terms over the per-receiver
cover's (the guess's ratio)."""
import math, re, sys
from collections import defaultdict

tree_log, jitter_log = sys.argv[1], sys.argv[2]
LEAST = -6  # grain index 0 is 2^-6 bits
jit = {}
for line in open(jitter_log):
    if not line.startswith('FAR_JITTER '):
        continue
    h = int(re.search(r' head=(\d+)', line).group(1)); k = int(re.search(r' tick=(\d+)', line).group(1))
    for o, med in re.findall(r' o(\d+):[0-9.]+/([0-9.]+)/[0-9.]+', line):
        jit[(h, k, int(o))] = float(med)
acc = defaultdict(lambda: [0, 0, 0, 0, 0])  # pairs, cover_lo, tree_lo, cover_hi, tree_hi
kinds = {}
for line in open(tree_log):
    if not line.startswith('OPEN_CROWDS_GRAINS '):
        continue
    h = int(re.search(r' head=(\d+)', line).group(1)); k = int(re.search(r' tick=(\d+)', line).group(1))
    kinds[h] = re.search(r' kind=(\w+)', line).group(1)
    for o, pairs, cov, tre in re.findall(r' o(\d+):(\d+):([\d,]+):([\d,]+)', line):
        o, pairs = int(o), int(pairs)
        cov = list(map(int, cov.split(','))); tre = list(map(int, tre.split(',')))
        med = jit.get((h, k, o))
        if med is None:
            continue
        hi = int(round(math.log2(med))) - LEAST          # the bin's upper edge
        lo = hi - 1                                       # its lower edge
        clamp = lambda g: max(0, min(len(cov) - 1, g))
        a = acc[(h, k)]
        a[0] += pairs; a[1] += cov[clamp(lo)]; a[2] += tre[clamp(lo)]; a[3] += cov[clamp(hi)]; a[4] += tre[clamp(hi)]
for (h, k), (p, cl, tl, ch, th) in sorted(acc.items()):
    print("TREE_AT_JITTER head=%d kind=%s tick=%d far_pairs=%d lower_edge: cover=%.4f tree=%.4f ratio=%.3f  upper_edge: cover=%.4f tree=%.4f ratio=%.3f"
          % (h, kinds[h], k, p, cl / p, tl / p, tl / max(cl, 1), ch / p, th / p, th / max(ch, 1)))
