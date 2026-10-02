#!/usr/bin/env python3
"""Whether a latched sheet, kept across windows, tells the tree anything (the contact loop record,
section 34).

[measured-diagnostic; exterior] The latched-sheet law `s_(t+1) = sign(a s_t + L_t)` (a tie keeps
`s_t`), its state handed to the tree as the first letter of a bundle tree joined with the cell tree
(`regime_letters.py`'s count face and join; coins of the same width are the control). Two inputs,
each the field's best case:
- `pca`: `L_t` the top principal direction of the cells' counts decayed at `1 - 2^-2` (a readout of
  the last few cells), scaled to unit spread on the development cells; the hold `a` on the ladder
  1/2, 1, 2, 4 in that unit, chosen on the development cells;
- `set/reset`: `L_t = +2` at a set cell, `-2` at a reset cell, `0` otherwise, `a = 1`: the latch
  holds between them. The pair is the one whose state leaves the least empirical conditional entropy
  of the next cell on the development cells, among the 30 most frequent cells there (an exterior
  search, the field's best case).
Arguments: the cut file, its cells, the held-out start. Floating point is a search outside the
machine; each total is the exact dyadic of its float at 24 significant bits.
"""
import math
import random
import sys
from collections import Counter

import numpy as np

from receiver_oracle import exact
from regime_letters import code


def latch(inputs, hold):
    """The state read before cell t, from the inputs at t (each a function of cells before t)."""
    s, out = 1, []
    for value in inputs:
        v = hold * s + value
        if v != 0:
            s = 1 if v > 0 else -1
        out.append(1 if s > 0 else 0)
    return out


def conditional_entropy(cells, states, held):
    joint = Counter(zip(states[:held], cells[:held]))
    marg = Counter(states[:held])
    return -sum(c * math.log2(c / marg[s]) for (s, _), c in joint.items())


def main(path, n, held):
    cells = list(open(path, "rb").read()[:n])
    rng = random.Random(1)
    base = code(cells, None)
    coins = code(cells, [rng.getrandbits(1) for _ in cells])
    print(f"cell tree: development {exact(sum(base[:held]))}, held out {exact(sum(base[held:]))}; "
          f"coins: development {exact(sum(coins[:held]))}, held out {exact(sum(coins[held:]))}", flush=True)
    rho = 1 - 2.0 ** -2
    f = np.zeros(256)
    feats = []
    for x in cells:
        m = f.sum()
        feats.append(f / m if m > 0 else f.copy())
        f *= rho
        f[x] += 1
    F = np.array(feats)
    mean = F[:held].mean(axis=0)
    _, _, vt = np.linalg.svd(F[:held] - mean, full_matrices=False)
    proj = (F - mean) @ vt[0]
    proj = proj / proj[:held].std()
    best = None
    for hold in (0.5, 1.0, 2.0, 4.0):
        states = latch(proj, hold)
        c = code(cells, states)
        print(f"pca latch, hold {hold}: development {exact(sum(c[:held]))}, held out {exact(sum(c[held:]))}", flush=True)
    common = [x for x, _ in Counter(cells[:held]).most_common(30)]
    prev = np.array([-1] + cells[:-1])
    idx = np.arange(len(cells))
    nxt = np.array(cells)
    scored = []
    for a in common:
        last_a = np.maximum.accumulate(np.where(prev == a, idx, -1))
        for b in common:
            if a == b:
                continue
            last_b = np.maximum.accumulate(np.where(prev == b, idx, -1))
            # The latch from s_0 = +1: set by a, reset by b, holding between.
            states = np.where(last_b > last_a, 0, 1)[:held]
            key = states * 256 + nxt[:held]
            counts = np.bincount(key, minlength=512).astype(float)
            marg = np.array([counts[:256].sum(), counts[256:].sum()])
            nz = counts > 0
            h = -sum(counts[i] * math.log2(counts[i] / marg[i // 256]) for i in np.nonzero(nz)[0])
            scored.append((h, a, b))
    scored.sort()
    h, a, b = scored[0]
    inputs = [2 if x == a else (-2 if x == b else 0) for x in [None] + cells[:-1]]
    states = latch(inputs, 1.0)
    c = code(cells, states)
    print(f"set/reset latch (set {a}, reset {b}; development conditional entropy {exact(h)}): "
          f"development {exact(sum(c[:held]))}, held out {exact(sum(c[held:]))}", flush=True)


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
