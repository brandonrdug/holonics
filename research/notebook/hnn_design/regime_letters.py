#!/usr/bin/env python3
"""Whether a passage-level state the field could hold tells the tree anything (the contact loop
record, section 33).

[measured-diagnostic; exterior] The strongest form of a field state on text that campaign 1's
library admits (section 33's derivation): signs of linear projections of the passage's decayed
cell counts, with no clock in between. The counts f_t decay at 1 - 2^-k a cell; the projections are
the top r principal directions of f over the development cells (an exterior search, the field's
best case); the state is the r signs about the development mean. The replica's count face (prior
mass 2^-3, the root's base read at grain 1/16, depth 16) codes the cells twice: the cell tree, and a
bundle tree whose first letter is the state, its digit trees' base read from the state's node (the
root switched by state); the two are joined in each dyadic cell by their evidence from 1/2 each. A
control replaces the state by fair coins of the same width. Arguments: the cut file, its cells, the
held-out start. Floating point is a search outside the machine; each total is the exact dyadic of
its float at 24 significant bits.
"""
import math
import random
import sys

import numpy as np

from receiver_oracle import exact

ALPHA = 2.0 ** -3
DEPTH = 16


def base_of(node):
    n0, n1, _ = node
    k0 = (n0 + ALPHA) / (n0 + n1 + 2 * ALPHA)
    p0 = math.floor(((k0 + 0.5) / 2) * 16 + 0.5) / 16
    return [p0, 1 - p0]


def read(nodes, prefix, context, base_level):
    path = [nodes.setdefault((prefix, context[:d]), [0, 0, 0.0]) for d in range(len(context) + 1)]
    pi = base_of(path[min(base_level, len(path) - 1)])
    rev = list(reversed(path))
    ks, qs = [], []
    for level, node in enumerate(rev):
        n0, n1, lb = node
        k = [(n0 + 2 * ALPHA * pi[0]) / (n0 + n1 + 2 * ALPHA), (n1 + 2 * ALPHA * pi[1]) / (n0 + n1 + 2 * ALPHA)]
        ks.append(k)
        if level == 0:
            q = k[:]
        else:
            lam = 1 / (1 + math.exp(-lb)) if lb > -700 else 0.0
            q = [lam * k[0] + (1 - lam) * q[0], lam * k[1] + (1 - lam) * q[1]]
        qs.append(q[:])
    return q, rev, ks, qs


def deposit(r, b):
    q, rev, ks, qs = r
    for level, node in enumerate(rev):
        if level > 0:
            node[2] += math.log(ks[level][b] / qs[level - 1][b])
        node[b] += 1


def code(cells, letters):
    cell_tree, bundle_tree, joins, out = {}, {}, {}, []
    for j, x in enumerate(cells):
        ctx = tuple(cells[max(0, j - DEPTH):j][::-1])
        bctx = (("s", letters[j]),) + ctx if letters is not None else None
        bits, prefix = 0.0, 1
        for i in range(7, -1, -1):
            b = (x >> i) & 1
            a = read(cell_tree, prefix, ctx, 0)
            if bctx is None:
                p = a[0][b]
            else:
                c = read(bundle_tree, prefix, bctx, 1)
                lw = joins.setdefault(prefix, [math.log(0.5), math.log(0.5)])
                top = max(lw)
                w = [math.exp(v - top) for v in lw]
                p = (w[0] * a[0][b] + w[1] * c[0][b]) / (w[0] + w[1])
                lw[0] += math.log(a[0][b])
                lw[1] += math.log(c[0][b])
                deposit(c, b)
            bits -= math.log2(p)
            deposit(a, b)
            prefix = 2 * prefix + b
        out.append(bits)
    return out


def main(path, n, held):
    cells = list(open(path, "rb").read()[:n])
    base = code(cells, None)
    print(f"cell tree: development {exact(sum(base[:held]))}, held out {exact(sum(base[held:]))}", flush=True)
    rng = random.Random(0)
    for k in (6, 8, 10):
        rho = 1 - 2.0 ** -k
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
        for r in (1, 2, 3):
            proj = (F - mean) @ vt[:r].T
            letters = [int(sum(1 << i for i in range(r) if row[i] > 0)) for row in proj]
            coins = [rng.getrandbits(r) for _ in cells]
            s = code(cells, letters)
            c = code(cells, coins)
            print(
                f"memory 2^{k}, r = {r}: state development {exact(sum(s[:held]))}, held out {exact(sum(s[held:]))}; "
                f"coins development {exact(sum(c[:held]))}, held out {exact(sum(c[held:]))}",
                flush=True,
            )


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
