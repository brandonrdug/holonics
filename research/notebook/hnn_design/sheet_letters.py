#!/usr/bin/env python3
"""Whether relative-phase sheets of the receiving anchors tell the tree anything (the contact loop
record, section 27).

[measured-diagnostic; exterior] Reads the samples `hnn_exposure ablation ... samples <path>` writes
(sample i is the reading of cell i; its anchor z is formed before cell i is read) and the cut. Each
anchor's eleven complex nodes give ten sheets, node k's side against node 0's axis,
`Re(z_k conj(z_0)) < 0`, which the ring's common rotation leaves fixed. The first r of them form one
letter f_i. Two count faces at prior mass 2^-3 (`tree_estimator.py`'s law): the cell tree over
[x_(i-1), ..., x_(i-4)] and the bundle tree over [f_i, x_(i-1), ..., x_(i-4)], joined in each dyadic
cell by their own evidence from 1/2 each (the enlarged tree's join). A control replaces f_i by the
same number of fair coin bits. It prints the codes over all cells and over the last aeon's (a closing aeon under 512 cells joins
the one before it).
Floating point is a search outside the machine; each total is the exact dyadic of its float at 24
significant bits.
"""
import math
import random
import sys

from receiver_combined import read
from receiver_oracle import exact

ALPHA = 2.0 ** -3


def faces(nodes, prefix, context, alpha):
    path = []
    for d in range(len(context) + 1):
        path.append(nodes.setdefault((prefix, context[:d]), [0, 0, 0.0]))
    rev = list(reversed(path))
    ks, qs = [], []
    for level, node in enumerate(rev):
        n0, n1, lb = node
        k = [(n0 + alpha) / (n0 + n1 + 2 * alpha), (n1 + alpha) / (n0 + n1 + 2 * alpha)]
        ks.append(k)
        if level == 0:
            q = k[:]
        else:
            lam = 1 / (1 + math.exp(-lb)) if lb > -700 else 0.0
            q = [lam * k[0] + (1 - lam) * q[0], lam * k[1] + (1 - lam) * q[1]]
        qs.append(q[:])
    return q, rev, ks, qs


def deposit(read_, b):
    q, rev, ks, qs = read_
    for level, node in enumerate(rev):
        if level > 0:
            node[2] += math.log(ks[level][b] / qs[level - 1][b])
        node[b] += 1


def code(cells, letters):
    cell_tree, bundle_tree, joins = {}, {}, {}
    codes = []
    for j, x in enumerate(cells):
        cells_context = tuple(cells[max(0, j - 4):j][::-1])
        bundle_context = (("f", letters[j]),) + cells_context
        bits, prefix = 0.0, 1
        for i in range(7, -1, -1):
            b = (x >> i) & 1
            a = faces(cell_tree, prefix, cells_context, ALPHA)
            c = faces(bundle_tree, prefix, bundle_context, ALPHA)
            lw = joins.setdefault(prefix, [math.log(0.5), math.log(0.5)])
            top = max(lw)
            w = [math.exp(v - top) for v in lw]
            p = (w[0] * a[0][b] + w[1] * c[0][b]) / (w[0] + w[1])
            bits -= math.log2(p)
            lw[0] += math.log(a[0][b])
            lw[1] += math.log(c[0][b])
            deposit(a, b)
            deposit(c, b)
            prefix = 2 * prefix + b
        codes.append(bits)
    return codes


def cells_only(cells):
    tree, codes = {}, []
    for j, x in enumerate(cells):
        context = tuple(cells[max(0, j - 4):j][::-1])
        bits, prefix = 0.0, 1
        for i in range(7, -1, -1):
            b = (x >> i) & 1
            a = faces(tree, prefix, context, ALPHA)
            bits -= math.log2(a[0][b])
            deposit(a, b)
            prefix = 2 * prefix + b
        codes.append(bits)
    return codes


def main(samples_path, cut_path):
    samples, _ = read(samples_path)
    cut = open(cut_path, "rb").read()
    n = len(samples)
    cells = list(cut[:n])
    assert all(cells[i] == samples[i][1] for i in range(n)), "sample i is the reading of cell i"
    # The last aeon of at least 512 cells (a short closing aeon joins the one before it).
    aeons = sorted({a for a, _, _, _ in samples})
    starts = {a: min(i for i in range(n) if samples[i][0] == a) for a in aeons}
    tail = starts[aeons[-1]]
    if n - tail < 512 and len(aeons) > 1:
        tail = starts[aeons[-2]]
    base = cells_only(cells)
    print(f"{n} cells; the last aeon from cell {tail}")
    print(f"cell tree: all {exact(sum(base))}; last aeon {exact(sum(base[tail:]))}")
    sheets = []
    for _, _, z, _ in samples:
        nodes = [complex(z[2 * k], z[2 * k + 1]) for k in range(len(z) // 2)]
        ref = nodes[0]
        sheets.append([(node * ref.conjugate()).real < 0 for node in nodes[1:]])
    rng = random.Random(0)
    for r in (1, 2, 3, 4):
        letters = [sum(bit << k for k, bit in enumerate(s[:r])) for s in sheets]
        control = [rng.getrandbits(r) for _ in range(n)]
        with_sheets = code(cells, letters)
        with_coins = code(cells, control)
        print(
            f"r = {r}: sheets all {exact(sum(with_sheets))}, last aeon {exact(sum(with_sheets[tail:]))}; "
            f"coins all {exact(sum(with_coins))}, last aeon {exact(sum(with_coins[tail:]))}",
            flush=True,
        )


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
