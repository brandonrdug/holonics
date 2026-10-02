#!/usr/bin/env python3
"""The field as each node's base measure (the contact loop record, §30).

[measured-diagnostic; exterior] The count face's replica at prior mass 2^-3 and depth 16, with each
node's two prior masses `2^(-j)` (the `+1` of `(2^j n_b + 1)/(2^j n + 2)`) split by a base measure
pi instead of evenly: `(2^j n_b + 2 pi_b)/(2^j n + 2)`. The base is the wave's own prediction at the
reading: its exponents `W z` (bits) with `W` the receiving map published at the reading's aeon's
opening close and `z` the reading's anchor (the samples `hnn_exposure ablation ... samples` writes),
softmaxed and split down the digit's dyadic cell. A control gives each reading another reading's
base. Cells of the first aeon (where the published map is zero) and every node keep the even base
where the wave is not read. It prints the code of the aeons after the first, the even base against
the wave's and the control's. Floating point is a search outside the machine; each total is the
exact dyadic of its float at 24 significant bits.
"""
import math
import random
import sys

import numpy as np

from receiver_combined import read
from receiver_oracle import exact

ALPHA = 2.0 ** -3
DEPTH = 16


def digit_bases(p):
    """pi(prefix) = mass of the prefix's lower half over the prefix's mass, for every internal digit node."""
    mass = np.zeros(512)
    mass[256:512] = p
    for node in range(255, 0, -1):
        mass[node] = mass[2 * node] + mass[2 * node + 1]
    out = np.full(256, 0.5)
    for node in range(1, 256):
        if mass[node] > 0:
            out[node] = mass[2 * node] / mass[node]
    return out


def run(cells, bases):
    nodes = {}
    codes = []
    for j, x in enumerate(cells):
        context = tuple(cells[max(0, j - DEPTH):j][::-1])
        base = bases[j]
        bits, prefix = 0.0, 1
        for i in range(7, -1, -1):
            b = (x >> i) & 1
            pi0 = 0.5 if base is None else float(base[prefix])
            pi = [pi0, 1 - pi0]
            path = []
            for d in range(len(context) + 1):
                path.append(nodes.setdefault((prefix, context[:d]), [0, 0, 0.0]))
            rev = list(reversed(path))
            ks, qs = [], []
            for level, node in enumerate(rev):
                n0, n1, lb = node
                k = [(n0 + 2 * ALPHA * pi[0]) / (n0 + n1 + 2 * ALPHA),
                     (n1 + 2 * ALPHA * pi[1]) / (n0 + n1 + 2 * ALPHA)]
                ks.append(k)
                if level == 0:
                    q = k[:]
                else:
                    lam = 1 / (1 + math.exp(-lb)) if lb > -700 else 0.0
                    q = [lam * k[0] + (1 - lam) * q[0], lam * k[1] + (1 - lam) * q[1]]
                qs.append(q[:])
            bits -= math.log2(max(q[b], 1e-300))
            for level, node in enumerate(rev):
                if level > 0:
                    node[2] += math.log(ks[level][b] / qs[level - 1][b])
                node[b] += 1
            prefix = 2 * prefix + b
        codes.append(bits)
    return codes


def main(samples_path, cut_path):
    samples, maps = read(samples_path)
    cut = open(cut_path, "rb").read()
    n = len(samples)
    cells = list(cut[:n])
    assert all(cells[i] == samples[i][1] for i in range(n))
    bases = []
    for aeon, _, z, _ in samples:
        if aeon == 0 or aeon >= len(maps):
            bases.append(None)
            continue
        v = maps[aeon] @ z
        p = np.exp2(v - v.max())
        bases.append(digit_bases(p / p.sum()))
    rng = random.Random(0)
    read_indices = [i for i, b in enumerate(bases) if b is not None]
    shuffled = read_indices[:]
    rng.shuffle(shuffled)
    control = list(bases)
    for i, k in zip(read_indices, shuffled):
        control[i] = bases[k]
    first = min(read_indices) if read_indices else n
    even = run(cells, [None] * n)
    wave = run(cells, bases)
    shuffle = run(cells, control)
    print(f"{n} cells; the wave read from cell {first}")
    for name, codes in [("even base", even), ("the wave's base", wave), ("a shuffled wave's base", shuffle)]:
        print(f"  {name}: after the first aeon {exact(sum(codes[first:]))} bits", flush=True)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
