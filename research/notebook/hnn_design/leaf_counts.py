#!/usr/bin/env python3
"""Where the tree's remaining code sits, by the coding leaf's count (the contact loop record, §30).

[measured-diagnostic; exterior] The count face's replica (`tree_estimator.py`'s law) at prior mass
2^-3 and depth 16. At each digit, the leaf is the deepest node on the opened path that has counts
before the digit is read; its count n buckets the digit's code: 0 (a digit tree never opened at
this prefix), 1, 2-3, 4-7, 8-15, 16-63, 64 and more. It prints, per bucket, the digits and their
code on the development and held-out cells, and the share of each. Floating point is a search
outside the machine; each total is the exact dyadic of its float at 24 significant bits.
"""
import math
import sys

from receiver_oracle import exact

ALPHA = 2.0 ** -3
DEPTH = 16
BUCKETS = [(0, 0), (1, 1), (2, 3), (4, 7), (8, 15), (16, 63), (64, 1 << 62)]


def bucket(n):
    return next(i for i, (lo, hi) in enumerate(BUCKETS) if lo <= n <= hi)


def run(cells, held):
    nodes = {}
    sums = [[0.0, 0, 0.0, 0] for _ in BUCKETS]
    for j, x in enumerate(cells):
        context = tuple(cells[max(0, j - DEPTH):j][::-1])
        prefix = 1
        for i in range(7, -1, -1):
            b = (x >> i) & 1
            path = []
            for d in range(len(context) + 1):
                path.append(nodes.setdefault((prefix, context[:d]), [0, 0, 0.0]))
            leaf = max((node for node in path if node[0] + node[1] > 0), key=lambda node: path.index(node), default=None)
            n = 0 if leaf is None else leaf[0] + leaf[1]
            rev = list(reversed(path))
            ks, qs = [], []
            for level, node in enumerate(rev):
                n0, n1, lb = node
                k = [(n0 + ALPHA) / (n0 + n1 + 2 * ALPHA), (n1 + ALPHA) / (n0 + n1 + 2 * ALPHA)]
                ks.append(k)
                if level == 0:
                    q = k[:]
                else:
                    lam = 1 / (1 + math.exp(-lb)) if lb > -700 else 0.0
                    q = [lam * k[0] + (1 - lam) * q[0], lam * k[1] + (1 - lam) * q[1]]
                qs.append(q[:])
            bits = -math.log2(q[b])
            s = sums[bucket(n)]
            if j < held:
                s[0] += bits
                s[1] += 1
            else:
                s[2] += bits
                s[3] += 1
            for level, node in enumerate(rev):
                if level > 0:
                    node[2] += math.log(ks[level][b] / qs[level - 1][b])
                node[b] += 1
            prefix = 2 * prefix + b
    return sums


def main(path, n_star, held):
    cells = list(open(path, "rb").read()[:n_star])
    sums = run(cells, held)
    dev = sum(s[0] for s in sums)
    hold = sum(s[2] for s in sums)
    print(f"development {exact(dev)} bits, held out {exact(hold)} bits")
    for (lo, hi), s in zip(BUCKETS, sums):
        label = f"{lo}" if lo == hi else (f"{lo}-{hi}" if hi < (1 << 62) else f"{lo}+")
        print(
            f"  leaf count {label}: development {s[1]} digits, {exact(s[0])} bits (share {exact(s[0] / dev)}); "
            f"held out {s[3]} digits, {exact(s[2])} bits (share {exact(s[2] / hold)})"
        )


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
