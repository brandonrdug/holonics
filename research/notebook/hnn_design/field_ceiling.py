#!/usr/bin/env python3
"""What a clock-free linear field could add to the tree (the contact loop record, section 29).

[measured-diagnostic; exterior] The count face's replica (`tree_estimator.py`'s law, prior mass
2^-3, depth 4) gives each cell's full 256-class face before the cell is read. A clock-free field
would hand the receiver a fixed linear image of the recent passage: here the passage's cells decayed
at 1 - 2^-k a cell, normalized (256 numbers), with no clock in between, the best case of §27's entry
for a linear receiver. The receiver adds W f to the tree's exponents (bits) and learns W online by
R's own law (the class-metric replay of `receiver_combined.py`: W += k (q - p)(X f)^T,
X = (I + sum f f^T)^-1, k = (|A| - 1)/(1 - sum p^2), its step capped at one bit of oscillation on
the reading as the machine's certificate caps it), every cell scored before its update. It prints
the tree alone and the tree with the field on the development and held-out cells. Floating point is
a search outside the machine; each total is the exact dyadic of its float at 24 significant bits.
"""
import math
import sys

import numpy as np

from receiver_oracle import exact

ALPHA = 2.0 ** -3
DEPTH = 4


def full_faces(cells):
    nodes = {}
    out = []
    for j, x in enumerate(cells):
        context = tuple(cells[max(0, j - DEPTH):j][::-1])
        # q(prefix) for every internal digit node, read before the cell's deposit.
        def q_at(prefix):
            path = [nodes.get((prefix, context[:d])) for d in range(len(context) + 1)]
            q = None
            for d in range(len(context), -1, -1):
                node = path[d] or [0, 0, 0.0]
                n0, n1, lb = node
                k0 = (n0 + ALPHA) / (n0 + n1 + 2 * ALPHA)
                if q is None:
                    q = k0
                else:
                    lam = 1 / (1 + math.exp(-lb)) if lb > -700 else 0.0
                    q = lam * k0 + (1 - lam) * q
            return q
        logp = np.zeros(256)
        stack = [(1, 0.0, 0)]
        while stack:
            prefix, acc, level = stack.pop()
            if level == 8:
                logp[prefix - 256] = acc
                continue
            q0 = q_at(prefix)
            stack.append((2 * prefix, acc + math.log2(q0), level + 1))
            stack.append((2 * prefix + 1, acc + math.log2(1 - q0), level + 1))
        out.append(logp)
        # Deposit the cell along its digits (beta' = beta k(b)/q_child(b), then count).
        prefix = 1
        for i in range(7, -1, -1):
            b = (x >> i) & 1
            path = []
            for d in range(len(context) + 1):
                path.append(nodes.setdefault((prefix, context[:d]), [0, 0, 0.0]))
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
            for level, node in enumerate(rev):
                if level > 0:
                    node[2] += math.log(ks[level][b] / qs[level - 1][b])
                node[b] += 1
            prefix = 2 * prefix + b
    return np.array(out)


def main(path, n_star, held):
    cells = list(open(path, "rb").read()[:n_star])
    tree = full_faces(cells)
    alone = np.array([-tree[j, x] for j, x in enumerate(cells)])
    print(f"tree alone: development {exact(alone[:held].sum())}, held out {exact(alone[held:].sum())}", flush=True)
    for k in (2, 4, 6, 8):
        rho = 1 - 2.0 ** -k
        f = np.zeros(256)
        W = np.zeros((256, 256))
        X = np.eye(256)
        codes = []
        for j, x in enumerate(cells):
            mass = f.sum()
            feat = f / mass if mass > 0 else f.copy()
            v = tree[j] + W @ feat
            top = v.max()
            p = np.exp2(v - top)
            p /= p.sum()
            codes.append(-math.log2(p[x]))
            Xf = X @ feat
            X -= np.outer(Xf, Xf) / (1.0 + feat @ Xf)
            g = -p
            g[x] += 1
            kk = 255 / max(1e-12, 1 - (p * p).sum())
            step = kk * g
            # The machine's cap: the move's oscillation on this reading at most one bit
            # (eta max(osc, 1) <= 1, section 19).
            osc = (step.max() - step.min()) * float(feat @ X @ feat)
            eta = 1.0 / max(osc, 1.0)
            W += (eta * step)[:, None] * (X @ feat)[None, :]
            f *= rho
            f[x] += 1
        codes = np.array(codes)
        print(
            f"memory 2^{k} cells: development {exact(codes[:held].sum())}, held out {exact(codes[held:].sum())}",
            flush=True,
        )


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
