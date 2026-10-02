#!/usr/bin/env python3
"""The landmark tree's estimator at contexts seen a few times (the contact loop record, section 25).

[measured-diagnostic; exterior] A reduced replica of the landmark tree's count face
(`compression::landmark::context`): context-tree weighting over the last D = 4 cells, the cell's
eight odometer digits each read in the trees of its dyadic cell, binary masses
k(b) = (n(b) + alpha)/(n + 2 alpha) at each node, the stop weight 1/2 (beta founded at 1,
lambda = beta/(1 + beta), beta' = beta k(b)/q_child(b)), prequential. alpha = 1/2 is the tree's
Krichevsky-Trofimov law; the run reads alpha on the dyadic ladder 2^-j. It omits the executed
tree's lattice, its storage where paths part, its stop mixture per digit tree and its count
ceiling, so it is a yardstick for the estimator's law, not a replica of the machine's numbers.
Arguments: the cut file, n*, the aeons' closing cells (comma-separated). Floating point is a search
outside the machine; each total is reported as the exact dyadic of its float at 24 significant bits.
It also reads the eight masses mixed in each digit tree (each dyadic cell's own weights over the
members, uniform at the start), the stop mixture's form.
"""
import math
import sys

from receiver_oracle import exact

DEPTH = 4
DIGITS = 8


def ctw_codes(cells, alpha, depth=DEPTH):
    nodes = {}
    codes = []
    for j, x in enumerate(cells):
        context = tuple(cells[max(0, j - depth):j][::-1])  # newest first
        bits = 0.0
        prefix = 1
        for i in range(DIGITS - 1, -1, -1):
            b = (x >> i) & 1
            path = []
            for d in range(depth + 1):
                if d > len(context):
                    break
                key = (prefix, context[:d])
                path.append(nodes.setdefault(key, [0, 0, 1.0]))
            # From the deepest node up: q_d = lam k_d + (1 - lam) q_(d+1).
            q = [0.0, 0.0]
            ks = []
            for level, node in enumerate(reversed(path)):
                n0, n1, beta = node
                k = [(n0 + alpha) / (n0 + n1 + 2 * alpha), (n1 + alpha) / (n0 + n1 + 2 * alpha)]
                ks.append(k)
                if level == 0:
                    q = k[:]
                    node_q = [q[:]]
                else:
                    lam = beta / (1 + beta)
                    child = q
                    q = [lam * k[0] + (1 - lam) * child[0], lam * k[1] + (1 - lam) * child[1]]
                    node_q.append(q[:])
            bits -= math.log2(q[b])
            # Deposit bottom-up: beta' = beta k(b)/q_child(b), then count.
            rev = list(reversed(path))
            for level, node in enumerate(rev):
                if level > 0:
                    node[2] *= ks[level][b] / node_q[level - 1][b]
                node[b] += 1
            prefix = 2 * prefix + b
        codes.append(bits)
    return codes


def digit_tree_mixture(cells, alphas, depth=DEPTH):
    """The members' digit faces mixed in each dyadic cell by that cell's own evidence."""
    members = [{} for _ in alphas]
    weights = {}
    codes = []
    for j, x in enumerate(cells):
        context = tuple(cells[max(0, j - depth):j][::-1])
        bits = 0.0
        prefix = 1
        for i in range(DIGITS - 1, -1, -1):
            b = (x >> i) & 1
            reads = []
            for nodes, alpha in zip(members, alphas):
                path = []
                for d in range(depth + 1):
                    if d > len(context):
                        break
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
                reads.append((q, rev, ks, qs))
            lw = weights.setdefault(prefix, [math.log(1 / len(alphas))] * len(alphas))
            top = max(lw)
            w = [math.exp(v - top) for v in lw]
            p = sum(wm * r[0][b] for wm, r in zip(w, reads)) / sum(w)
            bits -= math.log2(p)
            for m, (q, rev, ks, qs) in enumerate(reads):
                lw[m] += math.log(q[b])
                for level, node in enumerate(rev):
                    if level > 0:
                        node[2] += math.log(ks[level][b] / qs[level - 1][b])
                    node[b] += 1
            prefix = 2 * prefix + b
        codes.append(bits)
    return codes


def main(path, n_star, closes):
    cells = list(open(path, "rb").read()[:n_star])
    bounds = [0] + closes + [n_star]
    for j in (1, 2, 3, 4, 5, 6):
        alpha = 2.0 ** -j
        codes = ctw_codes(cells, alpha)
        print(
            f"alpha 2^-{j}: whole {exact(sum(codes))}; by aeon "
            + ", ".join(exact(sum(codes[a:b])) for a, b in zip(bounds, bounds[1:])),
            flush=True,
        )
    codes = digit_tree_mixture(cells, [2.0 ** -j for j in range(1, 9)])
    print(
        f"the eight masses mixed in each digit tree: whole {exact(sum(codes))}; by aeon "
        + ", ".join(exact(sum(codes[a:b])) for a, b in zip(bounds, bounds[1:])),
        flush=True,
    )


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), [int(x) for x in sys.argv[3].split(",")])
