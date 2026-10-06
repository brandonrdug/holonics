#!/usr/bin/env python3
"""The receiver on its own objective, the combined face (the contact loop record, section 21).

[measured-diagnostic; exterior] Reads the samples `hnn_exposure ablation ... samples <path>` writes
with the tree's exponents beside each receiving input (after a `|`), and the receiving map R at
each close. The combined face's exponents are v = tree + W z in bits, p_c = 2^(v_c)/sum 2^(v_d).
For each close k it reports, on the next aeon's readings (never fitted on):
- the tree alone (W = 0);
- the machine's R at close k (the map it published, frozen);
- a fitted receiver: W minimizing the combined code over the readings R had seen, with ridge
  `ridge * |W|^2 / 2` (argument 2, default 1/256);
- an online replay of the class-metric law on the combined face, one pass over the same readings:
  W += k (q - p)(X z)^T, X = (I + sum z z^T)^-1, k = (|A| - 1)/(1 - sum p^2), p the combined face's own
  masses (its own gradient and curvature, not an odometer chart).
Floating point is a search outside the machine; each value is the exact dyadic of its float at 24
significant bits.
"""
import sys
from fractions import Fraction

import numpy as np

from receiver_oracle import exact


def read(path):
    samples, maps = [], []
    with open(path) as handle:
        for line in handle:
            parts = line.split()
            if parts[0] == "sample":
                if "|" not in parts:
                    continue
                cut = parts.index("|")
                z = np.array([float(Fraction(x)) for x in parts[3:cut]])
                tree = np.array([float(Fraction(x)) for x in parts[cut + 1:]])
                samples.append((int(parts[1]), int(parts[2]), z, tree))
            elif parts[0] == "map":
                rows, cols = int(parts[2]), int(parts[3])
                maps.append(np.array([float(Fraction(x)) for x in parts[4:]]).reshape(rows, cols)[0::2, :])
    return samples, maps


def code(W, data):
    out = []
    for _, t, z, tree in data:
        v = tree + W @ z
        top = v.max()
        out.append(top + np.log2(np.exp2(v - top).sum()) - v[t])
    return float(np.mean(out))


def fit(data, classes, n, ridge, iterations=1000):
    Z = np.array([z for _, _, z, _ in data])
    T0 = np.array([tree for _, _, _, tree in data])
    T = np.array([t for _, t, _, _ in data])
    N = len(T)
    Y = np.zeros((N, classes))
    Y[np.arange(N), T] = 1.0

    def loss_grad(W):
        V = T0 + Z @ W.T
        top = V.max(axis=1, keepdims=True)
        E = np.exp2(V - top)
        P = E / E.sum(axis=1, keepdims=True)
        log_norm = top[:, 0] + np.log2(E.sum(axis=1))
        loss = (log_norm - V[np.arange(N), T]).mean() + ridge * (W * W).sum() / (2 * N)
        return loss, (P - Y).T @ Z / N + ridge * W / N

    W = np.zeros((classes, n))
    step = 1.0
    loss, grad = loss_grad(W)
    for _ in range(iterations):
        while True:
            trial = W - step * grad
            trial_loss, trial_grad = loss_grad(trial)
            if trial_loss <= loss - 0.5 * step * (grad * grad).sum() or step < 1e-12:
                break
            step /= 2
        W, loss, grad = trial, trial_loss, trial_grad
        step *= 2
    return W


def replay(data, classes, n):
    W = np.zeros((classes, n))
    H = np.eye(n)
    for _, t, z, tree in data:
        v = tree + W @ z
        p = np.exp2(v - v.max())
        p /= p.sum()
        H += np.outer(z, z)
        X = np.linalg.inv(H)
        g = -p.copy()
        g[t] += 1
        k = (classes - 1) / max(1e-12, 1 - (p * p).sum())
        W += (k * g)[:, None] * (X @ z)[None, :]
    return W


def main(path, ridge):
    samples, maps = read(path)
    classes, n = maps[0].shape
    for close in range(1, len(maps)):
        seen = [s for s in samples if s[0] < close]
        nxt = [s for s in samples if s[0] == close]
        if not nxt:
            continue
        tree = code(np.zeros((classes, n)), nxt)
        machine = code(maps[close], nxt)
        fitted = code(fit(seen, classes, n, ridge), nxt)
        replayed = code(replay(seen, classes, n), nxt)
        print(
            f"close {close}: next aeon's {len(nxt)} readings, combined code in bits a reading: tree alone {exact(tree)}, "
            f"R in the machine {exact(machine)}, fitted (ridge {exact(ridge)}) {exact(fitted)}, class-metric replay {exact(replayed)}",
            flush=True,
        )


if __name__ == "__main__":
    main(sys.argv[1], float(Fraction(sys.argv[2])) if len(sys.argv) > 2 else 1 / 256)
