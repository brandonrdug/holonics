#!/usr/bin/env python3
"""The fitted receiver beside the machine's own (the contact loop record, section 17).

[measured-diagnostic; exterior] Reads the samples `hnn_exposure ablation ... samples <path>` writes:
each refined phase's receiving input z (the rotated anchor the receiving map R reads), its target
class and its aeon; and R at each aeon close (the opening's first). For each close k it fits, outside
the machine, the cross-entropy-optimal receiver of R's own form, exponents v = W z in bits with
p_c = 2^(v_c) / sum_d 2^(v_d), on the same readings R had seen by that close (aeons 0..k-1), with
the ridge ridge*sum(W^2)/2 (default 1, R's normal law's unit prior; argument 2 sets it, argument 3
the iterations). It then reads both W and R_k
(R's even rows, the classes' exponents) on those readings and on the next aeon's.

The fit runs in floating point: it is a search outside the machine, not a law. Every value it
reports is the exact dyadic rational of the float it computed, at 24 significant bits.
"""
import sys
from fractions import Fraction

import numpy as np


def exact(x):
    """A float's exact dyadic value at 24 significant bits, as p/2^k."""
    f = Fraction(float(x))
    if f == 0:
        return "0"
    sign = "-" if f < 0 else ""
    f = abs(f)
    k = 0
    while f < 2**23:
        f *= 2
        k += 1
    while f >= 2**24:
        f /= 2
        k -= 1
    p = int(f)
    return f"{sign}{p}/2^{k}" if k >= 0 else f"{sign}{p * 2**(-k)}"


def read(path):
    samples, maps = [], []
    with open(path) as handle:
        for line in handle:
            parts = line.split()
            if parts[0] == "sample":
                samples.append((int(parts[1]), int(parts[2]), [float(Fraction(x)) for x in parts[3:]]))
            elif parts[0] == "map":
                rows, cols = int(parts[2]), int(parts[3])
                entries = [float(Fraction(x)) for x in parts[4:]]
                maps.append(np.array(entries).reshape(rows, cols))
    return samples, maps


def code_and_span(W, Z, T):
    """Mean code in bits and the largest exponent span over the readings."""
    V = Z @ W.T
    top = V.max(axis=1, keepdims=True)
    log_norm = top[:, 0] + np.log2(np.exp2(V - top).sum(axis=1))
    code = (log_norm - V[np.arange(len(T)), T]).mean()
    span = (V.max(axis=1) - V.min(axis=1)).max()
    return code, span


def fit(Z, T, classes, iterations=400, ridge=1.0):
    """Full-batch gradient descent on the mean cross-entropy (bits) plus ridge/(2N), with a
    backtracking step: the search, outside the machine."""
    n = Z.shape[1]
    W = np.zeros((classes, n))
    N = len(T)
    Y = np.zeros((N, classes))
    Y[np.arange(N), T] = 1.0

    def loss_grad(W):
        V = Z @ W.T
        top = V.max(axis=1, keepdims=True)
        E = np.exp2(V - top)
        P = E / E.sum(axis=1, keepdims=True)
        log_norm = top[:, 0] + np.log2(E.sum(axis=1))
        loss = (log_norm - V[np.arange(N), T]).mean() + ridge * (W * W).sum() / (2 * N)
        grad = (P - Y).T @ Z / N + ridge * W / N
        return loss, grad

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


def main(path, ridge=1.0, iterations=400):
    samples, maps = read(path)
    aeons = max(a for a, _, _ in samples) + 1
    classes = maps[0].shape[0] // 2
    for close in range(1, len(maps)):
        seen = [(t, z) for a, t, z in samples if a < close]
        nxt = [(t, z) for a, t, z in samples if a == close]
        Z = np.array([z for _, z in seen])
        T = np.array([t for t, _ in seen])
        R = maps[close][0::2, :]
        W = fit(Z, T, classes, iterations, ridge)
        r_code, r_span = code_and_span(R, Z, T)
        w_code, w_span = code_and_span(W, Z, T)
        line = (
            f"close {close}: {len(T)} readings seen; R: mean code {exact(r_code)} bits, span {exact(r_span)} bits; "
            f"fitted: mean code {exact(w_code)} bits, span {exact(w_span)} bits"
        )
        if nxt:
            Zn = np.array([z for _, z in nxt])
            Tn = np.array([t for t, _ in nxt])
            rn, _ = code_and_span(R, Zn, Tn)
            wn, _ = code_and_span(W, Zn, Tn)
            line += f"; on the next aeon's {len(Tn)} readings: R {exact(rn)} bits, fitted {exact(wn)} bits"
        print(line, flush=True)


if __name__ == "__main__":
    ridge = float(Fraction(sys.argv[2])) if len(sys.argv) > 2 else 1.0
    iterations = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    main(sys.argv[1], ridge, iterations)
