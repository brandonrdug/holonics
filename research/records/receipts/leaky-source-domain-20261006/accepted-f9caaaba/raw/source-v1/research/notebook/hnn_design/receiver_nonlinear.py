#!/usr/bin/env python3
"""What the anchors carry beyond the tree under receivers richer than R's form (the contact loop
record, section 23).

[measured-diagnostic; exterior] Reads the samples `hnn_exposure ablation ... samples <path>` writes
(each receiving input z with the tree's exponents after a `|`). For each close k it fits on the
readings of the aeons before k and scores the combined code, bits a reading, on aeon k's readings
(never fitted on):
- the tree alone;
- linear: exponents tree + W z (R's form), ridge 1/256;
- quadratic: tree + W phi(z), phi = (z, the products z_i z_j), standardized on the fitted readings;
- random Fourier: tree + W phi(z), phi = cos(Omega z + b) with 512 features at the median distance;
- each of linear, quadratic and random Fourier also by R's own law in one pass (`-replay`), the features carried at the anchors' root-mean-square
  scale `u` so R's unit prior keeps its units (the products as `z_i z_j / u`);
- nearest anchors: the linear face mixed with the next classes of the 16 nearest fitted anchors,
  p = (1 - lam) p_linear + lam (counts + 1/|A|)/(16 + 1), lam chosen on the last fifth of the
  fitted readings.
Each ridge is chosen from {2^-4, 1, 2^4} (150 descent iterations a fit) on the last fifth of the fitted readings, then refit
on all of them. Floating point is a search outside the machine; each value is reported as the exact
dyadic of its float at 24 significant bits.
"""
import sys

import numpy as np

from receiver_combined import read
from receiver_oracle import exact

RIDGES = [2.0**-4, 1.0, 2.0**4]
ITERATIONS = 150


def softmax2(V):
    top = V.max(axis=1, keepdims=True)
    E = np.exp2(V - top)
    return E / E.sum(axis=1, keepdims=True)


def code_of(P, T):
    return float(np.mean(-np.log2(np.maximum(P[np.arange(len(T)), T], 1e-300))))


def fit(Phi, T0, T, classes, ridge, iterations=ITERATIONS):
    N, n = Phi.shape
    Y = np.zeros((N, classes))
    Y[np.arange(N), T] = 1.0

    def loss_grad(W):
        V = T0 + Phi @ W.T
        top = V.max(axis=1, keepdims=True)
        E = np.exp2(V - top)
        P = E / E.sum(axis=1, keepdims=True)
        log_norm = top[:, 0] + np.log2(E.sum(axis=1))
        loss = (log_norm - V[np.arange(N), T]).mean() + ridge * (W * W).sum() / (2 * N)
        return loss, (P - Y).T @ Phi / N + ridge * W / N

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


def arrays(data):
    Z = np.array([z for _, _, z, _ in data])
    T0 = np.array([tree for _, _, _, tree in data])
    T = np.array([t for _, t, _, _ in data])
    return Z, T0, T


def chosen_fit(features, seen, classes):
    """Choose the ridge on the last fifth of the seen readings, then refit on all of them."""
    Z, T0, T = arrays(seen)
    cut = len(T) * 4 // 5
    Phi = features(Z)
    best = min(
        RIDGES,
        key=lambda r: code_of(
            softmax2(T0[cut:] + Phi[cut:] @ fit(Phi[:cut], T0[:cut], T[:cut], classes, r).T), T[cut:]
        ),
    )
    return fit(Phi, T0, T, classes, best), best


def standardizer(Z, build):
    raw = build(Z)
    mean, scale = raw.mean(axis=0), raw.std(axis=0)
    live = scale > 1e-9 * max(1.0, scale.max())
    return lambda X: (build(X)[:, live] - mean[live]) / scale[live]


def quadratic(X):
    i, j = np.triu_indices(X.shape[1])
    return np.hstack([X, X[:, i] * X[:, j]])


def fourier(Z, count=512, seed=0):
    rng = np.random.default_rng(seed)
    sample = Z[rng.choice(len(Z), size=min(len(Z), 400), replace=False)]
    d = np.sqrt(((sample[:, None, :] - sample[None, :, :]) ** 2).sum(-1))
    width = np.median(d[d > 0]) if (d > 0).any() else 1.0
    Omega = rng.normal(size=(count, Z.shape[1])) / width
    b = rng.uniform(0, 2 * np.pi, size=count)
    return lambda X: np.sqrt(2.0 / count) * np.cos(X @ Omega.T + b)


def neighbours(Zf, Tf, Zq, classes, k=16, exclude_self=False):
    d = ((Zq[:, None, :] - Zf[None, :, :]) ** 2).sum(-1)
    if exclude_self:
        np.fill_diagonal(d, np.inf)
    idx = np.argsort(d, axis=1)[:, :k]
    counts = np.zeros((len(Zq), classes))
    for row, near in enumerate(idx):
        np.add.at(counts[row], Tf[near], 1.0)
    return (counts + 1.0 / classes) / (k + 1.0)


def replay(Phi, T0, T, classes):
    """R's own law on the features, one pass: W += k (q - p)(X phi)^T, X = (I + sum phi phi^T)^-1 by
    Sherman-Morrison, k = (|A| - 1)/(1 - sum p^2) (the class metric, section 19)."""
    n = Phi.shape[1]
    W = np.zeros((classes, n))
    X = np.eye(n)
    for phi, t, tree in zip(Phi, T, T0):
        v = tree + W @ phi
        p = np.exp2(v - v.max())
        p /= p.sum()
        Xphi = X @ phi
        X -= np.outer(Xphi, Xphi) / (1.0 + phi @ Xphi)
        g = -p
        g[t] += 1.0
        k = (classes - 1) / max(1e-12, 1.0 - (p * p).sum())
        W += (k * g)[:, None] * (X @ phi)[None, :]
    return W


def main(path, close, method):
    samples, maps = read(path)
    classes = maps[0].shape[0]
    seen = [s for s in samples if s[0] < close]
    nxt = [s for s in samples if s[0] == close]
    Zs, T0s, Ts = arrays(seen)
    Zn, T0n, Tn = arrays(nxt)
    head = f"close {close}: fitted on {len(Ts)}, scored on the next aeon's {len(Tn)}"
    if method.endswith("-replay"):
        base = method[: -len("-replay")]
        f = {"linear": lambda X: X, "quadratic": standardizer(Zs, quadratic), "fourier": fourier(Zs)}[base]
        # The features carried at the anchors' own scale, so R's unit prior keeps its units.
        unit = np.sqrt((Zs * Zs).mean())
        if base == "linear":
            g = lambda X: X
        elif base == "quadratic":
            # The products divided by the anchors' scale: each feature at the anchors' own scale.
            g = lambda X: quadratic(X) / np.concatenate([np.ones(X.shape[1]), np.full(quadratic(X).shape[1] - X.shape[1], unit)])
        else:
            g = lambda X: unit * f(X)
        W = replay(g(Zs), T0s, Ts, classes)
        print(f"{head}; {method} {exact(code_of(softmax2(T0n + g(Zn) @ W.T), Tn))}", flush=True)
    elif method == "tree":
        print(f"{head}; tree alone {exact(code_of(softmax2(T0n), Tn))}", flush=True)
    elif method == "linear":
        W, r = chosen_fit(lambda X: X, seen, classes)
        print(f"{head}; linear {exact(code_of(softmax2(T0n + Zn @ W.T), Tn))} (ridge {exact(r)})", flush=True)
    elif method in ("quadratic", "fourier"):
        f = standardizer(Zs, quadratic) if method == "quadratic" else fourier(Zs)
        W, r = chosen_fit(f, seen, classes)
        print(f"{head}; {method} {exact(code_of(softmax2(T0n + f(Zn) @ W.T), Tn))} (ridge {exact(r)})", flush=True)
    elif method == "nearest":
        Wl, rl = chosen_fit(lambda X: X, seen, classes)
        Pl = softmax2(T0n + Zn @ Wl.T)
        cut = len(Ts) * 4 // 5
        Wc = fit(Zs[:cut], T0s[:cut], Ts[:cut], classes, rl)
        Pc = softmax2(T0s[cut:] + Zs[cut:] @ Wc.T)
        Kc = neighbours(Zs[:cut], Ts[:cut], Zs[cut:], classes)
        lam = min([0.0, 1 / 16, 1 / 8, 1 / 4, 1 / 2], key=lambda a: code_of((1 - a) * Pc + a * Kc, Ts[cut:]))
        Kn = neighbours(Zs, Ts, Zn, classes)
        print(f"{head}; nearest anchors {exact(code_of((1 - lam) * Pl + lam * Kn, Tn))} (lam {exact(lam)})", flush=True)


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), sys.argv[3])
