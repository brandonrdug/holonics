#!/usr/bin/env python3
"""The receiving map's prior scale against its anchors (the receiving-prior record).

[measured-diagnostic; exterior] Reads the samples `hnn_exposure ablation ... samples <path>` writes
(each receiving input z with the landmark tree's exponents beside it) and

1. reads the anchors' energies: the mean of |z|^2 / n and the largest |z|^2, against the prior
   `H_0 = I`'s unit;
2. replays the receiving map's executed law on the combined face, prequentially (each reading
   scored before its window's deposit), at the priors `H_0 = s I`, `s = 2^k`:
   H' = H + sum_w z z^T, D = kappa sum_w g (H'^-1 z)^T, g = q - p, kappa the power of two at or
   below the window's inverse mean class Fisher eigenvalue; the step eta is the largest power of
   two with eta * C <= a and eta * max(osc, 1) <= 1, a = sum_w <g, D z>,
   C = sum_w (119/80) Var_p(D z), osc = max_w (max D z - min D z); W += eta D;
3. reads, at each prior, the prequential certificate: before each reading's deposit, the map's move
   on it `delta_t = W_t z_t`, its alignment `a_pre = sum_t <g_t, delta_t>` (`g_t` the combined
   face's `q - p`) and its curvature `V = ln 2 sum_t Var_p(delta_t)`. Scaling the map by `phi`
   changes the prequential code by `-phi a_pre + phi^2 V/2 + ...` about the map, so the code's
   Newton point is `phi = 1 + a_pre/V`, and since the map is `1/s` times its unit in the prior's
   regime, the located prior is `s/phi`;
4. reads the same law at the opening (`s` above every reading, the map `M_t/s` with
   `M_t = sum_(u<t) kappa_u g_u z_u^T` read at the tree face): `s_open = ln 2 sum_t Var_p(M_t z_t)
   / sum_t <g_t, M_t z_t>`.

The replay keeps the anchors as the machine produced them (its other loci are not replayed) and
reads the magnitude rows only. Its prequential code over every reading is the code the prior's
scale is judged by. Floating point is a search outside the machine; each reported value is the
exact dyadic of its float at 24 significant bits.
"""
import sys
from fractions import Fraction

import numpy as np

from receiver_oracle import exact


def read(path):
    samples = []
    with open(path) as handle:
        for line in handle:
            parts = line.split()
            if parts[0] != "sample" or "|" not in parts:
                continue
            cut = parts.index("|")
            z = np.array([float(Fraction(x)) for x in parts[3:cut]])
            tree = np.array([float(Fraction(x)) for x in parts[cut + 1:]])
            samples.append((int(parts[1]), int(parts[2]), z, tree))
    return samples


def masses(v):
    top = v.max()
    e = np.exp2(v - top)
    return e / e.sum(), top + np.log2(e.sum())


def floor_pow2(x):
    return 2.0 ** np.floor(np.log2(x))


def replay(samples, prior, window=2):
    """`prior` a number (the fixed `H_0 = prior I`) or `"unit"` (the unit-information prior: the
    readings' own mean energy per coordinate so far, `H_0 = (sum |z|^2 / (N n)) I`)."""
    n = len(samples[0][2])
    classes = len(samples[0][3])
    W = np.zeros((classes, n))
    F = np.zeros((n, n))
    seen, energy = 0, 0.0
    codes, steps = [], []
    a_pre, curvature = 0.0, 0.0
    for start in range(0, len(samples), window):
        here = samples[start:start + window]
        reads = []
        for aeon, t, z, tree in here:
            delta = W @ z
            p, log_norm = masses(tree + delta)
            codes.append((aeon, log_norm - (tree + delta)[t]))
            q = np.zeros(classes)
            q[t] = 1.0
            a_pre += (q - p) @ delta
            curvature += np.log(2) * (p @ (delta - p @ delta) ** 2)
            reads.append((z, q - p, p))
        if all(not z.any() for z, _, _ in reads):
            steps.append(0.0)  # nothing reached the locus: no deposit (`NormalLaw::prepare`)
            continue
        # The window's class metric.
        mean = np.mean([(1 - (p * p).sum()) / (classes - 1) for _, _, p in reads])
        kappa = floor_pow2(1.0 / mean)
        for z, _, _ in reads:
            F += np.outer(z, z)
            seen += 1
            energy += z @ z
        scale = energy / (seen * n) if prior == "unit" else prior
        X = np.linalg.inv(scale * np.eye(n) + F)
        D = sum(kappa * np.outer(g, X @ z) for z, g, _ in reads)
        a, C, osc = 0.0, 0.0, 0.0
        for z, g, p in reads:
            delta = D @ z
            a += g @ delta
            mean_delta = p @ delta
            C += (119 / 80) * (p @ (delta - mean_delta) ** 2)
            osc = max(osc, delta.max() - delta.min())
        if a <= 0:
            steps.append(0.0)
            continue
        bound = min(a / C if C > 0 else np.inf, 1.0 / max(osc, 1.0))
        eta = floor_pow2(bound)
        steps.append(eta)
        W += eta * D
    return codes, steps, (a_pre, curvature)


def opening(samples, window=2):
    """The located prior read at the opening: the map `M_t/s`, `M_t` the class-metric gradients'
    sum before reading `t`, all at the tree face."""
    n = len(samples[0][2])
    classes = len(samples[0][3])
    M = np.zeros((classes, n))
    a, curvature = 0.0, 0.0
    for start in range(0, len(samples), window):
        here = samples[start:start + window]
        reads = []
        for _, t, z, tree in here:
            p, _ = masses(tree)
            q = np.zeros(classes)
            q[t] = 1.0
            delta = M @ z
            a += (q - p) @ delta
            curvature += np.log(2) * (p @ (delta - p @ delta) ** 2)
            reads.append((z, q - p, p))
        mean = np.mean([(1 - (p * p).sum()) / (classes - 1) for _, _, p in reads])
        M += sum(floor_pow2(1.0 / mean) * np.outer(g, z) for z, g, _ in reads)
    return a, curvature


def main(path):
    samples = read(path)
    n = len(samples[0][2])
    energies = np.array([z @ z for _, _, z, _ in samples])
    print(f"readings {len(samples)}, anchor width n = {n}, classes {len(samples[0][3])}")
    print(f"anchor energy |z|^2: mean {exact(energies.mean())}, largest {exact(energies.max())}, "
          f"mean per coordinate {exact(energies.mean() / n)}")
    total = np.cumsum(energies)
    reach = int(np.argmax(total >= 1.0)) + 1 if total[-1] >= 1.0 else None
    gram = sum(np.outer(z, z) for _, _, z, _ in samples)
    print(f"accumulated tr F {exact(total[-1])}; tr F reaches 1 at reading {reach}; "
          f"largest eigenvalue of F {exact(np.linalg.eigvalsh(gram).max())}")
    aeons = sorted({a for a, _, _, _ in samples})
    tree_codes = [masses(tree)[1] - tree[t] for _, t, _, tree in samples]
    print("tree alone: prequential code per aeon (bits a reading): "
          + ", ".join(f"aeon {a}: {exact(np.mean([c for (b, _, _, _), c in zip(samples, tree_codes) if b == a]))}"
                      for a in aeons))
    a, curvature = opening(samples)
    print(f"the opening's prequential certificate: a {exact(a)}, curvature {exact(curvature)}; "
          f"located prior s_open {exact(curvature / a)}", flush=True)
    for k in [None] + list(range(-14, -6, 2)) + list(range(-6, 7)):
        prior = "unit" if k is None else 2.0 ** k
        codes, steps, (a_pre, curv) = replay(samples, prior)
        total = sum(c for _, c in codes)
        per = ", ".join(f"aeon {a}: {exact(np.mean([c for b, c in codes if b == a]))}" for a in aeons)
        moved = [s for s in steps if s > 0]
        median = exact(np.median(moved)) if moved else "none"
        name = "unit information" if k is None else f"2^{k}"
        print(f"prior {name}: total prequential code {exact(total)} bits; per aeon {per}; "
              f"steps moved {len(moved)} of {len(steps)}, median {median}; prequential a {exact(a_pre)}, "
              f"curvature {exact(curv)}, located prior {exact(prior_value(prior, samples) / (1 + a_pre / curv))}",
              flush=True)


def prior_value(prior, samples):
    if prior != "unit":
        return prior
    n = len(samples[0][2])
    return np.mean([z @ z for _, _, z, _ in samples]) / n


if __name__ == "__main__":
    main(sys.argv[1])
