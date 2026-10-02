#!/usr/bin/env python3
"""The receiving map's online law replayed outside the machine (the contact loop record, section 20).

[measured-diagnostic; exterior] Reads the samples `hnn_exposure ablation ... samples <path>` writes
(each refined phase's receiving input z, its target and its aeon) and replays an online normal-law
update of a wave-alone receiver v = W z in bits over the first two aeons, then scores the third
aeon with W frozen: W += k * (q - p)(X z)^T, X = (lam I + sum z z^T)^-1, with k = 1 (the identity
class metric) or k = (|A| - 1)/(1 - sum p^2) (the readings' class metric, unheld). It trains on the
wave's own distribution, not on the machine's combined face, so it bounds what the law can do on
these anchors alone. Floating point is a search outside the machine; each reported value is the
exact dyadic of its float at 24 significant bits.
"""
import sys
from fractions import Fraction

import numpy as np

from receiver_oracle import exact


def main(path):
    samples = []
    with open(path) as handle:
        for line in handle:
            parts = line.split()
            if parts[0] == "sample":
                samples.append((int(parts[1]), int(parts[2]), np.array([float(Fraction(x)) for x in parts[3:]])))
    classes = 256
    for lam in (1.0, 1 / 16, 1 / 256):
        for mode in ("identity", "class"):
            n = len(samples[0][2])
            W = np.zeros((classes, n))
            H = lam * np.eye(n)
            scored = []
            for aeon, target, z in samples:
                v = W @ z
                v = v - v.max()
                p = np.exp2(v)
                p /= p.sum()
                if aeon == 2:
                    scored.append(-np.log2(max(p[target], 1e-300)))
                    continue
                if aeon > 2:
                    continue
                H += np.outer(z, z)
                X = np.linalg.inv(H)
                g = -p.copy()
                g[target] += 1
                k = 1.0 if mode == "identity" else (classes - 1) / max(1e-12, 1 - (p * p).sum())
                W += (k * g)[:, None] * (X @ z)[None, :]
            print(f"prior {exact(lam)}, {mode} metric: third aeon's mean code {exact(np.mean(scored))} bits over {len(scored)} readings", flush=True)


if __name__ == "__main__":
    main(sys.argv[1])
