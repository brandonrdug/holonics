#!/usr/bin/env python3
"""How far back the receiving anchors remember the passage (the contact loop record, section 23).

[measured-diagnostic; exterior] Reads the samples `hnn_exposure ablation ... samples <path>` writes
(sample i is the reading of cell i of the cut) and the cut file. For each depth j, readings are
grouped by their preceding j cells; the report is the mean squared distance between two anchors in
the same group over the mean squared distance between two anchors overall (pairs within one
aeon's readings onward from aeon 1, groups of at least two). It also reports
the distance at each time lag, and each context's distance over the distance at its pairs' own lags.
A ratio well below one means the anchor separates that context. Last, per phase, the anchors'
linear transport over two readings and its residual (the innovation), grouped by the cells entered,
and the context test on the anchors' shift-invariant spectrum (the ring's rotation removed). Floating point is a search outside the machine; each value is reported as
the exact dyadic of its float at 24 significant bits.
"""
import sys
from collections import defaultdict

import numpy as np

from receiver_combined import read
from receiver_oracle import exact


def main(samples_path, cut_path):
    samples, _ = read(samples_path)
    cut = open(cut_path, "rb").read()
    Z = np.array([z for _, _, z, _ in samples])
    aeon = np.array([a for a, _, _, _ in samples])
    keep = np.nonzero(aeon >= 1)[0]
    Zk = Z[keep]
    total = 2 * ((Zk - Zk.mean(axis=0)) ** 2).sum(axis=1).mean()
    print(f"readings {len(keep)} (aeon 1 onward); overall mean squared pair distance {exact(total)}")
    # The anchors' passage in time: the mean squared distance at each lag, over the overall.
    index = {int(i): k for k, i in enumerate(keep)}
    profile = {}
    for lag in range(1, len(keep)):
        rows = [index[i] for i in keep if int(i) + lag in index]
        if not rows:
            continue
        a = Zk[rows]
        b = Zk[[index[int(keep[r]) + lag] for r in rows]]
        profile[lag] = ((a - b) ** 2).sum(axis=1).mean()
    print("lag profile (mean squared distance at the lag over the overall): " + "; ".join(
        f"{lag} {exact(profile[lag] / total)}" for lag in (1, 2, 3, 4, 8, 16, 64, 256, 1024) if lag in profile))
    for depth in (1, 2, 3, 4, 6, 8, 12, 16, 24, 32):
        groups = defaultdict(list)
        for i in keep:
            if i >= depth:
                groups[cut[i - depth:i]].append(i)
        within, matched, pairs = 0.0, 0.0, 0
        for members in groups.values():
            for x in range(len(members)):
                for y in range(x + 1, len(members)):
                    i, l = members[x], members[y]
                    within += ((Z[i] - Z[l]) ** 2).sum()
                    matched += profile.get(abs(l - i), total)
                    pairs += 1
        covered = sum(len(v) for v in groups.values() if len(v) >= 2)
        if not pairs:
            continue
        print(f"depth {depth}: {covered} readings in repeated contexts, {pairs} pairs; within over overall {exact(within / pairs / total)}, within over the same lags {exact(within / matched)}", flush=True)

    # The anchors' transport and innovation per phase: z_i against z_(i-2) by least squares, the
    # residual's share of the anchors' variance, and the residual grouped by the cells entered.
    idx = np.array([i for i in range(2, len(Z)) if aeon[i] >= 1 and aeon[i - 2] == aeon[i]])
    for phase in (0, 1):
        rows = idx[idx % 2 == phase]
        X, Y = Z[rows - 2], Z[rows]
        M = np.linalg.lstsq(X, Y, rcond=None)[0]
        E = Y - X @ M
        moduli = sorted(abs(e) for e in np.linalg.eigvals(M.T))
        print(f"phase {phase}: {len(rows)} readings; innovation over the anchors' variance "
              f"{exact((E ** 2).sum() / ((Y - Y.mean(axis=0)) ** 2).sum())}; the transport's largest eigenvalue moduli "
              + " ".join(exact(m) for m in moduli[-4:]))
        overall = 2 * ((E - E.mean(axis=0)) ** 2).sum(axis=1).mean()
        for name, key in (("the two cells entered", lambda i: cut[i - 2:i]), ("the cell before", lambda i: cut[i - 1:i])):
            groups = defaultdict(list)
            for k, i in enumerate(rows):
                groups[key(i)].append(k)
            within, pairs = 0.0, 0
            for members in groups.values():
                if len(members) >= 2:
                    G = E[members]
                    within += len(members) * ((G - G.mean(axis=0)) ** 2).sum()
                    pairs += len(members) * (len(members) - 1) // 2
            print(f"  the innovation grouped by {name}: {pairs} pairs; within over overall {exact(within / pairs / overall)}")

    # The same context test on the anchors' shift-invariant spectrum: the magnitudes of the 11-point
    # transform of the complex node values, unchanged by a cyclic rotation of the ring.
    spectrum = np.abs(np.fft.fft(Z[:, 0::2] + 1j * Z[:, 1::2], axis=1))
    Sk = spectrum[keep]
    overall = 2 * ((Sk - Sk.mean(axis=0)) ** 2).sum(axis=1).mean()
    line = []
    for depth in (1, 2, 3, 4):
        groups = defaultdict(list)
        for i in keep:
            if i >= depth:
                groups[cut[i - depth:i]].append(i)
        within, pairs = 0.0, 0
        for members in groups.values():
            if len(members) >= 2:
                G = spectrum[members]
                within += len(members) * ((G - G.mean(axis=0)) ** 2).sum()
                pairs += len(members) * (len(members) - 1) // 2
        line.append(f"depth {depth} {exact(within / pairs / overall)}")
    print("the shift-invariant spectrum, within over overall: " + "; ".join(line))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
