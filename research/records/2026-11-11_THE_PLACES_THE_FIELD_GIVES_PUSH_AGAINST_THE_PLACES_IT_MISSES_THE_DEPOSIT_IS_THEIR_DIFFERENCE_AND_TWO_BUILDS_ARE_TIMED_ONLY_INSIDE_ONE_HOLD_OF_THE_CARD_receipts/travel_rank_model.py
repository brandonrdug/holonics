#!/usr/bin/env -S python3 -I
"""travel_rank_model.py: what state_travel.py's rank reading prints on drawn travel of a known shape (a ruler's calibration; no
state of a line is read). Two laps' displacements D_k = S + N_k of WIDTH by COLUMNS: S the common travel, with squared singular
values falling geometrically so that their participation ratio is PR_S (COLUMNS: flat), in drawn directions; N_k noise drawn anew
each lap, scaled so that the common travel's share of a lap's squared length is C (the laps' cosine). Printed: the means over
DRAWS of the lap's pr, first share, the pair's cosine, f1, f4, f8 and pr_held."""
import sys
import numpy as np

WIDTH, COLUMNS, DRAWS = 64, 32, 40


def shares(pr, n):
    if pr >= n:
        return np.full(n, 1.0 / n)
    lo, hi = 0.0, 1.0
    for _ in range(80):  # the ratio r of a geometric fall whose participation ratio over n terms is pr
        r = (lo + hi) / 2
        p = r ** np.arange(n)
        p /= p.sum()
        if 1.0 / (p ** 2).sum() < pr:
            lo = r
        else:
            hi = r
    return p


def main():
    rng = np.random.default_rng(57)
    print("pr_s\tc\tpr\ttop1\tcos\tf1\tf4\tf8\tpr_held")
    for pr_s in (1, 2, 4, 8, 16, 32):
        for c in (0.3, 0.5, 0.7):
            acc = []
            for _ in range(DRAWS):
                u = np.linalg.qr(rng.normal(size=(WIDTH, COLUMNS)))[0]
                v = np.linalg.qr(rng.normal(size=(COLUMNS, COLUMNS)))[0]
                s = (u * np.sqrt(shares(pr_s, COLUMNS))) @ v.T        # squared length 1
                laps = []
                for _ in range(2):
                    n = rng.normal(size=(WIDTH, COLUMNS))
                    n *= np.sqrt((1 - c) / c) / np.linalg.norm(n)
                    laps.append(s + n)
                uu, sv, _ = np.linalg.svd(laps[0], full_matrices=False)
                p = sv ** 2 / (sv ** 2).sum()
                h = ((uu.T @ laps[1]) ** 2).sum(axis=1) / (laps[1] ** 2).sum()
                cos = (laps[0] * laps[1]).sum() / (np.linalg.norm(laps[0]) * np.linalg.norm(laps[1]))
                acc.append((1 / (p ** 2).sum(), p[0], cos, h[0], h[:4].sum(), h[:8].sum(), h.sum() ** 2 / (h ** 2).sum()))
            m = np.mean(acc, axis=0)
            print(f"{pr_s}\t{c}\t{m[0]:.1f}\t{m[1]:.3f}\t{m[2]:.3f}\t{m[3]:.3f}\t{m[4]:.3f}\t{m[5]:.3f}\t{m[6]:.1f}")


if __name__ == "__main__":
    main()
