#!/usr/bin/env -S python3 -I
"""level_tension_bound.py CUT ROWS: a ruler (the lead, November 23, the level's receipt record §5; the formal thread's G-H12). Whether the
fine comparison asks the level for a function of bound units.

`read-strand-cut ... past links` (CUT) writes, beside the level's links, the covector the reverse holds at each open place's state after
the prolongation (`lambda.i64`, the level's locus), with the cut. At every open place that is handed an epoch, this reads the share of that
covector's power removed on the held half (least squares by ridge, fitted on the even passages, read on the odd, the shrinkage chosen on
a split of the even) by three tables of features:
  - `linear`: the handed epoch's bytes as a bag (the 31 commonest bytes and the rest) and the place's last byte (the same), side by side,
    the table of `deposition.no-linear-tension-at-the-levels-locus`;
  - `bound`: beside them, their products: each byte of the handed epoch's bag times the place's last byte (31 by 31 and the rests), a
    function of the handed unit bound to the place, which no linear read of either holds;
  - `bound_only` less `linear`: the bound table's share above the linear one's.
Then the planted control (rule 11): a law in the bound table's span, planted at a tenth of the covector's power, its share recovered.
Outside the machine; shares only, floats at the exterior.
"""
import sys

import numpy as np


def main():
    d, rows_f = sys.argv[1], sys.argv[2]
    dims = dict(l.split('\t') for l in open(f'{d}/dims.tsv').read().split('\n') if l)
    d0 = int(dims['read'])
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    lam = np.fromfile(f'{d}/lambda.i64', dtype='<i8').reshape(-1, d0).astype(np.float64)
    places, bags, lasts, sides = [], [], [], []
    offset = 0
    for line in open(f'{d}/cut.tsv'):
        r, n, anchors, source = line.rstrip('\n').split('\t')
        r, n = int(r), int(n)
        text = texts[r][:n]
        anchors = [int(a) for a in anchors.split(',') if a]
        source = [None if s == '-' else int(s) for s in source.split(',')]
        for t in range(1, n):
            j = source[t]
            if j is None:
                continue
            e = anchors[j + 1] if j + 1 < len(anchors) else n
            places.append(offset + t)
            bags.append(text[anchors[j]:e])
            lasts.append(text[t - 1])
            sides.append(r % 2 == 0)
        offset += n
    assert offset == len(lam), (offset, len(lam))
    Y = lam[places]
    side = np.array(sides)
    counts = np.bincount(np.frombuffer(b''.join(bags), dtype=np.uint8), minlength=256)
    top = list(np.argsort(-counts)[:31])
    at = {int(b): i for i, b in enumerate(top)}
    k = len(top) + 1
    bag = np.zeros((len(places), k))
    for i, s in enumerate(bags):
        for b in s:
            bag[i, at.get(b, k - 1)] += 1.0
    last = np.zeros((len(places), k))
    last[np.arange(len(places)), [at.get(b, k - 1) for b in lasts]] = 1.0
    linear = np.hstack([bag, last])
    prod = (bag[:, :, None] * last[:, None, :]).reshape(len(places), k * k)
    bound = np.hstack([linear, prod])

    def ridge(Xa, Ya, lam_):
        mx, my = Xa.mean(0), Ya.mean(0)
        W = np.linalg.solve((Xa - mx).T @ (Xa - mx) + lam_ * np.eye(Xa.shape[1]), (Xa - mx).T @ (Ya - my))
        return lambda Z: (Z - mx) @ W + my

    def removed(X, Y):
        sd = X.std(0)
        keep = sd > 0
        X = (X[:, keep] - X[:, keep].mean(0)) / sd[keep]
        tr, te = np.where(side)[0], np.where(~side)[0]
        a, b = tr[: len(tr) // 2], tr[len(tr) // 2:]
        best, best_lam = -1e9, 1.0
        for l_ in np.array([0.01, 0.1, 1, 10, 100, 1000]) * len(a) / X.shape[1]:
            f = ridge(X[a], Y[a], l_)
            v = 1.0 - ((Y[b] - f(X[b])) ** 2).sum() / ((Y[b] - Y[a].mean(0)) ** 2).sum()
            if v > best:
                best, best_lam = v, l_ * len(tr) / len(a)
        f = ridge(X[tr], Y[tr], best_lam)
        return 1.0 - ((Y[te] - f(X[te])) ** 2).sum() / ((Y[te] - Y[tr].mean(0)) ** 2).sum()

    r_lin, r_bound = removed(linear, Y), removed(bound, Y)
    print(f"LEVEL_TENSION {d.rstrip('/').split('/')[-1]} open_places={len(places)} D0={d0} linear={r_lin:.4f} bound={r_bound:.4f} bound_above_linear={r_bound - r_lin:.4f}")
    # The planted control: a law in the products' span at a tenth of the covector's power.
    rng = np.random.default_rng(20261123)
    Pz = (prod - prod.mean(0)) / (prod.std(0) + 1e-9)
    law = Pz @ rng.standard_normal((Pz.shape[1], d0))
    law *= np.sqrt(0.1 * ((Y - Y.mean(0)) ** 2).sum() / (law ** 2).sum())
    Yp = Y + law
    r_lin_p, r_bound_p = removed(linear, Yp), removed(bound, Yp)
    print(f"LEVEL_TENSION_PLANTED a tenth of the power in the products' span: linear={r_lin_p:.4f} bound={r_bound_p:.4f} bound_above_linear={r_bound_p - r_lin_p:.4f} (the plant alone is 0.0909 of the planted covector's power)")


if __name__ == '__main__':
    main()
