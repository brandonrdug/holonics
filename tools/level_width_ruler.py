#!/usr/bin/env -S python3 -I
"""level_width_ruler.py CUT ROWS CODEC: a ruler (the lead, November 27; the formal thread's capacity read of 04:01 UTC, G-Z11). The
width the level's restriction needs, read from the strand face's capacity price (`code.capacity-price`), never picked.

From the dump `tools/level_unit_ruler.py` reads (`read-strand-cut ... past links`), each epoch's strand face `m_j = Σ_t ρ(t − s_j)
r̂(E(u_t))` on the fine rings of periods 2, 3 and 4 (six terms a place) is built; its columns are standardized; on one half of the rows
(even, then odd) its leading directions are found (the principal axes of that half) and the face is restricted to the first `k` of them,
`k` in 16, 32, 64, 128 and the face's full width; each restriction is read on the other half by ridge regression (the shrinkage chosen
on a split of the fitting half) for the bytes at the epoch's first eight places. A width's read is the mean of its two halves, its
spread the absolute difference between them. The width's receipt: the least `k` whose read at each of places 1 to 6 stands within the
unrestricted face's read less the larger of the two spreads. Outside the machine; shares only, floats at the exterior.
"""
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
import level_unit_ruler as U  # noqa: E402


def main():
    d, rows_f, codec_f = sys.argv[1], sys.argv[2], sys.argv[3]
    lines = open(codec_f).read().split('\n')
    head = lines[0].split(' ')
    void = int(head[2]) if head[0] == 'field-codec-v3' else None
    used = [int(w) for w in lines[1].split(' ')]
    void = len(used) if void is None else void
    klass = {u: (i if i < void else i + 1) for i, u in enumerate(used)}
    dims = dict(line.split('\t') for line in open(f'{d}/dims.tsv').read().split('\n') if line)
    d0 = int(dims['read'])
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    cuts = []
    for line in open(f'{d}/cut.tsv'):
        f = line.rstrip('\n').split('\t')
        cuts.append((int(f[0]), int(f[1]), [int(a) for a in f[2].split(',') if a]))
    enc = np.fromfile(f'{d}/enc.i32', dtype='<i4').astype(np.float64).reshape(-1, d0)
    lanes = 7
    # each encoding row as a ratio to its own power, lane by lane (the lane chart's read)
    lane_w = d0 // lanes
    rows = enc.reshape(enc.shape[0], lanes, lane_w)
    rms = np.sqrt((rows ** 2).mean(axis=2, keepdims=True))
    E_read = (rows / np.where(rms > 0, rms, 1.0)).reshape(enc.shape[0], d0)
    X, Ys, side = [], [[] for _ in range(8)], []
    for r, n, anchors in cuts:
        text = texts[r][:n]
        for j, a in enumerate(anchors):
            end = anchors[j + 1] if j + 1 < len(anchors) else n
            if j == 0 or j + 1 >= len(anchors):
                continue
            ts = np.arange(a, end)
            G = np.array([U.ring_terms(t - a, (2, 3, 4)) for t in ts])
            X.append((G.T @ E_read[[klass[text[t]] for t in ts]]).ravel())
            for p in range(8):
                Ys[p].append(text[a + p] if a + p < end else -1)
            side.append(r % 2 == 0)
    X = np.array(X)
    sd = X.std(0)
    X = (X - X.mean(0)) / np.where(sd > 0, sd, 1.0)
    side = np.array(side)

    def onehot(vals):
        keys = sorted(set(vals))
        at = {k: i for i, k in enumerate(keys)}
        out = np.zeros((len(vals), len(keys)))
        out[np.arange(len(vals)), [at[v] for v in vals]] = 1.0
        return out

    Ys = [onehot(v) for v in Ys]

    def read(fit_idx, read_idx, k):
        mx = X[fit_idx].mean(0)
        _, _, Vt = np.linalg.svd(X[fit_idx] - mx, full_matrices=False)
        P = Vt[:k].T
        Z = (X - mx) @ P
        a, b = fit_idx[: len(fit_idx) // 2], fit_idx[len(fit_idx) // 2:]
        out = []
        for Y in Ys:
            best, best_lam = -1e9, 1.0
            za = Z[a] - Z[a].mean(0)
            for lam in np.array([0.001, 0.01, 0.1, 1, 10, 100]) * len(a):
                W = np.linalg.solve(za.T @ za + lam * np.eye(k), za.T @ (Y[a] - Y[a].mean(0)))
                f = (Z[b] - Z[a].mean(0)) @ W + Y[a].mean(0)
                v = 1.0 - ((Y[b] - f) ** 2).sum() / ((Y[b] - Y[a].mean(0)) ** 2).sum()
                if v > best:
                    best, best_lam = v, lam
            zf = Z[fit_idx] - Z[fit_idx].mean(0)
            W = np.linalg.solve(zf.T @ zf + best_lam * 2 * np.eye(k), zf.T @ (Y[fit_idx] - Y[fit_idx].mean(0)))
            f = (Z[read_idx] - Z[fit_idx].mean(0)) @ W + Y[fit_idx].mean(0)
            out.append(1.0 - ((Y[read_idx] - f) ** 2).sum() / ((Y[read_idx] - Y[fit_idx].mean(0)) ** 2).sum())
        return np.array(out)

    even, odd = np.where(side)[0], np.where(~side)[0]
    full = X.shape[1]
    reads = {}
    for k in (16, 32, 64, 128, full):
        h1, h2 = read(even, odd, k), read(odd, even, k)
        reads[k] = ((h1 + h2) / 2, np.abs(h1 - h2))
        m, s = reads[k]
        print(f"LEVEL_WIDTH {d.rstrip('/').split('/')[-1]} width={k} epochs={len(X)} " + ' '.join(f"pos{p + 1}={m[p]:.3f}(±{s[p]:.3f})" for p in range(8)))
    fm, fs = reads[full]
    receipt = next((k for k in (16, 32, 64, 128, full) if all(reads[k][0][p] >= fm[p] - max(fs[p], reads[k][1][p]) for p in range(6))), full)
    ratio = reads[64][0][:6] / fm[:6]
    print(f"LEVEL_WIDTH_RECEIPT least_width={receipt} of {full}; at 64 the share of the full face's read at places 1 to 6: " + ' '.join(f"{v:.3f}" for v in ratio))


if __name__ == '__main__':
    main()
