#!/usr/bin/env -S python3 -I
"""level_back_ruler.py CUT ROWS CODEC [P,P,…]: a ruler (the lead, November 27; the formal thread's premise G-Z19 of 08:22 UTC). How far back the
level's own state holds its epochs.

From `read-strand-cut ... past links` (CUT): each epoch's restricted state before the level's ticks (`restricted.i64`) and its read
after them (`coarse.i32`), and, built here, the epoch's strand face (`E` on the fine rings of periods 2, 3 and 4 from its site, as
`tools/level_unit_ruler.py` builds it, the ceiling). For each epoch `j` of the rows of ROWS and each `k` in 0, 1, 2, 4, 8 and 16, each
representation of epoch `j` is read by the ridge regression of `level_unit_ruler.py` (fitted on the even rows, read on the odd) for the
bytes at the first three places of epoch `j − k` (where it exists), and the share each removes is printed with `k`. The level's ticks
hear the epochs before (one-sided), so `coarse` at `k ≥ 1` is what it carries forward. Where the dump holds the level's clock
(`tau.i64`, `τ¹_j` on the pace grain, in sections of news), `bank` is the formal thread's slow store built here (its premise G-Z20,
November 27 08:55 UTC): `m_P(j) = Σ_(i ≤ j) e^(−(τ_j − τ_i)/P) e^(−2πi (τ_j − τ_i)/P) x¹_i` on the octave periods `P` of 2 to 64 sections,
each faded at one e-fold a turn and charged by each epoch's restricted state before the level's ticks, its real and imaginary parts
(or on the periods given as a fourth word, for the read of the rings' count: the formal thread, 09:12 UTC). Outside the machine; shares
only.
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
    d0, d1 = int(dims['read']), int(dims['coarse'])
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    cuts = []
    for line in open(f'{d}/cut.tsv'):
        f = line.rstrip('\n').split('\t')
        cuts.append((int(f[0]), int(f[1]), [int(a) for a in f[2].split(',') if a]))
    e_all = sum(len(a) for _, _, a in cuts)
    restricted = np.fromfile(f'{d}/restricted.i64', dtype='<i8').astype(np.float64).reshape(e_all, d1)
    coarse = np.fromfile(f'{d}/coarse.i32', dtype='<i4').astype(np.float64).reshape(e_all, d1)
    enc = np.fromfile(f'{d}/enc.i32', dtype='<i4').astype(np.float64).reshape(-1, d0)
    backs = (0, 1, 2, 4, 8, 16)
    reps = {'face': [], 'restricted': [], 'coarse': []}
    import os
    tau = np.fromfile(f'{d}/tau.i64', dtype='<i8').astype(np.float64) / 2.0 ** 24 if os.path.exists(f'{d}/tau.i64') else None
    periods = tuple(int(p) for p in sys.argv[4].split(',')) if len(sys.argv) > 4 else (2, 4, 8, 16, 32, 64)
    only_bank = len(sys.argv) > 4
    if tau is not None:
        reps['bank'] = []
    targets = {k: [[] for _ in range(3)] for k in backs}
    side = []
    e0 = 0
    for r, n, anchors in cuts:
        text = texts[r][:n]
        spans = [(a, anchors[j + 1] if j + 1 < len(anchors) else n) for j, a in enumerate(anchors)]
        if tau is not None:
            bank, m = [], np.zeros((len(periods), d1), dtype=np.complex128)
            for j in range(len(anchors)):
                dt = tau[e0 + j] - tau[e0 + j - 1] if j > 0 else 0.0
                for q, P in enumerate(periods):
                    m[q] = m[q] * np.exp(-dt / P) * np.exp(-2j * np.pi * dt / P) + restricted[e0 + j]
                bank.append(np.concatenate([m.real.ravel(), m.imag.ravel()]))
        for j, (a, end) in enumerate(spans):
            if j < 16:
                continue
            ts = np.arange(a, end)
            G = np.array([U.ring_terms(t - a, (2, 3, 4)) for t in ts])
            reps['face'].append((G.T @ enc[[klass[text[t]] for t in ts]]).ravel())
            reps['restricted'].append(restricted[e0 + j])
            reps['coarse'].append(coarse[e0 + j])
            if tau is not None:
                reps['bank'].append(bank[j])
            for k in backs:
                ba, be = spans[j - k]
                for p in range(3):
                    targets[k][p].append(text[ba + p] if ba + p < be else -1)
            side.append(r % 2 == 0)
        e0 += len(anchors)
    side = np.array(side)
    tr, te = np.where(side)[0], np.where(~side)[0]
    a_idx, b_idx = tr[: len(tr) // 2], tr[len(tr) // 2:]

    def onehot(vals):
        keys = sorted(set(vals))
        at = {k: i for i, k in enumerate(keys)}
        out = np.zeros((len(vals), len(keys)))
        out[np.arange(len(vals)), [at[v] for v in vals]] = 1.0
        return out

    def fitter(Xa):
        mx = Xa.mean(0)
        Uu, S, Vt = np.linalg.svd(Xa - mx, full_matrices=False)
        return mx, Uu, S, Vt

    def predict(fit, Ya, lam, Z):
        mx, Uu, S, Vt = fit
        my = Ya.mean(0)
        W = Vt.T @ ((S / (S * S + lam))[:, None] * (Uu.T @ (Ya - my)))
        return (Z - mx) @ W + my

    label = d.rstrip('/').split('/')[-1]
    for rep, rows in reps.items():
        if only_bank and rep != 'bank':
            continue
        X = np.array(rows)
        sd = X.std(0)
        X = (X - X.mean(0)) / np.where(sd > 0, sd, 1.0)
        fa, ft = fitter(X[a_idx]), fitter(X[tr])
        scale = float((fa[2] ** 2).mean())
        for k in backs:
            out = []
            for p in range(3):
                Y = onehot(targets[k][p])
                best, best_lam = -1e9, scale
                for lam in scale * np.array([0.001, 0.01, 0.1, 1, 10, 100]):
                    f = predict(fa, Y[a_idx], lam, X[b_idx])
                    v = 1.0 - ((Y[b_idx] - f) ** 2).sum() / ((Y[b_idx] - Y[a_idx].mean(0)) ** 2).sum()
                    if v > best:
                        best, best_lam = v, lam
                f = predict(ft, Y[tr], best_lam * len(tr) / len(a_idx), X[te])
                out.append(1.0 - ((Y[te] - f) ** 2).sum() / ((Y[te] - Y[tr].mean(0)) ** 2).sum())
            print(f"LEVEL_BACK {label} rep={rep} periods={','.join(map(str, periods)) if rep == 'bank' else '-'} back={k} epochs={len(X)} pos1={out[0]:.3f} pos2={out[1]:.3f} pos3={out[2]:.3f}")


if __name__ == '__main__':
    main()
