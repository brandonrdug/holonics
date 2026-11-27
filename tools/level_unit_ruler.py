#!/usr/bin/env -S python3 -I
"""level_unit_ruler.py CUT ROWS CODEC: a ruler (the lead, November 27; the formal thread's premise of 03:28 UTC, its G-Z8 to G-Z10). What a
level's unit keeps of its epoch, by the term it sums and the chart it sums it on.

`read-strand-cut ... past links` (CUT) writes, for passages read by two streams, the known stream's anchors (`cut.tsv`), each known
site's read at the split (`known.i32`, `[n][D₀]`), each known site's harmonics of its news phase (`harmonics.i64`, `[n][H]`), each
epoch's built moment (`moment.i64`, `[j][H D₀]`), its restricted state before the level's ticks (`restricted.i64`, `[j][D₁]`, the
control), the encoding's rows (`enc.i32`, `[A][D₀]`) and the declaration's widths (`dims.tsv`); CODEC is the codec the read used (a
byte's class is its index among the codec's used units, one past it beyond the void's, `codec.rs`). Over the epochs of ROWS (the passage's
text, each row's first epoch aside), each representation is read by ridge regression (columns standardized; fitted on the even rows and
read on the odd, the shrinkage chosen on a split of the even) for the share of each quantity's indicator it removes:
  cells     the term `r` (her read at the split, what the built level sums) or `E` (the symbol's encoding row `E(u_t)`), summed over
            the epoch's places on the chart `news` (the level's six harmonics of the news phase, `h_k(φ_t)`; `r` on it is the built
            moment) or `rings` (the fine field's rings' phases counted from the epoch's site, `t − s_j`: the constant term and each
            ring's turn, `cos 2π(t − s_j)/P` and its sine, on the rings of periods 2, 3 and 4 for six terms a place, the news chart's
            count, and with 9 and 16 beside them for ten, `rings10`); the strand face `m_j = Σ_t Ĝ(t − s_j)⁻¹ E(u_t)` is `E` on `rings`;
  control   the built restriction `A m + b_A` (`restricted`);
  ceiling   `E` of the epoch's first eight places side by side (`E_places`): every position is present by construction, the ruler's
            proof that it reads them;
  quantities  the byte at each of the epoch's first eight places (`pos1` … `pos8`, a class of its own where the epoch is shorter),
            the epoch's text as one identity hashed into 64 cells (`identity`), the next epoch's first byte (`next_first`, what the
            join would carry), and a cell drawn by a key from the row and the epoch (`planted`, the floor).
A line `LEVEL_UNIT_CHECK` gives the correlation of `r` on `news` with the dumped built moment, so the dump's layout is read before any
share is. Outside the machine; shares only, floats at the exterior.
"""
import hashlib
import sys

import numpy as np


def ring_terms(dt, periods):
    out = [1.0]
    for p in periods:
        out.append(np.cos(2 * np.pi * dt / p))
        if p > 2:
            out.append(np.sin(2 * np.pi * dt / p))
    return out


def main():
    d, rows_f, codec_f = sys.argv[1], sys.argv[2], sys.argv[3]
    lines = open(codec_f).read().split('\n')
    head = lines[0].split(' ')
    void = int(head[2]) if head[0] == 'field-codec-v3' else None
    used = [int(w) for w in lines[1].split(' ')]
    void = len(used) if void is None else void
    klass = {u: (i if i < void else i + 1) for i, u in enumerate(used)}
    dims = dict(line.split('\t') for line in open(f'{d}/dims.tsv').read().split('\n') if line)
    d0, d1, h = int(dims['read']), int(dims['coarse']), int(dims['harmonics'])
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    cuts = []
    for line in open(f'{d}/cut.tsv'):
        f = line.rstrip('\n').split('\t')
        cuts.append((int(f[0]), int(f[1]), [int(a) for a in f[2].split(',') if a]))
    n_all = sum(n for _, n, _ in cuts)
    e_all = sum(len(a) for _, _, a in cuts)
    known = np.fromfile(f'{d}/known.i32', dtype='<i4').astype(np.float64).reshape(n_all, d0)
    harm = np.fromfile(f'{d}/harmonics.i64', dtype='<i8').astype(np.float64).reshape(n_all, h) / 2.0 ** 30
    moment = np.fromfile(f'{d}/moment.i64', dtype='<i8').astype(np.float64).reshape(e_all, h * d0)
    restricted = np.fromfile(f'{d}/restricted.i64', dtype='<i8').astype(np.float64).reshape(e_all, d1)
    enc = np.fromfile(f'{d}/enc.i32', dtype='<i4').astype(np.float64).reshape(-1, d0)
    cell = lambda w: int(hashlib.sha256(w).hexdigest()[:8], 16) % 64
    names = ['pos1', 'pos2', 'pos3', 'pos4', 'pos5', 'pos6', 'pos7', 'pos8', 'identity', 'next_first', 'planted']
    reps = {k: [] for k in ('restricted', 'r_news', 'r_rings', 'r_rings10', 'E_news', 'E_rings', 'E_rings10', 'E_places')}
    qs, side, check = [], [], []
    p0 = e0 = 0
    for r, n, anchors in cuts:
        text = texts[r][:n]
        for j, a in enumerate(anchors):
            end = anchors[j + 1] if j + 1 < len(anchors) else n
            if j == 0 or j + 1 >= len(anchors):
                continue
            ts = np.arange(a, end)
            R, E = known[p0 + ts], enc[[klass[text[t]] for t in ts]]
            Hn = harm[p0 + ts]
            G6 = np.array([ring_terms(t - a, (2, 3, 4)) for t in ts])
            G10 = np.array([ring_terms(t - a, (2, 3, 4, 9, 16)) for t in ts])
            built = Hn.T @ R
            reps['restricted'].append(restricted[e0 + j])
            reps['r_news'].append(built.ravel())
            reps['r_rings'].append((G6.T @ R).ravel())
            reps['r_rings10'].append((G10.T @ R).ravel())
            reps['E_news'].append((Hn.T @ E).ravel())
            reps['E_rings'].append((G6.T @ E).ravel())
            reps['E_rings10'].append((G10.T @ E).ravel())
            first = np.zeros((8, d0))
            k = min(8, end - a)
            first[:k] = E[:k]
            reps['E_places'].append(first.ravel())
            if len(check) < 2000:
                check.append((built.ravel(), moment[e0 + j]))
            key = int(hashlib.sha256(f'{r}:{j}'.encode()).hexdigest()[:8], 16) % 64
            qs.append([text[a + p] if a + p < end else -1 for p in range(8)] + [cell(text[a:end]), text[end], key])
            side.append(r % 2 == 0)
        p0 += n
        e0 += len(anchors)
    side = np.array(side)
    u = np.concatenate([c[0] for c in check])
    v = np.concatenate([c[1] for c in check])
    print(f"LEVEL_UNIT_CHECK r_news_against_the_built_moment corr={np.corrcoef(u, v)[0, 1]:.4f} values={len(u)}")

    def onehot(vals):
        keys = sorted(set(vals))
        at = {k: i for i, k in enumerate(keys)}
        out = np.zeros((len(vals), len(keys)))
        out[np.arange(len(vals)), [at[v] for v in vals]] = 1.0
        return out

    def fitter(Xa):
        mx = Xa.mean(0)
        U, S, Vt = np.linalg.svd(Xa - mx, full_matrices=False)
        return mx, U, S, Vt

    def predict(fit, Ya, lam, Z):
        mx, U, S, Vt = fit
        my = Ya.mean(0)
        W = Vt.T @ ((S / (S * S + lam))[:, None] * (U.T @ (Ya - my)))
        return (Z - mx) @ W + my

    tr, te = np.where(side)[0], np.where(~side)[0]
    a_idx, b_idx = tr[: len(tr) // 2], tr[len(tr) // 2:]
    Ys = [onehot([q[k] for q in qs]) for k in range(len(names))]
    label = d.rstrip('/').split('/')[-1]
    for rep, rows in reps.items():
        X = np.array(rows)
        sd = X.std(0)
        X = (X - X.mean(0)) / np.where(sd > 0, sd, 1.0)
        fa, ft = fitter(X[a_idx]), fitter(X[tr])
        scale = float((fa[2] ** 2).mean())
        out = []
        for Y in Ys:
            best, best_lam = -1e9, scale
            for lam in scale * np.array([0.001, 0.01, 0.1, 1, 10, 100]):
                f = predict(fa, Y[a_idx], lam, X[b_idx])
                v = 1.0 - ((Y[b_idx] - f) ** 2).sum() / ((Y[b_idx] - Y[a_idx].mean(0)) ** 2).sum()
                if v > best:
                    best, best_lam = v, lam
            f = predict(ft, Y[tr], best_lam * len(tr) / len(a_idx), X[te])
            out.append(1.0 - ((Y[te] - f) ** 2).sum() / ((Y[te] - Y[tr].mean(0)) ** 2).sum())
        print(f"LEVEL_UNIT {label} cell={rep} width={X.shape[1]} epochs={X.shape[0]} " + ' '.join(f"{n}={s:.3f}" for n, s in zip(names, out)))


if __name__ == '__main__':
    main()
