#!/usr/bin/env -S python3 -I
"""level_link_presence.py CUT STATES ROWS: a ruler (the lead, November 23, the level's receipt record §5). Where along the level's own
equation the words before a word's first letter slip.

`read-strand-cut ... past links` (CUT) writes each epoch's restricted state before the level's ticks and its read after them, and each
open place's added row and the state it made at the split; `read-strand-states ... past rows` (STATES) writes each open place's read after
every tick. At each word start three or more words into its passage (a letter after a space or a line feed), this reads, by the ridge
regression of `word_presence.py` (fitted on the even passages and read on the odd, the shrinkage chosen on a split of the even), the share
of each quantity present at each link:
  1. the restricted state of the epoch the open place reads (`D₁`);
  2. that epoch's read after the level's ticks (`D₁`);
  3. the row the prolongation added at the open place (`D₀`);
  4. the open place's state after the addition (`D₀`);
  5. the open place's read after the last tick (`D₀`, what the face reads).
The quantities: the word before and the word two before (64 cells each, hashed), the first letter of the word two before, the handed
epoch's own text and the epochs one and two before it (the level's own grain, 64 cells each; the formal thread's offer of November 23),
the handed epoch's first and last bytes and the last bytes of the three epochs before it (a byte the restriction sums, the ruler's
positive control; the two farther ones the formal thread's G-Q3),
and a cell drawn by a key from the place's row and position (the floor). Word starts whose handed epoch has three epochs before it. Outside the machine; shares only, floats at the exterior.
"""
import hashlib
import sys

import numpy as np


def main():
    cut_d, st_d, rows_f = sys.argv[1], sys.argv[2], sys.argv[3]
    dims = dict(l.split('\t') for l in open(f'{cut_d}/dims.tsv').read().split('\n') if l)
    d0, d1 = int(dims['read']), int(dims['coarse'])
    sdims = dict(l.split('\t') for l in open(f'{st_d}/dims.tsv').read().split('\n') if l)
    ticks = int(sdims['ticks'])
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    letter = lambda b: 65 <= b <= 90 or 97 <= b <= 122
    cell = lambda w: int(hashlib.sha256(w).hexdigest()[:8], 16) % 64
    restricted = np.fromfile(f'{cut_d}/restricted.i64', dtype='<i8').reshape(-1, d1).astype(np.float64)
    coarse = np.fromfile(f'{cut_d}/coarse.i32', dtype='<i4').reshape(-1, d1).astype(np.float64)
    row = np.fromfile(f'{cut_d}/row.i32', dtype='<i4').reshape(-1, d0).astype(np.float64)
    joined = np.fromfile(f'{cut_d}/joined.i32', dtype='<i4').reshape(-1, d0).astype(np.float64)
    final = np.fromfile(f'{st_d}/open_{ticks - 1}.i32', dtype='<i4').reshape(-1, d0).astype(np.float64)
    assert len(row) == len(final), (len(row), len(final))
    samples = []   # (row index, epoch offset, place offset, word before, word two before, its first letter, floor)
    epoch_at, place_at = 0, 0
    for line in open(f'{cut_d}/cut.tsv'):
        r, n, anchors, source = line.rstrip('\n').split('\t')
        r, n = int(r), int(n)
        text = texts[r][:n]
        anchors = [int(a) for a in anchors.split(',') if a]
        source = [None if s == '-' else int(s) for s in source.split(',')]
        firsts = [t for t in range(n) if letter(text[t]) and (t == 0 or not letter(text[t - 1]))]

        def word_at(t):
            e = t
            while e < n and letter(text[e]):
                e += 1
            return text[t:e]
        for i, t in enumerate(firsts):
            j = source[t]
            if i < 2 or text[t - 1] not in (32, 10) or j is None or j < 3:
                continue
            key = int(hashlib.sha256(f'{r}:{t}'.encode()).hexdigest()[:8], 16) % 64
            w1, w2 = word_at(firsts[i - 1]), word_at(firsts[i - 2])
            spans = [text[anchors[k]:(anchors[k + 1] if k + 1 < len(anchors) else n)] for k in (j, j - 1, j - 2, j - 3)]
            ep = [cell(x) for x in spans]
            samples.append((r, epoch_at + j, place_at + t, cell(w1), cell(w2), w2[0], key, ep[0], ep[1], ep[2], spans[0][0], spans[0][-1], spans[1][-1], spans[2][-1], spans[3][-1]))
        epoch_at += len(anchors)
        place_at += n
    assert epoch_at == len(restricted) == len(coarse), (epoch_at, len(restricted), len(coarse))
    side = np.array([s[0] % 2 == 0 for s in samples])

    def onehot(vals):
        keys = sorted(set(vals))
        at = {k: i for i, k in enumerate(keys)}
        out = np.zeros((len(vals), len(keys)))
        out[np.arange(len(vals)), [at[v] for v in vals]] = 1.0
        return out

    def ridge(Xa, Ya, lam):
        mx, my = Xa.mean(0), Ya.mean(0)
        W = np.linalg.solve((Xa - mx).T @ (Xa - mx) + lam * np.eye(Xa.shape[1]), (Xa - mx).T @ (Ya - my))
        return lambda Z: (Z - mx) @ W + my

    def share(X, Y):
        X = (X - X.mean(0)) / (X.std(0) + 1e-9)  # each coordinate at unit spread: a link whose coordinates stand at unlike sizes is read whole
        tr, te = np.where(side)[0], np.where(~side)[0]
        scale = np.trace(np.cov(X[tr].T)) / X.shape[1]
        a, b = tr[: len(tr) // 2], tr[len(tr) // 2:]
        best, best_lam = -1e9, scale
        for lam in scale * np.array([0.01, 0.1, 1, 10, 100, 1000]) * len(a):
            f = ridge(X[a], Y[a], lam)
            v = 1.0 - ((Y[b] - f(X[b])) ** 2).sum() / ((Y[b] - Y[a].mean(0)) ** 2).sum()
            if v > best:
                best, best_lam = v, lam * len(tr) / len(a)
        f = ridge(X[tr], Y[tr], best_lam)
        return 1.0 - ((Y[te] - f(X[te])) ** 2).sum() / ((Y[te] - Y[tr].mean(0)) ** 2).sum()

    links = [('restricted', restricted[[s[1] for s in samples]]), ('coarse', coarse[[s[1] for s in samples]]),
             ('row', row[[s[2] for s in samples]]), ('joined', joined[[s[2] for s in samples]]), ('final', final[[s[2] for s in samples]])]
    qs = [('prev_word', 3), ('prev2_word', 4), ('prev2_first', 5), ('handed_epoch', 7), ('epoch_before_it', 8), ('epoch_two_before_it', 9), ('handed_first_byte', 10), ('handed_last_byte', 11), ('last_byte_before_it', 12), ('last_byte_two_before_it', 13), ('last_byte_three_before_it', 14), ('planted', 6)]
    print(f"LEVEL_LINKS {cut_d.rstrip('/').split('/')[-1]} word_starts={len(samples)} D0={d0} D1={d1}")
    for name, X in links:
        print(f"LEVEL_LINK {name} " + ' '.join(f"{q}={share(X, onehot([s[k] for s in samples])):.3f}" for q, k in qs))


if __name__ == '__main__':
    main()
