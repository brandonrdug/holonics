#!/usr/bin/env -S python3 -I
"""word_presence.py DUMP ROWS [more]: a ruler (the lead, November 23). What her state holds at a word's first letter.

`read-strand-states ... past rows` writes, for passages read by two streams, each open place's read after every tick (`open_K.i32`,
one row of `read` counts a place). At every place where a word begins (a letter after a space or a line feed), this reads by ridge
regression, fitted on the even rows and read on the odd (the shrinkage chosen on a split of the even rows), the share of each
quantity's indicator the open read after the last tick removes:
  - `byte_2`: the byte two places before (the last letter of the word before, or what stands there);
  - `prev_first`: the first letter of the word before;
  - `prev_word`: the word before, hashed into 64 cells;
  - `prev2_word`: the word two before, hashed into 64 cells;
  - `target`: the letter the place holds (what the read is for);
  - `planted`: a cell of 64 drawn from the place's own row and position by a key, which nothing in the passage fixes (the ruler's null:
    a share near zero is its floor);
  - `prev_len`: the length of the word before (1 to 12, longer as 12);
  - `line_words`: the count of words since the line's start (1 to 12, more as 12), read at word starts three or more words into a line
    (the formal thread's G-A2, November 23).
A share is a presence: how much of a quantity the state at that place carries, read the same way for each. Outside the machine;
shares only, floats at the exterior.

With `more` (the formal thread's guesses of November 23, receipts/2026-11-23_handed_cycle/GUESS.txt), three reads beside:
  - G-H1: the word before and the word two before read from products of the read's coordinates (2,048 pairs drawn by a fixed key, each
    product standardized), the same ridge and split, the keyed cell as the floor: a word held in relative phases a linear read misses;
  - G-H2: the count of words since the line's start with the place's index in its line (in buckets of eight) taken out of both sides;
  - G-H3: the word two before, split by the length of the word between (2 to 3, 4 to 6, 7 or more letters);
  - G-H4: the word two before with the word before's cell taken out of both sides (its one-hot regressed out);
  - G-H5: the word before, read at the current word's letters 1 to 6, in words of six letters or more.
"""
import hashlib
import sys

import numpy as np


def main():
    d, rows_f = sys.argv[1], sys.argv[2]
    dims = dict(line.split('\t') for line in open(f'{d}/dims.tsv').read().split('\n') if line)
    width, ticks = int(dims['read']), int(dims['ticks'])
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    rowsel = [int(line.split('\t')[0]) for line in open(f'{d}/rows.tsv')]
    count = {}
    for r in rowsel:
        count[r] = count.get(r, 0) + 1
    offset, acc = {}, 0
    for r in sorted(count):
        offset[r] = acc
        acc += count[r]
    letter = lambda b: 65 <= b <= 90 or 97 <= b <= 122
    cell = lambda w: int(hashlib.sha256(w).hexdigest()[:8], 16) % 64
    samples = []
    for r in sorted(count):
        text = texts[r][:count[r]]
        for t in range(1, len(text)):
            if letter(text[t]) and text[t - 1] in (32, 10):
                # the words before: maximal runs of letters ending before t
                j, ws = t - 1, []
                while j >= 0 and len(ws) < 2:
                    while j >= 0 and not letter(text[j]):
                        j -= 1
                    end = j + 1
                    while j >= 0 and letter(text[j]):
                        j -= 1
                    if end > j + 1:
                        ws.append(text[j + 1:end])
                if len(ws) < 2 or t < 2:
                    continue
                key = int(hashlib.sha256(f'{r}:{t}'.encode()).hexdigest()[:8], 16) % 64
                start = text.rfind(b'\n', 0, t) + 1
                line_words = sum(1 for k in range(start, t) if letter(text[k]) and (k == start or not letter(text[k - 1])))
                samples.append((r, t, text[t - 2], ws[0][0], cell(ws[0]), cell(ws[1]), text[t], key, min(len(ws[0]), 12), min(line_words, 12)))
    opens = np.fromfile(f'{d}/open_{ticks - 1}.i32', dtype='<i4').reshape(acc, width).astype(np.float64) / 65536.0
    X = opens[[offset[s[0]] + s[1] for s in samples]]
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

    def share(Y):
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

    names = ['byte_2', 'prev_first', 'prev_word', 'prev2_word', 'target', 'planted', 'prev_len']
    line = f"WORD_PRESENCE {d.rstrip('/').split('/')[-1]} word_starts={len(samples)} read={width} tick={ticks - 1} " + ' '.join(f"{n}={share(onehot([s[2 + k] for s in samples])):.3f}" for k, n in enumerate(names))
    deep = np.array([s[9] >= 3 for s in samples])
    X_all, side_all = X, side
    X, side = X_all[deep], side_all[deep]
    line += f" | three or more words into a line ({int(deep.sum())}): line_words={share(onehot([s[9] for s, k in zip(samples, deep) if k])):.3f}"
    X, side = X_all, side_all
    print(line)
    if len(sys.argv) > 3 and sys.argv[3] == 'more':
        rng = np.random.default_rng(20261123)
        pairs = rng.integers(0, width, size=(2048, 2))
        P = X_all[:, pairs[:, 0]] * X_all[:, pairs[:, 1]]
        P = (P - P.mean(0)) / (P.std(0) + 1e-12)
        X = P
        h1 = ' '.join(f"{n}={share(onehot([s[2 + k] for s in samples])):.3f}" for k, n in ((2, 'prev_word'), (3, 'prev2_word'), (5, 'planted')))
        X = X_all
        print(f"WORD_PRESENCE_GH1 products=2048 {h1}")
        index = np.array([s[1] - (texts[s[0]].rfind(b'\n', 0, s[1]) + 1) for s in samples]) // 8
        Y = onehot([s[9] for s in samples])
        Xr, Yr = X_all.copy(), Y.copy()
        for b in np.unique(index):
            at = index == b
            Xr[at] -= Xr[at].mean(0)
            Yr[at] -= Yr[at].mean(0)
        X, side = Xr[deep], side_all[deep]
        print(f"WORD_PRESENCE_GH2 line_words_less_index={share(Yr[deep]):.3f} ({int(deep.sum())} word starts)")
        out = []
        for lo, hi in ((2, 3), (4, 6), (7, 99)):
            sel = np.array([lo <= s[8] <= hi for s in samples])
            X, side = X_all[sel], side_all[sel]
            out.append(f"between_{lo}_{hi if hi < 99 else 'more'}={share(onehot([s[5] for s, k in zip(samples, sel) if k])):.3f}({int(sel.sum())})")
        X, side = X_all, side_all
        print("WORD_PRESENCE_GH3 prev2_word " + ' '.join(out))
        # G-H4: the word before's cell regressed out of both sides.
        Z = onehot([s[4] for s in samples])
        Z = np.hstack([Z, np.ones((len(samples), 1))])
        coef_x, *_ = np.linalg.lstsq(Z, X_all, rcond=None)
        Y2 = onehot([s[5] for s in samples])
        coef_y, *_ = np.linalg.lstsq(Z, Y2, rcond=None)
        X, side = X_all - Z @ coef_x, side_all
        print(f"WORD_PRESENCE_GH4 prev2_word_less_prev_word={share(Y2 - Z @ coef_y):.3f}")
        # G-H5: the word before at the current word's letters 1 to 6, words of six letters or more.
        at_letter = {k: [] for k in range(1, 7)}
        for r in sorted(count):
            text = texts[r][:count[r]]
            for t in range(1, len(text)):
                if letter(text[t]) and text[t - 1] in (32, 10):
                    e = t
                    while e < len(text) and letter(text[e]):
                        e += 1
                    if e - t < 6:
                        continue
                    j = t - 1
                    while j >= 0 and not letter(text[j]):
                        j -= 1
                    end = j + 1
                    while j >= 0 and letter(text[j]):
                        j -= 1
                    if end <= j + 1:
                        continue
                    prev = cell(text[j + 1:end])
                    for k in range(1, 7):
                        at_letter[k].append((r, t + k - 1, prev))
        out = []
        for k in range(1, 7):
            rows_k = at_letter[k]
            X = opens[[offset[q[0]] + q[1] for q in rows_k]]
            side = np.array([q[0] % 2 == 0 for q in rows_k])
            out.append(f"letter_{k}={share(onehot([q[2] for q in rows_k])):.3f}")
        X, side = X_all, side_all
        print(f"WORD_PRESENCE_GH5 prev_word ({len(at_letter[1])} words of six letters or more) " + ' '.join(out))


if __name__ == '__main__':
    main()
