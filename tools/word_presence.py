#!/usr/bin/env -S python3 -I
"""word_presence.py DUMP ROWS: a ruler (the lead, November 23). What her state holds at a word's first letter.

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
    a share near zero is its floor).
A share is a presence: how much of a quantity the state at that place carries, read the same way for each. Outside the machine;
shares only, floats at the exterior.
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
                samples.append((r, t, text[t - 2], ws[0][0], cell(ws[0]), cell(ws[1]), text[t], key))
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

    names = ['byte_2', 'prev_first', 'prev_word', 'prev2_word', 'target', 'planted']
    print(f"WORD_PRESENCE {d.rstrip('/').split('/')[-1]} word_starts={len(samples)} read={width} tick={ticks - 1} " + ' '.join(f"{n}={share(onehot([s[2 + k] for s in samples])):.3f}" for k, n in enumerate(names)))


if __name__ == '__main__':
    main()
