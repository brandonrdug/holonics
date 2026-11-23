#!/usr/bin/env -S python3 -I
"""ring_presence.py MOMENTS ROWS: a ruler (the lead, November 23, the level's receipt record §5; the formal thread's §19 item 4). What each
ring's moment holds of the words before a place, by the ring's period.

`read-strand-cut ... moments` writes each open place's retarded cavity moment (`M` complex modes a place, real parts then imaginary) and
each mode's ring period. Each mode weighs the places before by its ring's skin, `e^(−2π d/n)` at distance `d` on a ring of period `n`
(`skin_decay`, one fade a radian for every ring), so a ring of period `n` reaches about `n/(2π)` places. This reads, by the ridge
regression of `word_presence.py` (fitted on the even passages and read on the odd), the share of each quantity present in the modes of each
period, and in all modes together:
  - the word before (64 cells, hashed) at the current word's letters 1 to 6, over words of six letters or more;
  - the word two before at a word's first letter, three or more words into its passage;
  - a cell drawn by a key from the place's row and position (the floor).
Outside the machine; shares only, floats at the exterior.
"""
import hashlib
import sys
from collections import defaultdict

import numpy as np


def main():
    d, rows_f = sys.argv[1], sys.argv[2]
    m = int(dict(l.split('\t') for l in open(f'{d}/dims.tsv').read().split('\n') if l)['modes'])
    periods = [int(l) for l in open(f'{d}/periods.tsv') if l.strip()]
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    moments = np.fromfile(f'{d}/moments.i64', dtype='<i8').reshape(-1, 2 * m).astype(np.float64)
    letter = lambda b: 65 <= b <= 90 or 97 <= b <= 122
    cell = lambda w: int(hashlib.sha256(w).hexdigest()[:8], 16) % 64
    at_letter, at_start = defaultdict(list), []
    offset = 0
    for r, text in enumerate(texts):
        n = len(text)
        firsts = [t for t in range(n) if letter(text[t]) and (t == 0 or not letter(text[t - 1]))]

        def word_at(t):
            e = t
            while e < n and letter(text[e]):
                e += 1
            return text[t:e]
        for i, t in enumerate(firsts):
            if i < 1 or text[t - 1] not in (32, 10):
                continue
            w, w1 = word_at(t), word_at(firsts[i - 1])
            if len(w) >= 6:
                for k in range(1, 7):
                    at_letter[k].append((r, offset + t + k - 1, cell(w1)))
            if i >= 2:
                key = int(hashlib.sha256(f'{r}:{t}'.encode()).hexdigest()[:8], 16) % 64
                at_start.append((r, offset + t, cell(word_at(firsts[i - 2])), key))
        offset += n
    assert offset == len(moments), (offset, len(moments))

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

    def share(X, Y, side):
        X = (X - X.mean(0)) / (X.std(0) + 1e-9)
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

    groups = sorted(set(p for p in periods if p > 0))
    cols = {p: [i for i, q in enumerate(periods) if q == p] for p in groups}
    cols['all'] = [i for i, q in enumerate(periods) if q > 0]
    print(f"RING_PRESENCE {d.rstrip('/').split('/')[-1]} modes={m} periods " + ' '.join(f"{p}:{len(cols[p])}" for p in groups)
          + f" | words of six letters or more {len(at_letter[1])}, word starts {len(at_start)}")
    for p in groups + ['all']:
        c = cols[p] + [m + i for i in cols[p]]
        parts = []
        for k in range(1, 7):
            rows = at_letter[k]
            side = np.array([q[0] % 2 == 0 for q in rows])
            parts.append(f"letter_{k}={share(moments[[q[1] for q in rows]][:, c], onehot([q[2] for q in rows]), side):.3f}")
        side = np.array([q[0] % 2 == 0 for q in at_start])
        X = moments[[q[1] for q in at_start]][:, c]
        parts.append(f"prev2_at_start={share(X, onehot([q[2] for q in at_start]), side):.3f}")
        parts.append(f"planted={share(X, onehot([q[3] for q in at_start]), side):.3f}")
        print(f"RING_PRESENCE period={p} reach={(p / 6.2832):.1f} " + ' '.join(parts) if p != 'all' else 'RING_PRESENCE all ' + ' '.join(parts))


if __name__ == '__main__':
    main()
