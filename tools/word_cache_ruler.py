#!/usr/bin/env -S python3 -I
"""word_cache_ruler.py ROWS FACES: a ruler (the lead, November 27; the formal thread's G-Z35 of 15:55 UTC). The ceiling of a level heard
by address at a word's letters: how much a leaky count of the whole words met earlier in the row adds to her own face.

FACES is a `read-reach ... faces:all` output (her face whole at every place, every class's code on `2^(−20)` bits). At every letter of a
word of ROWS's rows (a word is a run of letters), both faces know that the place holds a letter: hers is renormalized over the letters.
The count is charged at each word's close with one, and the charge leaks by `e^(−d/L)` over the `d` places from that close; at the `k`-th
letter of a word whose first `k − 1` letters are a prefix, its face over the letter is the charge of the earlier words that begin with that
prefix and run to at least `k` letters, shared by their `k`-th letters. It joins her face by one coefficient, `(1 − λ) q + λ c` where the
count has a charge and `q` alone where it has none; `λ` and `L` are chosen on the even rows (every letter place) and read on the odd, then
chosen on the odd and read on the even, and the two halves' gains, by part, are the read's scatter. The parts: the place in its word (1,
2, 3, the rest) and whether the word was last met within 30 places of its start, over 30, or not before. Beside it: the coefficient chosen
for each place in the word on its own; one chosen for each place and part, an upper ceiling that knows whether the word was met before;
and one set by the count's own state (the place in the word and how many earlier words share its prefix). ROWS and FACES may each be a
comma-separated list read in step; with a third argument `joined` (the formal thread's test past her reach, November 27 16:12 UTC) a
passage's stretches (rows labelled `group:passage:stretch`, stretch zero where the label has two fields) are one passage to the count while
her face is read stretch by stretch, reset at each, and a word last met in an earlier stretch is its own part (`earlier_stretch`): what a
level carried across her reach could hand her where her own address has none. Outside the machine; counts and codes, floats at the exterior.
"""
import math
import sys
from collections import defaultdict

import numpy as np

LN2_20 = math.log(2) / (1 << 20)
LEAKS = (8, 32, 128, 512, 2048, None)
PARTS = ("within_30", "over_30", "not_before", "earlier_stretch")
LAMBDAS = (0.0, 0.01, 0.02, 0.05, 0.1, 0.15, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9)


def letter(b):
    return 65 <= b <= 90 or 97 <= b <= 122


def main():
    # ROWS and FACES may each be a comma-separated list read in step (a faces dir a rows file); with `joined` a passage's stretches (its
    # rows labelled `group:passage[:stretch]`, the stretch zero where absent) are read as one passage by the count, her face reset at each.
    rows_fs, fds = sys.argv[1].split(','), sys.argv[2].split(',')
    joined = len(sys.argv) > 3 and sys.argv[3] == 'joined'
    texts, halves, keys, source = [], [], [], []
    for k_, rows_f in enumerate(rows_fs):
        for local, line in enumerate(open(rows_f, encoding='utf-8')):
            r = len(texts)
            f = line.rstrip('\n').split('\t')
            # a row's text is escaped (`\\n` a line's end) or `hex:` and its octets, as read-reach reads it
            texts.append(b''.join(bytes.fromhex(t[4:]) if t.startswith('hex:') else t.replace('\\n', '\n').encode() for t in f[1:3]))
            # a label of three fields (`group:passage:piece`, a passage cut into rows) takes its half from its passage, so a passage's
            # pieces stand on one side; otherwise the row's own parity
            label = f[0].split(':')
            halves.append(int(label[1]) % 2 == 0 if len(label) > 2 or joined else r % 2 == 0)
            keys.append(((label[0], label[1]), int(label[2]) if len(label) > 2 else 0) if joined else ((r,), 0))
            source.append((k_, local))
    byte_class = {}
    for line in open(f'{fds[0]}/classes.tsv'):
        f = line.rstrip('\n').split('\t')
        if len(f) > 1 and len(f[1]) == 2:
            byte_class[int(f[1], 16)] = int(f[0])
    alphabet = len(open(f'{fds[0]}/classes.tsv').read().split('\n')) - 1
    raws, ats = [], []
    for fd in fds:
        index = [tuple(int(v) for v in line.split('\t')[:2]) for line in open(f'{fd}/faces.tsv')]
        raws.append(np.memmap(f'{fd}/faces.i32', dtype='<i4', mode='r', shape=(len(index), alphabet)))
        ats.append({key: i for i, key in enumerate(index)})
    letters = [b for b in range(256) if letter(b) and b in byte_class]
    cols = np.array([byte_class[b] for b in letters])
    col_of = {b: i for i, b in enumerate(letters)}
    passages = defaultdict(list)
    for r, (key, stretch) in enumerate(keys):
        passages[key].append((stretch, r))
    # One record a letter place: her renormalized probability of the written letter, its part, its half, and the count's share of the
    # written letter under each leak (None where the count holds no charge).
    hers, place_k, recur, even, shares, spread = [], [], [], [], {L: [] for L in LEAKS}, []
    for key in passages:
        stretches = sorted(passages[key])
        text, owner = b'', []  # the passage's octets, and each place's (row, place in its row, the place its stretch opens at)
        for _, r in stretches:
            owner.extend((r, t, len(text)) for t in range(len(texts[r])))
            text += texts[r]
        n = len(text)
        words, i = [], 0
        while i < n:
            if letter(text[i]):
                j = i
                while j < n and letter(text[j]):
                    j += 1
                words.append((i, j, bytes(text[i:j])))
                i = j
            else:
                i += 1
        closes = []  # (close place, word) of the words met so far in the passage
        last_start = {}
        for s, e, w in words:
            gap = s - last_start[w] if w in last_start else None
            if gap is not None and joined and last_start[w] < owner[s][2]:
                part = "earlier_stretch"
            else:
                part = "not_before" if gap is None else ("within_30" if gap <= 30 else "over_30")
            for k in range(1, len(w) + 1):
                p = s + k - 1
                r, t, _ = owner[p]
                k_, local = source[r]
                if t == 0 or (local, t) not in ats[k_]:
                    continue
                logq = -np.asarray(raws[k_][ats[k_][(local, t)], cols], dtype=np.float64) * LN2_20
                logq -= logq.max()
                q = np.exp(logq)
                hers.append(q[col_of[w[k - 1]]] / q.sum())
                place_k.append(min(k, 4))
                recur.append(part)
                even.append(halves[r])
                prefix = w[:k - 1]
                matches = [(c, v) for c, v in closes if len(v) >= k and v[:k - 1] == prefix]
                kinds = len({v for _, v in matches})
                spread.append(0 if kinds == 0 else (1 if kinds == 1 else (2 if kinds <= 3 else (3 if kinds <= 15 else 4))))
                for L in LEAKS:
                    if not matches:
                        shares[L].append(None)
                        continue
                    num = tot = 0.0
                    for c, v in matches:
                        g = 1.0 if L is None else math.exp(-(p - c) / L)
                        tot += g
                        if v[k - 1] == w[k - 1]:
                            num += g
                    shares[L].append(num / tot if tot > 0 else None)
            closes.append((e, w))
            last_start[w] = s
    hers = np.array(hers)
    place_k, recur, even, spread = np.array(place_k), np.array(recur), np.array(even), np.array(spread)
    has = {L: np.array([c is not None for c in shares[L]]) for L in LEAKS}
    share = {L: np.array([0.0 if c is None else c for c in shares[L]]) for L in LEAKS}
    own = -np.log(hers)

    def mixed(L, lam, m):
        p = np.where(has[L][m], (1 - lam) * hers[m] + lam * share[L][m], hers[m])
        return -np.log(np.maximum(p, 1e-300))

    print(f"WORD_CACHE letter_places={len(hers)} even={int(even.sum())} odd={int((~even).sum())} her_nats_odd={own[~even].mean():.3f} her_nats_even={own[even].mean():.3f} count_has_charge={has[None].mean():.3f}", flush=True)
    gains = defaultdict(list)
    for name, fit_on, read_on in (("even_to_odd", even, ~even), ("odd_to_even", ~even, even)):
        best = min(((mixed(L, lam, fit_on).mean(), L, lam) for L in LEAKS for lam in LAMBDAS), key=lambda t: t[0])
        _, L, lam = best
        code = mixed(L, lam, read_on)
        base = own[read_on]
        print(f"WORD_CACHE fit={name} leak={L} coefficient={lam} her_nats={base.mean():.3f} joined_nats={code.mean():.3f} gain={base.mean() - code.mean():+.4f}", flush=True)
        for k in (1, 2, 3, 4):
            for part in PARTS:
                m = (place_k[read_on] == k) & (recur[read_on] == part)
                if m.sum():
                    g = base[m] - code[m]
                    gains[(k, part)].append(g.mean())
                    print(f"WORD_CACHE fit={name} place={'rest' if k == 4 else k} part={part} places={int(m.sum())} her_nats={base[m].mean():.3f} joined_nats={code[m].mean():.3f} gain={g.mean():+.4f} (±{g.std() / math.sqrt(m.sum()):.4f}) count_has_charge={has[L][read_on][m].mean():.3f}", flush=True)
        # Beside it: the coefficient chosen for each place in the word on its own, at the same leak.
        for k in (1, 2, 3, 4):
            mk_fit = fit_on & (place_k == k)
            mk_read = read_on & (place_k == k)
            lam_k = min(LAMBDAS, key=lambda x: mixed(L, x, mk_fit).mean())
            c = mixed(L, lam_k, mk_read)
            print(f"WORD_CACHE fit={name} place={'rest' if k == 4 else k} own_coefficient={lam_k} gain={own[mk_read].mean() - c.mean():+.4f}", flush=True)
        # Beside it, an upper ceiling: the coefficient chosen for each place in the word and each part on its own, as if the level knew
        # whether the word had been met (which a count at a first letter cannot tell).
        for k in (1, 2, 3, 4):
            for part in ("within_30", "over_30", "earlier_stretch"):
                mk_fit = fit_on & (place_k == k) & (recur == part)
                mk_read = read_on & (place_k == k) & (recur == part)
                if not mk_fit.any() or not mk_read.any():
                    continue
                lam_k = min(LAMBDAS, key=lambda x: mixed(L, x, mk_fit).mean())
                c = mixed(L, lam_k, mk_read)
                print(f"WORD_CACHE fit={name} place={'rest' if k == 4 else k} part={part} known_part_coefficient={lam_k} gain={own[mk_read].mean() - c.mean():+.4f}", flush=True)
        # Beside it, the coefficient the count's own state sets, which knows no more than the place's prefix: one a place in the word and
        # a count of the earlier words that share the prefix (one, two or three, four to fifteen, more), chosen on the fitting half.
        gate = np.zeros(len(hers))
        for k in (1, 2, 3, 4):
            for b in (1, 2, 3, 4):
                cell = (place_k == k) & (spread == b)
                gate[cell] = min(LAMBDAS, key=lambda x: mixed(L, x, fit_on & cell).mean() if (fit_on & cell).any() else 0.0)
        p_gate = np.where(has[L], (1 - gate) * hers + gate * share[L], hers)
        code_gate = -np.log(np.maximum(p_gate, 1e-300))
        for k in (1, 2, 3, 4):
            for part in PARTS:
                m = read_on & (place_k == k) & (recur == part)
                if m.sum():
                    g = own[m] - code_gate[m]
                    gains[(k, part, 'gate')].append(g.mean())
                    print(f"WORD_CACHE fit={name} place={'rest' if k == 4 else k} part={part} count_state_coefficient gain={g.mean():+.4f} (±{g.std() / math.sqrt(m.sum()):.4f})", flush=True)
        print(f"WORD_CACHE fit={name} count_state_coefficient all_letters gain={own[read_on].mean() - code_gate[read_on].mean():+.4f} coefficients=" + ','.join(f"{k}:{b}:{gate[(place_k == k) & (spread == b)][0] if ((place_k == k) & (spread == b)).any() else '-'}" for k in (1, 2, 3, 4) for b in (1, 2, 3, 4)), flush=True)
    for key, g in sorted(gains.items(), key=lambda t: str(t[0])):
        k, part = key[0], key[1]
        tag = ' count_state' if len(key) > 2 else ''
        print(f"WORD_CACHE{tag} place={'rest' if k == 4 else k} part={part} gain_mean={np.mean(g):+.4f} halves_scatter={abs(g[0] - g[-1]):.4f}", flush=True)


if __name__ == '__main__':
    main()
