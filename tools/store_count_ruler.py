#!/usr/bin/env -S python3 -I
"""store_count_ruler.py DUMP ROWS STORE MB [depth]: a ruler (the lead, November 27; the formal thread's G-Z30 and G-Z31 of 15:04 UTC). How much
of a held place a count of the store's own text tells from the unit before it, with the writers' words as units and with her epochs.

The counting text is the first `MB/2` megabytes of the store's web documents and as many of its books (`DOCS_web.bin`, `DOCS_books.bin`,
training text, raw bytes). A suffix array of it is built once (prefix doubling), so each held unit's string is found by binary search.
For every place of the held rows of ROWS a join tells the unit before (its spelling `A`) and the place's distance `d` into its own unit:
  words   the units are the writers' (a run of non-space bytes with the spaces after it);
  epochs  the units are her epochs (DUMP's `cut.tsv`, the known stream's anchors and the epoch each open place reads).
Its code given `(A, d)` is read from the bytes that stand `d` places after each occurrence of `A` in the counting text (up to 20,000
occurrences a string, taken evenly across its range of the array, whose order sorts them by the bytes that follow), backed off to `A`'s last four, two and one bytes by interpolated absolute
discounting (a count less 0.75, the mass taken handed down in proportion to its distinct bytes), over the counting text's unigram with one
added to every byte; how many of those orders a count uses (none, then the last byte, two, four, the whole string) is chosen on the held
rows' even half, by part, and the shares are read on the odd half (a string met a few dozen times in the counting text is otherwise
trusted past what it holds). The share a count leaves unsaid is the place's code given `(A, d)` over its unigram code, summed over the place's
part: a word's first letter, a letter inside a word, any other byte. With `depth` (the formal thread's G-Z32, November 27 15:16 UTC), at
each word's first letter: its code given the word before (its unit with the spaces after it, `A1`, backed off by its last bytes) against
its code given the word two back and the word before together (`A2 A1`, backed off to `A1`'s chain): the share depth adds where a count
can price it (`STORE_COUNT_DEPTH`). Outside the machine; counts and ratios, floats at the exterior.
"""
import math
import sys
from collections import defaultdict

import numpy as np

DISCOUNT = 0.75
CAP = 20000


def suffix_array(t):
    """The suffix array of the byte string `t` by prefix doubling (ranks sorted in pairs, `np.lexsort`)."""
    n = len(t)
    rank = t.astype(np.int64)
    sa = np.argsort(rank, kind='stable')
    k = 1
    while True:
        second = np.full(n, -1, dtype=np.int64)
        second[:n - k] = rank[k:]
        sa = np.lexsort((second, rank))
        key_a, key_b = rank[sa], second[sa]
        new = np.empty(n, dtype=np.int64)
        new[sa] = np.concatenate([[0], np.cumsum((key_a[1:] != key_a[:-1]) | (key_b[1:] != key_b[:-1]))])
        rank = new
        if rank.max() == n - 1:
            return sa
        k *= 2


def occurrences(text, sa, s):
    """The positions where `s` occurs in `text`, by binary search on its suffix array (up to `CAP` of them)."""
    n, m = len(sa), len(s)

    def low(upper):
        lo, hi = 0, n
        while lo < hi:
            mid = (lo + hi) // 2
            piece = text[sa[mid]:sa[mid] + m]
            if piece < s or (upper and piece == s):
                lo = mid + 1
            else:
                hi = mid
        return lo

    a, b = low(False), low(True)
    if b - a <= CAP:
        return sa[a:b]
    # evenly across the range: the array's order sorts the occurrences by the bytes after the string, so its first ones are no sample
    return sa[np.linspace(a, b - 1, CAP).astype(np.int64)]


def main():
    d, rows_f, store, mb = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    part = mb * (1 << 20) // 2
    with open(f'{store}/DOCS_web.bin', 'rb') as f:
        web = f.read(part)
    with open(f'{store}/DOCS_books.bin', 'rb') as f:
        books = f.read(part)
    text = web + b'\n' + books
    t = np.frombuffer(text, dtype=np.uint8)
    uni = np.bincount(t, minlength=256).astype(np.float64)
    p_alone = (uni + 1) / (uni.sum() + 256)
    sa = suffix_array(t)
    print(f"STORE_COUNT_TEXT octets={len(text)} suffix_array={len(sa)}", flush=True)
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    letter = lambda b: 65 <= b <= 90 or 97 <= b <= 122
    kind = lambda s, i: "word_first" if letter(s[i]) and (i == 0 or s[i - 1] in (32, 10)) else ("letter_inside" if letter(s[i]) else "other")
    samples = {'words': [], 'epochs': []}
    for line in open(f'{d}/cut.tsv'):
        f = line.rstrip('\n').split('\t')
        r, n = int(f[0]), int(f[1])
        text_r = texts[r][:n]
        anchors = [int(a) for a in f[2].split(',') if a]
        source = [None if s == '-' else int(s) for s in f[3].split(',')] if len(f) > 3 and f[3] else []
        epoch_of = [0] * n
        for j, a in enumerate(anchors):
            for q in range(a, anchors[j + 1] if j + 1 < len(anchors) else n):
                epoch_of[q] = j
        for p, j in enumerate(source):
            if j is None or p == 0:
                continue
            e = epoch_of[p - 1]
            A = text_r[anchors[j]:anchors[j + 1] if j + 1 < len(anchors) else n]
            samples['epochs'].append((A, p - anchors[e], text_r[p], kind(text_r, p), r % 2 == 0))
        units = [q for q in range(n) if q == 0 or (text_r[q] not in (32, 10) and text_r[q - 1] in (32, 10))]
        u = 0
        for p in range(1, n):
            while u + 1 < len(units) and units[u + 1] <= p - 1:
                u += 1
            if u == 0:
                continue
            A = text_r[units[u - 1]:units[u]]
            samples['words'].append((A, p - units[u], text_r[p], kind(text_r, p), r % 2 == 0))
    depth_rows = []
    if len(sys.argv) > 5 and sys.argv[5] == 'depth':
        for r, text_r in enumerate(texts):
            n = len(text_r)
            units = [q for q in range(n) if q == 0 or (text_r[q] not in (32, 10) and text_r[q - 1] in (32, 10))]
            for u in range(2, len(units)):
                p = units[u]
                if letter(text_r[p]):
                    depth_rows.append((text_r[units[u - 2]:units[u - 1]], text_r[units[u - 1]:p], text_r[p], r % 2 == 0))
    tables = {}

    def table(s, dist):
        key = (s, dist)
        if key not in tables:
            pos = occurrences(text, sa, s)
            at = pos + len(s) + dist
            at = at[at < len(t)]
            tables[key] = np.bincount(t[at], minlength=256).astype(np.float64) if len(at) else None
        return tables[key]

    if depth_rows:
        chains = {'word_before': lambda a2, a1: (a1[-1:], a1[-2:], a1[-4:], a1), 'two_back_and_before': lambda a2, a1: (a1[-1:], a1[-2:], a1[-4:], a1, a2 + a1)}
        best = {}
        for name, chain in chains.items():
            codes = [[0.0, 0.0] for _ in range(6)]
            for a2, a1, byte, even in depth_rows:
                h = 0 if even else 1
                p = p_alone[byte]
                codes[0][h] += -math.log(p)
                for k, s_ in enumerate(chain(a2, a1), start=1):
                    c = table(s_, 0) if s_ else None
                    if c is not None and c.sum() > 0:
                        p = (max(c[byte] - DISCOUNT, 0.0) + DISCOUNT * np.count_nonzero(c) * p) / c.sum()
                    codes[k][h] += -math.log(p)
            ks = range(len(chain(b'', b'')) + 1)
            kb = min(ks, key=lambda k: codes[k][0])
            best[name] = codes[kb][1]
            odd = sum(1 for *_, e in depth_rows if not e)
            print(f"STORE_COUNT_DEPTH chain={name} first_letters={odd} depth={kb} code_given={codes[kb][1] / max(odd, 1):.3f} unigram={codes[0][1] / max(odd, 1):.3f} by_depth_odd=" + ','.join(f"{codes[k][1] / max(odd, 1):.3f}" for k in ks), flush=True)
        print(f"STORE_COUNT_DEPTH joint_over_word_before={best['two_back_and_before'] / best['word_before']:.4f}", flush=True)
    for unit, rows in samples.items():
        # codes[depth] by part and half: [even, odd] sums, and the unigram's
        codes = defaultdict(lambda: [[0.0, 0.0] for _ in range(5)])
        alone, count = defaultdict(lambda: [0.0, 0.0]), defaultdict(lambda: [0, 0])
        for A, dist, byte, part_, even in rows:
            h = 0 if even else 1
            p = p_alone[byte]
            codes[part_][0][h] += -math.log(p)
            for depth, s in enumerate((A[-1:], A[-2:], A[-4:], A), start=1):
                c = table(s, dist) if s else None
                if c is not None and c.sum() > 0:
                    p = (max(c[byte] - DISCOUNT, 0.0) + DISCOUNT * np.count_nonzero(c) * p) / c.sum()
                codes[part_][depth][h] += -math.log(p)
            alone[part_][h] += -math.log(p_alone[byte])
            count[part_][h] += 1
        for part_ in ("word_first", "letter_inside", "other"):
            best = min(range(5), key=lambda k: codes[part_][k][0])
            R, Z, k = codes[part_][best][1], alone[part_][1], count[part_][1]
            print(f"STORE_COUNT units={unit} part={part_} places={k} depth={best} code_given={R / max(k, 1):.3f} code_alone={Z / max(k, 1):.3f} unsaid_share={R / max(Z, 1e-12):.3f} by_depth_odd=" + ','.join(f"{codes[part_][j][1] / max(Z, 1e-12):.3f}" for j in range(5)), flush=True)


if __name__ == '__main__':
    main()
