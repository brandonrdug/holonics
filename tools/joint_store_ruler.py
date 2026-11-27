#!/usr/bin/env -S python3 -I
"""joint_store_ruler.py ROWS FACES [joined]: a ruler (the lead, November 27; the formal thread's G-Z48 of 18:51 UTC). Whether a carry-keyed
store charged by the joined face's covector holds more for her than one charged by its own news.

The store is `carry_store_ruler.py`'s on drawn turns at 512 circles, read at a word's `k`-th letter as `r = Re(χ(p)* F)/J`, with no leak.
The two paths join in the log chart, `p ∝ q · e^(g r)`, with `q` her letter-renormalized face and `g = λβ` one slope. Two charges at each
word's close, each prefix's carry with the symbol that came:
  own    `F ← F + η (e − r) χ`, the store's own news (its delta charge, §22);
  joint  `F ← F + η g (e − p_joined) χ`, the joined face's covector at the store's locus, so the store charges only what her face misses.
For `own`, `g` is chosen on the fitting half over a grid; for `joint` the store depends on `g`, so each `g` of the grid walks the passages
once, and the one the fitting half codes best is read on the other half (and back). By the place in the word and by where the word was
last met (ROWS, FACES and `joined` as `word_cache_ruler.py` reads them). Outside the machine; floats at the exterior.
"""
import math
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from word_cache_ruler import LN2_20, PARTS, letter  # noqa: E402

J = 512
ETA = 0.25
SLOPES = (0.25, 0.5, 1.0, 2.0, 4.0, 8.0)
MAXLEN = 64


def walk(texts, keys, source, halves, raws, ats, cols, col_of, turns, joined, charge, g):
    """One walk of every passage: at each letter place her log face over the letters and the store's read before the word closed; the
    store charged at each word's close by `charge` (`own` or `joint` at slope `g`)."""
    passages = defaultdict(list)
    for r, (key, stretch) in enumerate(keys):
        passages[key].append((stretch, r))
    nl = len(cols)
    logqs, reads, ys, place_k, recur, even = [], [], [], [], [], []
    for key in passages:
        text, owner = b'', []
        for _, r in sorted(passages[key]):
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
        F = np.zeros((J, nl), dtype=np.complex128)
        last_start = {}
        for s, e, w_ in words:
            gap = s - last_start[w_] if w_ in last_start else None
            if gap is not None and joined and last_start[w_] < owner[s][2]:
                part = "earlier_stretch"
            else:
                part = "not_before" if gap is None else ("within_30" if gap <= 30 else "over_30")
            ids = [col_of[b] for b in w_[:MAXLEN]]
            L_ = len(ids)
            phase = np.zeros((L_, J))
            for k in range(1, L_):
                phase[k] = phase[k - 1] + turns[k - 1, ids[k - 1]]
            carry = np.exp(1j * phase)
            her_at = [None] * L_
            for k in range(1, L_ + 1):
                p = s + k - 1
                r, t, _ = owner[p]
                k_, local = source[r]
                if t == 0 or (local, t) not in ats[k_]:
                    continue
                logq = -np.asarray(raws[k_][ats[k_][(local, t)], cols], dtype=np.float64) * LN2_20
                logq -= logq.max()
                logq -= np.log(np.exp(logq).sum())
                her_at[k - 1] = logq
                logqs.append(logq.astype(np.float32))
                reads.append(((np.conj(carry[k - 1]) @ F).real / J).astype(np.float32))
                ys.append(ids[k - 1])
                place_k.append(min(k, 4))
                recur.append(part)
                even.append(halves[r])
            for k in range(L_):
                c = carry[k]
                r_now = (np.conj(c) @ F).real / J
                target = np.zeros(nl)
                target[ids[k]] = 1.0
                if charge == 'own':
                    F += ETA * np.outer(c, target - r_now)
                    continue
                if her_at[k] is None:
                    continue
                z = her_at[k] + g * r_now
                z -= z.max()
                pj = np.exp(z)
                pj /= pj.sum()
                F += ETA * g * np.outer(c, target - pj)
            last_start[w_] = s
    return (np.array(logqs), np.array(reads), np.array(ys), np.array(place_k), np.array(recur), np.array(even))


def codes(logq, reads, ys, g):
    z = logq + g * reads
    z -= z.max(1, keepdims=True)
    return -(z[np.arange(len(ys)), ys] - np.log(np.exp(z).sum(1)))


def main():
    rows_fs, fds = sys.argv[1].split(','), sys.argv[2].split(',')
    joined = len(sys.argv) > 3 and sys.argv[3] == 'joined'
    texts, halves, keys, source = [], [], [], []
    for k_, rows_f in enumerate(rows_fs):
        for local, line in enumerate(open(rows_f, encoding='utf-8')):
            r = len(texts)
            f = line.rstrip('\n').split('\t')
            texts.append(b''.join(bytes.fromhex(t[4:]) if t.startswith('hex:') else t.replace('\\n', '\n').encode() for t in f[1:3]))
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
    turns = np.random.default_rng(1130).uniform(0, 2 * np.pi, (MAXLEN, len(letters), 4096))[:, :, :J]
    args = (texts, keys, source, halves, raws, ats, cols, col_of, turns, joined)
    logq, reads, ys, place_k, recur, even = walk(*args, 'own', None)
    own = -logq[np.arange(len(ys)), ys]
    print(f"JOINT_STORE circles={J} eta={ETA} letter_places={len(ys)} her_nats_odd={own[~even].mean():.3f}", flush=True)
    runs = {'own': {g: (reads, codes(logq, reads, ys, g)) for g in SLOPES}}
    runs['joint'] = {}
    for g in SLOPES:
        _, reads_g, *_ = walk(*args, 'joint', g)
        runs['joint'][g] = (reads_g, codes(logq, reads_g, ys, g))
        print(f"JOINT_STORE walked joint slope={g}", flush=True)
    for charge in ('own', 'joint'):
        gains = defaultdict(list)
        for name, fit_on, read_on in (("even_to_odd", even, ~even), ("odd_to_even", ~even, even)):
            g = min(SLOPES, key=lambda x: runs[charge][x][1][fit_on].mean())
            code = runs[charge][g][1]
            base = own[read_on]
            print(f"JOINT_STORE charge={charge} fit={name} slope={g} her_nats={base.mean():.3f} joined_nats={code[read_on].mean():.3f} gain={base.mean() - code[read_on].mean():+.4f}", flush=True)
            for k in (1, 2, 3, 4):
                for part in PARTS:
                    m = read_on & (place_k == k) & (recur == part)
                    if m.sum():
                        gm = own[m] - code[m]
                        gains[(k, part)].append(gm.mean())
                        print(f"JOINT_STORE charge={charge} fit={name} place={'rest' if k == 4 else k} part={part} places={int(m.sum())} her_nats={own[m].mean():.3f} gain={gm.mean():+.4f} (±{gm.std() / math.sqrt(m.sum()):.4f})", flush=True)
        for (k, part), gl in sorted(gains.items()):
            print(f"JOINT_STORE charge={charge} place={'rest' if k == 4 else k} part={part} gain_mean={np.mean(gl):+.4f} halves_scatter={abs(gl[0] - gl[-1]):.4f}", flush=True)


if __name__ == '__main__':
    main()
