#!/usr/bin/env -S python3 -I
"""part_store_ruler.py ROWS FACES ENC [joined|plain] [her|centered|onehot]: a ruler (the lead, November 27; the formal thread's G-Z38 and G-Z39 of 17:17 UTC). What a
part store of a fixed width, charged by a passage's own closed words, could hand her at a word's letters: the host form of the level's part
store, read beside her face as `word_cache_ruler.py` reads its count.

A word's strand face is `m_w = Σ_i ρ(i) ⊗ e(u_i)`: the level's six terms of a place's distance `i` from the word's start (the constant,
the period two's cosine, and the cosine and the negative sine of the periods three and four, as `strand_face_terms` builds them) against
the unit-norm row of her encoding for its letter (ENC, a dump's `enc.i32`, `[class][D₀]`), 6 × D₀ terms in all. The store is a field of
width `W` (the face carried through a fixed random orthonormal projection to `W` terms, since the level's own restriction is no linear map
of the dumped moments): at each word's close it charges `P m_w (P m_w)ᵀ` and leaks by `e^(−d/L)` over the places since. At a word's `k`-th
letter (from the second) the open prefix's face `P m_p` pairs with the field, and the completion `F P m_p` is read at the place's own terms:
the score of a letter `a` is the cosine of `P (ρ(k − 1) ⊗ e(a))` with the completion, and its face `softmax(β s)`. It joins her
letter-renormalized face by one coefficient, `(1 − λ) q + λ c`, with `β`, `λ` and `L` chosen on the fitting half (ROWS and FACES as
`word_cache_ruler.py` reads them, `joined` a passage's stretches as one passage to the store while her face is reset at each), read on the
other half and back, by the place in the word and by where the word was last met. Widths 64 (the level's), 128 and 256. Outside the
machine; floats at the exterior.
"""
import math
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from word_cache_ruler import LN2_20, PARTS, letter  # noqa: E402

WIDTHS = (64, 128, 256, 512)
LEAKS = (128, 512, None)
BETAS = (2.0, 4.0, 8.0, 16.0, 32.0, 64.0)
LAMBDAS = (0.0, 0.01, 0.02, 0.05, 0.1, 0.15, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9)
RINGS = (2, 3, 4, 9, 16, 27, 32, 81, 128, 243, 256, 729, 1024, 2187, 4096, 6561)
MAXLEN = 16


def terms(i, kind='level'):
    """A place's terms at a distance `i` from its unit's start: `level` the level's six (the constant, the period two's cosine, the cosine
    and the negative sine of the periods three and four, as `strand_face_terms` builds them); `rings` the constant and every one of her
    ring periods' turns (32 terms); `onehot` the distance's own column (the planted limit: no two places overlap)."""
    if kind == 'onehot':
        out = np.zeros(MAXLEN)
        out[min(i, MAXLEN - 1)] = 1.0
        return out
    out = [1.0, math.cos(math.pi * i)]
    for p in ((3, 4) if kind == 'level' else RINGS[1:]):
        out += [math.cos(2 * math.pi * i / p), -math.sin(2 * math.pi * i / p)]
    return np.array(out[:6] if kind == 'level' else out)


def main():
    rows_fs, fds, enc_f = sys.argv[1].split(','), sys.argv[2].split(','), sys.argv[3]
    joined = len(sys.argv) > 4 and sys.argv[4] == 'joined'
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
    # CODES (a fifth argument, the lead's diagnosis of the first read, November 27): `her` her encoding's rows as they stand, `centered`
    # less their mean row (the rows share a common part, a cosine of 0.40 between letters on the mean), `onehot` a letter's own column
    # (the planted limit: no two letters overlap)
    codes = sys.argv[5] if len(sys.argv) > 5 else 'her'
    # TERMS (a sixth argument): the place's terms, `level`, `rings` or `onehot` (see `terms`)
    kind = sys.argv[6] if len(sys.argv) > 6 else 'level'
    nterms = len(terms(0, kind))
    enc = np.fromfile(enc_f, dtype='<i4').astype(np.float64)
    d0 = len(enc) // alphabet
    enc = enc.reshape(alphabet, d0)[cols]
    if codes == 'centered':
        enc -= enc.mean(0)
    if codes == 'onehot':
        enc, d0 = np.eye(len(letters)), len(letters)
    enc /= np.linalg.norm(enc, axis=1, keepdims=True) + 1e-12
    rng = np.random.default_rng(1127)
    projections = {}
    for w in [w for w in WIDTHS if w < nterms * d0] + ([nterms * d0] if nterms * d0 <= 1024 else []):
        if w == nterms * d0:
            projections[w] = np.eye(w)  # the full face, no projection
            continue
        q, _ = np.linalg.qr(rng.standard_normal((nterms * d0, w)))
        projections[w] = q.T  # [w][6 D₀], orthonormal rows
    maxlen = 64
    widths = sorted(projections)
    # each letter's face at each distance, through each projection: [k][letter][w]
    letter_faces = {w: np.stack([np.stack([P @ np.kron(terms(i, kind), enc[a]) for a in range(len(letters))]) for i in range(maxlen)]) for w, P in projections.items()}
    passages = defaultdict(list)
    for r, (key, stretch) in enumerate(keys):
        passages[key].append((stretch, r))
    hers, place_k, recur, even, written = [], [], [], [], []
    scores = {(w, L): [] for w in widths for L in LEAKS}  # one [52] row a place, None at a place the store cannot read
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
        fields = {(w, L): np.zeros((w, w)) for w in widths for L in LEAKS}
        last_charge = 0
        last_start = {}
        for s, e, w_ in words:
            gap = s - last_start[w_] if w_ in last_start else None
            if gap is not None and joined and last_start[w_] < owner[s][2]:
                part = "earlier_stretch"
            else:
                part = "not_before" if gap is None else ("within_30" if gap <= 30 else "over_30")
            ids = [col_of[b] for b in w_[:maxlen]]
            for k in range(1, len(ids) + 1):
                p = s + k - 1
                r, t, _ = owner[p]
                k_, local = source[r]
                if t == 0 or (local, t) not in ats[k_]:
                    continue
                logq = -np.asarray(raws[k_][ats[k_][(local, t)], cols], dtype=np.float64) * LN2_20
                logq -= logq.max()
                qv = np.exp(logq)
                hers.append(qv[ids[k - 1]] / qv.sum())
                written.append(ids[k - 1])
                place_k.append(min(k, 4))
                recur.append(part)
                even.append(halves[r])
                for (w, L), F in fields.items():
                    if k == 1 or not F.any():
                        scores[(w, L)].append(None)
                        continue
                    key_ = letter_faces[w][np.arange(k - 1), ids[:k - 1]].sum(0)
                    g = 1.0 if L is None else math.exp(-(p - last_charge) / L)
                    comp = g * (F @ key_)
                    lf = letter_faces[w][k - 1]
                    norm = np.linalg.norm(comp)
                    scores[(w, L)].append(None if norm == 0 else (lf @ comp) / (np.linalg.norm(lf, axis=1) * norm + 1e-12))
            for (w, L), F in fields.items():
                face = letter_faces[w][np.arange(len(ids)), ids].sum(0)
                g = 1.0 if L is None else math.exp(-(e - last_charge) / L)
                F *= g
                F += np.outer(face, face)
            last_charge = e
            last_start[w_] = s
    hers = np.array(hers)
    place_k, recur, even = np.array(place_k), np.array(recur), np.array(even)
    own = -np.log(hers)
    print(f"PART_STORE codes={codes} terms={kind} widths={widths} letter_places={len(hers)} even={int(even.sum())} odd={int((~even).sum())} her_nats_odd={own[~even].mean():.3f}", flush=True)
    written = np.array(written)
    for w in widths:
        packed = {}
        for L in LEAKS:
            rows = scores[(w, L)]
            has = np.array([s is not None for s in rows])
            S = np.zeros((len(rows), len(letters)))
            S[has] = np.stack([s for s in rows if s is not None])
            packed[L] = (has, S)

        def mixed(L, beta, lam, m):
            has, S = packed[L]
            z = beta * S[m]
            z -= z.max(1, keepdims=True)
            c = np.exp(z)
            c /= c.sum(1, keepdims=True)
            cy = c[np.arange(m.sum()), written[m]]
            p = np.where(has[m], (1 - lam) * hers[m] + lam * cy, hers[m])
            return -np.log(np.maximum(p, 1e-300))

        gains = defaultdict(list)
        for name, fit_on, read_on in (("even_to_odd", even, ~even), ("odd_to_even", ~even, even)):
            best = min(((mixed(L, b, lam, fit_on).mean(), L, b, lam) for L in LEAKS for b in BETAS for lam in LAMBDAS), key=lambda t: t[0])
            _, L, b, lam = best
            code = mixed(L, b, lam, read_on)
            base = own[read_on]
            print(f"PART_STORE width={w} fit={name} leak={L} beta={b} coefficient={lam} her_nats={base.mean():.3f} joined_nats={code.mean():.3f} gain={base.mean() - code.mean():+.4f}", flush=True)
            for k in (1, 2, 3, 4):
                for part in PARTS:
                    m = (place_k[read_on] == k) & (recur[read_on] == part)
                    if m.sum():
                        g = base[m] - code[m]
                        gains[(k, part)].append(g.mean())
                        print(f"PART_STORE width={w} fit={name} place={'rest' if k == 4 else k} part={part} places={int(m.sum())} her_nats={base[m].mean():.3f} joined_nats={code[m].mean():.3f} gain={g.mean():+.4f} (±{g.std() / math.sqrt(m.sum()):.4f})", flush=True)
        for (k, part), g in sorted(gains.items()):
            print(f"PART_STORE width={w} place={'rest' if k == 4 else k} part={part} gain_mean={np.mean(g):+.4f} halves_scatter={abs(g[0] - g[-1]):.4f}", flush=True)


if __name__ == '__main__':
    main()
