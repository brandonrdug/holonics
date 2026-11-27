#!/usr/bin/env -S python3 -I
"""carry_store_ruler.py ROWS FACES [joined]: a ruler (the lead, November 27; the formal thread's G-Z43 of 17:30 UTC). What a part store
keyed by a prefix's carry could hand her at a word's letters, read beside her face as `word_cache_ruler.py` reads its count.

A key binds by a product: a prefix `p = u₁ … u_(k−1)` carries one phase on each of `J` circles, `Φ_j(p) = Σ_i θ_j(u_i, i)`, its carry
`χ(p) = e^(iΦ(p))`, with each letter's turn at each place drawn once uniform on the circle (a ruler's stand-in for her located turns: an
ideal hash). Two carries pair as `(1/J) Σ_j cos(Φ_j(a) − Φ_j(b))`, one where they agree on every circle and scattered about zero at
`1/√J` otherwise. The store is one field `F` of `J` circles by the letters: at each word's close it charges `Σ_k χ(w_(<k)) ⊗ e(w_k)` (a
letter's own column) and leaks by `e^(−d/L)` over the places since; at a word's `k`-th letter it reads `r = Re(χ(p)* F)/J`, the leaky
count of earlier words that share the prefix and continue with each letter, with its scatter, and its face is `softmax(β r)`. It joins
her letter-renormalized face by one coefficient, with the coefficient, `β` and the leak chosen on the fitting half and read on the other,
and back; beside it, the coefficient set by the store's own state (the place in the word and the octave of the read's largest entry). By the place in the word and by
where the word was last met (ROWS, FACES and `joined` as `word_cache_ruler.py` reads them). Circles 64, 256, 1,024 and 4,096. Outside the
machine; floats at the exterior.
"""
import math
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from word_cache_ruler import LN2_20, PARTS, letter  # noqa: E402

CIRCLES = (64, 256, 1024, 4096)
LEAKS = (128, 512, 2048, None)
BETAS = (1.0, 2.0, 4.0, 8.0, 16.0, 32.0)
LAMBDAS = (0.0, 0.01, 0.02, 0.05, 0.1, 0.15, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9)
MAXLEN = 64
FROM = 1
ETA = None


def main():
    rows_fs, fds = sys.argv[1].split(','), sys.argv[2].split(',')
    joined = len(sys.argv) > 3 and sys.argv[3] == 'joined'
    global FROM
    FROM = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    # CHARGE (a fifth argument): `sum` charges each prefix's carry with its letter; `delta:η` charges the news at the rate η
    global ETA, CIRCLES, LEAKS
    charge = sys.argv[5] if len(sys.argv) > 5 else 'sum'
    ETA = float(charge.split(':')[1]) if charge.startswith('delta:') else None
    if ETA is not None:
        CIRCLES, LEAKS = (1024, 4096), (2048, None)
    # TURNS (a sixth argument, the formal thread's G-Z46, November 27 18:00 UTC): `random` the drawn turns; `her:DIR,…` her own gates on her
    # carry circles (a `read-reach … gates` output a faces dir, in step), a place's turn on a circle the argument of its gate `γ` there, so a
    # prefix's carry is the sum of her own turns at its places; `random:J` the drawn turns on `J` circles alone, the control beside her
    turns_arg = sys.argv[6] if len(sys.argv) > 6 else 'random'
    her_gates = None
    if turns_arg.startswith('her:'):
        her_gates = turns_arg[4:].split(',')
    if turns_arg.startswith('random:'):
        CIRCLES = (int(turns_arg.split(':')[1]),)
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
    nl = len(letters)
    rng = np.random.default_rng(1130)
    turns = rng.uniform(0, 2 * np.pi, (MAXLEN, nl, max(CIRCLES)))  # θ_j(u, i), the first J columns for J circles
    angle_at = None
    if her_gates is not None:
        # her turn at each place of each row: arg γ on each circle, from the gates read in step with the faces dirs
        angle_at = []
        for gd in her_gates:
            counts = [int(line.split('\t')[1]) for line in open(f'{gd}/gates.tsv')]
            raw_g = np.fromfile(f'{gd}/gates.i32', dtype='<i4')
            c2 = len(raw_g) // sum(counts)
            raw_g = raw_g.reshape(sum(counts), c2)
            offs = np.concatenate([[0], np.cumsum(counts)])
            angle_at.append([np.arctan2(raw_g[offs[i]:offs[i + 1], c2 // 2:], raw_g[offs[i]:offs[i + 1], :c2 // 2]).astype(np.float32) for i in range(len(counts))])
        CIRCLES = (angle_at[0][0].shape[1],)
    passages = defaultdict(list)
    for r, (key, stretch) in enumerate(keys):
        passages[key].append((stretch, r))
    hers, place_k, recur, even, written = [], [], [], [], []
    reads = {(J, L): [] for J in CIRCLES for L in LEAKS}  # one [letters] row a place
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
        fields = {(J, L): np.zeros((J, nl), dtype=np.complex128) for J in CIRCLES for L in LEAKS}
        last_charge, last_start = 0, {}
        for s, e, w_ in words:
            gap = s - last_start[w_] if w_ in last_start else None
            if gap is not None and joined and last_start[w_] < owner[s][2]:
                part = "earlier_stretch"
            else:
                part = "not_before" if gap is None else ("within_30" if gap <= 30 else "over_30")
            ids = [col_of[b] for b in w_[:MAXLEN]]
            L_ = len(ids)
            # the carries of the word's prefixes: Φ(w_<k) for k = 1..L (the empty prefix's carry is one on every circle)
            phase = np.zeros((L_, max(CIRCLES)))
            for k in range(1, L_):
                if angle_at is None:
                    phase[k] = phase[k - 1] + turns[k - 1, ids[k - 1]]
                else:
                    r0, t0, _ = owner[s + k - 1]
                    k0, local0 = source[r0]
                    phase[k] = phase[k - 1] + angle_at[k0][local0][t0]
            carry = np.exp(1j * phase)
            places = []
            for k in range(1, L_ + 1):
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
                places.append((k, p))
            for (J, L), F in fields.items():
                if not places:
                    break
                ks = [k for k, _ in places]
                g = np.array([1.0 if L is None else math.exp(-(p - last_charge) / L) for _, p in places])
                R = (np.conj(carry[np.array(ks) - 1, :J]) @ F).real / J * g[:, None]
                reads[(J, L)].extend(R)
            onehot = np.zeros((L_, nl))
            onehot[np.arange(L_), ids] = 1.0
            # FROM (a fourth argument, the lead's diagnosis, November 27): the first prefix length charged; at 1 the empty prefix, whose
            # carry is one on every circle, is charged by every word, and its count leaks into every read as its count over √(2J)
            for (J, L), F in fields.items():
                F *= 1.0 if L is None else math.exp(-(e - last_charge) / L)
                if ETA is None:
                    F += carry[FROM - 1:, :J].T @ onehot[FROM - 1:]
                    continue
                # the delta charge: each prefix's carry deposits only the news, the letter that came less what the store already reads
                # there, at the rate ETA, so an address read as its letter takes no more charge and a heavy prefix stands once
                for k in range(FROM - 1, L_):
                    c = carry[k, :J]
                    r = (np.conj(c) @ F).real / J
                    F += ETA * np.outer(c, onehot[k] - r)
            last_charge, last_start[w_] = e, s
    hers = np.array(hers)
    place_k, recur, even, written = np.array(place_k), np.array(recur), np.array(even), np.array(written)
    own = -np.log(hers)
    print(f"CARRY_STORE turns={turns_arg.split(':')[0]} from={FROM} charge={'sum' if ETA is None else f'delta:{ETA}'} letter_places={len(hers)} even={int(even.sum())} odd={int((~even).sum())} her_nats_odd={own[~even].mean():.3f}", flush=True)
    for J in CIRCLES:
        # the store's face is `softmax(β r)` over the letters (the first form, its positive part's share, drowned the one matching item's
        # read under the scatter of the 51 others): the written letter's share under each leak and each β, and the octave of the read's
        # largest entry, the store's own state for the gate
        share, octave = {}, {}
        for L in LEAKS:
            R = np.array(reads[(J, L)])
            top = R.max(1)
            octave[L] = np.clip(np.floor(np.log2(np.maximum(top, 1e-300) * 4.0)), -1, 5).astype(int)
            for beta in BETAS:
                z = beta * R
                z -= z.max(1, keepdims=True)
                c = np.exp(z)
                share[(L, beta)] = c[np.arange(len(R)), written] / c.sum(1)

        def mixed(L, beta, lam, m):
            return -np.log(np.maximum((1 - lam) * hers[m] + lam * share[(L, beta)][m], 1e-300))

        gains = defaultdict(list)
        for name, fit_on, read_on in (("even_to_odd", even, ~even), ("odd_to_even", ~even, even)):
            _, L, beta, lam = min(((mixed(L, b_, lam, fit_on).mean(), L, b_, lam) for L in LEAKS for b_ in BETAS for lam in LAMBDAS), key=lambda t: t[0])
            code = mixed(L, beta, lam, read_on)
            base = own[read_on]
            print(f"CARRY_STORE circles={J} fit={name} leak={L} beta={beta} coefficient={lam} her_nats={base.mean():.3f} joined_nats={code.mean():.3f} gain={base.mean() - code.mean():+.4f}", flush=True)
            # the coefficient set by the store's own state: the place in the word and the octave of the read's largest entry
            gate = np.zeros(len(hers))
            for k in (1, 2, 3, 4):
                for o in range(-1, 6):
                    cell = (place_k == k) & (octave[L] == o)
                    if (fit_on & cell).any():
                        gate[cell] = min(LAMBDAS, key=lambda x: mixed(L, beta, x, fit_on & cell).mean())
            code_gate = -np.log(np.maximum((1 - gate[read_on]) * hers[read_on] + gate[read_on] * share[(L, beta)][read_on], 1e-300))
            for k in (1, 2, 3, 4):
                for part in PARTS:
                    m = (place_k[read_on] == k) & (recur[read_on] == part)
                    if m.sum():
                        g1, g2 = base[m] - code[m], base[m] - code_gate[m]
                        gains[(k, part)].append((g1.mean(), g2.mean()))
                        print(f"CARRY_STORE circles={J} fit={name} place={'rest' if k == 4 else k} part={part} places={int(m.sum())} her_nats={base[m].mean():.3f} gain={g1.mean():+.4f} (±{g1.std() / math.sqrt(m.sum()):.4f}) state_gain={g2.mean():+.4f}", flush=True)
        for (k, part), g in sorted(gains.items()):
            a_, b2 = [x[0] for x in g], [x[1] for x in g]
            print(f"CARRY_STORE circles={J} place={'rest' if k == 4 else k} part={part} gain_mean={np.mean(a_):+.4f} halves_scatter={abs(a_[0] - a_[-1]):.4f} state_gain_mean={np.mean(b2):+.4f} state_scatter={abs(b2[0] - b2[-1]):.4f}", flush=True)

if __name__ == '__main__':
    main()
