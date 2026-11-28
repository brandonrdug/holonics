#!/usr/bin/env -S python3 -I
"""tree_store_ruler.py ROWS FACES J [joined]: a ruler (the lead, November 27; the formal thread's G-Z55 of 20:10 UTC). Depth located per
address: the suffix store of `suffix_store_ruler.py` (the last `k` places for `k = 1` to 8 on `J` drawn circles, every symbol) with a stop
weight held as a store beside it.

Each depth's address reads its symbols, `r_k = Re(χ_k* F)/J`, and a face `P_k = softmax(τ r_k)` (`τ` one number, chosen on the fitting
half from a grid); and a stop weight `β_k = Re(⟨B, χ_k⟩)/J` from a second field `B` of `J` circles. The store's face mixes the depths down
the flag, `M_k = σ(β_k) P_k + (1 − σ(β_k)) M_(k+1)` from the deepest read (`M_K = P_K`), and joins her face in the log chart,
`p ∝ q · M_1^g`, `g` one slope. After each place is read, `F` takes the joined face's covector at each address,
`η g (e − p_joined)`, and `B` takes at each address the code of going deeper less the code of stopping there,
`η (−log M_(k+1)(y) + log P_k(y))`, so an address whose own face codes the symbol better than what lies under it learns to stop
(the context tree's own weight held as a store). Beside it the same store read by one slope a depth (`suffix_store_ruler.py`'s global
form) is not read here: compare with its receipt at the same `J`. `τ` and `g` are walked over a grid on the fitting half and the best
read on the other half, and back. By the symbol's kind and, for a letter, its place in its word and where the word was last met. Outside
the machine; floats at the exterior.
"""
import math
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from word_cache_ruler import LN2_20, PARTS, letter  # noqa: E402

ETA = 0.25
DEPTH = 8
TAUS = (4.0, 16.0)
SLOPES = (0.5, 1.0)
PASS = False


def sigmoid(x):
    return 1.0 / (1.0 + np.exp(-x))


def main():
    rows_fs, fds, J = sys.argv[1].split(','), sys.argv[2].split(','), int(sys.argv[3])
    joined = len(sys.argv) > 4 and sys.argv[4] == 'joined'
    # `pass:TAU:G` (a fifth argument, the formal thread's G-Z56 of 20:14 UTC): the pass-through at the plain form's own `τ` and `g`
    global PASS, TAUS, SLOPES
    if len(sys.argv) > 5 and sys.argv[5].startswith('pass:'):
        _, tau_, g_ = sys.argv[5].split(':')
        PASS, TAUS, SLOPES = True, (float(tau_),), (float(g_),)
    # `grid:T,…:G,…` (the formal thread, 20:39 UTC): the plain form on a grid of its own, reaching below the first grid's edge
    if len(sys.argv) > 5 and sys.argv[5].startswith('grid:'):
        _, ts, gs = sys.argv[5].split(':')
        TAUS, SLOPES = tuple(float(v) for v in ts.split(',')), tuple(float(v) for v in gs.split(','))
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
    alphabet = len(open(f'{fds[0]}/classes.tsv').read().split('\n')) - 1
    raws, ats, written = [], [], []
    for fd in fds:
        rows_ = [tuple(int(v) for v in line.split('\t')[:3]) for line in open(f'{fd}/faces.tsv')]
        raws.append(np.memmap(f'{fd}/faces.i32', dtype='<i4', mode='r', shape=(len(rows_), alphabet)))
        ats.append({(r, t): i for i, (r, t, _) in enumerate(rows_)})
        written.append({(r, t): c for r, t, c in rows_})
    met = sorted({c for w in written for c in w.values()})
    col = {c: i for i, c in enumerate(met)}
    A = len(met)
    turns = np.random.default_rng(1127).uniform(0, 2 * np.pi, (DEPTH, A, J))
    passages = defaultdict(list)
    for r, (key, stretch) in enumerate(keys):
        passages[key].append((stretch, r))

    def walk(tau, g):
        out = defaultdict(list)
        for key in passages:
            text, owner = b'', []
            for _, r in sorted(passages[key]):
                owner.extend((r, t, len(text)) for t in range(len(texts[r])))
                text += texts[r]
            n = len(text)
            cls = [None] * n
            for p, (r, t, _) in enumerate(owner):
                k_, local = source[r]
                c = written[k_].get((local, t))
                cls[p] = None if c is None else col[c]
            word_part, word_k = [None] * n, [0] * n
            i, last_start = 0, {}
            while i < n:
                if letter(text[i]):
                    j = i
                    while j < n and letter(text[j]):
                        j += 1
                    w = bytes(text[i:j])
                    gap = i - last_start[w] if w in last_start else None
                    part = ("earlier_stretch" if gap is not None and joined and last_start[w] < owner[i][2] else
                            "not_before" if gap is None else ("within_30" if gap <= 30 else "over_30"))
                    for q in range(i, j):
                        word_part[q], word_k[q] = part, min(q - i + 1, 4)
                    last_start[w] = i
                    i = j
                else:
                    i += 1
            F = np.zeros((J, A), dtype=np.complex128)
            B = np.zeros(J, dtype=np.complex128)
            for p in range(1, n):
                r, t, _ = owner[p]
                k_, local = source[r]
                y = cls[p]
                if y is None:
                    continue
                carries, phase = [], np.zeros(J)
                for k in range(1, DEPTH + 1):
                    if p - k < 0 or cls[p - k] is None:
                        break
                    phase = phase + turns[k - 1, cls[p - k]]
                    carries.append(np.exp(1j * phase))
                logq = -np.asarray(raws[k_][ats[k_][(local, t)], met], dtype=np.float64) * LN2_20
                logq -= logq.max()
                logq -= np.log(np.exp(logq).sum())
                e = np.zeros(A)
                e[y] = 1.0
                if carries:
                    D = len(carries)
                    R = np.stack([(np.conj(c) @ F).real / J for c in carries])
                    beta = np.array([(np.conj(c) @ B).real / J for c in carries])
                    z = tau * R
                    z -= z.max(1, keepdims=True)
                    P = np.exp(z)
                    P /= P.sum(1, keepdims=True)
                    M = [None] * D
                    M[D - 1] = P[D - 1]
                    # PASS: where the deeper address reads at the field's background or under (the largest of `A` symbols' reads at a
                    # carry no charge has met, `σ √(2 ln A)` with `σ = √(‖F‖²/(2J²A))`), the depth stops there, `M_k = P_k`
                    floor = math.sqrt(float(np.vdot(F, F).real) / (2 * J * J * A)) * math.sqrt(2 * math.log(A)) if PASS else None
                    for k in range(D - 2, -1, -1):
                        if PASS and R[k + 1].max() <= floor:
                            M[k] = P[k]
                            continue
                        s_ = sigmoid(beta[k])
                        M[k] = s_ * P[k] + (1 - s_) * M[k + 1]
                    zj = logq + g * np.log(np.maximum(M[0], 1e-300))
                    zj -= zj.max()
                    pj = np.exp(zj)
                    pj /= pj.sum()
                    code = -math.log(max(pj[y], 1e-300))
                    for k, c in enumerate(carries):
                        F += ETA * g * np.outer(c, e - pj)
                        if k + 1 < D:
                            B += ETA * c * (-math.log(max(M[k + 1][y], 1e-300)) + math.log(max(P[k][y], 1e-300)))
                else:
                    code = -logq[y]
                out['code'].append(code)
                out['own'].append(-logq[y])
                b = text[p]
                out['kind'].append('letter' if letter(b) else ('space' if b in (32, 10) else 'other'))
                out['place_k'].append(word_k[p])
                out['recur'].append(word_part[p] or '-')
                out['even'].append(halves[r])
        return {k: np.array(v) for k, v in out.items()}

    runs = {(tau, g): walk(tau, g) for tau in TAUS for g in SLOPES}
    any_ = next(iter(runs.values()))
    own, kind, place_k, recur, even = any_['own'], any_['kind'], any_['place_k'], any_['recur'], any_['even']
    print(f"TREE_STORE pass={PASS} J={J} symbols={A} places={len(own)} her_nats_odd={own[~even].mean():.4f}", flush=True)
    gains = defaultdict(list)
    for name, fit_on, read_on in (("even_to_odd", even, ~even), ("odd_to_even", ~even, even)):
        tau, g = min(runs, key=lambda tg: runs[tg]['code'][fit_on].mean())
        code = runs[(tau, g)]['code']
        print(f"TREE_STORE fit={name} tau={tau} slope={g} her_nats={own[read_on].mean():.4f} joined_nats={code[read_on].mean():.4f} gain={own[read_on].mean() - code[read_on].mean():+.4f}", flush=True)
        gains[('all',)].append(own[read_on].mean() - code[read_on].mean())
        for kd in ('letter', 'space', 'other'):
            m = read_on & (kind == kd)
            gains[('kind', kd)].append((own[m] - code[m]).mean())
        for k in (1, 2, 3, 4):
            for part in PARTS:
                m = read_on & (kind == 'letter') & (place_k == k) & (recur == part)
                if m.sum():
                    gm = own[m] - code[m]
                    gains[(k, part)].append(gm.mean())
                    print(f"TREE_STORE fit={name} place={'rest' if k == 4 else k} part={part} places={int(m.sum())} her_nats={own[m].mean():.3f} gain={gm.mean():+.4f} (±{gm.std() / math.sqrt(m.sum()):.4f})", flush=True)
    for key, gl in sorted(gains.items(), key=lambda t: str(t[0])):
        label = 'all' if key[0] == 'all' else (f"kind={key[1]}" if key[0] == 'kind' else f"place={'rest' if key[0] == 4 else key[0]} part={key[1]}")
        print(f"TREE_STORE {label} gain_mean={np.mean(gl):+.4f} halves_scatter={abs(gl[0] - gl[-1]):.4f}", flush=True)


if __name__ == '__main__':
    main()
