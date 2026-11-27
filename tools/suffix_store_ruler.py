#!/usr/bin/env -S python3 -I
"""suffix_store_ruler.py ROWS FACES KEY J [joined]: a ruler (the lead, November 27; the formal thread's G-Z49 and G-Z50 of 19:28 UTC). A
carry-keyed store over every symbol of the passage, keyed with no cut or by a cut, joined to her face by the joined face's covector.

FACES is a `read-reach … faces:all` output in step with ROWS (comma-separated lists, as `word_cache_ruler.py` reads them); a place's symbol
is the class `faces.tsv` names as written there. A key is a carry on `J` circles, `χ = e^(iΣ_d θ(u_(p−d), d))` over a run of the symbols
before the place, each class's turn at each distance drawn once (an identity key). KEY names the runs:
  suffix   the last `k` places for `k = 1` to 8, each its own address (no cut);
  located  the same, but the address of `k + 1` places is charged only where the address of `k` read the symbol that came above the field's
           own noise, `√(n/2J)` with `n` the charges the field has taken in the passage (depth located as a chain becomes a part);
  floor    located depth with the field's own background as its floor, a symbol's read at a carry no charge has met,
           `√(‖F‖²/(2J²A))` (the formal thread's arm of 19:50 UTC);
  word     one address, the run since the last space or line's end (a cut: the writers' words, the codec's), up to 64 places.
At each place each address reads `r = Re(χ* F)/J` over the symbols met; the joined face is `p ∝ q · e^(Σ_k (g_k + a_k ρ_k) r_k)`, `q` her
face at the place and `ρ_k` the address's read power (its largest read), so a slope rises with how much the store has met that address
(the formal pass's law: the coefficient is the store's own temperature). After the read each address is charged at `η = 1/4` with the joined
face's covector, `(g_k + a_k ρ_k)(e − p_joined)` (the joint charge), at the slopes an `own` walk (each address charged with its news,
`e − r_k`) fitted on that half; the slopes are fitted again on the joint walk's reads on the fitting half and read on the other half, and
back. By the symbol's kind (a letter, a space or a line's end, any other) and, for a letter, by its place in its word and where the word was
last met (`earlier_stretch` with `joined`). Outside the machine; floats at the exterior.
"""
import math
import multiprocessing as mp
import os
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from word_cache_ruler import LN2_20, PARTS, letter  # noqa: E402

ETA = 0.25
DEPTH = 8
EXPONENT = False
WORKERS = int(os.environ.get('RULER_WORKERS', '1'))
_ONE = None


def _run(key):
    return _ONE(key)
WORD_RUN = 64


def features(R):
    """The read and the read scaled by its power, `[n][2K][A]`."""
    rho = R.max(2, keepdims=True)
    return np.concatenate([R, rho * R], axis=1)


def fit_slopes(X, logq, ys, m, steps=300):
    """Slopes (`2K`) minimizing the mean code of `softmax(logq + Σ_j s_j X_j)` at the places `m`, by Adam on draws of the places."""
    idx = np.where(m)[0]
    s_, ms, vs = np.zeros(X.shape[1]), np.zeros(X.shape[1]), np.zeros(X.shape[1])
    for step in range(1, steps + 1):
        sub = idx[np.random.default_rng(step).integers(0, len(idx), min(len(idx), 20000))]
        z = logq[sub] + np.einsum('j,nja->na', s_, X[sub])
        z -= z.max(1, keepdims=True)
        p = np.exp(z)
        p /= p.sum(1, keepdims=True)
        grad = (np.einsum('na,nja->nj', p, X[sub]) - X[sub][np.arange(len(sub)), :, ys[sub]]).mean(0)
        ms = 0.9 * ms + 0.1 * grad
        vs = 0.999 * vs + 0.001 * grad * grad
        s_ -= 0.05 * (ms / (1 - 0.9 ** step)) / (np.sqrt(vs / (1 - 0.999 ** step)) + 1e-8)
    return s_


def codes(X, logq, ys, s_):
    z = logq + np.einsum('j,nja->na', s_, X)
    z -= z.max(1, keepdims=True)
    return -(z[np.arange(len(ys)), ys] - np.log(np.exp(z).sum(1)))


def main():
    rows_fs, fds, key_mode, J = sys.argv[1].split(','), sys.argv[2].split(','), sys.argv[3], int(sys.argv[4])
    joined = len(sys.argv) > 5 and sys.argv[5] == 'joined'
    # `exponent` (a sixth argument, the formal thread's G-Z57 of 20:45 UTC): beside the global form, its per-address exponent arm
    global EXPONENT
    EXPONENT = len(sys.argv) > 6 and sys.argv[6] == 'exponent'
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
    # the symbols the passages write, the store's columns (her face renormalized over them)
    met = sorted({c for w in written for c in w.values()})
    col = {c: i for i, c in enumerate(met)}
    A = len(met)
    run = DEPTH if key_mode in ('suffix', 'located', 'floor') else WORD_RUN
    turns = np.random.default_rng(1127).uniform(0, 2 * np.pi, (run, A, J))
    nk = DEPTH if key_mode in ('suffix', 'located', 'floor') else 1
    passages = defaultdict(list)
    for r, (key, stretch) in enumerate(keys):
        passages[key].append((stretch, r))

    def walk(slopes, read_slopes=None):
        def one(key):
            logqs, reads, ys, kind, place_k, recur, even = [], [], [], [], [], [], []
            arm_codes = []
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
            Bf = np.zeros(J, dtype=np.complex128)
            n_charged = 0
            for p in range(1, n):
                r, t, _ = owner[p]
                k_, local = source[r]
                y = cls[p]
                if y is None:
                    continue
                if key_mode == 'word':
                    span = 0
                    while span < WORD_RUN and p - span - 1 >= 0 and cls[p - span - 1] is not None and text[p - span - 1] not in (32, 10):
                        span += 1
                    lengths = [span] if span > 0 else []
                else:
                    lengths = []
                    for k in range(1, DEPTH + 1):
                        if p - k < 0 or cls[p - k] is None:
                            break
                        lengths.append(k)
                carries, phase = [], np.zeros(J)
                for k in range(1, (max(lengths) if lengths else 0) + 1):
                    phase = phase + turns[k - 1, cls[p - k]]
                    if (key_mode == 'word' and k == lengths[0]) or key_mode != 'word':
                        carries.append(np.exp(1j * phase))
                # every depth's address read in one pass over the field, `R = Re(C* F)/J` (C the carries, a row a depth)
                R = np.zeros((nk, A))
                Cm = np.array(carries) if carries else np.zeros((0, J), dtype=np.complex128)
                if carries:
                    R[:len(carries)] = (np.conj(Cm) @ F).real / J
                logq = -np.asarray(raws[k_][ats[k_][(local, t)], met], dtype=np.float64) * LN2_20
                logq -= logq.max()
                logq -= np.log(np.exp(logq).sum())
                logqs.append(logq.astype(np.float32))
                reads.append(R.astype(np.float32))
                ys.append(y)
                b = text[p]
                kind.append('letter' if letter(b) else ('space' if b in (32, 10) else 'other'))
                place_k.append(word_k[p])
                recur.append(word_part[p] or '-')
                even.append(halves[r])
                e = np.zeros(A)
                e[y] = 1.0
                if slopes is not None:
                    X = features(R[None])[0]
                    z = logq + np.einsum('j,ja->a', slopes, X)
                    z -= z.max()
                    pj = np.exp(z)
                    pj /= pj.sum()
                    rho = R.max(1)
                if read_slopes is not None:
                    # the arm (the formal thread's G-Z57): each depth's exponent `g_k + a_k ρ_k + β_k`, with `β_k = Re⟨B, χ_k⟩/J` read
                    # from its own field `B`, charged by the exponent's own covector `r_k(y) − E_p[r_k]`; F is charged as without it
                    rho_ = R.max(1)
                    beta = np.zeros(nk)
                    if carries:
                        beta[:len(carries)] = (np.conj(Cm) @ Bf).real / J
                    lam = read_slopes[:nk] + read_slopes[nk:] * rho_ + beta
                    za = logq + lam @ R
                    za -= za.max()
                    pa = np.exp(za)
                    pa /= pa.sum()
                    arm_codes.append(-math.log(max(pa[y], 1e-300)))
                    if carries:
                        D = len(carries)
                        Bf += ETA * (Cm.T @ (R[:D, y] - R[:D] @ pa))
                noise = math.sqrt(max(n_charged, 1) / (2 * J))
                if key_mode == 'floor':
                    # the field's own background: a symbol's read at a carry no charge has met, `√(‖F‖² / (2 J² A))`
                    noise = math.sqrt(float(np.vdot(F, F).real) / (2 * J * J * A))
                # every depth's address charged in one pass over the field (the reads stand before any charge at the place, so the
                # depths' charges sum); located depth: the address of k + 1 places is charged only where the address of k read the
                # symbol above the noise
                D = len(carries)
                if key_mode in ('located', 'floor'):
                    for k in range(1, D):
                        if R[k - 1, y] <= noise:
                            D = k
                            break
                if D:
                    if slopes is None:
                        F += ETA * (Cm[:D].T @ (e[None, :] - R[:D]))
                    else:
                        coef = slopes[:D] + slopes[nk:nk + D] * rho[:D]
                        F += ETA * np.outer(Cm[:D].T @ coef, e - pj)
                    n_charged += D
            return logqs, reads, ys, kind, place_k, recur, even, n_charged, arm_codes

        # the passages are independent (each its own field), so they are walked on WORKERS processes and joined in their order
        global _ONE
        _ONE = one
        with mp.get_context("fork").Pool(WORKERS) as pool:
            parts = pool.map(_run, list(passages))
        cat = lambda j: [v for part in parts for v in part[j]]
        return (np.array(cat(0)), np.array(cat(1)), np.array(cat(2)), np.array(cat(3)), np.array(cat(4)), np.array(cat(5)), np.array(cat(6)), sum(part[7] for part in parts), np.array(cat(8)))

    logq, R, ys, kind, place_k, recur, even, charged_own, _ = walk(None)
    own = -logq[np.arange(len(ys)), ys]
    print(f"SUFFIX_STORE key={key_mode} J={J} symbols={A} places={len(ys)} her_nats_odd={own[~even].mean():.4f} her_nats_even={own[even].mean():.4f} charged_own={charged_own}", flush=True)
    X = features(R)
    halves_ = (("even_to_odd", even, ~even), ("odd_to_even", ~even, even))
    own_fit = {name: fit_slopes(X, logq, ys, fit_on) for name, fit_on, _ in halves_}
    gains = defaultdict(list)
    for name, fit_on, read_on in halves_:
        res = walk(own_fit[name])
        Rj, charged = res[1], res[7]
        Xj = features(Rj)
        s_ = fit_slopes(Xj, logq, ys, fit_on)
        code = codes(Xj, logq, ys, s_)
        own_code = codes(X, logq, ys, own_fit[name])
        print(f"SUFFIX_STORE fit={name} charged={charged} slopes={','.join(f'{v:.2f}' for v in s_)} her_nats={own[read_on].mean():.4f} joint_nats={code[read_on].mean():.4f} gain={own[read_on].mean() - code[read_on].mean():+.4f} own_charge_gain={own[read_on].mean() - own_code[read_on].mean():+.4f}", flush=True)
        gains[('all',)].append(own[read_on].mean() - code[read_on].mean())
        for kd in ('letter', 'space', 'other'):
            m = read_on & (kind == kd)
            gains[('kind', kd)].append((own[m] - code[m]).mean())
            print(f"SUFFIX_STORE fit={name} kind={kd} places={int(m.sum())} her_nats={own[m].mean():.4f} gain={(own[m] - code[m]).mean():+.4f}", flush=True)
        for k in (1, 2, 3, 4):
            for part in PARTS:
                m = read_on & (kind == 'letter') & (place_k == k) & (recur == part)
                if m.sum():
                    gm = own[m] - code[m]
                    gains[(k, part)].append(gm.mean())
                    print(f"SUFFIX_STORE fit={name} place={'rest' if k == 4 else k} part={part} places={int(m.sum())} her_nats={own[m].mean():.3f} gain={gm.mean():+.4f} (±{gm.std() / math.sqrt(m.sum()):.4f})", flush=True)
        if EXPONENT:
            # the per-address exponent: the same F (the joint walk's own charge), read with the global slopes and each address's β
            arm = walk(own_fit[name], s_)[8]
            gains[('arm', 'all')].append(own[read_on].mean() - arm[read_on].mean())
            print(f"SUFFIX_STORE fit={name} exponent_arm joined_nats={arm[read_on].mean():.4f} gain={own[read_on].mean() - arm[read_on].mean():+.4f}", flush=True)
            for k in (1, 2, 3, 4):
                for part in PARTS:
                    m = read_on & (kind == 'letter') & (place_k == k) & (recur == part)
                    if m.sum():
                        gm = own[m] - arm[m]
                        gains[('arm', k, part)].append(gm.mean())
    for key, gl in sorted(gains.items(), key=lambda t: str(t[0])):
        if key[0] == 'arm':
            label = 'exponent_arm ' + ('all' if key[1] == 'all' else f"place={'rest' if key[1] == 4 else key[1]} part={key[2]}")
        else:
            label = 'all' if key[0] == 'all' else (f"kind={key[1]}" if key[0] == 'kind' else f"place={'rest' if key[0] == 4 else key[0]} part={key[1]}")
        print(f"SUFFIX_STORE {label} gain_mean={np.mean(gl):+.4f} halves_scatter={abs(gl[0] - gl[-1]):.4f}", flush=True)


if __name__ == '__main__':
    main()
