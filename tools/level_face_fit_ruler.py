#!/usr/bin/env -S python3 -I
"""level_face_fit_ruler.py CUT ROWS OWN: a ruler (the lead, November 27; the formal thread's G-Z34 of 15:20 UTC). Whether a face the level
could form over a word's first letter, from what it holds with the slow store as its operand, codes those letters better than her own
face does.

From `read-strand-cut ... past links` (CUT): each epoch's restricted state before the level's ticks (`restricted.i64`), its read after
them (`coarse.i32`), the level's clock (`tau.i64`) and the epoch each open place reads (`cut.tsv`); the slow store is built here as the
engine builds it (`Scale::bank`, rings of 2 to 64 sections at one e-fold a turn, charged by the restricted states) and read as a ratio
to its own power, one lane a ring's part. At each word's first letter of the rows of ROWS (a letter after a space or a line feed) the
features are the read epoch's restricted state, its read after the ticks and its bank read (896, standardized); a face over the letter
(a softmax over the letters met, with an L2 shrinkage chosen on a split of the even rows) is fitted on the even rows and read on the odd.
Its code at each odd place is set beside her own code there (OWN: a `read-reach ... law` output's `codes.tsv`, on `2^(−20)` bits), the
difference read by whether the place's word was last met within 30 places, over 30, or not before. Beside it, the same face with no
features (its bias alone: the letters' frequencies at word starts), which knows as the fitted face does that the place holds a letter, so
what the level's features add is the fitted face less that. Outside the machine; codes only,
floats at the exterior.

With a fourth argument FACES (a `read-reach ... faces` output: her face whole at each word's first place; the formal thread, November
27 15:27 UTC), both faces know that the place holds a letter: her face is renormalized over the letters, and an offset fit reads the
handing question directly, her letter-renormalized log face as a fixed offset (coefficient one) and the level's features beside it, with
its shrinkage chosen on a split of the fitting half from a grid whose largest member leaves her face nearly as it is. It is fitted on
the even rows and read on the odd, then fitted on the odd and read on the even; the two halves' gains, by part, are its scatter.
"""
import math
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
import bank_tension_ruler as B  # noqa: E402

LN2_20 = math.log(2) / (1 << 20)


def fit_softmax(X, y, k, lam, steps=400, lr=0.05):
    """A softmax over `k` classes, `W` (`[F][k]`) and `b`, by Adam on the mean cross-entropy plus `lam |W|²/2`."""
    n, f = X.shape
    W, b = np.zeros((f, k)), np.zeros(k)
    mW, vW, mb, vb = np.zeros_like(W), np.zeros_like(W), np.zeros_like(b), np.zeros_like(b)
    Y = np.zeros((n, k))
    Y[np.arange(n), y] = 1.0
    for s in range(1, steps + 1):
        z = X @ W + b
        z -= z.max(axis=1, keepdims=True)
        p = np.exp(z)
        p /= p.sum(axis=1, keepdims=True)
        gW = X.T @ (p - Y) / n + lam * W
        gb = (p - Y).mean(axis=0)
        for g, m, v, w in ((gW, mW, vW, W), (gb, mb, vb, b)):
            m *= 0.9
            m += 0.1 * g
            v *= 0.999
            v += 0.001 * g * g
            w -= lr * (m / (1 - 0.9 ** s)) / (np.sqrt(v / (1 - 0.999 ** s)) + 1e-8)
    return W, b


def fit_offset(X, O, y, k, lam, steps=400, lr=0.05):
    """A face `O + X W + b` over `k` classes with the offset `O` (`[n][k]`, log masses) held at coefficient one, by Adam on the mean
    cross-entropy plus `lam |W|²/2`."""
    n, f = X.shape
    W, b = np.zeros((f, k)), np.zeros(k)
    mW, vW, mb, vb = np.zeros_like(W), np.zeros_like(W), np.zeros_like(b), np.zeros_like(b)
    Y = np.zeros((n, k))
    Y[np.arange(n), y] = 1.0
    for s in range(1, steps + 1):
        z = O + X @ W + b
        z -= z.max(axis=1, keepdims=True)
        p = np.exp(z)
        p /= p.sum(axis=1, keepdims=True)
        gW = X.T @ (p - Y) / n + lam * W
        gb = (p - Y).mean(axis=0)
        for g, m, v, w in ((gW, mW, vW, W), (gb, mb, vb, b)):
            m *= 0.9
            m += 0.1 * g
            v *= 0.999
            v += 0.001 * g * g
            w -= lr * (m / (1 - 0.9 ** s)) / (np.sqrt(v / (1 - 0.999 ** s)) + 1e-8)
    return W, b


def offset_codes(X, O, y, W, b):
    z = O + X @ W + b
    z -= z.max(axis=1, keepdims=True)
    logp = z - np.log(np.exp(z).sum(axis=1, keepdims=True))
    return -logp[np.arange(len(y)), y]


def codes(X, y, W, b):
    z = X @ W + b
    z -= z.max(axis=1, keepdims=True)
    logp = z - np.log(np.exp(z).sum(axis=1, keepdims=True))
    return -logp[np.arange(len(y)), y]


def main():
    d, rows_f, own_d = sys.argv[1], sys.argv[2], sys.argv[3]
    dims = dict(line.split('\t') for line in open(f'{d}/dims.tsv').read().split('\n') if line)
    d1 = int(dims['coarse'])
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    own = {}
    for line in open(f'{own_d}/codes.tsv'):
        f = line.rstrip('\n').split('\t')
        own[(int(f[0]), int(f[2]))] = int(f[3]) * LN2_20
    cuts = []
    for line in open(f'{d}/cut.tsv'):
        f = line.rstrip('\n').split('\t')
        source = [None if s == '-' else int(s) for s in f[3].split(',')] if len(f) > 3 and f[3] else []
        cuts.append((int(f[0]), int(f[1]), [int(a) for a in f[2].split(',') if a], source))
    e_all = sum(len(c[2]) for c in cuts)
    x1 = np.fromfile(f'{d}/restricted.i64', dtype='<i8').astype(np.float64).reshape(e_all, d1)
    coarse = np.fromfile(f'{d}/coarse.i32', dtype='<i4').astype(np.float64).reshape(e_all, d1)
    tau = np.fromfile(f'{d}/tau.i64', dtype='<i8').astype(np.float64) / 2.0 ** 24
    letter = lambda b_: 65 <= b_ <= 90 or 97 <= b_ <= 122
    her = None
    if len(sys.argv) > 4:
        fd = sys.argv[4]
        byte_class = {}
        for line in open(f'{fd}/classes.tsv'):
            f = line.rstrip('\n').split('\t')
            if len(f) > 1 and len(f[1]) == 2:
                byte_class[int(f[1], 16)] = int(f[0])
        index = [tuple(int(v) for v in line.split('\t')[:2]) for line in open(f'{fd}/faces.tsv')]
        alphabet = len(open(f'{fd}/classes.tsv').read().split('\n')) - 1
        raw = np.fromfile(f'{fd}/faces.i32', dtype='<i4').reshape(len(index), alphabet)
        letters = [b_ for b_ in range(256) if letter(b_) and b_ in byte_class]
        cols = [byte_class[b_] for b_ in letters]
        # her log masses over the letters, renormalized: a code on 2^(-20) bits is -log2 p
        logq = -raw[:, cols].astype(np.float64) * LN2_20
        logq -= np.log(np.exp(logq - logq.max(1, keepdims=True)).sum(1, keepdims=True)) + logq.max(1, keepdims=True)
        her = ({key: i for i, key in enumerate(index)}, logq, letters)
    feats, ys, side, last, own_code, offs = [], [], [], [], [], []
    e0 = 0
    for r, n, anchors, source in cuts:
        k = len(anchors)
        bank = B.lanes(B.bank_of(x1[e0:e0 + k], tau[e0:e0 + k], B.PERIODS))
        text = texts[r][:n]
        seen, i = {}, 0
        word_at = {}
        while i < n:
            if letter(text[i]):
                j = i
                while j < n and letter(text[j]):
                    j += 1
                w = bytes(text[i:j])
                word_at[i] = i - seen[w] if w in seen else None
                seen[w] = i
                i = j
            else:
                i += 1
        for p, j in enumerate(source):
            if j is None or p == 0 or not (letter(text[p]) and text[p - 1] in (32, 10)) or (r, p) not in own:
                continue
            if her is not None:
                if (r, p) not in her[0]:
                    continue
                offs.append(her[1][her[0][(r, p)]])
            feats.append(np.concatenate([x1[e0 + j], coarse[e0 + j], bank[j]]))
            ys.append(text[p])
            side.append(r % 2 == 0)
            gap = word_at.get(p)
            last.append("not_before" if gap is None else ("within_30" if gap <= 30 else "over_30"))
            own_code.append(own[(r, p)])
        e0 += k
    X = np.array(feats)
    X = (X - X.mean(0)) / (X.std(0) + 1e-12)
    classes = sorted(set(ys))
    at = {c: i for i, c in enumerate(classes)}
    y = np.array([at[c] for c in ys])
    side, last, own_code = np.array(side), np.array(last), np.array(own_code)
    tr, te = np.where(side)[0], np.where(~side)[0]
    a, b_ = tr[: len(tr) // 2], tr[len(tr) // 2:]
    best, best_lam = 1e9, 1e-3
    for lam in (1e-4, 1e-3, 1e-2, 1e-1):
        W, bb = fit_softmax(X[a], y[a], len(classes), lam)
        c = codes(X[b_], y[b_], W, bb).mean()
        if c < best:
            best, best_lam = c, lam
    W, bb = fit_softmax(X[tr], y[tr], len(classes), best_lam)
    face = codes(X[te], y[te], W, bb)
    label = d.rstrip('/').split('/')[-1]
    W0, b0 = fit_softmax(np.zeros((len(tr), 1)), y[tr], len(classes), 0.0)
    bare = codes(np.zeros((len(te), 1)), y[te], W0, b0)
    print(f"LEVEL_FACE_FIT {label} bias_alone_nats={bare.mean():.3f}")
    print(f"LEVEL_FACE_FIT {label} first_letters_odd={len(te)} classes={len(classes)} shrinkage={best_lam} face_nats={face.mean():.3f} own_nats={own_code[te].mean():.3f} face_less_own={face.mean() - own_code[te].mean():+.3f}")
    for part in ("within_30", "over_30", "not_before"):
        m = last[te] == part
        if m.sum():
            diff = face[m] - own_code[te][m]
            print(f"LEVEL_FACE_FIT {label} part={part} places={int(m.sum())} face_nats={face[m].mean():.3f} own_nats={own_code[te][m].mean():.3f} face_less_own={diff.mean():+.3f} (±{diff.std() / math.sqrt(m.sum()):.3f})")
    if her is None:
        return
    # Both faces know the place holds a letter: her face renormalized over the letters, the fits over the letters met (columns in
    # `her[2]`'s order, so the offset and the fit share their classes).
    at_l = {c: i for i, c in enumerate(her[2])}
    yl = np.array([at_l[c] for c in ys])
    O = np.array(offs)
    k = len(her[2])
    hers = -O[np.arange(len(yl)), yl]
    print(f"LEVEL_FACE_OFFSET {label} letters={k} places={len(yl)} her_renormalized_nats_odd={hers[te].mean():.3f} her_renormalized_nats_even={hers[tr].mean():.3f} own_nats_odd={own_code[te].mean():.3f}")
    gains = {}
    for name, fit_on, read_on in (("even_to_odd", tr, te), ("odd_to_even", te, tr)):
        a, b_ = fit_on[: len(fit_on) // 2], fit_on[len(fit_on) // 2:]
        best, best_lam = 1e9, 1.0
        for lam in (1e-2, 1e-1, 1.0, 10.0):
            W, bb = fit_offset(X[a], O[a], yl[a], k, lam)
            c = offset_codes(X[b_], O[b_], yl[b_], W, bb).mean()
            if c < best:
                best, best_lam = c, lam
        W, bb = fit_offset(X[fit_on], O[fit_on], yl[fit_on], k, best_lam)
        fitted = offset_codes(X[read_on], O[read_on], yl[read_on], W, bb)
        Wb, bb0 = fit_offset(np.zeros((len(fit_on), 1)), O[fit_on], yl[fit_on], k, 0.0)
        biased = offset_codes(np.zeros((len(read_on), 1)), O[read_on], yl[read_on], Wb, bb0)
        print(f"LEVEL_FACE_OFFSET {label} fit={name} shrinkage={best_lam} offset_fit_nats={fitted.mean():.3f} offset_bias_alone_nats={biased.mean():.3f} her_nats={hers[read_on].mean():.3f} gain={hers[read_on].mean() - fitted.mean():+.4f}")
        for part in ("within_30", "over_30", "not_before"):
            m = last[read_on] == part
            if m.sum():
                g = hers[read_on][m] - fitted[m]
                gains.setdefault(part, []).append(g.mean())
                print(f"LEVEL_FACE_OFFSET {label} fit={name} part={part} places={int(m.sum())} her_nats={hers[read_on][m].mean():.3f} offset_fit_nats={fitted[m].mean():.3f} gain={g.mean():+.4f} (±{g.std() / math.sqrt(m.sum()):.4f}) bias_alone_gain={(hers[read_on][m] - biased[m]).mean():+.4f}")
    for part, g in gains.items():
        print(f"LEVEL_FACE_OFFSET {label} part={part} gain_mean={np.mean(g):+.4f} halves_scatter={abs(g[0] - g[-1]):.4f}")
    # The ruler's null held to a planted law: beside the level's features, the written letter's own column at three places in ten
    # (another letter's at the rest), fitted and read as above; the fit recovers it as a gain over her face.
    rng = np.random.default_rng(27)
    hit = rng.random(len(yl)) < 0.3
    planted = np.zeros((len(yl), k))
    planted[np.arange(len(yl)), np.where(hit, yl, rng.integers(0, k, len(yl)))] = 1.0
    Xp = np.concatenate([X, (planted - planted.mean(0)) / (planted.std(0) + 1e-12)], axis=1)
    a, b_ = tr[: len(tr) // 2], tr[len(tr) // 2:]
    best, best_lam = 1e9, 1.0
    for lam in (1e-2, 1e-1, 1.0, 10.0):
        W, bb = fit_offset(Xp[a], O[a], yl[a], k, lam)
        c = offset_codes(Xp[b_], O[b_], yl[b_], W, bb).mean()
        if c < best:
            best, best_lam = c, lam
    W, bb = fit_offset(Xp[tr], O[tr], yl[tr], k, best_lam)
    fitted = offset_codes(Xp[te], O[te], yl[te], W, bb)
    print(f"LEVEL_FACE_OFFSET {label} planted=letter_three_in_ten shrinkage={best_lam} offset_fit_nats={fitted.mean():.3f} her_nats={hers[te].mean():.3f} gain={hers[te].mean() - fitted.mean():+.4f}")


if __name__ == '__main__':
    main()
