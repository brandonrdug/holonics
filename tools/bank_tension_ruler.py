#!/usr/bin/env -S python3 -I
"""bank_tension_ruler.py CUT ROWS: a ruler (the lead, November 27; the formal thread's premise of 14:41 UTC, G-Z25 and G-Z26). What the
slow store's read holds beyond its own standing part, and what of the fine covector at the level's locus it can remove.

From `read-strand-cut ... past links` (CUT): each epoch's restricted state before the level's ticks (`restricted.i64`), the level's clock
(`tau.i64`), the epoch each open place reads (`cut.tsv`) and the covector at the level's locus at each open place (`lambda.i64`). The bank
is built here as the engine builds it (`Scale::bank`: rings of 2 to 64 sections of news, one e-fold a turn), charged two ways:
  charged   with `x¹_j` whole, as built;
  centered  with `x¹_j − x̄¹`, `x̄¹` the restricted states' mean over the even rows' epochs (the level's standing state: the formal
            thread's law, the same anchor as the join's rest).
G-Z25: the standing part (each ring's response to `x̄¹` alone through the same turns, the rise at a stretch's start included), its share of
the charged bank's power over the odd rows' epochs, by ring and whole.
G-Z26: each open place's bank read (the bank of the epoch it reads, read as a ratio to its own power one lane a ring's part, as the
level's block reads it) taken as a linear read of the covector at the level's locus, fitted by ridge regression on the even rows (the
shrinkage chosen on a split of them) and read on the odd: the share of the covector's power it removes, at a word's first letter and at
every place, charged and centered; where the dump holds the open places' news harmonics (`open_harmonics.i64`, `[n][H]`), also in the
full form `B_bank` reads, `h(φ_t) ⊗ r̂(bank_j)` (`H` times as wide), at a word's first letter, and in that form up to its harmonic basis:
one 768-wide map for each sixth of the news phase, each fitted on its own places (the formal thread's G-Z28, with its planted tenth in
that form); and the ruler's proof (rule 11): the same read of a planted covector, the real one plus a linear
image of the centered reads holding a tenth of its power, which a sound read recovers near 0.1. Outside the machine; shares only, floats at
the exterior.
"""
import sys

import numpy as np

PERIODS = (2, 4, 8, 16, 32, 64)


def bank_of(x, tau, periods):
    """The bank over one region's epochs: `m_P(j) = e^(−Δτ/P) e^(−2πi Δτ/P) m_P(j − 1) + x_j`, `[j][R][D₁]` complex."""
    m = np.zeros((len(periods), x.shape[1]), dtype=np.complex128)
    out = np.zeros((x.shape[0], len(periods), x.shape[1]), dtype=np.complex128)
    for j in range(x.shape[0]):
        dt = tau[j] - tau[j - 1] if j > 0 else 0.0
        for q, p in enumerate(periods):
            m[q] = (m[q] * np.exp(-dt / p) * np.exp(-2j * np.pi * dt / p) if j > 0 else 0) + x[j]
        out[j] = m
    return out


def lanes(b):
    """A bank read as a ratio to its own power, one lane a ring's real or imaginary part: `[j][2 R D₁]`."""
    parts = np.concatenate([b.real, b.imag], axis=1)  # [j][2R][D1]
    rms = np.sqrt((parts ** 2).mean(axis=2, keepdims=True))
    return (parts / np.where(rms > 0, rms, 1.0)).reshape(b.shape[0], -1)


def main():
    d, rows_f = sys.argv[1], sys.argv[2]
    dims = dict(line.split('\t') for line in open(f'{d}/dims.tsv').read().split('\n') if line)
    d0, d1 = int(dims['read']), int(dims['coarse'])
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    cuts = []
    for line in open(f'{d}/cut.tsv'):
        f = line.rstrip('\n').split('\t')
        source = [None if s == '-' else int(s) for s in f[3].split(',')] if len(f) > 3 and f[3] else []
        cuts.append((int(f[0]), int(f[1]), [int(a) for a in f[2].split(',') if a], source))
    e_all = sum(len(c[2]) for c in cuts)
    n_all = sum(c[1] for c in cuts)
    x1 = np.fromfile(f'{d}/restricted.i64', dtype='<i8').astype(np.float64).reshape(e_all, d1)
    tau = np.fromfile(f'{d}/tau.i64', dtype='<i8').astype(np.float64) / 2.0 ** 24
    lam = np.fromfile(f'{d}/lambda.i64', dtype='<i8').astype(np.float64).reshape(n_all, d0)
    letter = lambda b: 65 <= b <= 90 or 97 <= b <= 122
    # the standing state: the mean restricted state over the even rows' epochs
    e0, evens = 0, []
    for r, n, anchors, _ in cuts:
        if r % 2 == 0:
            evens.append(x1[e0:e0 + len(anchors)])
        e0 += len(anchors)
    xbar = np.concatenate(evens).mean(axis=0)
    import os
    oh = np.fromfile(f'{d}/open_harmonics.i64', dtype='<i8').astype(np.float64) / 2.0 ** 30 if os.path.exists(f'{d}/open_harmonics.i64') else None
    H = oh.size // n_all if oh is not None else 0
    if oh is not None:
        oh = oh.reshape(n_all, H)
    feats = {'charged': [], 'centered': []}
    full = {'charged': [], 'centered': []}
    sixth = []
    target, first, side = [], [], []
    stand_p, total_p = np.zeros(len(PERIODS)), np.zeros(len(PERIODS))
    e0 = p0 = 0
    for r, n, anchors, source in cuts:
        k = len(anchors)
        xs, ts = x1[e0:e0 + k], tau[e0:e0 + k]
        charged = bank_of(xs, ts, PERIODS)
        centered = bank_of(xs - xbar, ts, PERIODS)
        standing = bank_of(np.tile(xbar, (k, 1)), ts, PERIODS)
        if r % 2 == 1:
            stand_p += (np.abs(standing) ** 2).sum(axis=(0, 2))
            total_p += (np.abs(charged) ** 2).sum(axis=(0, 2))
        lc, lz = lanes(charged), lanes(centered)
        text = texts[r][:n]
        for p, j in enumerate(source):
            if j is None:
                continue
            feats['charged'].append(lc[j])
            feats['centered'].append(lz[j])
            is_first = p < len(text) and letter(text[p]) and (p == 0 or text[p - 1] in (32, 10))
            if oh is not None and is_first:
                full['charged'].append((np.kron(oh[p0 + p], lc[j]), len(target)))
                full['centered'].append((np.kron(oh[p0 + p], lz[j]), len(target)))
                sixth.append((int(((np.arctan2(oh[p0 + p][2], oh[p0 + p][1]) / (2 * np.pi)) % 1.0) * 6) % 6, len(target)))
            target.append(lam[p0 + p])
            first.append(p < len(text) and letter(text[p]) and (p == 0 or text[p - 1] in (32, 10)))
            side.append(r % 2 == 0)
        e0 += k
        p0 += n
    label = d.rstrip('/').split('/')[-1]
    print(f"BANK_STANDING {label} share_of_power=" + f"{stand_p.sum() / total_p.sum():.3f} by_ring " + ' '.join(f"P{p}={s / t:.3f}" for p, s, t in zip(PERIODS, stand_p, total_p)))
    Y = np.array(target)
    Y = Y / (np.sqrt((Y ** 2).mean()) or 1.0)
    side, first = np.array(side), np.array(first)
    tr, te = np.where(side)[0], np.where(~side)[0]
    a, b = tr[: len(tr) // 2], tr[len(tr) // 2:]
    rng = np.random.default_rng(20261127)
    Xz = np.array(feats['centered'])
    Xz = (Xz - Xz.mean(0)) / (Xz.std(0) + 1e-12)
    P = Xz @ rng.standard_normal((Xz.shape[1], Y.shape[1]))
    P *= np.sqrt(0.1 / 0.9 * (Y ** 2).sum() / (P ** 2).sum())
    for name, rows, Yt in (('charged', feats['charged'], Y), ('centered', feats['centered'], Y), ('planted', feats['centered'], Y + P)):
        X = np.array(rows)
        Y_ = Yt
        mx = X[tr].mean(0)
        Xc = X - mx
        U, S, Vt = np.linalg.svd(Xc[a], full_matrices=False)
        ya = Y_[a] - Y_[a].mean(0)
        best, best_lam = -1e9, 1.0
        for lam_s in (np.array([0.001, 0.01, 0.1, 1, 10, 100]) * float((S ** 2).mean())):
            W = Vt.T @ ((S / (S * S + lam_s))[:, None] * (U.T @ ya))
            f = Xc[b] @ W + Y_[a].mean(0)
            v = 1.0 - ((Y_[b] - f) ** 2).sum() / ((Y_[b] - Y_[a].mean(0)) ** 2).sum()
            if v > best:
                best, best_lam = v, lam_s
        U, S, Vt = np.linalg.svd(Xc[tr], full_matrices=False)
        W = Vt.T @ ((S / (S * S + best_lam * len(tr) / len(a)))[:, None] * (U.T @ (Y_[tr] - Y_[tr].mean(0))))
        f = Xc[te] @ W + Y_[tr].mean(0)
        resid = ((Y_[te] - f) ** 2).sum(axis=1)
        base = ((Y_[te] - Y_[tr].mean(0)) ** 2).sum(axis=1)
        m = first[te]
        print(f"BANK_TENSION {label} charge={name} places={len(te)} share_all={1 - resid.sum() / base.sum():.4f} first_letters={int(m.sum())} share_first={1 - resid[m].sum() / base[m].sum():.4f}")
    if sixth:
        bins = np.array([b_ for b_, _ in sixth])
        idx = np.array([i_ for _, i_ in sixth])
        for name in ('charged', 'centered', 'planted'):
            Xa = np.array(feats['centered' if name == 'planted' else name])[idx]
            Ya = Y[idx]
            if name == 'planted':
                Pp = np.zeros_like(Ya)
                for k_ in range(6):
                    m_ = bins == k_
                    Xz_ = (Xa[m_] - Xa[m_].mean(0)) / (Xa[m_].std(0) + 1e-12)
                    Pp[m_] = Xz_ @ rng.standard_normal((Xa.shape[1], Ya.shape[1]))
                Pp *= np.sqrt(0.1 / 0.9 * (Ya ** 2).sum() / (Pp ** 2).sum())
                Ya = Ya + Pp
            rs = bs = 0.0
            for k_ in range(6):
                m_ = bins == k_
                if m_.sum() < 200:
                    continue
                sd = side[idx][m_]
                tr_, te_ = np.where(sd)[0], np.where(~sd)[0]
                sh = ridge_share(Xa[m_], Ya[m_], sd)
                base_ = ((Ya[m_][te_] - Ya[m_][tr_].mean(0)) ** 2).sum()
                rs += (1 - sh) * base_
                bs += base_
            print(f"BANK_TENSION_SIXTHS {label} charge={name} first_letters={len(idx)} share_first={1 - rs / bs:.4f}")
    for name, rows in full.items():
        if not rows:
            continue
        X = np.array([r_[0] for r_ in rows])
        idx = np.array([r_[1] for r_ in rows])
        Yf, sf = Y[idx], side[idx]
        print(f"BANK_TENSION_FULL {label} charge={name} width={X.shape[1]} first_letters={len(idx)} share_first={ridge_share(X, Yf, sf):.4f}")
        if name == 'centered':
            Xz = (X - X.mean(0)) / (X.std(0) + 1e-12)
            Pf = Xz @ rng.standard_normal((X.shape[1], Yf.shape[1]))
            Pf *= np.sqrt(0.1 / 0.9 * (Yf ** 2).sum() / (Pf ** 2).sum())
            print(f"BANK_TENSION_FULL {label} charge=planted width={X.shape[1]} first_letters={len(idx)} share_first={ridge_share(X, Yf + Pf, sf):.4f}")


def ridge_share(X, Y, side):
    """The share of `Y`'s power a ridge read of `X` removes on the odd rows, fitted on the even (the shrinkage on a split of them)."""
    tr, te = np.where(side)[0], np.where(~side)[0]
    a, b = tr[: len(tr) // 2], tr[len(tr) // 2:]
    mx = X[tr].mean(0)
    Xc = X - mx
    U, S, Vt = np.linalg.svd(Xc[a], full_matrices=False)
    ya = Y[a] - Y[a].mean(0)
    best, best_lam = -1e9, 1.0
    for lam_s in np.array([0.001, 0.01, 0.1, 1, 10, 100]) * float((S ** 2).mean()):
        W = Vt.T @ ((S / (S * S + lam_s))[:, None] * (U.T @ ya))
        v = 1.0 - ((Y[b] - (Xc[b] @ W + Y[a].mean(0))) ** 2).sum() / ((Y[b] - Y[a].mean(0)) ** 2).sum()
        if v > best:
            best, best_lam = v, lam_s
    U, S, Vt = np.linalg.svd(Xc[tr], full_matrices=False)
    W = Vt.T @ ((S / (S * S + best_lam * len(tr) / len(a)))[:, None] * (U.T @ (Y[tr] - Y[tr].mean(0))))
    f = Xc[te] @ W + Y[tr].mean(0)
    return 1.0 - ((Y[te] - f) ** 2).sum() / ((Y[te] - Y[tr].mean(0)) ** 2).sum()


if __name__ == '__main__':
    main()
