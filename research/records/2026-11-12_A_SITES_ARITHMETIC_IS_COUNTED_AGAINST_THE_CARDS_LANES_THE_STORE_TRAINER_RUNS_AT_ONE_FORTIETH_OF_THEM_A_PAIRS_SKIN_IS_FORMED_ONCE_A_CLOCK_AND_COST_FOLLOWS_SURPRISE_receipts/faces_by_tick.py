"""P57 item 2 (G132), a ruler on the host in floats: what a place's chart holds of its class at the opening and after each tick, by a fitted face.

A softmax face over the alphabet's classes on a stage's 64 chart words (on 2^-16, read as floats) is fit, a stage at a time, on the one-place
masks of the first four fifths of each slice's stretches pooled (the last eighth of those stretches held out to stop the fit), and read on the
last fifth by slice: f0 to f4 its code in nats a place. Beside them the trained readout's codes c0, c1, c2, c3, cK on the same places, the
unigram (the fit places' class frequencies, half a count added to each class), the rank agreement of the fitted opening's code with cK, the
restarting cut at 5.545 nats on cK, and the same fitted faces at the open places of each slice's whole masks (g0 to g4). Numbers only.

usage: python3 faces_by_tick.py OUT_DIR stage S [ITERS]   (one stage's fit, each in its own process)
       python3 faces_by_tick.py OUT_DIR             (the scores, from the five stages' fits)
"""
import math
import sys
import time

import numpy as np

BAR = 5.545
NATS = math.log(2) / (1 << 20)
SHIFT, PAST = 7, 32
STAGES, WIDTH, CLASSES = 5, 64, 244
out = sys.argv[1]


def rows(kind):
    r = []
    for line in open(f"{out}/cavity.tsv"):
        f = line.rstrip("\n").split("\t")
        if f[0] == kind:
            r.append((f[1], int(f[2]), int(f[3]), int(f[4]), int(f[5]), int(f[6]), int(f[8]), int(f[9]), int(f[10])))
    return r


P, W = rows("P"), rows("W")
words = np.fromfile(f"{out}/words.bin", dtype="<i4").reshape(len(P), STAGES, WIDTH)
whole = np.fromfile(f"{out}/words_whole.bin", dtype="<i4").reshape(len(W), STAGES, WIDTH) if W else np.zeros((0, STAGES, WIDTH), dtype="<i4")
slices = list(dict.fromkeys(r[0] for r in P))
cls = np.array([r[3] for r in P])
codes = np.array([[r[4], r[6], r[7], r[8], r[5]] for r in P], dtype=np.float64) * NATS  # c0, c1, c2, c3, cK
part = np.empty(len(P), dtype="<U4")
for s in slices:
    ks = sorted({r[1] for r in P if r[0] == s})
    n = len(ks)
    fit_k, read_k = set(ks[: (4 * n) // 5]), set(ks[(4 * n) // 5:])
    stop_k = set(sorted(fit_k)[-max(1, len(fit_k) // 8):])
    for i, r in enumerate(P):
        if r[0] == s:
            part[i] = "read" if r[1] in read_k else ("stop" if r[1] in stop_k else "fit")
fit, stop, read = part == "fit", part == "stop", part == "read"
print(f"# P57 item 2 (G132): {len(P)} one-place masks over {len(slices)} slices, fit {fit.sum()}, stop {stop.sum()}, read {read.sum()}; whole masks' open places {len(W)}. Numbers only.")
counts = np.bincount(cls[fit | stop], minlength=CLASSES) + 0.5
unigram = -np.log(counts / counts.sum())


def softmax_fit(x, y, xs, ys, iters=600, lr=0.05, l2=1e-5):
    """Full-batch Adam on the mean cross-entropy (nats), stopped where the held-out stretches' code is least."""
    rng = np.random.default_rng(0)
    xm, xsd = x.mean(0), x.std(0) + 1e-6
    x, xs = (x - xm) / xsd, (xs - xm) / xsd
    x = np.hstack([x, np.ones((len(x), 1))]).astype(np.float32)
    xs = np.hstack([xs, np.ones((len(xs), 1))]).astype(np.float32)
    w = (rng.standard_normal((x.shape[1], CLASSES)) * 0.01).astype(np.float32)
    m, v = np.zeros_like(w), np.zeros_like(w)
    rows_at = np.arange(len(y))
    best, best_w, since = np.inf, w.copy(), 0
    for it in range(1, iters + 1):
        z = x @ w
        z -= z.max(1, keepdims=True)
        p = np.exp(z, out=z)
        p /= p.sum(1, keepdims=True)
        p[rows_at, y] -= 1
        g = x.T @ p / len(y) + l2 * w
        m = 0.9 * m + 0.1 * g
        v = 0.999 * v + 0.001 * g * g
        w -= lr * (m / (1 - 0.9 ** it)) / (np.sqrt(v / (1 - 0.999 ** it)) + 1e-8)
        if it % 25 == 0:
            loss = code_of(xs, ys, w).mean()
            if it % 100 == 0:
                print(f"STOP_CODE iteration={it} code={loss:.4f}", flush=True)
            if loss < best - 1e-5:
                best, best_w, since = loss, w.copy(), 0
            else:
                since += 1
                if since >= 12:
                    break
    return lambda q: np.hstack([(q - xm) / xsd, np.ones((len(q), 1))]).astype(np.float32), best_w, it  # noqa: F821


def code_of(x, y, w):
    z = x @ w
    z = z - z.max(1, keepdims=True)
    lse = np.log(np.exp(z).sum(1))
    return lse - z[np.arange(len(y)), y]


def spearman(a, b):
    ra, rb = a.argsort().argsort().astype(float), b.argsort().argsort().astype(float)
    return float(np.corrcoef(ra, rb)[0, 1])


wcls = np.array([r[3] for r in W], dtype=int) if W else np.zeros(0, dtype=int)
if len(sys.argv) > 2 and sys.argv[2] == "stage":
    # One stage's fit (each stage in its own process): its codes at every place and whole-mask place, to OUT/fit_stage{S}.npz.
    s = int(sys.argv[3])
    t0 = time.time()
    x = words[:, s, :].astype(np.float64) / (1 << 16)
    prep, w, iters = softmax_fit(x[fit], cls[fit], x[stop], cls[stop], iters=int(sys.argv[4]) if len(sys.argv) > 4 else 600)
    fs = code_of(prep(x), cls, w)
    gs = code_of(prep(whole[:, s, :].astype(np.float64) / (1 << 16)), wcls, w) if W else np.zeros(0)
    np.savez(f"{out}/fit_stage{s}.npz", f=fs, g=gs, iters=iters, seconds=time.time() - t0)
    print(f"FIT stage={s} iterations={iters} seconds={time.time() - t0:.1f} fit_code={fs[fit].mean():.3f} stop_code={fs[stop].mean():.3f} read_code={fs[read].mean():.3f}", flush=True)
    sys.exit(0)
f = np.zeros((len(P), STAGES))
g = np.zeros((len(W), STAGES))
for s in range(STAGES):
    z = np.load(f"{out}/fit_stage{s}.npz")
    f[:, s], g[:, s] = z["f"], z["g"]
    print(f"FIT stage={s} iterations={int(z['iters'])} seconds={float(z['seconds']):.1f} fit_code={f[fit, s].mean():.3f} stop_code={f[stop, s].mean():.3f} read_code={f[read, s].mean():.3f}")
names = ["c0", "c1", "c2", "c3", "cK"]
for label, mask in [(s, read & (np.array([r[0] for r in P]) == s)) for s in slices] + [("pooled", read)]:
    fs = " ".join(f"f{k}={f[mask, k].mean():.3f}" for k in range(STAGES))
    cs = " ".join(f"{n}={codes[mask, k].mean():.3f}" for k, n in enumerate(names))
    rho = spearman(f[mask, 0], codes[mask, 4])
    print(f"G132 slice={label} places={mask.sum()} {fs} {cs} unigram={unigram[cls[mask]].mean():.3f} rank_f0_cK={rho:.3f}")
# (f) the restarting cut on cK along each stretch, every place, pooled over the slices.
def cut(cs, start=0):
    opens, a = [], None
    for t in range(start, len(cs)):
        c = cs[t]
        if a is None or a + c > BAR:
            opens.append(t)
            a = c
        else:
            a += c
    return opens


by_stretch = {}
for i, r in enumerate(P):
    by_stretch.setdefault((r[0], r[1]), []).append((r[2], codes[i, 4]))
lengths, kept, total = [], 0, 0
for key, places in by_stretch.items():
    cs = [c for _, c in sorted(places)]
    opens = cut(cs)
    lengths += [b - a for a, b in zip(opens, opens[1:])]
    a, b = set(t for t in opens if t > PAST), set(cut(cs, SHIFT))
    total += len(a)
    kept += len(a & b)
lengths = np.array(lengths)
print(f"G132_CUT on=cK stretches={len(by_stretch)} whole_epochs={len(lengths)} mean_epoch_places={lengths.mean():.3f} one_place_share={(lengths == 1).mean():.3f} kept_under_start_7_later={kept / max(total, 1):.4f}")
if W:
    wk = np.array([r[5] for r in W], dtype=np.float64) * NATS
    gs = " ".join(f"g{k}={g[:, k].mean():.3f}" for k in range(STAGES))
    print(f"G132_WHOLE places={len(W)} {gs} trained_cK={wk.mean():.3f} g4_over_cK={g[:, 4].mean() / wk.mean():.3f} g2_less_g4={g[:, 2].mean() - g[:, 4].mean():.3f} g3_less_g4={g[:, 3].mean() - g[:, 4].mean():.3f}")
