"""A ruler: a face fitted at each tick of the open place (the level's design record of November 17, its §10; guess G-V4).
From two `read-tension ... shares` dumps of boundary rows (48 known places, the next place open), one of the training passage's rows to
fit on and one of held rows to read: at each tick the open place's opening chart (`chart.i32`, the state the tick begins from) and its
pair chart (`read.i32`, the state inside the tick, after its contact), a linear readout to the symbols fitted as a softmax, and its
code of the written symbol in nats a place on the held rows; beside them the machine's own face after its last tick (`rows.tsv`).

Outside the machine, in floats. The line names every index it is keyed by.
Usage: python3 -I tick_face_ruler.py FIT_DUMP FIT_ROWS.tsv READ_DUMP READ_ROWS.tsv"""
import sys, math, time
import numpy as np

t0 = time.time()
fit_d, fit_t, read_d, read_t = sys.argv[1:5]
LN2 = math.log(2); G = float(1 << 20)

def load(d, table):
    sym = {}
    for l in open(table, encoding='utf-8'):
        lab, _, r = l.rstrip('\n').split('\t')[:3]
        sym[lab] = r.replace('\\n', '\n')
    dims = dict(l.split('\t') for l in open(d + '/dims.tsv').read().split('\n') if l)
    D, ticks = int(dims['read']), int(dims['ticks'])
    labels, code = [], []
    for i, l in enumerate(open(d + '/rows.tsv', encoding='utf-8')):
        lab, _, tick, c = l.rstrip('\n').split('\t')[:4]
        assert int(tick) == i % ticks
        if int(tick) == 0:
            labels.append(lab); code.append(int(c) / G * LN2)
    n = len(labels)
    chart = np.fromfile(d + '/chart.i32', dtype=np.int32).reshape(n, ticks, D).astype(np.float64) / 65536
    read = np.fromfile(d + '/read.i32', dtype=np.int32).reshape(n, ticks, D).astype(np.float64) / 65536
    return [sym[l] for l in labels], np.array(code), chart, read, ticks

ys_f, code_f, chart_f, read_f, ticks = load(fit_d, fit_t)
ys_r, code_r, chart_r, read_r, _ = load(read_d, read_t)
classes = {c: i for i, c in enumerate(sorted(set(ys_f)))}
A = len(classes)
yf = np.array([classes[c] for c in ys_f]); yr = np.array([classes.get(c, -1) for c in ys_r])
unseen = int((yr < 0).sum())
# A tenth of the fitted rows is kept aside: the fitted face's own held part.
rng = np.random.default_rng(11); perm = rng.permutation(len(yf)); aside = perm[: len(yf) // 10]; fit = perm[len(yf) // 10:]
print(f"TICKS fit rows {len(fit)} (a tenth kept aside: {len(aside)}), read rows {len(yr)} (held), symbols {A}, held symbols the fit never met {unseen}; ticks {ticks}")
print(f"TICKS the machine's own face after its last tick: held {code_r.mean():.3f} nats a place; on the fitted rows {code_f.mean():.3f}")
freq = np.bincount(yf[fit], minlength=A) + 0.5; freq /= freq.sum()
print(f"TICKS a face of the symbols' frequencies alone: held {-np.log(freq[np.maximum(yr, 0)]).mean():.3f}")

def softmax_fit(X, y, steps=300, l2=1e-4):
    """A linear readout fitted as a softmax by full-batch descent with a per-entry step (Adam), from zero, on whitened features.
    Returns the readout and its fitted code at half its steps and at its last."""
    n, d = X.shape
    W = np.zeros((d, A), np.float32); m = np.zeros_like(W); v = np.zeros_like(W)
    Y = np.zeros((n, A), np.float32); Y[np.arange(n), y] = 1.0
    half = final = float('nan')
    for s in range(1, steps + 1):
        Z = X @ W; Z -= Z.max(1, keepdims=True); P = np.exp(Z); P /= P.sum(1, keepdims=True)
        g = X.T @ (P - Y) / n + l2 * W
        m = 0.9 * m + 0.1 * g; v = 0.999 * v + 0.001 * g * g
        W -= 0.05 * (m / (1 - 0.9 ** s)) / (np.sqrt(v / (1 - 0.999 ** s)) + 1e-8)
        if s == steps // 2: half = float(-np.log(P[np.arange(n), y]).mean())
        if s == steps: final = float(-np.log(P[np.arange(n), y]).mean())
    return W, half, final

def code_of(X, W, y):
    Z = X @ W; Z -= Z.max(1, keepdims=True); L = Z - np.log(np.exp(Z).sum(1, keepdims=True))
    ok = y >= 0
    c = np.where(ok, -L[np.arange(len(y)), np.maximum(y, 0)], math.log(A) + 5.0)   # a symbol the fit never met is charged past the flat face
    return c.mean()

def prep(Xf_all, Xr):
    """Features whitened on the fitted rows (their mean taken off, their covariance's own axes at unit scale), a one beside them."""
    mu = Xf_all[fit].mean(0); C = np.cov((Xf_all[fit] - mu).T) + 1e-6 * np.eye(Xf_all.shape[1]); w, V = np.linalg.eigh(C); T = V / np.sqrt(w)
    z = lambda X: np.hstack([(X - mu) @ T, np.ones((len(X), 1))]).astype(np.float32)
    return z(Xf_all[fit]), z(Xf_all[aside]), z(Xr)

print("TICKS a face fitted at each stage of the open place, nats a place (stage: the state a tick begins from, then the state inside it after its contact):")
for k in range(ticks):
    for name, Ff, Fr in [(f"tick {k} begins (after {k} ticks)", chart_f[:, k], chart_r[:, k]), (f"inside tick {k}, after its contact", read_f[:, k], read_r[:, k])]:
        Xf, Xa, Xr = prep(Ff, Fr)
        W, mid, final = softmax_fit(Xf, yf[fit])
        print(f"TICKS   stage {name:36s} held {code_of(Xr, W, yr):.3f}   aside {code_of(Xa, W, yf[aside]):.3f}   fitted {final:.3f} (at half its steps {mid:.3f})   [{time.time() - t0:.0f} s]", flush=True)
print(f"TICKS done in {time.time() - t0:.0f} s on this host's numpy (one process)")
