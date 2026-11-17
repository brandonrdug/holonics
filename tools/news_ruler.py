"""A ruler: the backward trace re-read on the passage's own clock. A place's news is its code length under a count model of the fitted
text (a ruler's stand-in for the reader's own surprise); the passage's clock is the running sum of news S from the row's opening; a reader
of period sigma begins a unit wherever S crosses a multiple of sigma (the odometer, atlas deposition.return-on-news-clock). Read here:
(a) her next-place code against the count ruler's, by the arriving place's own news (the interior of a unit against its landmark);
(b) what of the unit in progress and of the unit before it is present in her state at the place, each as one identity, by period;
(c) how much of an earlier symbol's identity is present against its distance from the place in nats of passage.
Outside the machine; shares and nats only. Usage: python3 -I news_ruler.py DUMP TRACE_ROWS.tsv FIT.txt"""
import sys, math, collections
import numpy as np
d, table, fit_path = sys.argv[1], sys.argv[2], sys.argv[3]
fit_text = open(fit_path, encoding='utf-8', errors='replace').read()
K = 5
cnt = [collections.defaultdict(collections.Counter) for _ in range(K + 1)]
for i, ch in enumerate(fit_text):
    for k in range(K + 1):
        if i - k >= 0: cnt[k][fit_text[i - k:i]][ch] += 1
V = len(set(fit_text)) + 1
def news(ctx, ch):
    p = 1.0 / V
    for k in range(0, K + 1):
        c = cnt[k].get(ctx[len(ctx) - k:] if k else '')
        if not c: break
        n = sum(c.values()); t = len(c); lam = n / (n + t)
        p = lam * (c.get(ch, 0) / n) + (1 - lam) * p
    return -math.log(p)
text = {}
for l in open(table, encoding='utf-8'):
    lab, p, r = l.rstrip('\n').split('\t')[:3]; text[lab] = (p, r)
dims = dict(l.split('\t') for l in open(d + '/dims.tsv').read().split('\n') if l)
D, T = int(dims['read']), int(dims['ticks'])
rows = [l.rstrip('\n').split('\t') for l in open(d + '/rows.tsv')]
read = np.fromfile(d + '/read.i32', dtype=np.int32).reshape(-1, D).astype(np.float64) / 65536
chart = np.fromfile(d + '/chart.i32', dtype=np.int32).reshape(-1, D).astype(np.float64) / 65536
labels = [r[0] for r in rows[::T]]; N = len(labels)
her = np.array([int(r[3]) for r in rows[::T]]) / (1 << 20) * math.log(2)        # her own code at the place, nats
ctx = [text[l][0] for l in labels]; nxt = [text[l][1] for l in labels]
L = len(ctx[0])
c = np.array([[news(s[:j], s[j]) for j in range(K, L)] for s in ctx])            # news of the prompt's places K..L-1
c_next = np.array([news(s, x) for s, x in zip(ctx, nxt)])
S = np.cumsum(c, axis=1)                                                          # the row's clock, from its opening
rng = np.random.default_rng(17); perm = rng.permutation(N); fit, test = perm[:N // 2], perm[N // 2:]
print(f"NEWS places={N} mean news a place (count ruler) {c.mean():.3f} nats; the arriving place: ruler {c_next.mean():.3f}, her {her.mean():.3f}")
# (a) by the arriving place's own news
edges = [0, 0.25, 1, 2, 4, 99]
for lo, hi in zip(edges, edges[1:]):
    m = (c_next >= lo) & (c_next < hi)
    print(f"NEWS (a) arriving place's news {lo}-{hi} nats: places {m.sum()} ({100 * m.mean():.0f}%), ruler {c_next[m].mean():.3f}, her {her[m].mean():.3f}, her excess {her[m].mean() - c_next[m].mean():+.3f}, share of her whole excess {100 * (her[m] - c_next[m]).sum() / (her - c_next).sum():.0f}%")
def onehot(keys, top):
    cc = collections.Counter(keys[i] for i in fit); idx = {k: j for j, (k, _) in enumerate(cc.most_common(top))}
    Y = np.zeros((N, len(idx) + 1))
    for i, k in enumerate(keys): Y[i, idx.get(k, len(idx))] = 1.0
    return Y
def explained(X, Y, rows_mask=None, ridge=1e-3):
    X1 = np.hstack([X, np.ones((N, 1))]); A = X1[fit].T @ X1[fit]; A += ridge * np.trace(A) / len(A) * np.eye(len(A))
    W = np.linalg.solve(A, X1[fit].T @ Y[fit]); res = ((Y - X1 @ W) ** 2).sum(1); tot = ((Y - Y[fit].mean(0)) ** 2).sum(1)
    return res, tot
state = read[T - 1::T][:N]; opening = chart[0::T][:N]
def share(res, tot, mask):
    m = np.zeros(N, bool); m[test] = True; m &= mask
    return 1 - res[m].sum() / max(tot[m].sum(), 1e-12), int(m.sum())
# (b) the unit in progress and the unit before it, by the reader's period
for sigma in (2.0, 4.0, 8.0, 16.0):
    cur, prev, ulen = [], [], []
    for i in range(N):
        w = np.floor(S[i] / sigma); starts = [0] + [j for j in range(1, L - K) if w[j] > w[j - 1]]   # a unit begins where the clock carries
        a = starts[-1]; b = starts[-2] if len(starts) > 1 else None
        cur.append(ctx[i][K + a:]); prev.append(ctx[i][K + b:K + a] if b is not None else None); ulen.append(S[i][-1] - (S[i][a - 1] if a else 0))
    has_prev = np.array([p is not None for p in prev])
    Yc = onehot(cur, 400); Yp = onehot([p or '' for p in prev], 400)
    rc, tc = explained(state, Yc); rp, tp = explained(state, Yp); ro, to = explained(opening, Yc)
    allm = np.ones(N, bool)
    print(f"NEWS (b) period {sigma:g} nats: a unit is {np.mean([len(x) for x in cur]) :.1f} symbols in progress on average; present where her face reads: the unit in progress {1000 * share(rc, tc, allm)[0]:.0f}, the unit before it {1000 * share(rp, tp, has_prev)[0]:.0f}; the unit in progress at the opening {1000 * share(ro, to, allm)[0]:.0f} (thousandths)")
# (c) an earlier symbol's presence against its distance in nats of passage
bins = [(0, 1), (1, 2), (2, 4), (4, 8), (8, 16), (16, 99)]
acc = {b: [0.0, 0.0, 0] for b in bins}
for lag in range(1, 13):
    Y = onehot([s[-lag] for s in ctx], 30); res, tot = explained(state, Y)
    dist = S[:, -1] - (S[:, -lag - 1] if lag < L - K else 0) if lag < L - K else None
    for b in bins:
        m = np.zeros(N, bool); m[test] = True; m &= (dist >= b[0]) & (dist < b[1])
        acc[b][0] += res[m].sum(); acc[b][1] += tot[m].sum(); acc[b][2] += int(m.sum())
for b in bins:
    r, t, n = acc[b]
    print(f"NEWS (c) a symbol {b[0]}-{b[1]} nats of passage before the place: present {1000 * (1 - r / max(t, 1e-12)):.0f} thousandths (symbols read {n})")
