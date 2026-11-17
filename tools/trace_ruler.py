"""A ruler: the backward trace of a next-place read. For each held row (48 known places, the next place open) the place's charts at every
tick are read for what they still hold of the symbols that went in: the share of a target's variance a least-squares read of the chart
explains, fitted on half the rows and read on the other half. Targets: the single symbol d places back (d = 1..8), the pair and the
triple just before the place (their joint identity), and the symbol that arrives. Beside them, what the symbols themselves would explain
of the arriving symbol if held jointly (conditional means by the exact last one, two and three symbols, counted on the fit half), and the
rows' shares by distance. Outside the machine; it prints shares and counts only.
Usage: python3 -I trace_ruler.py DUMP TRACE_ROWS.tsv"""
import sys, collections
import numpy as np
d, table = sys.argv[1], sys.argv[2]
text = {}
for l in open(table, encoding='utf-8'):
    lab, p, r = l.rstrip('\n').split('\t')[:3]
    text[lab] = (p, r)
dims = dict(l.split('\t') for l in open(d + '/dims.tsv').read().split('\n') if l)
D, T = int(dims['read']), int(dims['ticks'])
rows = [l.rstrip('\n').split('\t') for l in open(d + '/rows.tsv')]
read = np.fromfile(d + '/read.i32', dtype=np.int32).reshape(-1, D).astype(np.float64) / 65536
chart = np.fromfile(d + '/chart.i32', dtype=np.int32).reshape(-1, D).astype(np.float64) / 65536
assert len(rows) == len(read) == len(chart), (len(rows), len(read), len(chart))
labels = [r[0] for r in rows[::T]]
N = len(labels)
tick = lambda a, k: a[k::T][:N]
ctx = [text[l][0] for l in labels]
nxt = [text[l][1] for l in labels]
rng = np.random.default_rng(17)
perm = rng.permutation(N)
fit, test = perm[:N // 2], perm[N // 2:]

def onehot(keys, top):
    c = collections.Counter(keys[i] for i in fit)
    idx = {k: j for j, (k, _) in enumerate(c.most_common(top))}
    Y = np.zeros((N, len(idx) + 1))
    for i, k in enumerate(keys):
        Y[i, idx.get(k, len(idx))] = 1.0
    return Y

def explained(X, Y, ridge=1e-3):
    X1 = np.hstack([X, np.ones((N, 1))])
    A = X1[fit].T @ X1[fit]
    A += ridge * np.trace(A) / len(A) * np.eye(len(A))
    W = np.linalg.solve(A, X1[fit].T @ Y[fit])
    res = Y[test] - X1[test] @ W
    tot = Y[test] - Y[fit].mean(0)
    return 1 - (res ** 2).sum() / (tot ** 2).sum()

def by_context(keys, Y):
    """What the exact context explains: the fit half's conditional mean of Y by key, read on the test half (a key unmet reads the mean)."""
    sums, cnt = collections.defaultdict(lambda: np.zeros(Y.shape[1])), collections.Counter()
    for i in fit:
        sums[keys[i]] += Y[i]; cnt[keys[i]] += 1
    mean = Y[fit].mean(0)
    pred = np.array([sums[keys[i]] / cnt[keys[i]] if cnt[keys[i]] else mean for i in test])
    return 1 - ((Y[test] - pred) ** 2).sum() / ((Y[test] - mean) ** 2).sum()

targets = [(f"symbol {k} back", onehot([c[-k] for c in ctx], 30)) for k in range(1, 9)]
targets += [("the pair before the place", onehot([c[-2:] for c in ctx], 150)), ("the pair two back", onehot([c[-3:-1] for c in ctx], 150)),
            ("the triple before the place", onehot([c[-3:] for c in ctx], 300)), ("the four before the place", onehot([c[-4:] for c in ctx], 400))]
Ynext = onehot(nxt, 30)
targets.append(("the symbol that arrives", Ynext))
stages = [("opening chart, tick 1", tick(chart, 0))] + [(f"pair chart, tick {k + 1}", tick(read, k)) for k in range(T)]
stages.append(("every tick's charts together", np.hstack([tick(read, k) for k in range(T)] + [tick(chart, 0)])))
print(f"TRACE places={N} fit={len(fit)} read={len(test)} width={D} ticks={T}")
print("TRACE held share explained (thousandths) | " + " | ".join(n for n, _ in stages))
for name, Y in targets:
    print(f"TRACE {name:28s} | " + " | ".join(f"{1000 * explained(X, Y):6.0f}" for _, X in stages))
print("TRACE the arriving symbol explained by the exact context (thousandths): one symbol back %.0f, the pair %.0f, the triple %.0f, the four %.0f" % tuple(
    1000 * by_context([c[-k:] for c in ctx], Ynext) for k in (1, 2, 3, 4)))
# the rows' shares by distance from the place
try:
    by = collections.defaultdict(lambda: collections.Counter()); top = collections.defaultdict(list); n = collections.Counter()
    for l in open(d + '/shares.tsv'):
        w = l.rstrip('\n').split('\t')
        k, h, site = int(w[2]), int(w[3]), int(w[4])
        srcs = [(int(a.split(':')[0]), int(a.split(':')[1])) for a in w[5].split()] if len(w) > 5 and w[5] else []
        n[(k, h)] += 1
        if srcs: top[(k, h)].append(max(p for _, p in srcs))
        for j, p in srcs:
            dist = site - j
            b = '1' if dist == 1 else '2' if dist == 2 else '3' if dist == 3 else '4-5' if dist <= 5 else '6-10' if dist <= 10 else '11+'
            by[(k, h)][b] += p
    print("TRACE a row's share by its source's distance from the place (thousandths of the row), and its largest single share")
    for (k, h) in sorted(n):
        tot = sum(by[(k, h)].values()) or 1
        print(f"TRACE tick {k + 1} head {h}: " + " ".join(f"{b}:{1000 * by[(k, h)][b] // tot}" for b in ('1', '2', '3', '4-5', '6-10', '11+')) + f" | largest {int(np.mean(top[(k, h)])) // 1000 if top[(k, h)] else 0}")
except FileNotFoundError:
    pass
