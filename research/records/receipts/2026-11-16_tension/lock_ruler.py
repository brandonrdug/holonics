# A ruler: a lock located from the covector's tension, by ruler arithmetic on a `read-tension … all` directory (every site's opening chart,
# the open place's covector). No label enters the location: for an open place i and a source j of its region, the potential use of j is
# u_ij = 2<λ_i, M r_j> − |M r_j|², with M the least-squares map from what the row gathers to its covector; the lock is the bilinear form of
# the receiver's and the source's charts that the centred potentials follow, W = C_r⁻¹ (Σ_i r_i (Σ_j ũ_ij r_j)ᵀ) C_s⁻¹ cut to a head's rank;
# the row's weights are its Gibbs face at a gain read on the fit half. Two rounds from uniform weights. The labels (which source is the
# aligned digit) are read only to say afterwards where the located lock put its weight.
import sys, os, hashlib, collections
import numpy as np
sys.path.insert(0, 'tools')
import tension_ruler as t

d, TICK = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 0
RANK = 16
dims = dict(l.split('\t') for l in open(d + '/dims.tsv').read().splitlines())
dw = int(dims['lambda'])
rows = [l.split('\t') for l in open(d + '/rows.tsv').read().splitlines()]
n = len(rows)
chart = np.fromfile(d + '/chart.i32', dtype='<i4').reshape(n, dw) / 2.0**16
lam = np.fromfile(d + '/lambda.i64', dtype='<i8').reshape(n, dw) / 2.0**24
groups = collections.defaultdict(list)
for k, r in enumerate(rows):
    if int(r[2]) == TICK:
        groups[(r[0], int(r[1]))].append(k)
R = []  # per open place: (label, receiver chart, covector, sources' charts, sources' sites, kinds…)
for (lab, place), idx in groups.items():
    idx = sorted(idx, key=lambda k: int(rows[k][4]))
    op = [k for k in idx if rows[k][5] == '1']
    if len(op) != 1:
        continue
    i = op[0]
    src = [k for k in idx if k != i]
    _, kind, o, a, b, v = lab.split(':')
    site = int(rows[i][4])
    _, kv, _ = t.site_role(lab, site)
    at_b = len(a) + 3
    ak = len(a) - 1 - kv if kv < len(a) else None
    bk = at_b + len(b) - 1 - kv if kv < len(b) else None
    sites = [int(rows[k][4]) for k in src]
    R.append(dict(lab=lab, r=chart[i], lam=lam[i], S=chart[src], sites=sites, ak=ak, bk=bk, kind=kind, op=o,
                  da=(int(a) // 10**kv) % 10, db=(int(b) // 10**kv) % 10,
                  half=hashlib.sha256(f'half:{lab}'.encode()).digest()[0] % 2))
fit = [x for x in R if x['half'] == 0]
test = [x for x in R if x['half'] == 1]
print(f'LOCK_READ tick={TICK} places={len(R)} fit={len(fit)} held={len(test)} mean_sources={np.mean([len(x["sites"]) for x in R]):.1f}')
one = lambda x: np.append(x, 1.0)

def gathered(X, weights):
    return np.array([w @ x['S'] for x, w in zip(X, weights)])

def ridge(F, Y, lam_=1e-3):
    F1 = np.hstack([F, np.ones((len(F), 1))])
    h = F1.T @ F1
    h += lam_ * np.trace(h) / len(h) * np.eye(len(h))
    return np.linalg.solve(h, F1.T @ Y)

def share(M, X, weights):
    G = gathered(X, weights)
    Y = np.array([x['lam'] for x in X])
    res = Y - np.hstack([G, np.ones((len(G), 1))]) @ M
    return 1 - (res**2).sum() / (Y**2).sum()

def report(name, X, weights, M):
    by = collections.defaultdict(lambda: [0, 0.0, 0.0])
    for x, w in zip(X, weights):
        if x['kind'] != 'met' or x['op'] != '+':
            continue
        cols = [c for c in (x['ak'], x['bk']) if c is not None]
        if not cols:
            continue
        part = 'both' if len(cols) == 2 else 'one'
        e = by[part]; e[0] += 1
        e[1] += sum(w[x['sites'].index(c)] for c in cols)
        e[2] += float(max(w) == max(w[x['sites'].index(c)] for c in cols))
    line = ' '.join(f'{p}: rows={e[0]} share_on_column={e[1] / e[0]:.3f} column_leads={e[2] / e[0]:.3f}' for p, e in sorted(by.items()))
    print(f'LOCK {name} covector_share_held={share(M, X, weights):.4f} | met sums, {line}', flush=True)

uniform = lambda X: [np.full(len(x['sites']), 1.0 / len(x['sites'])) for x in X]
w_fit, w_test = uniform(fit), uniform(test)
M = ridge(gathered(fit, w_fit), np.array([x['lam'] for x in fit]))
report('round=0 uniform', test, w_test, M)
Cr = np.cov(np.array([x['r'] for x in fit]).T) + 1e-3 * np.eye(dw)
Cs = np.cov(np.vstack([x['S'] for x in fit]).T) + 1e-3 * np.eye(dw)
for rnd in (1, 2, 3):
    A = M[:-1]  # [D gathered][D covector]
    cross = np.zeros((dw, dw))
    for x in fit:
        pred = x['S'] @ A + M[-1]                       # each source alone, read by M
        u = 2 * pred @ x['lam'] - (pred**2).sum(axis=1)  # its potential use to the row
        u = u - u.mean()
        cross += np.outer(x['r'], u @ x['S'])
    W = np.linalg.solve(Cr, cross) @ np.linalg.inv(Cs)
    U_, s_, Vt = np.linalg.svd(W)
    W = (U_[:, :RANK] * s_[:RANK]) @ Vt[:RANK]
    def weights_of(X, gain):
        out = []
        for x in X:
            z = gain * (x['r'] @ W @ x['S'].T)
            z = z - z.max()
            e = np.exp(z)
            out.append(e / e.sum())
        return out
    # The gain: the one at which the fit half's covector is best removed (a ruler's scan; a temperature is the head's to hold).
    zs = np.concatenate([x['r'] @ W @ x['S'].T for x in fit])
    best = None
    for g in (0.5, 1, 2, 4, 8, 16):
        gain = g / zs.std()
        wf = weights_of(fit, gain)
        Mg = ridge(gathered(fit, wf), np.array([x['lam'] for x in fit]))
        sh = share(Mg, fit, wf)
        if best is None or sh > best[0]:
            best = (sh, gain, g, Mg)
    _, gain, g, M = best
    w_fit, w_test = weights_of(fit, gain), weights_of(test, gain)
    report(f'round={rnd} gain={g}sd spectrum_top={s_[0] / s_[:RANK].sum():.2f}', test, w_test, M)
# What arrives under the located lock, and what a junction could then read (held half, met sums).
G = gathered(test, w_test)
sel = lambda part: np.array([x['kind'] == 'met' and x['op'] == '+' and ((x['ak'] is not None) and (x['bk'] is not None)) == (part == 'both') and (x['ak'] is not None or x['bk'] is not None) for x in test])
da, db = np.array([x['da'] for x in test]), np.array([x['db'] for x in test])
Y = np.array([x['lam'] for x in test])
for part in ('both', 'one'):
    m = sel(part)
    idx = np.nonzero(m)[0]
    h = np.arange(len(idx)) % 2 == 0
    f_, t_ = np.zeros(len(test), bool), np.zeros(len(test), bool)
    f_[idx[h]] = True; t_[idx[~h]] = True
    oa, ob = t.onehot(da) - t.onehot(da)[m].mean(0), t.onehot(db) - t.onehot(db)[m].mean(0)
    pair = (t.onehot(da)[:, :, None] * t.onehot(db)[:, None, :]).reshape(len(test), 100)
    line = f'LOCK_ARRIVES {part} rows={t_.sum()} a_from_gathered={t.removed(G, oa, f_, t_):.3f} b_from_gathered={t.removed(G, ob, f_, t_):.3f} covector: linear_of_gathered={t.removed(G, Y, f_, t_):.3f} table={t.removed(pair, Y, f_, t_):.3f}'
    print(line, flush=True)
