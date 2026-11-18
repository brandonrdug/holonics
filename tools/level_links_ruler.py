"""A ruler: the engine's level read link by link, and the tension at its locus (the level's design record of November 17, its §6).
From a `read-level ... links` dump (each region's epochs' anchors and news, each place's phase harmonics, its read at the split, its
prolonged row and the covector the reverse holds at the level's locus; each epoch's moment, its restricted state before the level's
ticks and its read after them) and the rows' table.

Reading A, the link trace: what each link still holds of a whole epoch, by least squares fitted on half the regions and read on the
other, in thousandths: its leading symbol, its symbols as a bag, the epoch as one identity, the epoch before as one identity and the
symbol that leads the next. Beside the built restriction, a restriction of the same width located from those keys.

Reading B, the tension: of the covector's power at the split, on the held half, what a refitted prolongation of the level's present
state removes, what a table of the two epochs' symbols removes, and what operands of the level's own width located from the moments
remove; with a planted law of the table's form recovered in the same run.

Outside the machine, in floats; shares and counts only. The line names every index it is keyed by.
Usage: python3 -I level_links_ruler.py DUMP ROWS.tsv [threads-note]"""
import sys, math, time, collections
import numpy as np

t0 = time.time()
d, table = sys.argv[1], sys.argv[2]
text = {}
for l in open(table, encoding='utf-8'):
    lab, p, r = l.rstrip('\n').split('\t')[:3]
    text[lab] = p.replace('\\n', '\n') + r.replace('\\n', '\n')
dims = dict(l.split('\t') for l in open(d + '/dims.tsv').read().split('\n') if l)
D1, H, D0 = int(dims['coarse']), int(dims['harmonics']), int(dims['fine'])
LN2 = math.log(2); G = float(1 << 20)

regions = []  # (label, sites, anchors, news nats)
for l in open(d + '/level.tsv', encoding='utf-8'):
    lab, sites, anc, news = l.rstrip('\n').split('\t')
    regions.append((lab, int(sites), [int(x) for x in anc.split(',')], np.array([int(x) for x in news.split(',')]) / G * LN2))
places = sum(r[1] for r in regions); epochs = sum(len(r[2]) for r in regions)
mm = lambda name, dt, w: np.memmap(d + '/' + name, dtype=dt, mode='r').reshape(-1, w)
phase = mm('phase.i64', np.int64, H); read = mm('read.i32', np.int32, D0); prolonged = mm('prolonged.i64', np.int64, D0)
covector = mm('covector.i64', np.int64, D0); moment = mm('moment.i64', np.int64, H * D0); restricted = mm('restricted.i64', np.int64, D1)
coarse = mm('coarse.i32', np.int32, D1)
assert len(phase) == len(read) == len(prolonged) == len(covector) == places and len(moment) == len(restricted) == len(coarse) == epochs
print(f"LINKS regions={len(regions)} places={places} epochs={epochs} D0={D0} D1={D1} H={H}")

# Each place and each epoch in the dump's order.
P_region = np.zeros(places, np.int64); P_epoch = np.zeros(places, np.int64); P_open = np.zeros(places, bool); P_sym = []
E = []  # (region, string, previous string or None, next's leading symbol or None, whole, first place row, last place row + 1, news nats, interior span in sections)
row = 0; erow = 0
for ri, (lab, sites, anc, news) in enumerate(regions):
    s = text[lab]; assert len(s) == sites, (lab, len(s), sites)
    S = np.concatenate([[0.0], np.cumsum(news)])
    strs = [s[a:b] for a, b in zip(anc, anc[1:] + [sites])]
    for j, a in enumerate(anc):
        b = anc[j + 1] if j + 1 < len(anc) else sites
        whole = b < sites
        E.append((ri, strs[j], strs[j - 1] if j else None, s[b] if whole else None, whole, row + a, row + b, S[b] - S[a], S[b] - S[a + 1]))
        P_epoch[row + a:row + b] = erow; erow += 1
    P_region[row:row + sites] = ri; P_open[row + sites - 1] = True; P_sym += list(s); row += sites
P_sym = np.array(P_sym)
h = np.asarray(phase, np.float64) / float(1 << 30)
n_reg = len(regions)
rng = np.random.default_rng(17); half = rng.permutation(n_reg)[: n_reg // 2]; infit = np.zeros(n_reg, bool); infit[half] = True
whole_news = [e[7] for e in E if e[4]]; whole_size = [e[6] - e[5] for e in E if e[4]]
print(f"LINKS a whole epoch: {np.mean(whole_size):.2f} places, {np.mean(whole_news):.2f} nats (median {np.median(whole_news):.2f}); whole epochs {len(whole_news)}")

def ridge(Xf, Yf):
    A = Xf.T @ Xf; A += 1e-3 * np.trace(A) / len(A) * np.eye(len(A))
    return np.linalg.solve(A, Xf.T @ Yf)

def onehot(keys, classes):
    y = np.zeros((len(keys), len(classes) + 1))
    for r_, k in enumerate(keys): y[r_, classes.get(k, len(classes))] = 1.0
    return y

def sixth(i, k):
    """The sixth of a turn the epoch's k-th place stands in, by its news phase from the epoch's anchor."""
    a = E[i][5]
    return int(((math.atan2(h[a + k, 2], h[a + k, 1]) / (2 * math.pi)) % 1.0) * 6) % 6
def presence(X, idx, key_of, top, bag=False):
    """Thousandths of the key's variance a least-squares read of X gives on the held half. `bag` True: the epoch's symbols counted;
    'before': the epoch before's symbols counted; 'phase': the epoch's symbols counted in each sixth of a turn of the news phase."""
    fit = [i for i in idx if infit[E[i][0]]]; test = [i for i in idx if not infit[E[i][0]]]
    if bag:
        src = (lambda i: E[i][2]) if bag == 'before' else (lambda i: E[i][1])
        cc = collections.Counter(c for i in fit for c in src(i)); cls = {k: j for j, (k, _) in enumerate(cc.most_common(top))}
        n = len(cls) + 1
        def Y(ix):
            y = np.zeros((len(ix), n * (6 if bag == 'phase' else 1)))
            for r_, i in enumerate(ix):
                for k, c in enumerate(src(i)): y[r_, (sixth(i, k) * n if bag == 'phase' else 0) + cls.get(c, len(cls))] += 1.0
            return y
    else:
        cc = collections.Counter(key_of(E[i]) for i in fit); cls = {k: j for j, (k, _) in enumerate(cc.most_common(top))}
        Y = lambda ix: onehot([key_of(E[i]) for i in ix], cls)
    Xf, Xt = np.hstack([X[fit], np.ones((len(fit), 1))]), np.hstack([X[test], np.ones((len(test), 1))])
    Yf, Yt = Y(fit), Y(test)
    W = ridge(Xf, Yf)
    return 1000 * (1 - ((Yt - Xt @ W) ** 2).sum() / ((Yt - Yf.mean(0)) ** 2).sum()), len(test)

def charted(X):
    """Each row over its root mean square, with the logarithm of that scale beside it (a chart reads a ratio, and a long epoch's sums are large)."""
    n = np.sqrt((X ** 2).mean(1, keepdims=True)) + 1e-12
    return np.hstack([X / n, np.log(n)])
lead_row = np.array([e[5] for e in E])
X_read = np.asarray(read[lead_row], np.float64) / 65536          # the fine read at the split, at the epoch's leading place
M_raw = np.asarray(moment, np.float64) / 65536
X_m = charted(M_raw)                                               # the moment, six harmonics of the places' reads
X_r = charted(np.asarray(restricted, np.float64) / 65536)          # the restricted state, before the level's ticks
# (i) a drawn restriction of the level's width, as the founding draws one (uniform on ±√(3/(H D₀))), three draws
drng = np.random.default_rng(29)
X_d = [charted(M_raw @ drng.uniform(-math.sqrt(3 / (H * D0)), math.sqrt(3 / (H * D0)), (H * D0, D1))) for _ in range(3)]
X_c = np.asarray(coarse, np.float64) / 65536                       # the level's read after its ticks
pro = np.asarray(prolonged, np.float64) / 65536
X_p = np.hstack([pro[lead_row], np.array([pro[e[5]:e[6]].mean(0) for e in E])])   # the prolonged rows: at the leading place, and the epoch's mean

W_ = lambda e: e[4]
B_ = lambda e: e[4] and e[2] is not None
keys = [("its leading symbol", W_, lambda e: e[1][0], 30, False), ("its symbols as a bag", W_, None, 40, True),
        ("its symbols by sixth of a turn", W_, None, 20, 'phase'), ("the epoch before's symbols as a bag", B_, None, 40, 'before'),
        ("the epoch as one identity", W_, lambda e: e[1], 400, False),
        ("the epoch before, as one identity", lambda e: e[4] and e[2] is not None, lambda e: e[2], 400, False),
        ("the symbol that leads the next", W_, lambda e: e[3], 30, False)]

# A restriction of the level's own width located from the keys: a reduced-rank fit of the first three keys on the moment.
fitE = [i for i in range(len(E)) if E[i][4] and infit[E[i][0]]]
def key_block(ix, cls_lead, cls_bag, cls_id):
    y1 = onehot([E[i][1][0] for i in ix], cls_lead); y3 = onehot([E[i][1] for i in ix], cls_id)
    y2 = np.zeros((len(ix), len(cls_bag) + 1))
    for r_, i in enumerate(ix):
        for c in E[i][1]: y2[r_, cls_bag.get(c, len(cls_bag))] += 1.0
    return [y1, y2, y3]
top = lambda it, n: {k: j for j, (k, _) in enumerate(collections.Counter(it).most_common(n))}
cl, cb, ci = top((E[i][1][0] for i in fitE), 30), top((c for i in fitE for c in E[i][1]), 40), top((E[i][1] for i in fitE), 400)
Yb = key_block(fitE, cl, cb, ci); Yb = [y - y.mean(0) for y in Yb]; Yb = np.hstack([y / math.sqrt((y ** 2).sum()) for y in Yb])
Xf = X_m[fitE]; mu = Xf.mean(0); Xf = Xf - mu
Gm = Xf.T @ Xf; Gm += 1e-3 * np.trace(Gm) / len(Gm) * np.eye(len(Gm))
ev, V = np.linalg.eigh(Gm); Wh = V / np.sqrt(ev)                    # whitening of the moment on the fitted half
M = Wh.T @ (Xf.T @ Yb)                                             # the whitened cross moment
U, sv, _ = np.linalg.svd(M, full_matrices=False)
R_loc = Wh @ U[:, :D1]                                             # the located restriction, the moment's 768 numbers to D1
X_l = (X_m - mu) @ R_loc
print(f"LINKS the located restriction: rank {D1} of the keys' fit on the moment, the singular values' share kept {100 * (sv[:D1] ** 2).sum() / (sv ** 2).sum():.0f}%")

# ---- Reading C: what a level hands each place of its unit, through the prolongation's form (harmonics times a state) ----
if len(sys.argv) > 3 and sys.argv[3] == 'places':
    written = ~P_open
    inside = np.zeros(places, bool); first = np.zeros(places, bool); lead_sym = np.empty(places, dtype=P_sym.dtype); news_at = np.zeros(places)
    r0 = 0
    for (lab, sites, anc, news) in regions:
        news_at[r0:r0 + sites] = news; r0 += sites
    for (ri, st, pv, nx, whole, a, b, nws, span) in E:
        if whole:
            inside[a:b] = True; first[a] = True; lead_sym[a:b] = st[0]
    fitP = infit[P_region]
    csym = top((c for c in P_sym[fitP & written]), 30)
    Yown = onehot(list(P_sym), csym); Ylead = onehot([c if ok else '' for c, ok in zip(lead_sym, inside)], csym)
    kron = lambda hh, g: (hh[:, :, None] * g[:, None, :]).reshape(len(hh), -1)
    def hands(state, name):
        F = np.hstack([kron(h, state[P_epoch]), h])
        out = []
        for label, rows, Yk in [("(a) its own symbol, places of a nat or more", inside & written & ~first & (news_at >= 1.0), Yown),
                                ("(b) its own symbol, places under a nat", inside & written & ~first & (news_at < 1.0), Yown),
                                ("(c) the unit's leading symbol, at its other places", inside & written & ~first, Ylead)]:
            fit, test = rows & fitP, rows & ~fitP
            W = ridge(F[fit], Yk[fit])
            out.append((label, 1000 * (1 - ((Yk[test] - F[test] @ W) ** 2).sum() / ((Yk[test] - Yk[fit].mean(0)) ** 2).sum()), int(test.sum())))
        print(f"LINKS reading C, a level's state read at each place's phase, state = {name}:")
        for label, v, n in out: print(f"LINKS   {label:52s} {v:6.0f}   (places read {n})")
    hands(X_l, f"a restriction of width {D1} located from the keys")
    hands(X_c, "the level's present read after its ticks")
    fitEp = np.array([infit[e[0]] for e in E])
    mfit = X_m[fitEp].mean(0); Cm = (X_m[fitEp] - mfit).T @ (X_m[fitEp] - mfit); wm, vm = np.linalg.eigh(Cm)
    hands((X_m - mfit) @ vm[:, -300:], "the moment, its 300 leading directions (a stand-in for full rank)")
    print(f"LINKS done in {time.time() - t0:.0f} s"); sys.exit(0)

links = [("the fine read at the leading place", X_read), ("the moment m(j), 768 numbers", X_m), ("the restricted state A m + b", X_r),
         ("a drawn restriction of the same width (mean of three)", X_d), ("a restriction of the same width located from the keys", X_l),
         ("the level's read after its ticks", X_c), ("the prolonged rows (leading place, epoch's mean)", X_p)]
print("LINKS reading A, present at each link, thousandths, read on half the regions (rows a key, columns a link):")
print("LINKS   links: " + " | ".join(f"{i}: {n}" for i, (n, _) in enumerate(links)))
tableA = {}
for name, mask, key_of, topn, bag in keys:
    idx = [i for i in range(len(E)) if mask(E[i])]
    vals = [float(np.mean([presence(x, idx, key_of, topn, bag)[0] for x in X])) if isinstance(X, list) else presence(X, idx, key_of, topn, bag)[0] for _, X in links]
    tableA[name] = vals
    print(f"LINKS   key {name:36s} " + " ".join(f"link{i}={v:5.0f}" for i, v in enumerate(vals)) + f"   (epochs {len(idx)})")
# The chart's fold: the bag in the moment, among whole epochs whose interior stays within one section and those that wind past it.
# The level's section is the flat face's code over the alphabet (the store's 244 classes), the news of a place nothing predicts.
ALPHABET = 244
sigma = math.log(ALPHABET)
short = [i for i in range(len(E)) if E[i][4] and E[i][8] < sigma]; long_ = [i for i in range(len(E)) if E[i][4] and E[i][8] >= sigma]
print(f"LINKS the fold: σ = {sigma:.2f} nats; whole epochs whose interior stays within a section {len(short)} ({100 * len(short) / (len(short) + len(long_)):.0f}%), winding past it {len(long_)}")
for kname, kf, topn, bag in [("its symbols as a bag", None, 40, True), ("its symbols by sixth of a turn", None, 20, 'phase'), ("its leading symbol", lambda e: e[1][0], 30, False), ("its last symbol", lambda e: e[1][-1], 30, False)]:
    vs, ns = presence(X_m, short, kf, topn, bag); vl, nl = presence(X_m, long_, kf, topn, bag)
    print(f"LINKS   the fold, in the moment, key {kname:32s} within a section {vs:5.0f}   winding past it {vl:5.0f}   (read {ns}, {nl})")

# ---- Reading B: the tension at the level's locus ----
Y = np.asarray(covector, np.float64) / float(1 << 24)
pw = (Y ** 2).sum(1)
print(f"LINKS reading B: the covector's power at the split: at the open place {100 * pw[P_open].sum() / pw.sum():.1f}% of it ({P_open.sum()} places), elsewhere {100 * pw[~P_open].sum() / pw.sum():.1f}% ({(~P_open).sum()} places)")
last = np.zeros(places, np.int64)  # each place's distance to its region's open place
row = 0
for (lab, sites, anc, news) in regions:
    last[row:row + sites] = sites - 1 - np.arange(sites); row += sites
print("LINKS   by places before the open one (0 the open place): " + " ".join(f"{k}:{100 * pw[last == k].sum() / pw.sum():.1f}%" for k in range(0, 9)))
fitP = infit[P_region]; testP = ~fitP
def removed(F, Yt_all=Y, note=""):
    """The share of the covector's power, on the held half, that a least-squares read of the features F removes."""
    Ff, Ft = F[fitP], F[testP]
    W = ridge(Ff, Yt_all[fitP])
    res = Yt_all[testP] - Ft @ W
    return 1 - (res ** 2).sum() / (Yt_all[testP] ** 2).sum(), 1 - (res[P_open[testP]] ** 2).sum() / (Yt_all[testP][P_open[testP]] ** 2).sum()
kron = lambda hh, g: (hh[:, :, None] * g[:, None, :]).reshape(len(hh), -1)
ones = np.ones((places, 1))
# (0) the place's own fine read
s0 = removed(np.hstack([np.asarray(read, np.float64) / 65536, ones]))
# (1) the level's present state through a refitted prolongation
F1 = np.hstack([kron(h, X_c[P_epoch]), h])
s1 = removed(F1)
# (2) the table: the epoch in progress and the epoch before, as their known symbols' moments on the news phase
TOP = 20
cs = top((c for c in P_sym[fitP]), TOP)
sym_idx = np.array([cs.get(c, TOP) for c in P_sym])
SM = np.zeros((epochs, H * (TOP + 1)))
known = ~P_open
for t in np.nonzero(known)[0]:
    SM[P_epoch[t], sym_idx[t] * H:(sym_idx[t] + 1) * H] += h[t]
prev = np.array([i - 1 if (i > 0 and E[i - 1][0] == E[i][0]) else -1 for i in range(epochs)])
SMp = np.where(prev[:, None] >= 0, SM[np.maximum(prev, 0)], 0.0)
g2 = np.hstack([SM, SMp])
F2 = np.hstack([kron(h, g2[P_epoch]), h])
s2 = removed(F2)
# (3) operands of the level's own width located from the moments of the two epochs
def pca(X, k, rows):
    m = X[rows].mean(0); C = (X[rows] - m).T @ (X[rows] - m); w, v = np.linalg.eigh(C); return (X - m) @ v[:, -k:]
fitEp = np.array([infit[e[0]] for e in E])
Zc = pca(X_m, 150, fitEp); Zp = np.where(prev[:, None] >= 0, Zc[np.maximum(prev, 0)], 0.0)
Z = np.hstack([Zc, Zp])
Zf = Z[fitEp]; Sz = Zf.T @ Zf / len(Zf) + 1e-6 * np.eye(Z.shape[1]); ez, vz = np.linalg.eigh(Sz); Zw = Z @ (vz / np.sqrt(ez))
F3 = kron(h, Zw[P_epoch])
Wfull = ridge(F3[fitP], Y[fitP])                                   # [(H × 300), D0]
C3 = Wfull.reshape(H, Z.shape[1], D0).transpose(0, 2, 1).reshape(H * D0, Z.shape[1])   # the map from the whitened moments to the harmonic blocks
Uc, sc, Vc = np.linalg.svd(C3, full_matrices=False)
Wloc = Vc[:D1].T                                                   # the located restriction, to D1 numbers
F3l = np.hstack([kron(h, (Zw @ Wloc)[P_epoch]), h])
s3 = removed(F3l); s3full = removed(np.hstack([F3, h]))
print("LINKS   share of the covector's power removed on the held half (all places | the open places alone):")
for name, s in [("(0) the place's own read at the split", s0), ("(1) the level's present state, prolongation refitted", s1), (f"(2) the table: two epochs' symbols on the news phase (top {TOP})", s2),
                (f"(3) operands of width {D1} located from the two epochs' moments", s3), ("(3') the same moments at full rank", s3full)]:
    print(f"LINKS   {name:66s} {s[0]:7.4f} | {s[1]:7.4f}")
# The planted law: a term of the table's own form (the epoch before's leading symbol, through the place's phase), a tenth of the power.
prng = np.random.default_rng(5)
# The plant is of the table's own form: the epoch before's symbols on the news phase, through a drawn map, read at the place's phase;
# it is added to the covector at a tenth of the covector's power and each reading is taken again on the sum.
Q = prng.standard_normal((H, SMp.shape[1], D0)) / math.sqrt(SMp.shape[1])
Pl = np.einsum('tk,tkd->td', h, np.einsum('ef,kfd->ekd', SMp, Q)[P_epoch])
Pl *= math.sqrt(0.1 * (Y ** 2).sum() / (Pl ** 2).sum())
Yp = Y + Pl
def recovered(F):
    """Of the plant's power on the held half, the part the features' fit on the planted covector takes back: 1 − |P − (fit(Y+P) − fit(Y))|²/|P|²."""
    Ff, Ft = F[fitP], F[testP]
    d_ = Ft @ (ridge(Ff, Yp[fitP]) - ridge(Ff, Y[fitP]))
    return 1 - ((Pl[testP] - d_) ** 2).sum() / (Pl[testP] ** 2).sum()
p2 = recovered(F2); p3 = removed(F3l, Pl)
print(f"LINKS   the planted law (the epoch before's symbols on the news phase through a drawn map, a tenth of the power): recovered {p2:.3f} by the table from the planted covector; with it the table removes {removed(F2, Yp)[0]:.4f} of the planted covector's power; operands located for the plain covector hold {p3[0]:.3f} of the plant")
# Operands located for the plant itself, from the moments: the instrument's own ceiling.
Wp = ridge(F3[fitP], Pl[fitP]); Cp = Wp.reshape(H, Z.shape[1], D0).transpose(0, 2, 1).reshape(H * D0, Z.shape[1])
_, _, Vp = np.linalg.svd(Cp, full_matrices=False)
p3own = removed(np.hstack([kron(h, (Zw @ Vp[:D1].T)[P_epoch]), h]), Pl)
print(f"LINKS   the planted law, operands of width {D1} located for it from the moments: recovered {p3own[0]:.3f}")
print(f"LINKS done in {time.time() - t0:.0f} s on this host's numpy (one process)")
