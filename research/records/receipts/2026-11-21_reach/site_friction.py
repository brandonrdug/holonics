"""A ruler: does a place's own read tell where head 0's friction pays (the lead, November 21, the reach)? Per place, the gain of the
ruler's friction of one bit an octave on head 0's listeners, g = c(law) − c(ψ = 1) in nats (read-reach's codes.tsv), against the open
place's read after the last tick (read-strand-states: open_3.i32 with `rows`, open_last.i32 with `carries`). Least squares on the
read, fitted on the even rows and read on the odd, on the terrain's passages and the held text together; then the codes if the friction
stood only where the fitted gain is positive: the held text's mean code a place and the terrain's answer digits' by kind. Outside the
machine; shares only. Usage: site_friction.py TERRAIN_DUMP TERRAIN_CODES PLACES TEXT_DUMP TEXT_CODES"""
import sys, math, collections
import numpy as np
td, tc, pf, xd, xc = sys.argv[1:6]
LN2 = math.log(2)
def codes(d, col):
    out = {}
    for line in open(d + '/codes.tsv'):
        f = line.rstrip('\n').split('\t')
        out[(int(f[0]), int(f[2]))] = (int(f[3]) / 2**20 * LN2, int(f[3 + col]) / 2**20 * LN2)
    return out
def reads(d, name):
    w = int(dict(l.split('\t') for l in open(d + '/dims.tsv').read().split('\n') if l)['read'])
    rows = [tuple(map(int, l.split('\t')[0:1] + l.split('\t')[2:3])) for l in open(d + '/rows.tsv')]
    x = np.fromfile(d + '/' + name, dtype='<i4').reshape(len(rows), w).astype(np.float64) / 65536.0
    return rows, x
setting = [l.strip() for l in open(tc + '/settings.tsv')].index('0:1:1000')
ct, cx = codes(tc, setting), codes(xc, setting)
rt, Xt = reads(td, 'open_3.i32')
rx, Xx = reads(xd, 'open_last.i32')
answer = {}
for line in open(pf):
    r, kind, p, *_ = line.rstrip('\n').split('\t')
    answer[(int(r), int(p))] = kind
rows, X, g, base, fr, tag = [], [], [], [], [], []
for (src, rr, XX, cc) in (('terrain', rt, Xt, ct), ('text', rx, Xx, cx)):
    for i, (r, p) in enumerate(rr):
        if p == 0 or (r, p) not in cc:
            continue
        a, b = cc[(r, p)]
        rows.append((src, r)); X.append(XX[i]); g.append(a - b); base.append(a); fr.append(b)
        tag.append(answer.get((r, p), 'other') if src == 'terrain' else 'text')
X, g, base, fr = np.array(X), np.array(g), np.array(base), np.array(fr)
tag = np.array(tag); even = np.array([r % 2 == 0 for _, r in rows])
Xa = np.hstack([X, np.ones((len(X), 1))])
W, *_ = np.linalg.lstsq(Xa[even], g[even], rcond=None)
pred = Xa @ W
te = ~even
r2 = 1 - ((g[te] - pred[te]) ** 2).sum() / ((g[te] - g[even].mean()) ** 2).sum()
print(f'SITE_FRICTION places={len(g)} held={te.sum()} gain_mean={g[te].mean():.4f} r2_held={r2:.3f}')
gated = np.where(pred > 0, fr, base)
for t in ('text', 'copy', 'reverse', 'sum', 'other'):
    s = te & (tag == t)
    if s.sum():
        print(f'SITE_FRICTION_CODES {t:8s} n={s.sum():6d} law={base[s].mean():.4f} friction_everywhere={fr[s].mean():.4f} friction_where_read={gated[s].mean():.4f} share_gated={(pred[s] > 0).mean():.3f}')
