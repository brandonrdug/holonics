# A ruler: where an aligned digit's identity is lost between its value word and the open row's current (head 0), on a read-tension all dump
# with value.i64 and shares.tsv. For each open place where both operands hold the column: the terms p(a_k) v(a_k), p(b_k) v(b_k), the rest of
# the row, and the engine's own current; a linear read of each for a_k's and b_k's digit (fit on half the records, read on the other).
import sys, os, hashlib, collections
import numpy as np
sys.path.insert(0, 'tools')
import tension_ruler as t
d = sys.argv[1]; H = 0; heads = 4
dims = dict(l.split('\t') for l in open(d + '/dims.tsv').read().splitlines())
dw, m2, ticks = int(dims['lambda']), int(dims['current']), int(dims['ticks'])
rows = [l.split('\t') for l in open(d + '/rows.tsv').read().splitlines()]
n = len(rows)
val = np.fromfile(d + '/value.i64', dtype='<i8').reshape(n, m2) / 2.0**16
cur = np.fromfile(d + '/current.i64', dtype='<i8').reshape(n, m2) / 2.0**16
nm = m2 // (2 * heads)
cols = np.r_[H * nm:(H + 1) * nm, m2 // 2 + H * nm:m2 // 2 + (H + 1) * nm]
at = {(r[0], int(r[1]), int(r[2]), int(r[4])): k for k, r in enumerate(rows)}  # (label, place, tick, site) -> row
out = collections.defaultdict(list)
for line in open(d + '/shares.tsv'):
    lab, place, k, h, i, *rest = line.rstrip('\n').split('\t')
    if int(h) != H: continue
    _, kind, op, a, b, v = lab.split(':')
    if op != '+' or kind != 'met': continue
    i = int(i); place = int(place); k = int(k)
    _, kv, _ = t.site_role(lab, i)
    if not (kv < len(a) and kv < len(b)): continue
    ak, bk = len(a) - 1 - kv, len(a) + 3 + len(b) - 1 - kv
    cells = [x.split(':') for x in (rest[0].split(' ') if rest and rest[0] else [])]
    p = {int(c[0]): int(c[1]) / 1e6 for c in cells}
    A = p.get(ak, 0.0) * val[at[(lab, place, k, ak)]][cols]
    B = p.get(bk, 0.0) * val[at[(lab, place, k, bk)]][cols]
    rest_sum = sum(pj * val[at[(lab, place, k, j)]][cols] for j, pj in p.items() if j not in (ak, bk))
    y = cur[at[(lab, place, k, i)]][cols]
    da, db = (int(a) // 10**kv) % 10, (int(b) // 10**kv) % 10
    half = hashlib.sha256(f'half:{lab}'.encode()).digest()[0] % 2
    out[k].append((A, B, rest_sum, y, da, db, half, p.get(ak, 0.0), p.get(bk, 0.0)))
print('ARRIVE tick rows mean_p_a mean_p_b synth_error | a from: A alone, A+B, A+B+rest, current | b from: B alone, A+B, A+B+rest, current')
for k in sorted(out):
    L = out[k]
    A, B, Rs, Y = (np.array([x[i] for x in L]) for i in range(4))
    da, db, half = (np.array([x[i] for x in L]) for i in (4, 5, 6))
    fit, test = half == 0, half == 1
    oa, ob = t.onehot(da) - t.onehot(da).mean(0), t.onehot(db) - t.onehot(db).mean(0)
    err = np.abs(A + B + Rs - Y).mean() / np.abs(Y).mean()
    r = lambda f, target: t.removed(f, target, fit, test)
    print(f'ARRIVE {k} {len(L)} {np.mean([x[7] for x in L]):.3f} {np.mean([x[8] for x in L]):.3f} {err:.3f} | {r(A, oa):.3f} {r(A + B, oa):.3f} {r(A + B + Rs, oa):.3f} {r(Y, oa):.3f} | {r(B, ob):.3f} {r(A + B, ob):.3f} {r(A + B + Rs, ob):.3f} {r(Y, ob):.3f}')
