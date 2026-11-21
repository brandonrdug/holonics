"""A ruler: where an answer digit's row puts its weight, and how much of the digit it needs arrives (the lead, November 21, the reach).

`read-strand-states ... past rows` writes, for passages read by two streams, each open place's row at every tick and head (`shares.tsv`)
and its read after every tick (`open_K.i32`). `places.tsv` (make_rows.py) names, at each answer digit of a passage's last record, the
source places its value is fixed by: a copy's and a reversal's one operand digit, a sum's two aligned digits. This prints, by kind,
tick and head, the row's mean share on the needed source(s), on the near field (distance under six), on the same answer digit's
counterparts in the earlier records, and on every other site; and by least squares (fitted on the even rows, read on the odd), the
share of the needed digit's indicator (ten digits) that the open read after each tick removes, beside the symbol two places back (the
answer digit just written). Outside the machine; shares only. Usage: reach_ruler.py DUMP PLACES ROWS"""
import sys, collections
import numpy as np
d, places_f, rows_f = sys.argv[1], sys.argv[2], sys.argv[3]
dims = dict(l.split('\t') for l in open(d + '/dims.tsv').read().split('\n') if l)
width, ticks, heads = int(dims['read']), int(dims['ticks']), int(dims['heads'])
texts = []
for line in open(rows_f, encoding='utf-8'):
    f = line.rstrip('\n').split('\t')
    texts.append(f[1].replace('\\n', '\n') + '\n')
rowsel = [int(l.split('\t')[0]) for l in open(d + '/rows.tsv')]
n_by_row = collections.Counter(rowsel)
offset, acc = {}, 0
for r in sorted(n_by_row):
    offset[r] = acc; acc += n_by_row[r]
for r, t in enumerate(texts):
    assert n_by_row[r] == len(t), (r, n_by_row[r], len(t))
P = []
for line in open(places_f):
    r, kind, p, k, L, src = line.rstrip('\n').split('\t')
    srcs = [int(s) for s in src.split(',') if int(s) >= 0]
    P.append((int(r), kind, int(p), int(k), L, srcs))
want = {(r, p) for r, _, p, *_ in P}
shares = collections.defaultdict(dict)  # (r, tick, head, p) -> {j: share}
for line in open(d + '/shares.tsv'):
    r, t, h, p, j, s = map(int, line.split('\t'))
    if (r, p) in want:
        shares[(r, t, h, p)][j] = s / 1e6
def counterparts(r, kind, p, k, srcs):
    """The same digit's places in the earlier records: each earlier record's answer digit k and its operand digit k (counted as the
    kind counts them), where the record holds one."""
    text = texts[r]; lines = text.split('\n')[:-1]; out = []; at = 0
    for li, rec in enumerate(lines[:-1]):
        eq = rec.index(' = ') + 3
        if kind == 'sum':
            a, b = rec.split(' = ')[0].split(' + '); c = rec.split(' = ')[1]
            if k < len(c): out.append(at + eq + len(c) - 1 - k)
            if k < len(a): out.append(at + len(a) - 1 - k)
            if k < len(b): out.append(at + len(a) + 3 + len(b) - 1 - k)
        else:
            L = (len(rec) - eq + 1) // 2
            if k < L:
                out.append(at + eq + 2 * k)
                first = rec.index(' ') + 1
                out.append(at + first + 2 * (k if kind == 'copy' else L - 1 - k))
        at += len(rec) + 1
    return out
table = collections.defaultdict(lambda: np.zeros(5))
for (r, kind, p, k, L, srcs) in P:
    cp = set(counterparts(r, kind, p, k, srcs))
    for t in range(ticks):
        for h in range(heads):
            row = shares.get((r, t, h, p), {})
            need = sum(row.get(s, 0.0) for s in srcs)
            near = sum(v for j, v in row.items() if p - j < 6 and j not in srcs)
            conf = sum(v for j, v in row.items() if j in cp and p - j >= 6)
            other = 1.0 - need - near - conf
            table[(kind, t, h)] += np.array([1, need, near, conf, other])
print('REACH rows: kind tick head | places | needed source(s) | near field | the digit\'s counterparts in earlier records | the rest')
for key in sorted(table):
    c = table[key]
    print(f'REACH_ROW {key[0]} tick={key[1]} head={key[2]} places={int(c[0])} needed={c[1]/c[0]:.3f} near={c[2]/c[0]:.3f} counterparts={c[3]/c[0]:.3f} rest={c[4]/c[0]:.3f}')
# Presence by least squares.
n = acc
opens = [np.fromfile(f'{d}/open_{t}.i32', dtype='<i4').reshape(n, width).astype(np.float64) / 65536.0 for t in range(ticks)]
def onehot(ch):
    v = np.zeros(10); v[int(ch)] = 1.0; return v
by_kind = collections.defaultdict(list)
for (r, kind, p, k, L, srcs) in P:
    text = texts[r]
    need = [onehot(text[s]) for s in srcs]
    back2 = text[p - 2] if p >= 2 and text[p - 2].isdigit() else None
    by_kind[kind].append((r, p, need, back2, onehot(text[p]) if text[p].isdigit() else None))
def share(X, Y, side):
    Xa = np.hstack([X, np.ones((len(X), 1))])
    tr, te = side, ~side
    if tr.sum() < Xa.shape[1] + 5 or te.sum() < 5: return float('nan')
    W, *_ = np.linalg.lstsq(Xa[tr], Y[tr], rcond=None)
    res = Y[te] - Xa[te] @ W; base = Y[te] - Y[tr].mean(0)
    return 1.0 - (res ** 2).sum() / (base ** 2).sum()
for kind, items in sorted(by_kind.items()):
    rows_ = np.array([offset[r] + p for r, p, *_ in items]); side = np.array([r % 2 == 0 for r, *_ in items])
    for t in range(ticks):
        X = opens[t][rows_]
        cols = []
        for si in range(max(len(it[2]) for it in items)):
            sel = np.array([len(it[2]) > si for it in items])
            Y = np.array([it[2][si] if len(it[2]) > si else np.zeros(10) for it in items])
            cols.append(f'needed[{si}]={share(X[sel], Y[sel], side[sel]):.3f} (n={sel.sum()})')
        sel = np.array([it[4] is not None for it in items])
        Y = np.array([it[4] if it[4] is not None else np.zeros(10) for it in items])
        cols.append(f'own={share(X[sel], Y[sel], side[sel]):.3f}')
        sel = np.array([it[3] is not None for it in items])
        Y = np.array([onehot(it[3]) if it[3] is not None else np.zeros(10) for it in items])
        cols.append(f'two_back={share(X[sel], Y[sel], side[sel]):.3f}')
        print(f'REACH_PRESENCE {kind} tick={t} ' + ' '.join(cols))
