"""A ruler: where a sum's answer digit takes its two operands and its carry, and how much of each arrives (the lead, November 22).

`read-strand-states ... past rows` writes, for passages read by two streams, each open place's row at every tick and head (`shares.tsv`)
and its read after every tick (`open_K.i32`). `places.tsv` (make_rows.py) names each answer digit of a passage's last record. For a sum
`a + b = c` written left to right, the digit `k` from the right is fixed by `a_k`, `b_k` and the carry into `k`, which the lower digits
`a_j`, `b_j` (`j < k`) fix: `carry_k = [a mod 10^k + b mod 10^k >= 10^k]`. This prints, by tick and head, the row's mean share on `a_k`, on
`b_k`, on the lower digits of both (the carry's sources), on the higher digits of both, on the answer digits already written, on the near
field (distance under six, not counted above), on the same digit's counterparts in the earlier records, and on the rest; then by least
squares (fitted on the even rows, read on the odd), the share of each quantity's indicator the open read after each tick removes: `a_k`,
`b_k`, the carry, `(a_k + b_k) mod 10` and the answer digit itself; split by whether the carry is one. Outside the machine; shares only.
Usage: sum_ruler.py DUMP PLACES ROWS"""
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
P = []
for line in open(places_f):
    r, kind, p, k, L, src = line.rstrip('\n').split('\t')
    if kind != 'sum':
        continue
    r, p, k = int(r), int(p), int(k)
    text = texts[r]
    start = text.rfind('\n', 0, p) + 1
    rec = text[start:text.index('\n', start)]
    lhs, c = rec.split(' = ')
    a, b = lhs.split(' + ')
    pos_a = lambda j: start + len(a) - 1 - j
    pos_b = lambda j: start + len(a) + 3 + len(b) - 1 - j
    ak = [pos_a(k)] if k < len(a) else []
    bk = [pos_b(k)] if k < len(b) else []
    lower = [pos_a(j) for j in range(min(k, len(a)))] + [pos_b(j) for j in range(min(k, len(b)))]
    higher = [pos_a(j) for j in range(k + 1, len(a))] + [pos_b(j) for j in range(k + 1, len(b))]
    eq = start + len(lhs) + 3
    written = list(range(eq, p))
    carry = int((int(a) % 10 ** k) + (int(b) % 10 ** k) >= 10 ** k)
    digit_a = int(a[len(a) - 1 - k]) if k < len(a) else 0
    digit_b = int(b[len(b) - 1 - k]) if k < len(b) else 0
    # counterparts: the same digit k of each earlier record's operands and answer
    cp = []
    at = 0
    for li, prev in enumerate(text.split('\n')[:-1]):
        if at >= start:
            break
        pl, pc = prev.split(' = ')
        pa, pb = pl.split(' + ')
        if k < len(pa): cp.append(at + len(pa) - 1 - k)
        if k < len(pb): cp.append(at + len(pa) + 3 + len(pb) - 1 - k)
        if k < len(pc): cp.append(at + len(pl) + 3 + len(pc) - 1 - k)
        at += len(prev) + 1
    P.append(dict(r=r, p=p, k=k, ak=ak, bk=bk, lower=lower, higher=higher, written=written, cp=cp, carry=carry,
                  da=digit_a, db=digit_b, own=int(text[p]), top=(k >= max(len(a), len(b)))))
want = {(x['r'], x['p']) for x in P}
shares = collections.defaultdict(dict)
for line in open(d + '/shares.tsv'):
    r, t, h, p, j, s = map(int, line.split('\t'))
    if (r, p) in want:
        shares[(r, t, h, p)][j] = s / 1e6
parts = ['a_k', 'b_k', 'lower', 'higher', 'written', 'near', 'counterparts', 'rest']
table = collections.defaultdict(lambda: np.zeros(len(parts) + 1))
for x in P:
    sets = [set(x['ak']), set(x['bk']), set(x['lower']), set(x['higher']), set(x['written'])]
    named = set().union(*sets)
    for t in range(ticks):
        for h in range(heads):
            row = shares.get((x['r'], t, h, x['p']), {})
            v = [sum(row.get(j, 0.0) for j in s) for s in sets]
            near = sum(s for j, s in row.items() if x['p'] - j < 6 and j not in named)
            conf = sum(s for j, s in row.items() if j in x['cp'] and x['p'] - j >= 6 and j not in named)
            rest = 1.0 - sum(v) - near - conf
            for key in (('all', t, h), ('carry' if x['carry'] else 'no_carry', t, h)):
                table[key] += np.array([1] + v + [near, conf, rest])
print('SUM rows: split tick head | places | ' + ' | '.join(parts))
for key in sorted(table):
    c = table[key]
    print(f'SUM_ROW {key[0]} tick={key[1]} head={key[2]} places={int(c[0])} ' + ' '.join(f'{n}={c[i + 1] / c[0]:.3f}' for i, n in enumerate(parts)))
n = acc
opens = [np.fromfile(f'{d}/open_{t}.i32', dtype='<i4').reshape(n, width).astype(np.float64) / 65536.0 for t in range(ticks)]
def onehot(v, m=10):
    o = np.zeros(m); o[v] = 1.0; return o
def ridge(X, Y, lam):
    mx, my = X.mean(0), Y.mean(0)
    Xc, Yc = X - mx, Y - my
    W = np.linalg.solve(Xc.T @ Xc + lam * np.eye(X.shape[1]), Xc.T @ Yc)
    return lambda Z: (Z - mx) @ W + my
def share(X, Y, side):
    """Ridge regression fitted on the even rows, its shrinkage chosen on a split of the even rows alone, read on the odd: the share of
    the indicator's variance the read removes (224 coordinates against some 700 fitted rows, so a plain least squares overfits)."""
    tr, te = np.where(side)[0], np.where(~side)[0]
    if len(tr) < 40 or len(te) < 5: return float('nan')
    scale = np.trace(np.cov(X[tr].T)) / X.shape[1]
    a, b = tr[: len(tr) // 2], tr[len(tr) // 2:]
    best, best_lam = -1e9, scale
    for lam in scale * np.array([0.01, 0.1, 1, 10, 100, 1000]) * len(a):
        f = ridge(X[a], Y[a], lam)
        r = 1.0 - ((Y[b] - f(X[b])) ** 2).sum() / ((Y[b] - Y[a].mean(0)) ** 2).sum()
        if r > best: best, best_lam = r, lam * len(tr) / len(a)
    f = ridge(X[tr], Y[tr], best_lam)
    return 1.0 - ((Y[te] - f(X[te])) ** 2).sum() / ((Y[te] - Y[tr].mean(0)) ** 2).sum()
rows_ = np.array([offset[x['r']] + x['p'] for x in P]); side = np.array([x['r'] % 2 == 0 for x in P])
inner = np.array([not x['top'] for x in P])
qty = {
    'a_k': np.array([onehot(x['da']) for x in P]),
    'b_k': np.array([onehot(x['db']) for x in P]),
    'carry': np.array([onehot(x['carry'], 2) for x in P]),
    'pair_mod10': np.array([onehot((x['da'] + x['db']) % 10) for x in P]),
    'answer': np.array([onehot(x['own']) for x in P]),
}
print(f'SUM presence: {len(P)} answer digits, {int(inner.sum())} under the top, {sum(x["carry"] for x in P)} with a carry in')
for t in range(ticks):
    X = opens[t][rows_]
    print(f'SUM_PRESENCE tick={t} ' + ' '.join(f'{name}={share(X[inner], Y[inner], side[inner]):.3f}' for name, Y in qty.items()))
