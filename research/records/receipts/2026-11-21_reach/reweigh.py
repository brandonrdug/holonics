"""A ruler: head 0's open rows at answer digits, reweighed at their present keys by a friction of distance `2^(−φ ⌊log₂ d⌋)` (the
octave falloff the turned heads carry), the needed source's share and its counterparts' read at each φ. First-order: the keys,
values and later ticks are the state's, so it reads what a located friction would buy at the row, not what the face then writes.
Usage: reweigh.py DUMP PLACES ROWS HEAD"""
import sys, collections, math
sys.argv += []
d, places_f, rows_f, head = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])

dims = dict(l.split('\t') for l in open(d + '/dims.tsv').read().split('\n') if l)
ticks = int(dims['ticks'])
texts = [l.rstrip('\n').split('\t')[1].replace('\\n', '\n') + '\n' for l in open(rows_f, encoding='utf-8')]
P = []
for line in open(places_f):
    r, kind, p, k, L, src = line.rstrip('\n').split('\t')
    P.append((int(r), kind, int(p), int(k), L, [int(s) for s in src.split(',') if int(s) >= 0]))
want = {(r, p) for r, _, p, *_ in P}
rows = collections.defaultdict(dict)
for line in open(d + '/shares.tsv'):
    r, t, h, p, j, s = map(int, line.split('\t'))
    if h == head and (r, p) in want:
        rows[(r, t, p)][j] = s / 1e6
def cps(r, kind, p, k):
    lines = texts[r].split('\n')[:-1]; out = []; at = 0
    for rec in lines[:-1]:
        eq = rec.index(' = ') + 3
        if kind == 'sum':
            a, b = rec.split(' = ')[0].split(' + '); c = rec.split(' = ')[1]
            if k < len(c): out.append(at + eq + len(c) - 1 - k)
            if k < len(a): out.append(at + len(a) - 1 - k)
            if k < len(b): out.append(at + len(a) + 3 + len(b) - 1 - k)
        else:
            L = (len(rec) - eq + 1) // 2
            if k < L:
                out.append(at + eq + 2 * k); first = rec.index(' ') + 1
                out.append(at + first + 2 * (k if kind == 'copy' else L - 1 - k))
        at += len(rec) + 1
    return set(out)
oct_ = lambda x: int(math.floor(math.log2(x)))
for kind in ('copy', 'reverse', 'sum'):
    for t in range(ticks):
        out = []
        for phi in (0.0, 0.5, 1.0, 2.0):
            acc = [0, 0.0, 0.0, 0]
            for (r, kd, p, k, L, srcs) in P:
                if kd != kind: continue
                row = rows.get((r, t, p))
                if not row: continue
                c = cps(r, kind, p, k)
                w = {j: v * 2 ** (-phi * oct_(p - j)) for j, v in row.items()}
                z = sum(w.values())
                acc[0] += 1; acc[1] += sum(w.get(s, 0) for s in srcs) / z; acc[2] += sum(v for j, v in w.items() if j in c) / z
            out.append(f'phi={phi}: needed {acc[1]/acc[0]:.3f} counterparts {acc[2]/acc[0]:.3f}')
        print(f'REWEIGH head={head} {kind} tick={t} | ' + ' | '.join(out))
