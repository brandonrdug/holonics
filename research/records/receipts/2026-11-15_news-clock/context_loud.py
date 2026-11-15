import sys, math, statistics as st
import importlib.util
spec = importlib.util.spec_from_file_location('lt', str(__import__('pathlib').Path(__file__).resolve().parents[4] / 'tools' / 'loudness_table.py')); lt = importlib.util.module_from_spec(spec); spec.loader.exec_module(lt)
rows, L = lt.read(sys.argv[1])
ps = [r for r in rows if r['row'] == 'P' and not math.isnan(r['loud'])]
by = {}
for p in ps:
    by.setdefault((p['slice'], p['stretch']), []).append(p)
gaps = 0
for seq in by.values():
    seq.sort(key=lambda p: p['t'])
    for a, b in zip(seq, seq[1:]):
        if b['t'] == a['t'] + 1:
            b['pc'] = a['code']; b['ploud'] = a['loud']
        else:
            gaps += 1
print('places', len(ps), 'stretches', len(by), 'gaps', gaps)
def rankq(v, x):
    # fifth of x in sorted v
    import bisect
    return min(4, bisect.bisect_right(v, x) * 5 // len(v))
def spearman(a, b):
    def rk(v):
        o = sorted(range(len(v)), key=lambda i: v[i]); r = [0] * len(v)
        for k, i in enumerate(o): r[i] = k
        return r
    ra, rb = rk(a), rk(b); n = len(a); ma = (n - 1) / 2
    num = sum((x - ma) * (y - ma) for x, y in zip(ra, rb)); den = sum((x - ma) ** 2 for x in ra)
    return num / den
for region in sorted({p['slice'] for p in ps}):
    q = [p for p in ps if p['slice'] == region and 'pc' in p]
    own = sorted(p['code'] for p in q); prev = sorted(p['pc'] for p in q)
    print('REGION', region, 'places', len(q), 'spearman loud~own_code %+.3f' % spearman([p['loud'] for p in q], [p['code'] for p in q]),
          'loud~prev_code %+.3f' % spearman([p['loud'] for p in q], [p['pc'] for p in q]), 'loud~prev_loud %+.3f' % spearman([p['loud'] for p in q], [p['ploud'] for p in q]))
    # loudness by the previous place's surprise fifth, within the place's own surprise fifth
    table = {}
    for p in q:
        table.setdefault((rankq(own, p['code']), rankq(prev, p['pc'])), []).append(p['loud'])
    for o in range(5):
        print('  own_q%d' % (o + 1), ' '.join('prev_q%d=%.3f(%d)' % (k + 1, st.mean(table.get((o, k), [float('nan')])), len(table.get((o, k), []))) for k in range(5)))
    # a piece's loudness across its occurrences: how much the piece explains, and how much the preceding surprise adds within a piece
    pieces = {}
    for p in q:
        if p['piece3']:
            pieces.setdefault(p['piece3'], []).append(p)
    big = {k: v for k, v in pieces.items() if len(v) >= 40}
    allv = [p['loud'] for v in big.values() for p in v]
    tot = st.pvariance(allv); within = sum(st.pvariance([p['loud'] for p in v]) * len(v) for v in big.values()) / len(allv)
    wc = []
    for v in big.values():
        if len({p['pc'] for p in v}) > 3:
            wc.append((len(v), spearman([p['loud'] for p in v], [p['pc'] for p in v])))
    print('  pieces(>=40) %d places %d loud_var_total %.4f within_piece_share %.3f  within-piece spearman loud~prev_code weighted %+.3f' % (
        len(big), len(allv), tot, within / tot, sum(n * r for n, r in wc) / sum(n for n, _ in wc)))
