import sys, math, bisect, statistics as st, importlib.util
spec = importlib.util.spec_from_file_location('lt', str(__import__('pathlib').Path(__file__).resolve().parents[4] / 'tools' / 'loudness_table.py')); lt = importlib.util.module_from_spec(spec); spec.loader.exec_module(lt)
rows, L = lt.read(sys.argv[1])
ps = [r for r in rows if r['row'] == 'P' and not math.isnan(r['loud'])]
seqs = {}
for p in ps:
    seqs.setdefault((p['slice'], p['stretch']), []).append(p)
for s in seqs.values():
    s.sort(key=lambda p: p['t'])
def fifth(v, x):
    return min(4, bisect.bisect_right(v, x) * 5 // len(v))
for region in sorted({p['slice'] for p in ps}):
    own = sorted(p['code'] for p in ps if p['slice'] == region)
    for oq in (0, 4):
        line = []
        for tau in list(range(1, 17)) + [24, 32, 64]:
            cell = {}
            for (sl, _), s in seqs.items():
                if sl != region:
                    continue
                for k in range(tau, len(s)):
                    p, b = s[k], s[k - tau]
                    if fifth(own, p['code']) != oq:
                        continue
                    cell.setdefault(fifth(own, b['code']), []).append(p['loud'])
            q1, q5 = cell.get(0, []), cell.get(4, [])
            gap = st.mean(q5) - st.mean(q1) if q1 and q5 else float('nan')
            line.append('%d:%+.3f' % (tau, gap))
        print('IMPULSE region=%s own=q%d gap_q5_minus_q1 %s' % (region, oq + 1, ' '.join(line)))
