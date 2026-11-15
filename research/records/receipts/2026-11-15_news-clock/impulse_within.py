import sys, math, bisect, statistics as st, importlib.util
spec = importlib.util.spec_from_file_location('lt', str(__import__('pathlib').Path(__file__).resolve().parents[4] / 'tools' / 'loudness_table.py')); lt = importlib.util.module_from_spec(spec); spec.loader.exec_module(lt)
rows, L = lt.read(sys.argv[1])
ps = [r for r in rows if r['row'] == 'P' and not math.isnan(r['loud'])]
seqs = {}
for p in ps:
    seqs.setdefault((p['slice'], p['stretch']), []).append(p)
for s in seqs.values():
    s.sort(key=lambda p: p['t'])
    m = st.mean(p['loud'] for p in s)
    codes = sorted(p['code'] for p in s)
    for p in s:
        p['rl'] = p['loud'] - m
        p['wq'] = min(4, bisect.bisect_right(codes, p['code']) * 5 // len(codes))
print('stretches', len(seqs), 'places a stretch median', st.median(len(s) for s in seqs.values()))
for region in sorted({p['slice'] for p in ps}):
    for oq in (0, 4):
        line = []
        for tau in (1, 2, 3, 4, 6, 8, 10, 16, 24, 32, 64):
            cell = {}
            for (sl, _), s in seqs.items():
                if sl != region:
                    continue
                for k in range(tau, len(s)):
                    p, b = s[k], s[k - tau]
                    if p['wq'] != oq:
                        continue
                    cell.setdefault(b['wq'], []).append(p['rl'])
            q1, q5 = cell.get(0, []), cell.get(4, [])
            line.append('%d:%+.3f' % (tau, st.mean(q5) - st.mean(q1) if q1 and q5 else float('nan')))
        print('WITHIN region=%s own=q%d %s' % (region, oq + 1, ' '.join(line)))
