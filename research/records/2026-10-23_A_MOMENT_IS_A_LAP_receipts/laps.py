"""Looking again as laps around the check loop. For each of Athena's
published lines, the circulation of the check loop on each cheap ring of
base ten, d_q = q(release) - T_q(q(a), q(b)) mod q, and the fibre left in
the size window after each lap (one ring per lap: 10, 9, 11, then 101).
Then the same lap count over every two-digit operand pair. Exact integer
work; this is an exterior reading of what the faces determine (a ceiling),
not the machine's own result."""
import json, collections

# Earlier set: the held-back draws published by the design thread and kept
# in the near-miss receipts (faces.py). Later set: the pumped tower's stream
# read on unseen pairs, published in the design thread on October 23.
EARLIER = ["85-42=43","71+41=102","73+31=104","23+51=84","56+3=56","8+82=90",
           "47-20=27","99-56=5","74-72=1","92*65=6090","83*27=2309","46*15=850","12*35=405"]
LATER = ["74-72=6","92*65=6030","85-42=43","46*15=700","71+41=112","86-43=43","83*27=2229",
         "73+31=106","14*39=526","23+51=74","56+3=59","53+18=71","80+14=94","8+82=80",
         "47-20=27","12*35=470","6+77=83","99-56=43","67-56=19","6+10=16","94-27=67"]
RINGS = [10, 9, 11, 101]

def ev(a, op, b): return a + b if op == '+' else a - b if op == '-' else a * b
def window(a, op, b):
    # the size face: lengths and one leading digit of each operand, exact enclosure
    def iv(x):
        s = len(str(x)) - 1; A = x // 10**s
        return A * 10**s, (A + 1) * 10**s - 1
    (al, ah), (bl, bh) = iv(a), iv(b)
    if op == '+': return al + bl, ah + bh
    if op == '*': return al * bl, ah * bh
    return max(al - bh, 0), ah - bl
def parse(line):
    lhs, r = line.split('='); op = next(c for c in "+-*" if c in lhs)
    a, b = map(int, lhs.split(op)); return a, op, b, int(r)
def fibres(a, op, b):
    t = ev(a, op, b); lo, hi = window(a, op, b)
    cand = list(range(lo, hi + 1)); sizes = [len(cand)]
    for q in RINGS:
        cand = [x for x in cand if (x - t) % q == 0]; sizes.append(len(cand))
    return sizes
def laps_to_close(sizes):
    return next((k for k, s in enumerate(sizes) if s == 1), None)

def read(lines):
    out = []
    for line in lines:
        a, op, b, r = parse(line); t = ev(a, op, b); lo, hi = window(a, op, b)
        d = {q: (r - t) % q for q in RINGS}
        sizes = fibres(a, op, b)
        out.append(dict(line=line, true=t, right=(r == t), size_kept=lo <= r <= hi,
                        defect={str(q): d[q] for q in RINGS},
                        first_failing_ring=next((q for q in RINGS if d[q]), None),
                        fibre_after_laps=sizes, laps_to_close=laps_to_close(sizes)))
    return out

earlier, later = read(EARLIER), read(LATER)
for name, rows in (("earlier", earlier), ("later", later)):
    print(name)
    for x in rows:
        print(f"  {x['line']:12s} true {x['true']:5d} right {x['right']!s:5s} size {x['size_kept']!s:5s} "
              f"defects {x['defect']}  fibre {x['fibre_after_laps']}  laps {x['laps_to_close']}")
    wrong = [x for x in rows if not x['right']]
    print(f"  wrong {len(wrong)} of {len(rows)}; caught on the first lap (ring 10): "
          f"{sum(x['defect']['10'] != 0 for x in wrong)}; by the third lap (rings 10, 9, 11): "
          f"{sum(any(x['defect'][str(q)] for q in (10, 9, 11)) for x in wrong)}; "
          f"closed by the third lap: {sum(x['laps_to_close'] is not None and x['laps_to_close'] <= 3 for x in wrong)}")

# The same questions in both sets: which changed between the two runs.
e = {x['line'].split('=')[0]: x for x in earlier}
both = [(k, e[k], x) for x in later for k in [x['line'].split('=')[0]] if k in e]
changes = [dict(question=k, earlier=a['line'], later=b['line'], earlier_right=a['right'], later_right=b['right'])
           for k, a, b in both]
print("same question in both runs:")
for c in changes: print(f"  {c['earlier']:12s} -> {c['later']:12s} {c['earlier_right']} -> {c['later_right']}")

# Every two-digit operand pair: how many laps close the release.
census = {}
for op in "+-*":
    hist = collections.Counter()
    for a in range(10, 100):
        for b in range(10, 100):
            if op == '-' and a < b: continue
            hist[laps_to_close(fibres(a, op, b))] += 1
    census[op] = {str(k): v for k, v in sorted(hist.items(), key=lambda kv: (kv[0] is None, kv[0] or 0))}
    print(op, census[op])

json.dump(dict(earlier=earlier, later=later, same_question=changes, census_two_digit=census),
          open('laps.json', 'w'), indent=1)
