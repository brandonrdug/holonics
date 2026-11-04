"""§16.42: the restated results' ends, from restate-field's RESTATEMENTS.tsv (private; this prints only counts and means).

Per state (alone open; the restatement open; the result and its restatement open; the `>>` and the restatement open;
every answer site but the result's open), per place (D's first, D's last, the
place after D) and per length |C|: the reads, the mean code the place costs, -log2 p(true) in bits, the reads whose face
gives the answer's class more than half, and at the last tick the mean share each head kind (still, turned) puts on the
restatement's offset |C| + 2 and on its two neighbours. Shares are on 2^-63 of their row; a report's reading, written here
in floating point.
"""
import csv, math, sys
from collections import defaultdict

rows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t'))
ticks = 1 + max(int(c.split('h')[0][1:]) for c in rows[0] if c.startswith('t') and 'h' in c and 'd' in c)
last = ticks - 1
kinds = {'still': (0, 1), 'turned': (2, 3)}
groups = defaultdict(list)
for r in rows:
    L = int(r['length'])
    groups[(r['state'], r['at'], min(L, 4))].append(r)  # lengths past 3 read outside the near field together
print("state\tat\tlength\treads\tcode_bits\thalf_or_more\tstill_at(d*-1,d*,d*+1)\tturned_at(d*-1,d*,d*+1)")
order = {'alone': 0, 'restated_open': 1, 'both_open': 2, 'between_open': 3, 'answer_open': 4}; place = {'first': 0, 'last': 1, 'stop': 2}
for (state, at, L), rs in sorted(groups.items(), key=lambda kv: (order[kv[0][0]], place[kv[0][1]], kv[0][2])):
    code = sum(-math.log2(max(int(r['p_true']), 1) / int(r['p_total'])) for r in rs) / len(rs)
    half = sum(2 * int(r['p_true']) > int(r['p_total']) for r in rs)
    def share(kind, delta):
        out = []
        for r in rs:
            d = int(r['offset']) + delta
            out.append(sum(int(r[f't{last}h{h}d{d}']) for h in kinds[kind]) / len(kinds[kind]) / 2**63 if 1 <= d <= 5 else float('nan'))
        good = [x for x in out if x == x]
        return sum(good) / len(good) if good else float('nan')
    s = tuple(round(share('still', k), 3) for k in (-1, 0, 1)); t = tuple(round(share('turned', k), 3) for k in (-1, 0, 1))
    print(f"{state}\t{at}\t{'4+' if L == 4 else L}\t{len(rs)}\t{code:.3f}\t{half}\t{s}\t{t}")
