#!/usr/bin/env -S python3 -I
"""found_between_ruler.py FORM: a ruler (the lead, November 28; the formal thread's G-Z63 of 00:57 UTC), run from the line's run
directory. Units founded between the rise cut's ends (`rise_cut_ruler.py`, FORM `rise` or `peak`) on the founding sample: each run of 2 to
8 octets between consecutive ends, in the sample's order, founded where its prequential saving passes the pool's charge,
`(n − 1)(c − log₂(U + 2)) > log₂|P| + 1`; the founded runs' octets in hex go to `long/found_between_FORM.tsv` (private, for
`unit_cut_ruler.py`). Outside the machine; counts and means.
"""
import sys, math
from collections import defaultdict
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import rise_cut_ruler as R
form = sys.argv[1]
st = R.rows_of('units/found_rows.tsv'); sc = R.codes_of('units/codes_sample', len(st))
total, count = defaultdict(int), defaultdict(int)
for r, t in enumerate(st):
    c = sc[r]
    for p in range(len(t) - 1):
        if p + 1 not in c: continue
        for k in range(1, 9):
            if p - k + 1 < 0: break
            s = t[p - k + 1:p + 1]; total[s] += c[p + 1]; count[s] += 1
def cut(t):
    n = len(t); nu = []
    for p in range(n):
        num = den = 0
        for k in range(1, 9):
            if p - k + 1 < 0: break
            s = t[p - k + 1:p + 1]
            if s in count: num += total[s]; den += count[s]
        nu.append(num / den if den else None)
    rise = [p > 0 and nu[p] is not None and nu[p - 1] is not None and nu[p] > nu[p - 1] for p in range(n)]
    a = [0]
    for p in range(n - 1):
        if rise[p] and (form == 'rise' or not (p + 1 < n and rise[p + 1])): a.append(p + 1)
    return a
# the sample's runs between consecutive ends, in order, each with her code over its places (2^-20 bits)
epochs = []
for r, t in enumerate(st):
    a = cut(t); c = sc[r]
    for x, y in zip(a, a[1:]):
        if 2 <= y - x <= 8 and all(q in c for q in range(x, y)):
            epochs.append((t[x:y], sum(c[q] for q in range(x, y)) / (1 << 20)))
P = len(epochs); seen = defaultdict(int); units = []
held = set()
for u, cbits in epochs:
    seen[u] += 1
    if u in held: continue
    saving = (seen[u] - 1) * (cbits - math.log2(len(held) + 2))
    if saving > math.log2(P) + 1:
        held.add(u); units.append(u)
print(f"FOUND_BETWEEN form={form} epochs={P} founded={len(units)} by_length=" + ','.join(str(sum(1 for u in units if len(u) == L)) for L in range(2, 9)))
open(f'long/found_between_{form}.tsv', 'w').write(''.join(u.hex() + '\n' for u in units))
