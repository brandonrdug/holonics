"""Summarize the segment probe's decision terms per constitution, exactly (integers and cells)."""
import re, sys
from collections import Counter, defaultdict

text = open(sys.argv[1]).read().splitlines()
term = re.compile(r'^      station (\d+) at refinement Some\((\d+)\): target (\d+), top (\d+), ℓ ∈ \[(-?\d+)/65536, (-?\d+)/65536\) nats, solved (\w+) \((\w+)\)')
req = re.compile(r'^    (\S+) request (\d+): target \[([^\]]*)\]; (released|held) \[([^\]]*)\], locks (.*); r\* (.*)$')
ln2_hi = 45427
rows = defaultdict(list)
label = None
for line in text:
    m = term.match(line)
    if m:
        rows[label].append(tuple(int(x) for x in m.groups()[:6]) + (m.group(7), m.group(8)))
        continue
    m = req.match(line)
    if m:
        label = m.group(1)
for label, ts in rows.items():
    top_right = sum(1 for s, r, t, top, lo, hi, *_ in ts if t == top)
    kinds = Counter(k for *_, k in ts)
    # ℓ cells: below ln 2 (solved region), [ln2, ln 5) roughly ties, above
    bands = Counter()
    for s, r, t, top, lo, hi, *_ in ts:
        if hi <= ln2_hi:
            bands['ℓ < ln 2'] += 1
        elif lo < 105476:  # ln 5 ∈ [105475/65536, 105476/65536)
            bands['ln 2 ≤ ℓ < ln 5'] += 1
        else:
            bands['ℓ ≥ ln 5'] += 1
    print(f'{label}: terms {len(ts)}; target on top {top_right}; kinds {dict(kinds)}; bands {dict(bands)}')
