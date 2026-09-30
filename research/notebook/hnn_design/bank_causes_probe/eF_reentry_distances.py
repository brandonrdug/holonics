"""Summarize a `bank_causes -- reentry` trace: at every insertion of each order, the open stations'
targets past one under the full placement and the denominator alone, and each first lost
comparison's distance from the nearest placed lock (exact counts; no float).

usage: eF_reentry_distances.py <reentry trace>"""
import re
import sys
from collections import Counter, defaultdict

text = open(sys.argv[1]).read().splitlines()
req = None
order_name = None
order = None
placed = []
first = {}
past = defaultdict(lambda: [0, 0, 0])  # (order, insertion) -> [full past one, denominator past one, open stations]
status = {}
line_re = re.compile(r'station (\d+) \(target (\d+)\): full (\w+) .*? past-one (\w+) .*\| denominator (\w+) .*? past-one (\w+)')
for line in text:
    m = re.match(r'request (\d+):', line)
    if m:
        req = int(m.group(1))
        continue
    m = re.match(r'\s+order (\w+) \[(.*)\]', line)
    if m:
        order_name = m.group(1)
        order = [int(x) for x in m.group(2).split(',')]
        placed = []
        continue
    m = re.match(r'\s+insertion (\d+): station (\d+) placed', line)
    if m:
        k = int(m.group(1))
        placed = order[:k]
        continue
    m = line_re.search(line)
    if m and placed:
        station = int(m.group(1))
        k = len(placed)
        cell = past[(order_name, k)]
        cell[0] += m.group(4) == 'true'
        cell[1] += m.group(6) == 'true'
        cell[2] += 1
        status[(req, order_name, k, station)] = (m.group(3), m.group(5))
        continue
    m = re.match(r'\s+FIRST LOSS \((\w+) order, (\w+)\): insertion (\d+), stations \[(.*)\]', line)
    if m:
        o, v, k, stations = m.group(1), m.group(2), int(m.group(3)), [int(x) for x in m.group(4).split(',')]
        first[(req, o, v)] = (k, stations, list(order[:k]))
for o in ('clock', 'gap'):
    print(o, 'targets past one at insertion k (full / denominator alone / open stations):',
          ' '.join(f'{k}: {past[(o, k)][0]}/{past[(o, k)][1]}/{past[(o, k)][2]}' for k in range(1, 8)))
for o in ('clock', 'gap'):
    dist = Counter()
    denominator_too = Counter()
    for (r, oo, v), (k, stations, locks) in sorted(first.items()):
        if oo != o or v != 'full':
            continue
        for s in stations:
            d = min(abs(s - l) for l in locks)
            dist[d] += 1
            if status[(r, o, k, s)][1] != 'holds':
                denominator_too[d] += 1
    print(o, 'first lost comparisons (full) by distance to the nearest placed lock:', dict(sorted(dist.items())),
          '; of these, lost also by the denominator alone at that insertion:', dict(sorted(denominator_too.items())))
