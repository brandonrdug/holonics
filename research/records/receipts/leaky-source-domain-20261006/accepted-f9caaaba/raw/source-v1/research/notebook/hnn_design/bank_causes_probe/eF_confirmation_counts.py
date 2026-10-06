"""Exact counts of an `executed evaluate` listing per constitution: released/held, whole, the first
lock at station 0 or 1 and, among those, right; the first lock's station distribution; stations
right; the first 16 rows as a markdown table.

usage: eF_confirmation_counts.py <evaluate listing> [rows]"""
import re
import sys
from collections import Counter

rows_wanted = int(sys.argv[2]) if len(sys.argv) > 2 else 16
blocks = {}
label = None
for line in open(sys.argv[1]):
    m = re.match(r'== (\S+) on (\S+), seed (\d+)', line)
    if m:
        label = m.group(1)
        blocks[label] = []
        continue
    m = re.match(r'(\d+) \| target \[(.*?)\] \| (released|held) \[(.*?)\] \| locks (\[.*\])', line)
    if m:
        blocks[label].append((m.group(1), [int(x) for x in m.group(2).split(',')], m.group(3),
                              [int(x) for x in m.group(4).split(',')], eval(m.group(5))))
for label, rows in blocks.items():
    released = sum(r[2] == 'released' for r in rows)
    whole = sum(r[2] == 'released' and r[1] == r[3] for r in rows)
    first01 = first01_right = 0
    first_st = Counter()
    for _, target, _, classes, locks in rows:
        if locks:
            s = locks[0][0]
            first_st[s] += 1
            if s < 2:
                first01 += 1
                first01_right += classes[s] == target[s]
    print(f'{label}: {len(rows)} requests, released {released}, whole {whole}; first lock at station 0 or 1 '
          f'{first01}, of them right {first01_right}; first lock stations {dict(sorted(first_st.items()))}')
    print('| Request (last four cells) | Target | Released | Lock order |')
    print('|---|---|---|---|')
    for request, target, state, classes, locks in rows[:rows_wanted]:
        order = ' '.join(str(s) for g in locks for s in g)
        tag = ' (whole)' if state == 'released' and target == classes else ('' if state == 'released' else ' (held)')
        print(f"| {' '.join(request[-4:])} | {' '.join(map(str, target))} | {' '.join(map(str, classes))}{tag} | {order} |")
