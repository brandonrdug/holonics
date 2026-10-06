"""Exact shape counts of an `executed evaluate` listing per constitution (the modulus's record,
September 30): over released sections, the released classes' histogram, the adjacent stations
equal (a lag-1 copy, x_t = x_(t-1)), the stations following their terrain's rule among the
section's own stations (order-2 x_t = x_(t-2) + 1, the alternation x_t = x_(t-2), the line
x_t = x_(t-1) + (x_1 - x_0)), the sections following it throughout, and the first two stations
right.

usage: eM_section_shapes.py <evaluate listing> <order2|alternation|line>"""
import re
import sys
from collections import Counter

path, terrain = sys.argv[1], sys.argv[2]
blocks = {}
label = None
for line in open(path):
    m = re.match(r'== (\S+) on (\S+), seed (\d+)', line)
    if m:
        label = m.group(1)
        blocks[label] = []
        continue
    m = re.match(r'(\d+) \| target \[(.*?)\] \| (released|held) \[(.*?)\] \| locks (\[.*\])', line)
    if m:
        blocks[label].append(([int(x) for x in m.group(2).split(',')], m.group(3),
                              [int(x) for x in m.group(4).split(',')]))


def follows(s, t):
    if terrain == 'order2':
        return s[t] == (s[t - 2] + 1) % 4
    if terrain == 'alternation':
        return s[t] == s[t - 2]
    return s[t] == (s[t - 1] + s[1] - s[0]) % 4


for label, rows in blocks.items():
    released = [(t, c) for t, state, c in rows if state == 'released']
    hist = Counter(x for _, c in released for x in c)
    copies = sum(c[t] == c[t - 1] for _, c in released for t in range(1, len(c)))
    rule = sum(follows(c, t) for _, c in released for t in range(2, len(c)))
    whole_rule = sum(all(follows(c, t) for t in range(2, len(c))) for _, c in released)
    first_two = sum(c[0] == t[0] and c[1] == t[1] for t, c in released)
    pairs = len(released) * 7
    print(f'{label}: released {len(released)}; classes {dict(sorted(hist.items()))}; adjacent equal '
          f'{copies} of {pairs}; stations following the rule {rule} of {len(released) * 6}; sections '
          f'following it throughout {whole_rule}; first two stations right {first_two}')
