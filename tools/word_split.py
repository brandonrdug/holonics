#!/usr/bin/env -S python3 -I
"""word_split.py CODEC FRONTIER_TSV: a ruler (the lead, November 23). Where the writer pays: her code at a word's first letter, inside a word, and elsewhere (two streams, S rows), by slice, in nats."""
import sys, math, collections
codec, path = sys.argv[1], sys.argv[2]
units = [int(x) for x in open(codec).read().split('\n')[1].split()]
byte = {k: u for k, u in enumerate(units)}
letter = lambda c: c in byte and (65 <= byte[c] <= 90 or 97 <= byte[c] <= 122)
space = lambda c: c in byte and byte[c] in (32, 10)
acc = collections.defaultdict(lambda: [0.0, 0])
prev = {}
for line in open(path):
    f = line.rstrip('\n').split('\t')
    if f[0] != 'S':
        continue
    sl, st, t, c, code = f[1], f[2], int(f[3]), int(f[4]), int(f[5])
    p = prev.get((sl, st, t - 1))
    kind = 'start' if (p is not None and space(p) and letter(c)) else 'inside' if (p is not None and letter(p) and letter(c)) else 'other'
    a = acc[(sl, kind)]; a[0] += code / 2**20 * math.log(2); a[1] += 1
    prev[(sl, st, t)] = c
for sl in sorted({k[0] for k in acc}):
    print(f"WORD_SPLIT {path.split('/')[-2]} {sl} " + ' '.join(f"{k}={acc[(sl, k)][0] / max(1, acc[(sl, k)][1]):.3f}({acc[(sl, k)][1]})" for k in ('start', 'inside', 'other')))
