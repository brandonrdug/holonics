#!/usr/bin/env python3
"""The space share of each write's last tenth against its first nine tenths, beside the truth's (the unified-theory reading of
November 6, 13:49). Usage: tenths.py HELD.txt SAMPLE.tsv [COUNT]. Pooled over the answers: spaces / bytes in each part."""
import sys
held_path, sample_path = sys.argv[1], sys.argv[2]
n = int(sys.argv[3]) if len(sys.argv) > 3 else 32
text = open(held_path, 'rb').read()
probs = []
for rec in text.split(b'\x1e'):
    if b'\x1f' in rec:
        q, a = rec.split(b'\x1f', 1)
        if q and a:
            probs.append(a)
def split(bs):
    cut = (len(bs) * 9) // 10
    return bs[:cut], bs[cut:]
def share(parts):
    sp = sum(p.count(b' ') for p in parts); tot = sum(len(p) for p in parts)
    return sp / tot if tot else float('nan'), tot
writes = []
for line in open(sample_path, 'rb'):
    k, t = line.rstrip(b'\n').split(b'\t', 1)
    writes.append(t.decode('latin-1').encode('latin-1').decode('unicode_escape').encode('latin-1', 'replace'))
for name, items in (("truth", probs[:n]), ("write", writes[:n])):
    heads, tails = zip(*(split(b) for b in items))
    (h, hn), (t, tn) = share(heads), share(tails)
    print(f"TENTHS {name}: first nine tenths {h:.3f} over {hn} bytes, last tenth {t:.3f} over {tn} bytes, ratio {t / h if h else float('nan'):.2f}")
