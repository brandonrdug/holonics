"""Exterior reading: the commonest byte at each place of GSM8K's training answers, and its share.
A per-place target with no coupling learns, at best, this marginal over phrasings. Data only.
Usage: python3 -I place_mode.py TRAIN_JSONL"""
import json, sys
from collections import Counter
rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8")]
ans = [r["answer"].encode("utf-8") for r in rows]
L = 64
line = []
spaces = 0
for t in range(L):
    c = Counter(a[t] for a in ans if len(a) > t)
    n = sum(c.values())
    b, k = c.most_common(1)[0]
    spaces += b == 32
    line.append((t, chr(b) if 32 < b < 127 else repr(chr(b)), k / n, n))
for t, ch, share, n in line:
    print(f"{t:3d} {ch!s:>6} {share:6.3f} {n}")
print(f"places 0..{L-1}: commonest byte is a space at {spaces} of {L}")
mode = "".join(chr(Counter(a[t] for a in ans if len(a) > t).most_common(1)[0][0]) for t in range(L))
print("place-wise commonest bytes:", repr(mode))
