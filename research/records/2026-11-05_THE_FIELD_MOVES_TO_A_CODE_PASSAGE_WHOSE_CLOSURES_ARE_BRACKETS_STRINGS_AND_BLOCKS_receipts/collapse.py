#!/usr/bin/env python3
"""The no-run read of a write's letter collapse (the unified-theory reading of November 5, 21:54, fixed before it was read).

Usage: collapse.py HELD.txt SAMPLE.tsv [ENDS.tsv]

Over the written answers and, beside them, their held answers: how many open with ```python; each write's first 'y' outside
that opening, how many start at places 0 to 5 (inside the first state's region, whatever its front), and the share of 'y'
past it; at each place from 10 to 255 reached by 8 or more answers the commonest byte's share across them, averaged; the
top byte's share of all bytes, the share of 'y', and the byte entropy in bits. Aggregates only.
"""
import collections
import math
import sys

OPEN = b"```python"


def records(path):
    return [r.split(b"\x1f", 1)[1] for r in open(path, "rb").read().split(b"\x1e") if b"\x1f" in r]


def read(answers, label):
    n = len(answers)
    opens = sum(a.startswith(OPEN) for a in answers)
    firsts, past_y, past_all = [], 0, 0
    for a in answers:
        start = len(OPEN) if a.startswith(OPEN) else 0
        at = a.find(b"y", start)
        if at >= 0:
            firsts.append(at)
            tail = a[at:]
            past_y += tail.count(b"y")
            past_all += len(tail)
    inside = sum(f <= 5 for f in firsts)
    shares = []
    for t in range(10, 256):
        here = [a[t] for a in answers if len(a) > t]
        if len(here) >= 8:
            shares.append(collections.Counter(here).most_common(1)[0][1] / len(here))
    bytes_ = collections.Counter(b for a in answers for b in a)
    total = sum(bytes_.values())
    top, top_n = bytes_.most_common(1)[0] if total else (0, 0)
    entropy = -sum(v / total * math.log2(v / total) for v in bytes_.values()) if total else float("nan")
    print(f"{label}: {n} answers, {opens} open with ```python; a 'y' outside it in {len(firsts)}, its first at places 0 to 5 in {inside} "
          f"(median first {sorted(firsts)[len(firsts) // 2] if firsts else '-'}), 'y' past it {past_y / max(past_all, 1):.3f}; "
          f"commonest byte's share at places 10 to 255 ({len(shares)} places) {sum(shares) / max(len(shares), 1):.3f}; "
          f"top byte {chr(top)!r} {top_n / max(total, 1):.3f}, 'y' {bytes_[ord('y')] / max(total, 1):.3f}, entropy {entropy:.2f} bits over {total} bytes")


def main():
    held = records(sys.argv[1])
    written = []
    for line in open(sys.argv[2], "rb"):
        k, _, text = line.rstrip(b"\n").partition(b"\t")
        if k.isdigit():
            written.append((int(k), text.decode("latin-1").encode("latin-1").decode("unicode_escape").encode("latin-1", "replace")))
    read([w for _, w in written], "written")
    read([held[k] for k, _ in written], "held   ")


if __name__ == "__main__":
    main()
