#!/usr/bin/env python3
"""Refinement until each answer settles, read beside the same keys' write of three passes (the unified-theory reading of
November 5, 23:26, fixed before the read).

Usage: settle.py HELD.txt SETTLE_DIR REFINE3_DIR

(b) each problem's stop: the last refine pass it read (PASSES.tsv), its median against 3; the answers' own code per byte by
pass, over the problems still refining; (c) of the answers whose first line in the three-pass write is not exactly ```python,
those one byte too long or too short (one insertion or deletion away), and how many of them the settled write mends to
exactly ```python. Aggregates only.
"""
import collections
import csv
import statistics
import sys

FENCE = b"```python"


def samples(d):
    out = {}
    for line in open(f"{d}/SAMPLE.tsv", "rb"):
        k, _, text = line.rstrip(b"\n").partition(b"\t")
        if k.isdigit():
            out[int(k)] = text.decode("latin-1").encode("latin-1").decode("unicode_escape").encode("latin-1", "replace")
    return out


def one_off(a, b):
    if abs(len(a) - len(b)) != 1:
        return False
    s, l = (a, b) if len(a) < len(b) else (b, a)
    return any(l[:i] + l[i + 1:] == s for i in range(len(l)))


def main():
    d, r3 = sys.argv[2], sys.argv[3]
    stop = collections.defaultdict(int)
    by_pass = collections.defaultdict(lambda: [0, 0])
    for r in csv.DictReader(open(f"{d}/PASSES.tsv"), delimiter="\t"):
        k, p, n, c = int(r["problem"]), int(r["pass"]), int(r["redrawn"]), int(r["code"])
        stop[k] = max(stop[k], p)
        by_pass[p][0] += n
        by_pass[p][1] += c
    stops = sorted(stop.values())
    print(f"STOP problems {len(stops)}: median pass {statistics.median(stops) if stops else '-'}, range {stops[0] if stops else '-'} to {stops[-1] if stops else '-'}, past pass 3 in {sum(s > 3 for s in stops)}")
    print("CODE by pass (bits a redrawn byte): " + " ".join(f"{p}:{c / n / (1 << 20):.3f}({n})" for p, (n, c) in sorted(by_pass.items())))
    s, t = samples(d), samples(r3)
    first = lambda a: a.split(b"\n", 1)[0]
    off = [k for k, a in t.items() if first(a) != FENCE]
    near = [k for k in off if one_off(first(t[k]), FENCE)]
    mended = [k for k in near if first(s.get(k, b"")) == FENCE]
    print(f"SHIFTS three-pass openings not ```python {len(off)}, a byte off {len(near)}, mended at the stop {len(mended)}; settled openings exactly ```python {sum(first(a) == FENCE for a in s.values())} of {len(s)}")


if __name__ == "__main__":
    main()
