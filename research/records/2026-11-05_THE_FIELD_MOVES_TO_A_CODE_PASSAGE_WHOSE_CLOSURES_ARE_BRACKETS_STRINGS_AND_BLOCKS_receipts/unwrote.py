#!/usr/bin/env python3
"""Whether a drawn void unwrote written letters (the unified-theory reading of November 5, 22:38, fixed before it was read).

Usage: unwrote.py WRITE_DIR

From LENGTH.tsv (problem, read, pass, L, letters, open; one row a problem a read) and ENDS.tsv (held and written lengths): in
the sweeps (pass 0), a read whose letters fall below the read before's is a void unwriting letters past it. Over the short
writes (written under held): how many had letters unwritten, and the letters unwritten in all. Aggregates only.
"""
import csv
import sys


def main():
    d = sys.argv[1]
    ends = {int(r["problem"]): (int(r["held"]), int(r["written"])) for r in csv.DictReader(open(f"{d}/ENDS.tsv"), delimiter="\t")}
    last, drops, lost = {}, {}, {}
    for r in csv.DictReader(open(f"{d}/LENGTH.tsv"), delimiter="\t"):
        if r["pass"] != "0":
            continue
        k, letters = int(r["problem"]), int(r["letters"])
        if k in last and letters < last[k]:
            drops[k] = drops.get(k, 0) + 1
            lost[k] = lost.get(k, 0) + last[k] - letters
        last[k] = letters
    short = [k for k, (h, w) in ends.items() if w < h]
    hit = [k for k in short if drops.get(k)]
    print(f"UNWROTE short writes {len(short)} of {len(ends)}: a void unwrote letters in {hit.__len__()} ({sum(drops.get(k, 0) for k in short)} reads, {sum(lost.get(k, 0) for k in short)} letters); in all writes {sum(1 for k in ends if drops.get(k))}")


if __name__ == "__main__":
    main()
