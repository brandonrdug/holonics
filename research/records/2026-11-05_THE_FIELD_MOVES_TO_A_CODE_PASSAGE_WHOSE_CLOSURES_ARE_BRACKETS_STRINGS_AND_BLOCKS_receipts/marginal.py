#!/usr/bin/env python3
"""The truth marginal's code of each held answer's length, beside a state's opening length code (the unified-theory reading of
November 6, 04:38): from order-field's ORDER.tsv and opening-field's LENGTHS.tsv (the training answers' lengths in places), the
mean of -log2 P_train(L = len) over the answers whose opening length code was read, and over all of them, with the state's own
mean length code over the same read answers. Aggregates only.

Usage: marginal.py ORDER.tsv LENGTHS.tsv
"""
import csv
import math
import sys

order = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
lengths = {int(r["length"]): int(r["answers"]) for r in csv.DictReader(open(sys.argv[2]), delimiter="\t")}
total = sum(lengths.values())
code = lambda l: -math.log2(lengths.get(l, 0) / total) if lengths.get(l) else float("inf")
read = [r for r in order if r["length_code"] != "-"]
state = sum(int(r["length_code"]) for r in read) / len(read) / (1 << 20) if read else float("nan")
m_read = sum(code(int(r["places"]) - 1) for r in read) / len(read) if read else float("nan")
m_all = sum(code(int(r["places"]) - 1) for r in order) / len(order)
diffs = [int(r["length_code"]) / (1 << 20) - code(int(r["places"]) - 1) for r in read]
mean = sum(diffs) / len(diffs) if diffs else float("nan")
spread = math.sqrt(sum((d - mean) ** 2 for d in diffs) / (len(diffs) - 1)) if len(diffs) > 1 else float("nan")
print(f"MARGINAL read {len(read)} of {len(order)}: the state's length code {state:.2f} bits an answer, the training marginal's on the same answers {m_read:.2f}, on all {m_all:.2f}; paired difference {mean:+.2f} with deviation {spread / math.sqrt(len(diffs)):.2f}")
