#!/usr/bin/env -S python3 -I
"""held_levels.py LINE_DIR [FIRST LAST]: a line's held code by lap, recomputed from its own read files (a host ruler; no card, no state
is opened). LINE_DIR holds out_P{n}/cavity.tsv as `athena train complete-language read-cavity` writes them: rows `P` (one place open
among known neighbours) and `W` (every place of a run open at once), column 7 the code after the last tick on 2^-20 bits.
Prints lap, the five text slices' mean one-place code, the arithmetic and word-problem slices' where the store holds them, and the text
slices' whole-mask code, in nats a place (mean of column 7 times ln 2 / 2^20). The text slices are code, web, science, books, wikidata:
the same 100,508 one-place rows and 3,717 whole-mask rows at every lap of the store line."""
import math, os, sys
line = sys.argv[1]
first, last = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (1, 10**6)
K = math.log(2) / (1 << 20)
print("lap\ttext_one_place\tarithmetic_one_place\twords_one_place\ttext_whole_masks")
n = first
while n <= last:
    path = os.path.join(line, f"out_P{n}", "cavity.tsv")
    if not os.path.exists(path):
        if last == 10**6:
            break
        n += 1
        continue
    s = {"text": [0, 0], "arithmetic": [0, 0], "words": [0, 0], "whole": [0, 0]}
    with open(path) as f:
        next(f)
        for row in f:
            c = row.split("\t", 7)
            kind = c[1] if c[1] in ("arithmetic", "words") else "text"
            if c[0] == "P":
                s[kind][0] += int(c[6]); s[kind][1] += 1
            elif c[0] == "W" and kind == "text":
                s["whole"][0] += int(c[6]); s["whole"][1] += 1
    cell = lambda k: "-" if s[k][1] == 0 else "%.4f" % (s[k][0] / s[k][1] * K)
    print(f"{n}\t{cell('text')}\t{cell('arithmetic')}\t{cell('words')}\t{cell('whole')}")
    n += 1
