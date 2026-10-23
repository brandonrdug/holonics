"""Read a tower's LINES.tsv over a terrain's dev.txt (tools/arithmetic_terrain.py; the tower's
read-lines command): the code of the result's content digits by operation and place (counted from
the right, the units place 0), unseen beside seen; the scale zeros and the line's end apart; and how
many of the written results equal the terrain's. An exterior reading, outside the machine.

usage: python3 -I arithmetic_lines.py DEV_TXT DEV_ROLES LINES_TSV WRITTEN (the read's WRITTEN count)
"""
import sys
from collections import defaultdict

GRAIN = 1 << 20


def main():
    dev, roles, lines_tsv, written_lines = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    text = open(dev, "rb").read()
    regions = open(roles, "rb").read()
    unseen_of = {}
    at = 0
    for i, line in enumerate(text.split(b"\n")[:-1]):
        eq = line.index(b"=")
        if regions[at + eq + 1] not in (0, 1):
            raise SystemExit("a result opens on a scale zero")
        unseen_of[i] = regions[at + eq + 1] == 0
        at += len(line) + 1
    code = defaultdict(lambda: [0, 0])
    written = defaultdict(lambda: [0, 0])
    shown = []
    for row in open(lines_tsv):
        i, head, rest, release, codes = row.rstrip("\n").split("\t")
        i = int(i)
        side = "unseen" if unseen_of[i] else "seen"
        op = next(c for c in "+-*" if c in head)
        codes = [int(c) for c in codes.split(",")]
        content = len(rest.rstrip("0")) if rest != "0" else 1
        for k, c in enumerate(codes[:-1]):
            place = len(rest) - 1 - k
            kind = f"place {place}" if k < content else "scale"
            for key in ((side, op, kind), (side, op, "all content" if k < content else "all scale"), (side, "all", "all content" if k < content else "all scale")):
                code[key][0] += c
                code[key][1] += 1
        code[(side, op, "line end")][0] += codes[-1]
        code[(side, op, "line end")][1] += 1
        if i < written_lines:
            written[(side, op)][0] += release == rest
            written[(side, op)][1] += 1
            if len(shown) < 40:
                shown.append(f"{side:6} {head}{release}")
    for key in sorted(code):
        total, n = code[key]
        print(f"CODE {key[0]:6} {key[1]:3} {key[2]:12} bits_a_digit={total / GRAIN / n:.3f} n={n}")
    for key in sorted(written):
        right, n = written[key]
        print(f"WRITTEN {key[0]:6} {key[1]} equal={right}/{n}")
    for s in shown:
        print("SHOWN", s)


if __name__ == "__main__":
    main()
