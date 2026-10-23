"""Read a tower's LOOKS.tsv (the read-lines-again and read-lines-redraw commands) over a terrain's
dev.txt (tools/arithmetic_terrain.py): by operation, over unseen lines whose pair the text meets for
the first time (as arithmetic_lines.py's `first`), how many whole results the first look and the
last look write right, how many lines turn right and how many turn wrong between them, how many
lines' last two looks agree, and the looks spent. An exterior reading, outside the machine.

usage: python3 -I arithmetic_looks.py DEV_TXT DEV_ROLES LOOKS_TSV
"""
import sys
from collections import defaultdict


def main():
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    dev, roles, looks_tsv = sys.argv[1:]
    text = open(dev, "rb").read()
    regions = open(roles, "rb").read()
    first_unseen = {}
    met = set()
    at = 0
    for i, line in enumerate(text.split(b"\n")[:-1]):
        eq = line.index(b"=")
        head = line[:eq].decode()
        op = next(c for c in "+-*" if c in head)
        a, b = head.split(op)
        pair = (op, frozenset((a, b))) if op in "+*" else (op, a, b)
        if regions[at + eq + 1] == 0 and pair not in met:
            first_unseen[i] = op
        met.add(pair)
        at += len(line) + 1
    count = defaultdict(lambda: defaultdict(int))
    for row in open(looks_tsv):
        i, head, truth, agreed, looked = row.rstrip("\n").split("\t")
        op = first_unseen.get(int(i))
        if op is None:
            continue
        looks = looked.split("|")
        c = count[op]
        c["lines"] += 1
        c["first right"] += looks[0] == truth
        c["last right"] += looks[-1] == truth
        c["any right"] += truth in looks
        c["turned right"] += looks[0] != truth and looks[-1] == truth
        c["turned wrong"] += looks[0] == truth and looks[-1] != truth
        c["agreed"] += agreed == "1"
        c["looks"] += len(looks)
    fields = ("lines", "first right", "last right", "any right", "turned right", "turned wrong", "agreed", "looks")
    print("op\t" + "\t".join(fields))
    for op in "+-*":
        print(op + "\t" + "\t".join(str(count[op][f]) for f in fields))


if __name__ == "__main__":
    main()
