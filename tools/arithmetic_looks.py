"""Read a tower's LOOKS.tsv (the read-lines-again and read-lines-redraw commands) over a terrain's
dev.txt (tools/arithmetic_terrain.py): by operation, over unseen lines whose pair the text meets for
the first time (as arithmetic_lines.py's `first`), how many whole results the first look and the
last look write right, how many lines turn right and how many turn wrong between them, how many
lines' last two looks agree, the looks spent, and how many lines look more than once among those
whose first look is right and among those whose first look is wrong (read-lines-own looks again
only where the tower writes the question again). A file that carries each look's cost of the true
result (its sixth column, on 2^-20 bits) adds the mean cost in bits a line at the first look and at
the last, and the floor: the least cost any look reached (what the looks could not place, the
frustration). Given a second LOOKS.tsv over the same lines, it also counts the lines this file's
last look writes right where the second's first look writes wrong, and the reverse. A file that
carries each look's lock with the true rest (its seventh and eighth columns: `λ`, the longest
order-consistent coupling, and its friction `F*`, the micro-control's §7 reading) first prints, by
operation, `Σλ` and `ΣF*` at the first look and the last, and how many lines' locks held or grew
(`λ` up or equal and `F*` down or equal) and how many fell; with a second file, that file's first
look beside them. The lock is the success reading: whole-result counts are readings beside it. An
exterior reading, outside the machine.

usage: python3 -I arithmetic_looks.py DEV_TXT DEV_ROLES LOOKS_TSV [BESIDE_LOOKS_TSV]
"""
import sys
from collections import defaultdict

GRAIN = 1 << 20


def main():
    if len(sys.argv) not in (4, 5):
        raise SystemExit(__doc__)
    dev, roles, looks_tsv = sys.argv[1:4]
    beside = {}
    beside_lock = {}
    if len(sys.argv) == 5:
        for row in open(sys.argv[4]):
            cols = row.rstrip("\n").split("\t")
            beside[int(cols[0])] = cols[4].split("|")[0]
            if len(cols) == 8:
                beside_lock[int(cols[0])] = (int(cols[6].split("|")[0]), int(cols[7].split("|")[0]))
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
    lock = defaultdict(lambda: defaultdict(int))
    costed = locked = False
    for row in open(looks_tsv):
        cols = row.rstrip("\n").split("\t")
        i, head, truth, agreed, looked = cols[:5]
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
        c["again, first right"] += len(looks) > 1 and looks[0] == truth
        c["again, first wrong"] += len(looks) > 1 and looks[0] != truth
        if beside:
            other = beside[int(i)] == truth
            c["beside first right"] += other
            c["last right, beside first wrong"] += looks[-1] == truth and not other
            c["last wrong, beside first right"] += looks[-1] != truth and other
        if len(cols) == 8:
            locked = True
            lam = [int(v) for v in cols[6].split("|")]
            fr = [int(v) for v in cols[7].split("|")]
            k = lock[op]
            k["lines"] += 1
            k["first λ"] += lam[0]
            k["last λ"] += lam[-1]
            k["first F*"] += fr[0]
            k["last F*"] += fr[-1]
            k["held or grew"] += lam[-1] >= lam[0] and fr[-1] <= fr[0]
            k["fell"] += lam[-1] < lam[0] or fr[-1] > fr[0]
            if int(i) in beside_lock:
                k["beside first λ"] += beside_lock[int(i)][0]
                k["beside first F*"] += beside_lock[int(i)][1]
        if len(cols) >= 6:
            costed = True
            costs = [int(v) for v in cols[5].split("|")]
            c["first cost"] += costs[0]
            c["last cost"] += costs[-1]
            c["floor"] += min(costs)
    if locked:
        lock_fields = ("lines", "first λ", "last λ", "first F*", "last F*", "held or grew", "fell")
        if beside_lock:
            lock_fields += ("beside first λ", "beside first F*")
        print("op\t" + "\t".join(lock_fields))
        for op in "+-*":
            print(op + "\t" + "\t".join(str(lock[op][f]) for f in lock_fields))
    fields = ("lines", "first right", "last right", "any right", "turned right", "turned wrong", "agreed", "looks",
              "again, first right", "again, first wrong")
    if beside:
        fields += ("beside first right", "last right, beside first wrong", "last wrong, beside first right")
    bits = ("first cost", "last cost", "floor") if costed else ()
    print("op\t" + "\t".join(fields + bits))
    for op in "+-*":
        c = count[op]
        row = [str(c[f]) for f in fields] + [f"{c[f] / GRAIN / max(c['lines'], 1):.3f}" for f in bits]
        print(op + "\t" + "\t".join(row))


if __name__ == "__main__":
    main()
