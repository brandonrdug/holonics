"""Read a tower's or a duplex's LINES.tsv over a terrain's dev.txt (tools/arithmetic_terrain.py; the
read-lines and read-lines-duplex commands): the code of the result's content digits by operation and
place (counted from the right, the units place 0), unseen beside seen; the scale zeros and the
line's end apart; and what the written results share with the terrain's, by the faces of the base's
tower: the whole word, its length, and its residues on the rings 2, 5, 9, 10 and 11. A duplex's file
adds the meeting's codes (each place read from both sides) and the refined release beside the
forward's. Two readings the mathematics thread asked for: a written difference's units against the
units of the operands' sum, and a carried sum's tens against the tens without the carry; and, after
its later note, each ring's shared face split by whether both operands are units of the ring or one
shares a prime with it, a sum's tens split by whether its units carried, and the first digit written
for a one-digit difference; and how many steps of the ring of ten a written sum's units sit from the
truth's (the turned tower's sums). An exterior reading, outside the machine.

A read that carries the stream (read-lines-stream) opens each line on the state the text's true
earlier lines left, so a line whose operation and operands (unordered for + and *) met earlier in
the text could be read against them; `first` keeps only the lines whose pair the text meets there
for the first time, and `again` only the rest.

usage: python3 -I arithmetic_lines.py DEV_TXT DEV_ROLES LINES_TSV WRITTEN [first|again]
(WRITTEN: the read's WRITTEN count)
"""
import sys
from collections import Counter, defaultdict
from math import gcd

GRAIN = 1 << 20
RINGS = (2, 5, 9, 10, 11)


def value(written):
    return int(written) if written.isdigit() else None


def faces(written, truth):
    """The faces a written result shares with the truth: the word, its length and each ring."""
    v = value(written)
    shared = {"word": written == str(truth), "length": len(written) == len(str(truth))}
    for q in RINGS:
        shared[f"mod {q}"] = v is not None and v % q == truth % q
    return shared


def main():
    dev, roles, lines_tsv, written_lines = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    keep = sys.argv[5] if len(sys.argv) > 5 else None
    if sys.argv[6:] or keep not in (None, "first", "again"):
        raise SystemExit("the fifth argument is `first`, `again` or absent")
    text = open(dev, "rb").read()
    regions = open(roles, "rb").read()
    unseen_of = {}
    met_before = set()
    met = set()
    at = 0
    for i, line in enumerate(text.split(b"\n")[:-1]):
        eq = line.index(b"=")
        head = line[:eq].decode()
        op = next(c for c in "+-*" if c in head)
        a, b = head.split(op)
        pair = (op, frozenset((a, b))) if op in "+*" else (op, a, b)
        if pair in met:
            met_before.add(i)
        met.add(pair)
        if regions[at + eq + 1] not in (0, 1):
            raise SystemExit("a result opens on a scale zero")
        unseen_of[i] = regions[at + eq + 1] == 0
        at += len(line) + 1
    code = defaultdict(lambda: [0, 0])
    shared = defaultdict(lambda: [0, 0])
    readings = defaultdict(lambda: [0, 0])
    settled = defaultdict(lambda: [0, 0])
    rings = defaultdict(lambda: [0, 0])
    tens = defaultdict(lambda: [0, 0])
    short = defaultdict(Counter)
    steps = defaultdict(Counter)
    shown = []
    for row in open(lines_tsv):
        cols = row.rstrip("\n").split("\t")
        if len(cols) == 5:
            i, head, rest, release, fcodes = cols
            releases, faces_read = {"forward": release}, {"forward": fcodes}
        else:
            i, head, rest, release, refined, sweeps, fcodes, mcodes = cols
            releases = {"forward": release, "refined": refined}
            faces_read = {"forward": fcodes, "meeting": mcodes}
        i = int(i)
        if keep is not None and (i in met_before) != (keep == "again"):
            continue
        side = "unseen" if unseen_of[i] else "seen"
        op = next(c for c in "+-*" if c in head)
        a, b = (int(x) for x in head[:-1].split(op))
        truth = a + b if op == "+" else a - b if op == "-" else a * b
        content = len(rest.rstrip("0")) if rest != "0" else 1
        for reader, codes in faces_read.items():
            codes = [int(c) for c in codes.split(",")]
            for k, c in enumerate(codes[: len(rest)]):
                place = len(rest) - 1 - k
                kind = f"place {place}" if k < content else "scale"
                whole = "all content" if k < content else "all scale"
                for key in ((reader, side, op, kind), (reader, side, op, whole), (reader, side, "all", whole)):
                    code[key][0] += c
                    code[key][1] += 1
            if len(codes) > len(rest):
                code[(reader, side, op, "line end")][0] += codes[-1]
                code[(reader, side, op, "line end")][1] += 1
        if i >= written_lines:
            continue
        for reader, written in releases.items():
            for face, hit in faces(written, truth).items():
                shared[(reader, side, op, face)][0] += hit
                shared[(reader, side, op, face)][1] += 1
            v = value(written)
            if v is not None:
                for q in RINGS:
                    pair = "units" if gcd(a, q) == 1 and gcd(b, q) == 1 else "shares a prime"
                    rings[(reader, side, op, q, pair)][0] += v % q == truth % q
                    rings[(reader, side, op, q, pair)][1] += 1
                if op == "+" and truth >= 10 and len(written) >= 2:
                    carried = "units carried" if a % 10 + b % 10 >= 10 else "no carry"
                    tens[(reader, side, carried)][0] += v // 10 % 10 == truth // 10 % 10
                    tens[(reader, side, carried)][1] += 1
                if op == "+":
                    step = (v - truth) % 10
                    steps[(reader, side)][min(step, 10 - step)] += 1
                if op == "-" and truth < 10:
                    short[(reader, side)][written[:1] + ("" if len(written) == 1 else "+")] += 1
            if v is None or v == truth:
                continue
            if op == "-" and v % 10 != truth % 10:
                readings[(reader, side, "difference's wrong units are the sum's units")][0] += v % 10 == (a + b) % 10
                readings[(reader, side, "difference's wrong units are the sum's units")][1] += 1
            if op == "+" and a % 10 + b % 10 >= 10 and len(written) >= 2 and v // 10 % 10 != truth // 10 % 10:
                residue = (a // 10 + b // 10) % 10
                readings[(reader, side, "carried sum's wrong tens are the tens without the carry")][0] += v // 10 % 10 == residue
                readings[(reader, side, "carried sum's wrong tens are the tens without the carry")][1] += 1
        if len(cols) == 8 and sweeps:
            settled[(side, op)][0] += not sweeps.endswith("+")
            settled[(side, op)][1] += 1
        if len(shown) < 60:
            shown.append(f"{side:6} {head}" + "  ".join(releases.values()))
    for key in sorted(code):
        total, n = code[key]
        print(f"CODE {key[0]:7} {key[1]:6} {key[2]:3} {key[3]:12} bits_a_digit={total / GRAIN / n:.3f} n={n}")
    for key in sorted(shared):
        hit, n = shared[key]
        print(f"SHARED {key[0]:7} {key[1]:6} {key[2]} {key[3]:7} {hit}/{n}")
    for key in sorted(readings):
        hit, n = readings[key]
        print(f"READING {key[0]:7} {key[1]:6} {key[2]}: {hit}/{n}")
    for key in sorted(rings):
        hit, n = rings[key]
        print(f"RING {key[0]:7} {key[1]:6} {key[2]} mod {key[3]:2} {key[4]:14} {hit}/{n}")
    for key in sorted(tens):
        hit, n = tens[key]
        print(f"SUM_TENS {key[0]:7} {key[1]:6} {key[2]:13} {hit}/{n}")
    for key in sorted(short):
        print(f"ONE_DIGIT_DIFFERENCE {key[0]:7} {key[1]:6} first written " + " ".join(f"{d}:{c}" for d, c in sorted(short[key].items())))
    for key in sorted(steps):
        print(f"SUM_UNITS_STEPS {key[0]:7} {key[1]:6} " + " ".join(f"{d}:{c}" for d, c in sorted(steps[key].items())))
    for key in sorted(settled):
        hit, n = settled[key]
        print(f"SETTLED {key[0]:6} {key[1]} {hit}/{n}")
    for s in shown:
        print("SHOWN", s)


if __name__ == "__main__":
    main()
