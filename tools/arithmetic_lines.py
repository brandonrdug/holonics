"""Read a tower's or a duplex's LINES.tsv over a terrain's dev.txt (tools/arithmetic_terrain.py; the
read-lines and read-lines-duplex commands): the code of the result's content digits by operation and
place (counted from the right, the units place 0), unseen beside seen; the scale zeros and the
line's end apart; and what the written results share with the terrain's, by the faces of the base's
tower: the whole word, its length, and its residues on the rings 2, 5, 9, 10 and 11. A duplex's file
adds the meeting's codes (each place read from both sides) and the refined release beside the
forward's. Two readings the mathematics thread asked for: a written difference's units against the
units of the operands' sum, and a carried sum's tens against the tens without the carry. An exterior
reading, outside the machine.

usage: python3 -I arithmetic_lines.py DEV_TXT DEV_ROLES LINES_TSV WRITTEN (the read's WRITTEN count)
"""
import sys
from collections import defaultdict

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
    shared = defaultdict(lambda: [0, 0])
    readings = defaultdict(lambda: [0, 0])
    settled = defaultdict(lambda: [0, 0])
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
    for key in sorted(settled):
        hit, n = settled[key]
        print(f"SETTLED {key[0]:6} {key[1]} {hit}/{n}")
    for s in shown:
        print("SHOWN", s)


if __name__ == "__main__":
    main()
