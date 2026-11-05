#!/usr/bin/env python3
"""The void's mass across the writer's opening (§16.46), from opening-field's OPENING.tsv and LENGTHS.tsv, with a write's
COUPLING.tsv (each written answer's length and its held answer's, in places).

Usage: opening.py OPENING_DIR [WRITE_DIR]

For each distance from the held answer's end (its first void place, at the held length), the mean over problems of the
face's void mass there, beside the question-blind length law's mass there: the share of training answers whose length is
at most that place (the place is past their last byte). B, the opening's byte mass past the end, is the sum over places past
the end of (1 - void mass), in places, beside the same sum for the length law. With a write, each written problem's B beside
its written length less its held length. Masses on 2^-20. Reading only; nothing here is a text.
"""
import csv
import statistics
import sys

UNIT = 1 << 20


def main():
    o = sys.argv[1]
    lengths = {}
    with open(f"{o}/LENGTHS.tsv") as f:
        for r in csv.DictReader(f, delimiter="\t"):
            lengths[int(r["length"])] = int(r["answers"])
    total = sum(lengths.values())
    room = None
    problems = {}
    with open(f"{o}/OPENING.tsv") as f:
        for r in csv.DictReader(f, delimiter="\t"):
            k = int(r["problem"])
            p = problems.setdefault(k, {"held": int(r["held"]), "void": []})
            p["void"].append(int(r["void"]) / UNIT)
    room = len(next(iter(problems.values()))["void"])
    # The length law: the share of training answers of length at most j.
    share, run = [], 0
    for j in range(room):
        run += lengths.get(j, 0)
        share.append(run / total)
    print(f"problems {len(problems)}, room {room} places, training answers {total}")
    print("distance\tproblems\tvoid_mass\tlength_law")
    for d in (-128, -32, 0, 32, 128, 512):
        vs, ss = [], []
        for p in problems.values():
            j = p["held"] + d
            if 0 <= j < room:
                vs.append(p["void"][j])
                ss.append(share[j])
        print(f"{d:+d}\t{len(vs)}\t{statistics.mean(vs):.3f}\t{statistics.mean(ss):.3f}" if vs else f"{d:+d}\t0\t-\t-")
    vs = [p["void"][j] for p in problems.values() for j in range(900, min(1200, room))]
    print(f"places 900 to 1199\t{len(vs)}\t{statistics.mean(vs):.3f}\t{statistics.mean(share[900:1200]):.3f}")
    b = {k: sum(1 - v for v in p["void"][p["held"] + 1:]) for k, p in problems.items()}
    blind = {k: sum(1 - s for s in share[p["held"] + 1:]) for k, p in problems.items()}
    before = {k: sum(p["void"][: p["held"]]) for k, p in problems.items()}
    bs = list(b.values())
    print(f"B past the end: mean {statistics.mean(bs):.0f} places, median {statistics.median(bs):.0f}, range {min(bs):.0f} to {max(bs):.0f}; the length law {statistics.mean(blind.values()):.0f}")
    print(f"void mass before the end: mean {statistics.mean(before.values()):.0f} places")
    if len(sys.argv) > 2:
        w = sys.argv[2]
        rows = []
        with open(f"{w}/COUPLING.tsv") as f:
            for r in csv.DictReader(f, delimiter="\t"):
                k = int(r["problem"])
                rows.append((k, int(r["held"]), int(r["written"])))
        over = sum(1 for _, h, wr in rows if wr > h)
        print(f"written: {len(rows)} problems, {over} written longer than held, {sum(1 for _, h, wr in rows if wr < h)} shorter")
        print("problem\theld\twritten_less_held\tB\tlength_law_B")
        for k, h, wr in rows:
            print(f"{k}\t{h}\t{wr - h:+d}\t{b[k]:.0f}\t{blind[k]:.0f}")
        xs = [b[k] for k, _, _ in rows]
        ys = [wr - h for _, h, wr in rows]
        if len(xs) > 2:
            print(f"correlation of B with the overrun over the written: {statistics.correlation(xs, ys):+.3f}")


if __name__ == "__main__":
    main()
