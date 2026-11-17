#!/usr/bin/env -S python3 -I
"""A ruler: a held read's one-place codes split by the kind of symbol (the lead, November 17).

Usage: cavity_by_kind.py CODEC CAVITY.tsv [CAVITY.tsv …]

For each `read-cavity` table and each slice: the share of places and the mean code in nats a place at digits, letters, spaces and
line feeds, and marks (every other byte). Why: a reading names its region. On November 17 the GSM8K test split's code rose three
laps in a row by 0.015 nats a place, and the whole rise stood at its marks (2.52 to 2.80 on 0.09 of its places) while its letters
fell and its digits held: a layout shift a slice's mean could not show. A ruler: it names kinds by bytes, outside the machine.
"""
import collections
import csv
import math
import sys


def main():
    codec = open(sys.argv[1]).read().split("\n")
    void = int(codec[0].split()[2])
    byte = {(k if k < void else k + 1): b for k, b in enumerate(int(x) for x in codec[1].split())}
    grain = math.log(2.0) / 2**20

    def kind(c):
        b = byte.get(c)
        if b is None:
            return "void"
        ch = chr(b)
        return "digit" if ch.isdigit() else "letter" if ch.isalpha() else "space" if ch in " \n" else "mark"

    print("CAVITY_KIND table slice kind share nats_a_place")
    for path in sys.argv[2:]:
        table = collections.defaultdict(lambda: collections.defaultdict(list))
        for r in csv.DictReader(open(path), delimiter="\t"):
            if r["row"] == "P" and r["cK"] not in ("-", ""):
                table[r["slice"]][kind(int(r["class"]))].append(int(r["cK"]) * grain)
        for name, kinds in table.items():
            total = sum(len(v) for v in kinds.values())
            for k in ("letter", "digit", "space", "mark"):
                v = kinds.get(k, [])
                if v:
                    print(f"CAVITY_KIND {path} {name} {k} {len(v) / total:.3f} {sum(v) / len(v):.4f}")


if __name__ == "__main__":
    main()
