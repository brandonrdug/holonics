#!/usr/bin/env -S python3 -I
"""A ruler: the arithmetic writes of a lap read by place (the lead, November 17).

Usage: arithmetic_writes_by_place.py FORMS.written [FORMS.written …]

Reads `write-forms`' table (`label<TAB>prompt<TAB>write<TAB>reference`) and, for the rows whose reference is a number, takes the
write's first line and prints, by the label's kind (`met`, `far`): the share that is a number at all, and the shares whose sign,
whose count of digits, whose leading digit, whose leading digit and count together, whose last digit and whose whole numeral agree
with the reference value. Why: a write that has the hundreds and the tens of a sum and not its units is a different state from one
that has nothing, and one count of whole agreements cannot tell them apart; the reading names the register it stands on. The
reference value is one specimen and the shares are agreements with it at this receiver, the world's interpreter. A ruler: it parses
numerals outside the machine.
"""
import collections
import re
import sys

NUMBER = re.compile(r"-?\d+")
KEYS = ("number", "sign", "length", "lead", "lead_and_length", "units", "whole")


def main():
    print("WRITES_BY_PLACE table kind rows " + " ".join(KEYS))
    for path in sys.argv[1:]:
        acc = collections.defaultdict(collections.Counter)
        for line in open(path):
            r = line.rstrip("\n").split("\t")
            if len(r) < 4 or not r[0].startswith("answer:"):
                continue
            ref = r[3].replace("\\n", "\n").split("\n")[0].strip()
            wr = r[2].replace("\\n", "\n").split("\n")[0].strip()
            if not NUMBER.fullmatch(ref):
                continue
            a = acc[r[0].split(":")[1]]
            a["rows"] += 1
            if not NUMBER.fullmatch(wr):
                continue
            rs, ws = ref.lstrip("-"), wr.lstrip("-")
            a["number"] += 1
            a["sign"] += (ref[0] == "-") == (wr[0] == "-")
            a["length"] += len(rs) == len(ws)
            a["lead"] += rs[0] == ws[0]
            a["lead_and_length"] += rs[0] == ws[0] and len(rs) == len(ws)
            a["units"] += rs[-1] == ws[-1]
            a["whole"] += ref == wr
        for kind in sorted(acc):
            a = acc[kind]
            print(f"WRITES_BY_PLACE {path} {kind} {a['rows']} " + " ".join(f"{a[k] / a['rows']:.3f}" for k in KEYS))


if __name__ == "__main__":
    main()
