#!/usr/bin/env python3
"""Which byte leads each held opening face as the writer meets it (the unified-theory reading of November 5, 22:02).

Usage: lead.py OPENING_DIR [COUNT]

Over the first COUNT problems (32, the write's): at place 0, how many faces lead with '`' and how many with 'y'; at places 10
to 255, the share of faces led by 'y' and the commonest leads, with the leading mass's mean. Aggregates only.
"""
import collections
import csv
import sys

UNIT = 1 << 20


def main():
    o, n = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 32
    at0, far, mass0, massfar = collections.Counter(), collections.Counter(), [], []
    with open(f"{o}/OPENING.tsv") as f:
        for r in csv.DictReader(f, delimiter="\t"):
            k, j = int(r["problem"]), int(r["place"])
            if k >= n:
                continue
            lead = r["lead"] if r["lead"] == "void" else bytes.fromhex(r["lead"]).decode("latin-1")
            if j == 0:
                at0[lead] += 1
                mass0.append(int(r["lead_mass"]) / UNIT)
            elif 10 <= j <= 255:
                far[lead] += 1
                massfar.append(int(r["lead_mass"]) / UNIT)
    total = sum(far.values())
    print(f"LEAD place 0 over {sum(at0.values())}: '`' {at0['`']}, 'y' {at0['y']}; leads {at0.most_common(5)}; mean lead mass {sum(mass0) / max(len(mass0), 1):.3f}")
    print(f"LEAD places 10-255 over {total}: 'y' {far['y'] / max(total, 1):.3f}; leads {[(c, round(v / total, 3)) for c, v in far.most_common(6)]}; mean lead mass {sum(massfar) / max(len(massfar), 1):.3f}")


if __name__ == "__main__":
    main()
