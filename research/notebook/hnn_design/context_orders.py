#!/usr/bin/env python3
"""What longer contexts of the past carry on campaign 1's cut (the contact loop record, section 23).

[measured-diagnostic; exterior] Prediction by partial matching with escape rule C and exclusion,
the law `compression::landmark::context::baseline::Ppm` states, run online over the cut's first n*
cells for orders 0 to 8, prequential (each cell coded at the counts before it). Masses are exact
fractions; each total code length is reported as the exact dyadic of its float sum of logarithms at
24 significant bits (the logarithm is an exterior search). Arguments: the cut file, n*, the held-out
start. It prints, per order, the training and held-out code in bits.
"""
import math
import sys
from fractions import Fraction

from receiver_oracle import exact


def ppm_codes(cells, order, alphabet=256):
    counts = {}
    codes = []
    for i, s in enumerate(cells):
        excluded = set()
        mass = Fraction(1)
        coded = False
        for k in range(min(order, i), -1, -1):
            table = counts.get((k, tuple(cells[i - k:i])))
            if not table:
                continue
            seen = {c: n for c, n in table.items() if c not in excluded}
            if not seen:
                continue
            n = sum(seen.values())
            d = len(seen)
            if s in seen:
                mass *= Fraction(seen[s], n + d)
                coded = True
                break
            mass *= Fraction(d, n + d)
            excluded |= set(seen)
        if not coded:
            mass *= Fraction(1, alphabet - len(excluded))
        codes.append(-math.log2(mass))
        for k in range(0, min(order, i) + 1):
            table = counts.setdefault((k, tuple(cells[i - k:i])), {})
            table[s] = table.get(s, 0) + 1
    return codes


def main(path, n_star, held):
    cells = list(open(path, "rb").read()[:n_star])
    for order in range(0, 9):
        codes = ppm_codes(cells, order)
        print(
            f"PPM order {order}: training {exact(sum(codes[:held]))} bits over {held} cells, "
            f"held out {exact(sum(codes[held:]))} bits over {n_star - held} cells",
            flush=True,
        )


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
