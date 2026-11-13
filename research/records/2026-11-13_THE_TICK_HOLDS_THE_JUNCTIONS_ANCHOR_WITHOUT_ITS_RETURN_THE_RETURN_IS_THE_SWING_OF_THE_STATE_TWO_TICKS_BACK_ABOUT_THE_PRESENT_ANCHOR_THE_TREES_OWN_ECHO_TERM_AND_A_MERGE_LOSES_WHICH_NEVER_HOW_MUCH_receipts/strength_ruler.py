"""A ruler (host, floats lawful): the read's mirror at finite strength, from read-mirror-strength's strength.tsv (G161).

Codes on 2^-20 bits are read as nats a place (code / places / 2^20 ln 2). Prints by mask and head, pooled over slices and then by slice, the
code a place with the mirror off and each strength's difference from it (negative: the mirror at that strength lowers the code).
Usage: python3 -I strength_ruler.py OUT...
"""
import math
import os
import sys
from collections import defaultdict

SLICES = ["code", "web", "science", "books", "wikidata"]
NATS = math.log(2) / 2**20


def main(outs):
    for out in outs:
        acc = defaultdict(lambda: [0, 0])
        with open(os.path.join(out, "strength.tsv")) as f:
            next(f)
            for row in f:
                s, m, h, st, n, code = (int(x) for x in row.split("\t"))
                for key in ((m, h, st, None), (m, h, st, s)):
                    acc[key][0] += code
                    acc[key][1] += n
        print(f"READ {out}")
        strengths = sorted({k[2] for k in acc if k[2] != 0})
        for m in (0, 1):
            for sl in [None] + list(range(5)):
                off = acc[(m, 0, 0, sl)]
                if off[1] == 0:
                    continue
                base = off[0] / off[1] * NATS
                name = "pooled" if sl is None else SLICES[sl]
                for h in range(4):
                    cells = []
                    for st in strengths:
                        c = acc[(m, h, st, sl)]
                        cells.append(f"{st / 65536:+.2f}:{c[0] / c[1] * NATS - base:+.5f}")
                    print(f"  STRENGTH mask={m} slice={name} head={h} off={base:.4f} | " + " ".join(cells))


if __name__ == "__main__":
    main(sys.argv[1:])
