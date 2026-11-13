"""A ruler (host, floats lawful): the field's own release returned at a lag, from read-release's release.tsv (G163).

Codes on 2^-20 bits are read as nats a place. Prints, pooled over slices and then by slice: the code and expected code by pass, the faces'
change (the root mean square a place, on 2^-16 shares) and the successive-change cosine. Usage: python3 -I release_ruler.py OUT...
"""
import math
import os
import sys
from collections import defaultdict

SLICES = ["code", "web", "science", "books", "wikidata"]
NATS = math.log(2) / 2**20


def show(label, acc):
    passes = sorted(acc)
    code = " ".join(f"p{p}={acc[p][1] / acc[p][0] * NATS:.4f}" for p in passes)
    exp = " ".join(f"p{p}={acc[p][2] / acc[p][0] * NATS:.4f}" for p in passes)
    change = " ".join(f"p{p}={math.sqrt(acc[p][3] / acc[p][0]):.0f}" for p in passes if acc[p][3])
    cos = " ".join(f"p{p}={acc[p][4] / math.sqrt(acc[p][3] * acc[p - 1][3]):.3f}" for p in passes if p - 1 in acc and acc[p][3] and acc[p - 1][3] and acc[p][4])
    print(f"  {label} places={acc[passes[0]][0]}\n    code {code}\n    expected {exp}\n    change {change}\n    cosine {cos}")


def main(outs):
    for out in outs:
        pooled = defaultdict(lambda: [0, 0, 0, 0, 0])
        by = defaultdict(lambda: defaultdict(lambda: [0, 0, 0, 0, 0]))
        with open(os.path.join(out, "release.tsv")) as f:
            next(f)
            for row in f:
                s, p, pl, code, exp, norm, inner = (int(x) for x in row.split("\t"))
                for a in (pooled[p], by[s][p]):
                    for i, v in enumerate((pl, code, exp, norm, inner)):
                        a[i] += v
        print(f"RELEASE {out}")
        show("pooled", pooled)
        for s in sorted(by):
            show(SLICES[s], by[s])


if __name__ == "__main__":
    main(sys.argv[1:])
