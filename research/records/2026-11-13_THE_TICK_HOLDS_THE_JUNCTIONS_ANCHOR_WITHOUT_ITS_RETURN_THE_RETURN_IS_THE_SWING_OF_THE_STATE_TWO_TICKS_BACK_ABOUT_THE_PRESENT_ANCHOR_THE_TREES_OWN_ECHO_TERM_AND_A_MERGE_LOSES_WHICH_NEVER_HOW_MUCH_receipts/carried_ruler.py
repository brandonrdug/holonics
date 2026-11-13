"""carried_ruler: read-carried's rows (G175) as d(code)/dα at the founding, nats a place a unit of the carried strength (a host ruler;
numbers only). r_t on the covector's grain against the state's moves the code by r 2^-40 bits; d(code)/dα = Σ r ln 2 2^-40 over the open
places. The random-sign floor is sqrt(2/π) sqrt(Σ r_t²); `ratio` is |Σ r| over it.
usage: python3 -I carried_ruler.py OUT_DIR
"""
import math
import sys

SLICES = ["code", "web", "science", "books", "wikidata"]
rows = [[int(x) for x in line.split("\t")] for line in list(open(sys.argv[1] + "/carried.tsv"))[1:]]


def line(name, rs):
    opened = sum(r[2] for r in rs)
    out = []
    for label, k in (("open", 3), ("written", 6), ("both", None)):
        if k is None:
            s, sq = sum(r[3] + r[6] for r in rs), sum(r[5] + r[8] for r in rs)
        else:
            s, sq = sum(r[k] for r in rs), sum(r[k + 2] for r in rs)
        floor = math.sqrt(2 / math.pi) * math.sqrt(sq) * 2**32
        out.append(f"{label}: dcode_dalpha={s * math.log(2) / 2**40 / opened:+.5f} ratio={abs(s) / floor:.2f}")
    print(f"{name} open_places={opened} | " + " | ".join(out))


line("pooled", rows)
for r in rows:
    line(SLICES[r[0]], [r])
