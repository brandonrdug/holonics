"""marked_ruler: read-marked's rows (G176) as the open places' code and expected code, nats a place, at each strength of the carried
release's mark, pooled and by slice, beside the built read (α = 0) (a host ruler; numbers only).
usage: python3 -I marked_ruler.py OUT_DIR
"""
import math
import sys
from collections import defaultdict

SLICES = ["code", "web", "science", "books", "wikidata"]
rows = [[int(x) for x in line.split("\t")] for line in list(open(sys.argv[1] + "/marked.tsv"))[1:]]
by = defaultdict(dict)
for s, alpha, places, code, expected in rows:
    by[alpha][s] = (places, code, expected)


def nats(c, n):
    return c / float(1 << 20) * math.log(2) / n


base = {s: v for s, v in by[0].items()}
for alpha in sorted(by):
    pl = sum(v[0] for v in by[alpha].values())
    code = sum(v[1] for v in by[alpha].values())
    exp = sum(v[2] for v in by[alpha].values())
    b = sum(v[1] for v in base.values())
    slices = " ".join(f"{SLICES[s]}={nats(v[1] - base[s][1], v[0]):+.4f}" for s, v in sorted(by[alpha].items()))
    slope = f" slope={nats(code - b, pl) / (alpha / 65536):+.4f}" if alpha else ""
    print(f"alpha={alpha / 65536:.5f} places={pl} code={nats(code, pl):.4f} expected={nats(exp, pl):.4f} change={nats(code - b, pl):+.5f}{slope} | {slices}")
