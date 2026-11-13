"""A ruler (host, floats lawful): each place's least code over its stages against stage 4, from read-depth's depth.tsv (G153).

Codes on 2^-20 bits are read as nats. Prints, pooled and by slice: the places, the mean code at stage 4, the mean least code over every stage
and its gap, and the best stage's histogram (the first stage at the least, ties to the earlier). Usage: python3 -I best_stage_ruler.py DEPTH_TSV...
"""
import math
import sys
from collections import Counter, defaultdict

NATS = math.log(2) / 2**20


def main(paths):
    for path in paths:
        by = defaultdict(list)
        with open(path) as f:
            head = next(f).rstrip("\n").split("\t")
            stages = sum(1 for h in head if h.startswith("code"))
            for row in f:
                w = row.rstrip("\n").split("\t")
                codes = [int(w[2 + 2 * s]) for s in range(stages)]
                by[w[0]].append(codes)
        rows = [c for v in by.values() for c in v]
        for name, group in [("pooled", rows)] + sorted(by.items()):
            n = len(group)
            at4 = sum(c[4] for c in group) / n * NATS
            least = sum(min(c) for c in group) / n * NATS
            best = Counter(c.index(min(c)) for c in group)
            past8 = sum(v for s, v in best.items() if s > 8) / n
            hist = " ".join(f"s{s}:{best.get(s, 0)}" for s in range(stages))
            print(f"BEST {path.split('/')[-2]} slice={name} places={n} stage4={at4:.4f} least={least:.4f} gap={at4 - least:.4f} share_at_4={best.get(4, 0) / n:.3f} share_past_8={past8:.3f} | {hist}")


if __name__ == "__main__":
    main(sys.argv[1:])
