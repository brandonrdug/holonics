"""A ruler (host, floats lawful): the junction's return's founding covector from read-junction's junction.tsv and coords.tsv (G152).

At the founding (Gamma = 0) the chart's covector is dl = (ln 2/2) <lambda^(k+1), x^(k+1) - x^(k-1)>, on 2^-16 of l at the covector's grain, so a
unit of l_b moves a region's code by sum(dl) 2^-24 bits. Prints, by mask (0: the cut's own; 1: the middle place alone open), tick and kind of
row, pooled and by slice: the rows, sum(dl), sum|dl|, the coherence |sum|/sum|.|, and the slope -sum(dl) ln 2 2^-24 / places in nats a place per
unit of l (positive: raising l lowers the code), places the open rows of the same mask, tick and slice. Then the chart L's covector by
coordinate of the tick's opening chart: per coordinate |sum(dl r_i)| / sum|dl r_i|, its median and largest over the coordinates.
Usage: python3 -I junction_ruler.py OUT
"""
import math
import os
import sys
from collections import defaultdict

SLICES = ["code", "web", "science", "books", "wikidata"]


def main(out):
    sums = defaultdict(lambda: [0, 0, 0])  # (mask, tick, written, slice) -> rows, sum, magnitude
    with open(os.path.join(out, "junction.tsv")) as f:
        next(f)
        for row in f:
            s, m, _k, t, w, _p, dl = (int(x) for x in row.split("\t"))
            a = sums[(m, t, w, s)]
            a[0] += 1
            a[1] += dl
            a[2] += abs(dl)
    masks = sorted({k[0] for k in sums})
    ticks = sorted({k[1] for k in sums})
    slices = sorted({k[3] for k in sums})

    def pooled(m, t, w, s=None):
        rows = tot = mag = 0
        for k, (r, a, b) in sums.items():
            if k[0] == m and k[1] == t and k[2] == w and (s is None or k[3] == s):
                rows, tot, mag = rows + r, tot + a, mag + b
        return rows, tot, mag

    for m in masks:
        for t in ticks:
            for w in (0, 1):
                for s in [None] + slices:
                    rows, tot, mag = pooled(m, t, w, s)
                    places = pooled(m, t, 0, s)[0]
                    if rows == 0:
                        continue
                    coh = abs(tot) / mag if mag else 0.0
                    slope = -tot * math.log(2) / 2**24 / places if places else 0.0
                    name = "pooled" if s is None else SLICES[s]
                    print(f"JUNCTION mask={m} tick={t} rows={'written' if w else 'open'} slice={name} n={rows} sum={tot} magnitude={mag} coherence={coh:.4f} slope_nats_per_place_per_unit={slope:+.5f}")
    coords = defaultdict(lambda: [0, 0])
    with open(os.path.join(out, "coords.tsv")) as f:
        next(f)
        for row in f:
            s, m, t, w, i, a, b = (int(x) for x in row.split("\t"))
            c = coords[(m, t, w, i)]
            c[0] += a
            c[1] += b
    for m in masks:
        for t in ticks:
            for w in (0, 1):
                cs = [abs(coords[(m, t, w, i)][0]) / coords[(m, t, w, i)][1] for i in range(64) if coords[(m, t, w, i)][1]]
                if not cs:
                    continue
                cs.sort()
                print(f"CHART mask={m} tick={t} rows={'written' if w else 'open'} coordinates={len(cs)} coherence_median={cs[len(cs) // 2]:.4f} coherence_max={cs[-1]:.4f} over_0.1={sum(1 for c in cs if c > 0.1)}")


if __name__ == "__main__":
    main(sys.argv[1])
