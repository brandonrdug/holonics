"""influence_ruler: G148's reading of read-influence's rows (a host ruler; numbers only).

usage: python3 -I influence_ruler.py DIR [DIR ...]   (each a read-influence output directory, influence.tsv)

A pair's influence is |code_moved - code| in bits (codes on 2^-20 bits): how far b's code moved when a's class was replaced. Read by state:
the rank correlation of the influence with the distance and with the news strictly between, over every pair; then the partial readings,
the correlation with the news inside each octave of distance and with the distance inside each octave of news (news in sections of the
flat face's 7.93 bits), each pooled as a mean weighted by its pairs; and the mean influence by octave of each.
"""
import math
import sys
from collections import defaultdict

import numpy as np

BIT = float(1 << 20)
SECTION = math.log2(244.0)


def ranks(v):
    v = np.asarray(v, dtype=float)
    order = np.argsort(v, kind="mergesort")
    r = np.empty(len(v))
    r[order] = np.arange(len(v))
    # average ties
    vals, inv, counts = np.unique(v, return_inverse=True, return_counts=True)
    sums = np.zeros(len(vals))
    np.add.at(sums, inv, r)
    return (sums / counts)[inv]


def spearman(x, y):
    if len(x) < 8:
        return float("nan")
    a, b = ranks(x), ranks(y)
    if a.std() == 0 or b.std() == 0:
        return float("nan")
    return float(np.corrcoef(a, b)[0, 1])


def octave(v):
    return int(math.floor(math.log2(v))) if v >= 1 else -1


for d in sys.argv[1:]:
    rows, clock_rows = [], []
    with open(d + "/influence.tsv") as f:
        f.readline()
        for line in f:
            w = line.rstrip("\n").split("\t")
            s, dist, between, c, cm = w[:5]
            rows.append((s, int(dist), int(between) / BIT, abs(int(cm) - int(c)) / BIT))
            if len(w) > 5 and w[5]:
                clock_rows.append([int(g) / float(1 << 24) for g in w[5].split(",")])
    dist = np.array([r[1] for r in rows], dtype=float)
    news = np.array([r[2] for r in rows], dtype=float)
    infl = np.array([r[3] for r in rows], dtype=float)
    print("INFLUENCE %s pairs=%d mean_bits=%.4f rho_distance=%.4f rho_news=%.4f" % (d.rstrip("/").split("/")[-1], len(rows), infl.mean(), spearman(infl, dist), spearman(infl, news)))
    for name, key, other, label in (("within_distance_octave", dist, news, "news"), ("within_news_octave", news / SECTION, dist, "distance")):
        groups = defaultdict(list)
        for i, k in enumerate(key):
            groups[octave(k)].append(i)
        acc, n = 0.0, 0
        parts = []
        for o in sorted(groups):
            idx = groups[o]
            r = spearman(infl[idx], other[idx])
            if not math.isnan(r):
                acc += r * len(idx)
                n += len(idx)
                parts.append("o%d:%d:%.3f" % (o, len(idx), r))
        print("  %s rho_%s_pooled=%.4f (%d pairs) %s" % (name, label, acc / max(n, 1), n, " ".join(parts)))
    for name, key in (("by_distance_octave", dist), ("by_news_sections_octave", news / SECTION)):
        groups = defaultdict(list)
        for i, k in enumerate(key):
            groups[octave(k)].append(i)
        print("  %s mean_bits %s" % (name, " ".join("o%d:%d:%.4f" % (o, len(groups[o]), infl[groups[o]].mean()) for o in sorted(groups))))
    if clock_rows and len(clock_rows) == len(rows):
        clocks = np.array(clock_rows, dtype=float)
        for h in range(clocks.shape[1]):
            gap = clocks[:, h]
            print("  head_clock %d rho_clock=%.4f" % (h, spearman(infl, gap)))
            for name, key, other, label in (("within_distance_octave", dist, gap, "clock"), ("within_clock_octave", gap, dist, "distance")):
                groups = defaultdict(list)
                for i, k in enumerate(key):
                    groups[octave(k)].append(i)
                acc, n = 0.0, 0
                for o in sorted(groups):
                    r = spearman(infl[groups[o]], other[groups[o]])
                    if not math.isnan(r):
                        acc += r * len(groups[o])
                        n += len(groups[o])
                print("    %s rho_%s_pooled=%.4f (%d pairs)" % (name, label, acc / max(n, 1), n))
    by_slice = defaultdict(list)
    for i, r in enumerate(rows):
        by_slice[r[0]].append(i)
    print("  by_slice %s" % " ".join("%s:%d:rho_d=%.3f:rho_news=%.3f" % (s, len(ix), spearman(infl[ix], dist[ix]), spearman(infl[ix], news[ix])) for s, ix in by_slice.items()))
