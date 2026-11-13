"""A ruler (host, floats lawful): each site's echo B by region from read-echo's echo.tsv (G151).

B_i = sum_j p_ji^(t) p_ij^(t+1), the share of a site's arrival that is its own state of two ticks before (the junction record, §7);
the constitution's own return is Gamma* = B/(1 - B) on the chart l* = -log2(1 - 2B). Prints, by mask (0: the cut's own; 1: the middle place
alone open), slice and kind of row, the rows, the median and quartiles of B, the shares at B = 0 and B >= 1/2, and the rows counted on
the chart l*; then the written rows by head. Usage: python3 -I echo_ruler.py OUT/echo.tsv
"""
import math
import sys
from collections import defaultdict

SLICES = ["code", "web", "science", "books", "wikidata"]
EDGES = [0.0, 0.125, 0.25, 0.5, 1.0, 2.0, 4.0]  # l* bins; B = 0 is its own, B >= 1/2 is past the chart


def chart(bs):
    zero = sum(1 for b in bs if b == 0.0)
    past = sum(1 for b in bs if b >= 0.5)
    counts = [0] * len(EDGES)
    for b in bs:
        if b == 0.0 or b >= 0.5:
            continue
        l = -math.log2(1.0 - 2.0 * b)
        k = max(i for i, e in enumerate(EDGES) if l >= e)
        counts[k] += 1
    bins = " ".join(f"[{EDGES[i]:g},{EDGES[i + 1] if i + 1 < len(EDGES) else 'inf'}):{c}" for i, c in enumerate(counts))
    return f"zero:{zero} {bins} past_half:{past}"


def q(bs, f):
    return bs[min(len(bs) - 1, int(f * len(bs)))] if bs else float("nan")


def line(label, bs):
    bs = sorted(bs)
    n = len(bs)
    if n == 0:
        return f"{label} rows=0"
    med = q(bs, 0.5)
    lmed = -math.log2(1.0 - 2.0 * med) if med < 0.5 else float("inf")
    half = sum(1 for b in bs if b >= 0.5) / n
    zero = sum(1 for b in bs if b == 0.0) / n
    return (f"{label} rows={n} median={med:.5f} (log2 {math.log2(med) if med > 0 else float('-inf'):.2f}; l*={lmed:.4f}; Gamma*={med / (1 - med):.4f}) "
            f"q10={q(bs, .1):.5f} q25={q(bs, .25):.5f} q75={q(bs, .75):.5f} q90={q(bs, .9):.5f} mean={sum(bs) / n:.5f} share_zero={zero:.4f} share_half={half:.4f}\n    chart {chart(bs)}")


def main(path):
    by = defaultdict(list)
    with open(path) as f:
        next(f)
        for row in f:
            s, m, k, h, w, b = row.split("\t")
            by[(int(s), int(m), int(k), int(h), int(w))].append(int(b) / 2.0**63)
    keys = list(by)
    pick = lambda **c: [b for key in keys if all(key[i] == v for i, v in c.items()) for b in by[key]]
    S, M, K, H, W = 0, 1, 2, 3, 4
    written_all = [b for key in keys if key[W] == 1 for b in by[key]]
    print(line("ECHO written pooled (both masks, all heads, all slices)", written_all))
    print(line("ECHO open pooled", [b for key in keys if key[W] == 0 for b in by[key]]))
    heads = sorted({key[H] for key in keys})
    for m in (0, 1):
        print(f"MASK {m}")
        for w in (1, 0):
            print("  " + line(f"{'written' if w else 'open'} all slices", [b for key in keys if key[M] == m and key[W] == w for b in by[key]]))
        for s in sorted({key[S] for key in keys}):
            name = SLICES[s] if s < len(SLICES) else str(s)
            for w in (1, 0):
                bs = [b for key in keys if key[M] == m and key[S] == s and key[W] == w for b in by[key]]
                print("    " + line(f"{name} {'written' if w else 'open'}", bs))
        for h in heads:
            print("    " + line(f"head {h} written", [b for key in keys if key[M] == m and key[H] == h and key[W] == 1 for b in by[key]]))
        for k in sorted({key[K] for key in keys}):
            print("    " + line(f"kind {k} written", [b for key in keys if key[M] == m and key[K] == k and key[W] == 1 for b in by[key]]))


if __name__ == "__main__":
    main(sys.argv[1])
