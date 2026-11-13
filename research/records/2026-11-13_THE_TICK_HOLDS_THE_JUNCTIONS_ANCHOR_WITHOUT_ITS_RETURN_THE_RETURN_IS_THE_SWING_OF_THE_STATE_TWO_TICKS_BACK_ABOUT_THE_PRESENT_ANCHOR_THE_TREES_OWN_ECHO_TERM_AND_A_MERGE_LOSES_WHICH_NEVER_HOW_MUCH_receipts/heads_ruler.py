"""A ruler (host, floats lawful): each row's round trips across heads from read-echo's heads.tsv (G154).

B(h, h') = sum_j p_ji^(t, h') p_ij^(t+1, h) on 2^-63, a row a line, h' fastest. Prints over written rows, pooled over masks and slices and then
by slice: the 4-by-4 table of medians and of means, and for each head h the median over rows of its row sum over h' against its diagonal.
Usage: python3 -I heads_ruler.py OUT
"""
import os
import sys
from collections import defaultdict

SLICES = ["code", "web", "science", "books", "wikidata"]


def median(v):
    v = sorted(v)
    return v[len(v) // 2] if v else float("nan")


def table(rows, heads, label):
    print(f"HEADS {label} rows={len(rows)}")
    for kind, f in (("median", median), ("mean", lambda v: sum(v) / len(v))):
        for h in range(heads):
            cells = " ".join(f"{f([r[h * heads + k] for r in rows]):.5f}" for k in range(heads))
            print(f"  {kind} h={h}: {cells}")
    for h in range(heads):
        ratio = median([sum(r[h * heads:(h + 1) * heads]) / r[h * heads + h] for r in rows if r[h * heads + h] > 0])
        print(f"  row_sum_over_diagonal h={h} median={ratio:.3f} (rows with a diagonal)")


def main(out):
    by = defaultdict(list)
    heads = 0
    with open(os.path.join(out, "heads.tsv")) as f:
        next(f)
        for line in f:
            w = line.rstrip("\n").split("\t")
            cells = [int(x) / 2.0**63 for x in w[4:]]
            heads = int(round(len(cells) ** 0.5))
            by[(int(w[0]), int(w[3]))].append(cells)
    written = [r for (s, w), v in by.items() if w == 1 for r in v]
    table(written, heads, "written pooled")
    for s in sorted({s for s, _ in by}):
        table(by[(s, 1)], heads, f"written {SLICES[s]}")


if __name__ == "__main__":
    main(sys.argv[1])
