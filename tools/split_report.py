#!/usr/bin/env python3 -I
"""split_report.py STATE OUT: G39's receipts from `split-field`'s output (theory, November 11 04:48).

OUT holds G.tsv (the section's deposit covector) and GQ.tsv (the same return with the loud places' face covector zeroed, the quiet places' part), one integer an entry of the
material. G_loud = G - G_quiet. Printed, for the whole material and for each family (the layout of part_rates.py, read from STATE's head line): |G_quiet| / |G| and
cos(G_loud, G), also |G_loud| / |G| and cos(G_quiet, G). Exact integer sums; the ratios as decimals in a report. STATE is read only."""
import math
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
from part_rates import layout, load  # noqa: E402


def ints(path):
    return [int(x) for x in open(path).read().split()]


def stats(g, q, lo, hi):
    n_g = n_q = n_l = d_lg = d_qg = 0
    for i in range(lo, hi):
        gi, qi = g[i], q[i]
        li = gi - qi
        n_g += gi * gi
        n_q += qi * qi
        n_l += li * li
        d_lg += li * gi
        d_qg += qi * gi
    return n_g, n_q, n_l, d_lg, d_qg


def line(name, entries, s):
    n_g, n_q, n_l, d_lg, d_qg = s
    if n_g == 0:
        return f"{name}\t{entries}\t0\t-\t-\t-\t-"
    cos = lambda d, n: d / math.sqrt(n * n_g) if n else float("nan")
    return f"{name}\t{entries}\t{math.sqrt(n_g):.6g}\t{math.sqrt(n_q / n_g):.4f}\t{cos(d_lg, n_l):.4f}\t{math.sqrt(n_l / n_g):.4f}\t{cos(d_qg, n_q):.4f}"


def main():
    state, out = sys.argv[1:3]
    _, d, _, _ = load(state)
    fam, total = layout(d)
    g, q = ints(out + "/G.tsv"), ints(out + "/GQ.tsv")
    assert len(g) == len(q) == total, (len(g), len(q), total)
    print("family\tentries\t|G|\t|G_quiet|/|G|\tcos(G_loud,G)\t|G_loud|/|G|\tcos(G_quiet,G)")
    print(line("TOTAL", total, stats(g, q, 0, total)))
    names = sorted(fam, key=fam.get)
    for i, name in enumerate(names):
        lo = fam[name]
        hi = fam[names[i + 1]] if i + 1 < len(names) else total
        if hi > lo:
            print(line(name, hi - lo, stats(g, q, lo, hi)))


if __name__ == "__main__":
    main()
