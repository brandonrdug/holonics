#!/usr/bin/env python3
"""Reads `read-reach`'s codes under the cut ruler's settings (`law`, `from:C`, `cut:C:MASK`) into nats a place past the cut.

    python3 -I cut_table.py OUT_DIR C [OUT_DIR ...]

OUT_DIR holds codes.tsv (row, group, place, then a code a setting on 2^-20 bits) and settings.tsv (a setting a line). A further
directory is a later read of the same rows: its settings are joined to the first's by row and place, and a row or a place that
differs between them is refused. Printed, over the places past the cut (C + 1 on; the place at the cut itself, which under a cut stands with nothing known, is given apart):

  CUT_MEAN     a setting's code, its gap to the law's, and the share of the region-alone gap it closes (paired over rows, with the
               standard error of the row means), over all rows and by group (a row's label up to its first colon);
  CUT_BY_AGE   a setting's code by octave of places since the cut;
  CUT_CONTROL  the largest difference a place between `cut:C:0` and `from:C`, where both were read.

A host ruler: it reads a table of codes and holds no law.
"""
import collections
import math
import sys

LN2_20 = math.log(2) / (1 << 20)


def main():
    c = int(sys.argv[2])
    settings = []
    rows = collections.defaultdict(lambda: collections.defaultdict(list))  # row -> setting -> codes by place
    group_of, keys = {}, None
    for out in [sys.argv[1]] + sys.argv[3:]:
        here = open(f"{out}/settings.tsv").read().split()
        seen = []
        for line in open(f"{out}/codes.tsv"):
            w = line.rstrip("\n").split("\t")
            r, group, codes = int(w[0]), w[1].split(":")[0], [int(v) * LN2_20 for v in w[3:]]
            seen.append((r, w[1], w[2]))
            group_of[r] = group
            for s, v in zip(here, codes):
                if s not in settings:
                    rows[r][s].append(v)
        if keys is not None and seen != keys:
            sys.exit(f"{out} holds other rows or places than {sys.argv[1]}")
        keys = seen
        settings += [s for s in here if s not in settings]
    used = [r for r in sorted(rows) if len(rows[r][settings[0]]) >= c + 2]
    print(f"CUT rows={len(used)} of {len(rows)} cut={c} settings={' '.join(settings)}")
    base, alone = "law", f"cut:{c}:0"

    def past(r, s):
        return rows[r][s][c + 1:]

    def mean_se(values):
        n = len(values)
        m = sum(values) / n
        se = math.sqrt(sum((v - m) ** 2 for v in values) / (n * (n - 1))) if n > 1 else float("nan")
        return m, se

    groups = ["all"] + sorted(set(group_of[r] for r in used))
    for g in groups:
        rs = [r for r in used if g == "all" or group_of[r] == g]
        places = sum(len(past(r, base)) for r in rs)
        gap_rows = [sum(past(r, alone)) / len(past(r, alone)) - sum(past(r, base)) / len(past(r, base)) for r in rs] if alone in settings else None
        gap = mean_se(gap_rows)[0] if gap_rows else float("nan")
        for s in settings:
            code = sum(sum(past(r, s)) for r in rs) / places
            over = [sum(past(r, s)) / len(past(r, s)) - sum(past(r, base)) / len(past(r, base)) for r in rs]
            m, se = mean_se(over)
            closed = (1 - m / gap) if gap_rows and gap else float("nan")
            at_cut = sum(rows[r][s][c] for r in rs) / len(rs)
            print(f"CUT_MEAN group={g} setting={s} rows={len(rs)} places={places} nats={code:.4f} over_law={m:+.4f} se={se:.4f} closes={closed:.3f} at_cut={at_cut:.3f}")
    edges = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
    for s in settings:
        cells = []
        for lo, hi in zip(edges, edges[1:]):
            vals = [v for r in used for a, v in enumerate(past(r, s), start=1) if lo <= a < hi]
            if vals:
                cells.append(f"{lo}-{hi - 1}:{sum(vals) / len(vals):.3f}")
        print(f"CUT_BY_AGE setting={s} " + " ".join(cells))
    if alone in settings and f"from:{c}" in settings:
        worst = max(abs(a - b) for r in used for a, b in zip(rows[r][alone][c:], rows[r][f"from:{c}"][c:]))
        mean = sum(abs(a - b) for r in used for a, b in zip(rows[r][alone][c:], rows[r][f"from:{c}"][c:])) / sum(len(rows[r][alone][c:]) for r in used)
        print(f"CUT_CONTROL cut:{c}:0 against from:{c}: largest difference a place {worst:.6f} nats, mean {mean:.6f}")


if __name__ == "__main__":
    main()
