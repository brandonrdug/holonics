#!/usr/bin/env python3
"""Parts an arm's gain across a cut by what the cut lets across: two reads of `read-reach` on the same rows, a control's and an arm's.

    python3 -I joined_split.py C CONTROL_OUT ARM_OUT

Each directory holds codes.tsv (row, group, place, then a code a setting on 2^-20 bits) and settings.tsv (a setting a line), with
`law` and `cut:C:0` among the settings and the same settings in both. A setting's price is its code less the law's code of the same
state, over the places past the cut (C + 1 on). Printed, in nats a place:

  SPLIT        a setting's price on the control and on the arm, the share of a cut's cost (`cut:C:0`) each closes, and the arm's
               price less the control's, paired by row, with the standard error of the row differences;
  SPLIT_BAND   the same difference in two bands of places past the cut (1 to 31, 32 on);
  SPLIT_STEP   between two settings that differ by one path (b less a): what the path brings back on each state and the arm's
               gain in it, paired by row.

A host ruler: it reads two tables of codes and holds no law. It prints means over places and rows and no place's code.
"""
import collections
import math
import sys

LN2_20 = math.log(2) / (1 << 20)
STEPS = [("cut:{c}:0", "cut:{c}:31"), ("cut:{c}:0", "cut:{c}:32"), ("cut:{c}:31", "cut:{c}:63"), ("cut:{c}:63", "cut:{c}:191"), ("cut:{c}:31", "cut:{c}:159")]


def read(out):
    settings = open(f"{out}/settings.tsv").read().split()
    rows = collections.defaultdict(dict)  # row -> place -> codes by setting
    for line in open(f"{out}/codes.tsv"):
        w = line.rstrip("\n").split("\t")
        rows[int(w[0])][int(w[2])] = [int(v) * LN2_20 for v in w[3:]]
    return settings, rows


def mean_se(values):
    n = len(values)
    m = sum(values) / n
    return m, math.sqrt(sum((v - m) ** 2 for v in values) / (n * (n - 1))) if n > 1 else 0.0


def main():
    c = int(sys.argv[1])
    (sa, a), (sb, b) = read(sys.argv[2]), read(sys.argv[3])
    if sa != sb or sorted(a) != sorted(b) or any(sorted(a[r]) != sorted(b[r]) for r in a):
        sys.exit("joined_split: the two reads differ in settings, rows or places")
    law = sa.index("law")

    def price(rows, r, s, lo, hi):  # a row's mean price of setting s over places c + lo .. c + hi
        v = [rows[r][p][s] - rows[r][p][law] for p in rows[r] if c + lo <= p <= c + hi]
        return sum(v) / len(v)

    far = max(max(a[r]) for r in a) - c
    print(f"SPLIT_HEAD cut={c} rows={len(a)} places_past={sum(1 for r in a for p in a[r] if p > c)} settings={','.join(sa)}")
    whole = {}
    for k, s in enumerate(sa):
        if k == law:
            continue
        ctl, arm = [price(a, r, k, 1, far) for r in sorted(a)], [price(b, r, k, 1, far) for r in sorted(a)]
        whole[s] = (ctl, arm)
    cost_c, cost_a = mean_se(whole[f"cut:{c}:0"][0])[0], mean_se(whole[f"cut:{c}:0"][1])[0]
    for s, (ctl, arm) in whole.items():
        (mc, _), (ma, _) = mean_se(ctl), mean_se(arm)
        d, se = mean_se([y - x for x, y in zip(ctl, arm)])
        print(f"SPLIT setting={s} control={mc:+.4f} arm={ma:+.4f} closes_control={1 - mc / cost_c:.3f} closes_arm={1 - ma / cost_a:.3f} arm_less_control={d:+.4f} se={se:.4f}")
    for k, s in enumerate(sa):
        if k == law:
            continue
        parts = []
        for name, lo, hi in (("1-31", 1, 31), ("32-on", 32, far)):
            d, se = mean_se([price(b, r, k, lo, hi) - price(a, r, k, lo, hi) for r in sorted(a)])
            parts.append(f"{name}:{d:+.4f}({se:.4f})")
        print(f"SPLIT_BAND setting={s} arm_less_control " + " ".join(parts))
    for lo_s, hi_s in STEPS:
        x, y = lo_s.format(c=c), hi_s.format(c=c)
        if x in whole and y in whole:
            back_c = [p - q for p, q in zip(whole[x][0], whole[y][0])]
            back_a = [p - q for p, q in zip(whole[x][1], whole[y][1])]
            (mc, _), (ma, _) = mean_se(back_c), mean_se(back_a)
            d, se = mean_se([q - p for p, q in zip(back_c, back_a)])
            print(f"SPLIT_STEP from={x} to={y} back_control={mc:+.4f} back_arm={ma:+.4f} gain={d:+.4f} se={se:.4f}")


if __name__ == "__main__":
    main()
