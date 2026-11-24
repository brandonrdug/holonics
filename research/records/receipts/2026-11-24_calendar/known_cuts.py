#!/usr/bin/env python3
"""[measurement; the formal thread, November 24] Cuts of a face read on a shown period, from codes already read.

    known_cuts.py ROWS.tsv CODES.tsv

A ruler on the host, and no part of the machine: it reads two tables and writes nothing.

ROWS is the lead's table of rows (`label<TAB>text<TAB>`, label `period:{kept|loose}:{P1}:{i}`): a kept row is drawn letters
in words of `L = P1 - 1` letters, each followed by a space; its loose twin cuts the same letters into words of `L - 1`, `L`
or `L + 1`. CODES is `read-reach`'s `codes.tsv` for those rows under the setting `law` (`row`, `group`, `place`, the code of
the place at its own frontier on `2^(-20)` bits). Codes are printed in nats.

Why the cuts. The mean code of a kept row's separators less its twin's mixes two things: what a shown period gives her, and
the curve of her code of a separator against the count of letters since the last one, since the twin's separators follow
`L - 1`, `L` and `L + 1` letters. The lines:

  KNOWN_MATCHED  P1, the kept separators' code, the twin's separators after exactly `L` letters, their difference with its
                 standard error over rows, the twin's by letters before (`L - 1`, `L`, `L + 1`), every separator of the twin,
                 and `ln P1`, the code of a reader that holds the separators' rate and no place in the period; last third.
  KNOWN_STRETCH  the separators' code by fifty places of the row, kept and loose.
  KNOWN_THIRDS   the twin's separators after exactly `L` letters less the kept row's, by hundred places of the row, each with
                 its standard error over separators.
  KNOWN_RUN      the twin's separators after exactly `L` letters by how many words before them in a run also had exactly `L`
                 (1, 2, 3 or more), against the kept row's; places 100 to 299.
  KNOWN_FIRST    the kept rows' first, second and third separator.
"""
import collections
import math
import sys


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def spread(xs):
    k = len(xs)
    if k < 2:
        return float("nan")
    mu = mean(xs)
    return (sum((x - mu) ** 2 for x in xs) / (k - 1) / k) ** 0.5


def main(rows_path, codes_path):
    rows = []
    with open(rows_path, encoding="utf-8") as f:
        for line in f:
            w = line.rstrip("\n").split("\t")
            rows.append((w[0], w[1]))
    codes = {}
    with open(codes_path, encoding="utf-8") as f:
        for line in f:
            r, _, place, code = line.rstrip("\n").split("\t")[:4]
            codes[(int(r), int(place))] = int(code) / 2**20 * math.log(2)
    by_row = collections.defaultdict(lambda: collections.defaultdict(list))   # (kind, P1) -> letters before -> a row's mean
    every = collections.defaultdict(list)                                      # (kind, P1) -> a row's mean, every separator
    stretch = collections.defaultdict(list)
    run_of = collections.defaultdict(list)
    thirds = collections.defaultdict(list)
    first = collections.defaultdict(list)
    for r, (label, text) in enumerate(rows):
        _, kind, p1, _ = label.split(":")
        p1 = int(p1)
        length = p1 - 1
        tail = collections.defaultdict(list)
        letters = matched = seen = 0
        for p, ch in enumerate(text):
            if (r, p) not in codes:
                continue
            if ch not in " \n":
                letters += 1
                continue
            code = codes[(r, p)]
            matched = matched + 1 if letters == length else 0
            seen += 1
            stretch[(kind, p1, p // 50)].append(code)
            if seen <= 3:
                first[(kind, p1, seen)].append(code)
            if p >= 200:
                tail[letters].append(code)
            if letters == length:
                thirds[(kind, p1, p // 100)].append(code)
            if p >= 100 and letters == length:
                run_of[(kind, p1, min(matched, 3))].append(code)
            letters = 0
        for n, v in tail.items():
            by_row[(kind, p1)][n].append(mean(v))
        if tail:
            every[(kind, p1)].append(mean([c for v in tail.values() for c in v]))
    periods = sorted({k[1] for k in by_row})
    print(f"KNOWN rows={len(rows)} codes={len(codes)} periods={','.join(map(str, periods))}")
    for p1 in periods:
        length = p1 - 1
        kept, loose = by_row[("kept", p1)][length], by_row[("loose", p1)]
        gain = mean(loose[length]) - mean(kept)
        err = (spread(loose[length]) ** 2 + spread(kept) ** 2) ** 0.5
        around = " ".join(f"{mean(loose[n]):.3f}" if loose.get(n) else "-" for n in (length - 1, length, length + 1))
        print(f"KNOWN_MATCHED P1={p1} kept={mean(kept):.3f} loose_matched={mean(loose[length]):.3f} gain={gain:+.3f} se={err:.3f} "
              f"loose_by_letters={around} loose_all={mean(every[('loose', p1)]):.3f} "
              f"kept_less_loose_all={mean(every[('kept', p1)]) - mean(every[('loose', p1)]):+.3f} ln_P1={math.log(p1):.3f}")
    for p1 in periods:
        for kind in ("kept", "loose"):
            print(f"KNOWN_STRETCH P1={p1} kind={kind} " + " ".join(f"{mean(stretch[(kind, p1, b)]):.3f}" for b in range(6)))
    for p1 in periods:
        cells = []
        for third in range(3):
            kept, loose = thirds[("kept", p1, third)], thirds[("loose", p1, third)]
            cells.append(f"{mean(loose) - mean(kept):+.3f}({(spread(loose) ** 2 + spread(kept) ** 2) ** 0.5:.3f})")
        print(f"KNOWN_THIRDS P1={p1} gain=" + " ".join(cells))
    for p1 in periods:
        kept = [c for k in (1, 2, 3) for c in run_of[("kept", p1, k)]]
        cells = " ".join(f"run{k}={mean(run_of[('loose', p1, k)]):.3f}({len(run_of[('loose', p1, k)])})" for k in (1, 2, 3))
        print(f"KNOWN_RUN P1={p1} kept={mean(kept):.3f}({len(kept)}) {cells}")
    for p1 in periods:
        print(f"KNOWN_FIRST P1={p1} " + " ".join(f"{mean(first[('kept', p1, s)]):.3f}" for s in (1, 2, 3)))


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2])
