#!/usr/bin/env python3
"""Reads how concentrated the price of a cut is over the places past it, from `read-reach`'s codes under the cut ruler's settings.

    python3 -I far_gain_concentration.py C OUT_DIR [OUT_DIR ...]

OUT_DIR is what `cut_table.py` reads (codes.tsv and settings.tsv of one read of the same rows). A place's price under a setting is
its code under that setting less its code under the law, in nats. Printed, over the places past the cut:

  CONC        a setting's total price, the count of places it stands on, and the share of the positive price that stands on the
              dearest 1%, 2%, 5%, 10%, 20% and 50% of places; the share of places whose price is under zero and what they give back;
              the participation count (sum g)^2 / sum g^2 over the places of positive price, as a share of the places;
  CONC_FIFTH  the price by fifth of the law's own code at the place (the cheapest fifth first), as nats a place and share of the total;
  CONC_DEAR   over the dearest tenth of places under `cut:C:0` and over the other nine tenths apart: a setting's price there and the
              share of the region-alone price there that it brings back;
  CONC_PLANT  the same shares for a planted price of equal total spread evenly (the control: its shares are the fractions themselves)
              and for one drawn from an exponential law (whose dearest 10% hold about 0.33).

A host ruler: it reads a table of codes and holds no law. It prints no place and no text, only sums over places.
"""
import collections
import math
import random
import sys

LN2_20 = math.log(2) / (1 << 20)
FRACTIONS = (0.01, 0.02, 0.05, 0.10, 0.20, 0.50)


def shares(g):
    pos = sorted((v for v in g if v > 0), reverse=True)
    total = sum(pos)
    n = len(g)
    out = []
    for f in FRACTIONS:
        k = max(1, int(round(f * n)))
        out.append(sum(pos[:k]) / total if total else float("nan"))
    part = (total * total / sum(v * v for v in pos)) / n if pos else float("nan")
    neg = [v for v in g if v < 0]
    return total, out, len(neg) / n, sum(neg), part


def line(tag, name, g):
    total, sh, negshare, negsum, part = shares(g)
    cells = " ".join(f"top{int(f * 100)}%={s:.3f}" for f, s in zip(FRACTIONS, sh))
    print(f"{tag} setting={name} places={len(g)} net={sum(g):.1f} positive={total:.1f} {cells} under_zero={negshare:.3f} giving_back={negsum:.1f} participation={part:.3f}")


def main():
    c = int(sys.argv[1])
    settings, keys = [], None
    code = collections.defaultdict(dict)  # (row, place index) -> setting -> nats
    for out in sys.argv[2:]:
        here = open(f"{out}/settings.tsv").read().split()
        seen, count = [], collections.Counter()
        for ln in open(f"{out}/codes.tsv"):
            w = ln.rstrip("\n").split("\t")
            r = int(w[0])
            i = count[r]
            count[r] += 1
            seen.append((r, w[1], w[2]))
            for s, v in zip(here, w[3:]):
                if s not in settings:
                    code[(r, i)][s] = int(v) * LN2_20
        if keys is not None and seen != keys:
            sys.exit(f"{out} holds other rows or places than {sys.argv[2]}")
        keys = seen
        settings += [s for s in here if s not in settings]
    past = sorted(k for k in code if k[1] > c)
    law = [code[k]["law"] for k in past]
    print(f"CONC_HEAD cut={c} places_past={len(past)} law_mean={sum(law) / len(law):.4f}")
    order = sorted(range(len(past)), key=lambda j: law[j])
    fifth = [0] * len(past)
    for rank, j in enumerate(order):
        fifth[j] = min(4, rank * 5 // len(past))
    for s in settings:
        if s == "law" or s.startswith("from:") or s.startswith("old:"):
            continue
        g = [code[k][s] - code[k]["law"] for k in past]
        line("CONC", s, g)
        tot = sum(g)
        cells = []
        for q in range(5):
            part = [g[j] for j in range(len(g)) if fifth[j] == q]
            lawq = [law[j] for j in range(len(g)) if fifth[j] == q]
            cells.append(f"{q + 1}:law={sum(lawq) / len(lawq):.3f},price={sum(part) / len(part):+.4f},share={sum(part) / tot:+.3f}")
        print(f"CONC_FIFTH setting={s} " + " ".join(cells))
    alone = f"cut:{c}:0"
    if alone in settings:
        g0 = [code[k][alone] - code[k]["law"] for k in past]
        cutoff = sorted(g0, reverse=True)[max(1, len(g0) // 10) - 1]
        dear = [j for j in range(len(g0)) if g0[j] >= cutoff]
        rest = [j for j in range(len(g0)) if g0[j] < cutoff]
        for s in settings:
            if s == "law" or s.startswith("from:") or s.startswith("old:"):
                continue
            g = [code[k][s] - code[k]["law"] for k in past]
            cells = []
            for name, idx in (("dear", dear), ("rest", rest)):
                tot0 = sum(g0[j] for j in idx)
                tot = sum(g[j] for j in idx)
                cells.append(f"{name}:places={len(idx)},alone={tot0:.1f},price={tot:.1f},back={1 - tot / tot0:+.3f}")
            lawdear = sum(law[j] for j in dear) / len(dear)
            print(f"CONC_DEAR setting={s} " + " ".join(cells) + f" law_at_dear={lawdear:.3f}")
    rng = random.Random(20261125)
    n = len(past)
    line("CONC_PLANT", "even", [1.0] * n)
    line("CONC_PLANT", "exponential", [rng.expovariate(1.0) for _ in range(n)])
    line("CONC_PLANT", "one-in-fifty", [50.0 if rng.random() < 0.02 else 0.0 for _ in range(n)])


main()
