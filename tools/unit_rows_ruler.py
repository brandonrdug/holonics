#!/usr/bin/env -S python3 -I
"""A ruler: how many rows closing a unit needs (the lead, November 18; the record of the two streams §12 and §13).

A count of the places before a place codes the interior of a unit sharply, and holds millions of entries to do it. This reads how
that sharpness is spread over contexts: a count of at most BASE places before is kept whole (what a reader already binds), and of
the longer contexts (BASE + 1 to KMAX places before) only the N met most often in the fitted text keep their rows, at each length;
a place whose longer context holds no row backs off to the longest one that does. For each N the held code is read over all places
and at the places of little news (under a quarter of a nat, and a quarter to one, under the whole count at KMAX): the interior of a
unit. So a row here is a context with the symbols met after it, and the reading is how the code falls as rows are added from the
most met. CAUTION (November 18): the bins of little news are by the whole count's code of the symbol that arrived, which selects
the places where the count gave the arriving symbol most of its mass; those columns lean the count's way and are no sizes. The column over all places is not
selected, and is the one to quote.

Fitted on the first TRAIN octets of a slice's training documents (Witten-Bell backing off), read on about HELD_PLACES of its held
octets with SKIP or more places before each. A host instrument: a count table enters no law, and a row a context is the form the
stores' law calls a cache; the reading sizes what a store that shares rows would have to hold.

Usage: unit_rows_ruler.py STORE SLICE TRAIN_OCTETS HELD_PLACES BASE KMAX N[,N...] [SKIP]"""
import math, sys

def main():
    store, name, train_n, held_n, base, kmax = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    budgets = [int(w) for w in sys.argv[7].split(",")]
    skip = int(sys.argv[8]) if len(sys.argv) > 8 else 64
    train = open(f"{store}/DOCS_{name}.bin", "rb").read(train_n)
    held = open(f"{store}/HELD_{name}.bin", "rb").read()
    uni = [0] * 256
    for c in train:
        uni[c] += 1
    tot, seen = sum(uni), sum(1 for v in uni if v)
    counts = [dict() for _ in range(kmax + 1)]
    totals = [dict() for _ in range(kmax + 1)]
    for k in range(1, kmax + 1):
        cn, tt = counts[k], totals[k]
        for i in range(k, len(train)):
            ctx, key = train[i - k:i], train[i - k:i + 1]
            v = cn.get(key, 0)
            cn[key] = v + 1
            t = tt.get(ctx)
            if t is None:
                tt[ctx] = [1, 1]
            else:
                t[0] += 1
                if v == 0:
                    t[1] += 1
    # Each longer length's contexts, the most met first: a context's rank is its row's place in the budget.
    rank = [dict() for _ in range(kmax + 1)]
    for k in range(base + 1, kmax + 1):
        for r, (ctx, _) in enumerate(sorted(totals[k].items(), key=lambda kv: -kv[1][0])):
            rank[k][ctx] = r
    first = max(skip, kmax)
    step = max(1, (len(held) - first) // held_n)
    edges = [0.25, 1.0]
    # sums[n][bin] over budgets (the last index the whole count), bins: under 0.25, 0.25 to 1, the rest, all
    sums = [[0.0] * 4 for _ in range(len(budgets) + 2)]
    places = [0] * 4
    for i in range(first, len(held), step):
        c = held[i]
        p = (uni[c] + seen / 256.0) / (tot + seen)
        ps = [p] * (len(budgets) + 2)       # budgets..., the base alone, the whole count
        for k in range(1, kmax + 1):
            ctx = held[i - k:i]
            t = totals[k].get(ctx)
            if t is None:
                continue
            got = counts[k].get(held[i - k:i + 1], 0)
            step_p = lambda prev: (got + t[1] * prev) / (t[0] + t[1])
            ps[-1] = step_p(ps[-1])
            if k <= base:
                for n in range(len(budgets) + 1):
                    ps[n] = step_p(ps[n])
            else:
                r = rank[k][ctx]
                for n, budget in enumerate(budgets):
                    if r < budget:
                        ps[n] = step_p(ps[n])
        whole = -math.log(ps[-1])
        b = sum(1 for e in edges if whole >= e)
        for which in (b, 3):
            places[which] += 1
            for n in range(len(budgets) + 2):
                sums[n][which] -= math.log(ps[n])
    names = ["under_0.25", "0.25_to_1", "over_1", "all"]
    held_rows = {k: len(totals[k]) for k in range(base + 1, kmax + 1)}
    print(f"UNIT_ROWS slice={name} train_octets={len(train)} held_places={places[3]} base={base} kmax={kmax} contexts_held: " + " ".join(f"{k}={v}" for k, v in held_rows.items())
          + " shares: " + " ".join(f"{names[b]}={places[b] / places[3]:.3f}" for b in range(3)), flush=True)
    labels = [f"rows={n}" for n in budgets] + [f"base_{base}_alone", "whole_count"]
    order = [len(budgets)] + list(range(len(budgets))) + [len(budgets) + 1]
    for n in order:
        print(f"UNIT_ROWS slice={name} {labels[n]} " + " ".join(f"{names[b]}={sums[n][b] / max(places[b], 1):.4f}" for b in range(4)), flush=True)

if __name__ == "__main__":
    main()
