#!/usr/bin/env -S python3 -I
"""A ruler: what rows shared on coprime rings hold of a unit's interior (the lead, November 18; the record of the two streams §13
and §14).

`unit_rows_ruler.py` sizes the rows closing a unit needs with a row a context, the form the stores' law calls a cache. This reads the
form the repository holds for the store instead (the symbol's record of November 12, §8.1; the located transport of October 5): a
context of three to five places before a place is a word in radix 256, read as a residue on each of J coprime rings, and each ring
holds one row a residue, shared by every context that reaches it. A row holds the symbols met after the contexts at its residue. A
context's reading is what every one of its rings agrees on: a symbol's count is the least its J rows hold (so a row shared with
other contexts cannot raise it), the context's total is the sum of those least counts over the symbols and its count of distinct
symbols the symbols whose least count is not zero. The count of two places before is kept whole, as in `unit_rows_ruler.py`, and
the longer lengths back off Witten-Bell onto it.

For each budget of ROWS a length (the rings' periods are the J primes just under ROWS / J), the held code is read over all places and
at the places of little news under the whole count, so the two rulers stand side by side at equal rows.

Fitted on the first TRAIN octets of a slice's training documents, read on about HELD_PLACES of its held octets. A host instrument:
its address is a fixed residue of the octets, a ruler's and never the machine's (the machine locates a symbol's key); a count table
enters no law.

Usage: ring_rows_ruler.py STORE SLICE TRAIN_OCTETS HELD_PLACES KMAX J ROWS[,ROWS...] [SKIP]"""
import math, sys

BASE = 2

def primes_under(n, count):
    out, c = [], n
    while len(out) < count and c > 2:
        c -= 1
        if all(c % p for p in range(2, int(c ** 0.5) + 1)):
            out.append(c)
    return out

def main():
    store, name, train_n, held_n, kmax, rings = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    budgets = [int(w) for w in sys.argv[7].split(",")]
    skip = int(sys.argv[8]) if len(sys.argv) > 8 else 64
    train = open(f"{store}/DOCS_{name}.bin", "rb").read(train_n)
    held = open(f"{store}/HELD_{name}.bin", "rb").read()
    uni = [0] * 256
    for c in train:
        uni[c] += 1
    tot, seen = sum(uni), sum(1 for v in uni if v)
    # The whole count: every length to kmax (the base's lengths are read from it, and it names the places of little news).
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
    # The rings' rows: for a budget, a length and a ring, the symbols met at each residue with their counts.
    periods = [primes_under(max(b // rings, 8), rings) for b in budgets]
    rows = [[[dict() for _ in range(rings)] for _ in range(kmax + 1)] for _ in budgets]
    for k in range(BASE + 1, kmax + 1):
        for key, n_key in counts[k].items():
            word, c = int.from_bytes(key[:-1], "big"), key[-1]
            for b in range(len(budgets)):
                for j, m in enumerate(periods[b]):
                    row = rows[b][k][j].setdefault(word % m, {})
                    row[c] = row.get(c, 0) + n_key
    first = max(skip, kmax)
    step = max(1, (len(held) - first) // held_n)
    edges = [0.25, 1.0]
    sums = [[0.0] * 4 for _ in range(len(budgets) + 2)]
    places = [0] * 4
    for i in range(first, len(held), step):
        c = held[i]
        p = (uni[c] + seen / 256.0) / (tot + seen)
        ps = [p] * (len(budgets) + 2)       # budgets..., the base alone, the whole count
        for k in range(1, kmax + 1):
            ctx = held[i - k:i]
            t = totals[k].get(ctx)
            if t is not None:
                got = counts[k].get(held[i - k:i + 1], 0)
                ps[-1] = (got + t[1] * ps[-1]) / (t[0] + t[1])
                if k <= BASE:
                    for n in range(len(budgets) + 1):
                        ps[n] = (got + t[1] * ps[n]) / (t[0] + t[1])
            if k <= BASE:
                continue
            word = int.from_bytes(ctx, "big")
            for b in range(len(budgets)):
                met = [rows[b][k][j].get(word % m) for j, m in enumerate(periods[b])]
                if any(row is None for row in met):
                    continue
                small = min(met, key=len)
                n_ctx, distinct, got = 0, 0, 0
                for sym, v in small.items():
                    least = min(row.get(sym, 0) for row in met)
                    if least > 0:
                        n_ctx += least
                        distinct += 1
                        if sym == c:
                            got = least
                if n_ctx > 0:
                    ps[b] = (got + distinct * ps[b]) / (n_ctx + distinct)
        whole = -math.log(ps[-1])
        bin_ = sum(1 for e in edges if whole >= e)
        for which in (bin_, 3):
            places[which] += 1
            for n in range(len(budgets) + 2):
                sums[n][which] -= math.log(ps[n])
    names = ["under_0.25", "0.25_to_1", "over_1", "all"]
    print(f"RING_ROWS slice={name} train_octets={len(train)} held_places={places[3]} base={BASE} kmax={kmax} rings={rings} shares: " + " ".join(f"{names[b]}={places[b] / places[3]:.3f}" for b in range(3)), flush=True)
    labels = [f"rows={n} periods={'x'.join(map(str, periods[b]))}" for b, n in enumerate(budgets)] + [f"base_{BASE}_alone", "whole_count"]
    order = [len(budgets)] + list(range(len(budgets))) + [len(budgets) + 1]
    for n in order:
        print(f"RING_ROWS slice={name} {labels[n]} " + " ".join(f"{names[b]}={sums[n][b] / max(places[b], 1):.4f}" for b in range(4)), flush=True)

if __name__ == "__main__":
    main()
