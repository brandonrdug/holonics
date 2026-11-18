#!/usr/bin/env -S python3 -I
"""A ruler: where the frontier's excess over a count of the places before stands, by the arriving place's news (the lead, November 18;
the store line's form of the reading of November 17, atlas `deposition.excess-inside-units`).

Each held stretch of a `read-cavity` output is rebuilt as octets from its one-place rows (`P` rows of `cavity.tsv`, a class an octet by
the codec). A place's news is its code under a Witten-Bell count of at most KMAX places before it within its stretch, fitted on the
first TRAIN octets of the slice's training documents: a ruler's stand-in for a reader's own surprise. The frontier rows of KIND (`F`
the law's, `K` a known stream's, `S` two streams') of each named read are set beside the count's at the same places, by the place's
news under the count: the interior of a unit (little news) against its landmark (much). Beside them, at the same places, the count's
code at every k from 0 (the count of octets) to KMAX, so a read's code in a bin can be set against the order of count that stands
level with it there. Nats a place; codes and counts only.

A cavity's codes are on 2^-20 bits. Outside the machine; a count table enters no law.

Usage: frontier_excess_ruler.py STORE CODEC TRAIN_OCTETS KMAX KIND NAME=DIR [NAME=DIR ...]"""
import math, sys

G = float(1 << 20)
LN2 = math.log(2)
EDGES = [0.25, 1.0, 2.0, 4.0]
NAMES = ["under 0.25", "0.25 to 1", "1 to 2", "2 to 4", "over 4"]

def fit(train, kmax):
    uni = [0] * 256
    for c in train:
        uni[c] += 1
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
    return uni, counts, totals

def news(model, seq, i, kmax):
    """The place's code under the count of at most k places before, for every k from 0 to kmax."""
    uni, counts, totals = model
    tot, seen = sum(uni), sum(1 for v in uni if v)
    p = (uni[seq[i]] + seen / 256.0) / (tot + seen)
    out = [-math.log(p)]
    for k in range(1, kmax + 1):
        t = totals[k].get(seq[i - k:i]) if k <= i else None
        if t is not None:
            p = (counts[k].get(seq[i - k:i + 1], 0) + t[1] * p) / (t[0] + t[1])
        out.append(-math.log(p))
    return out

def main():
    store, codec, train_n, kmax, kind = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    reads = [a.split("=", 1) for a in sys.argv[6:]]
    head, used = open(codec).read().split("\n")[:2]
    void = int(head.split(" ")[2])
    used = [int(w) for w in used.split(" ")]
    octet = lambda c: None if c == void else (used[c] if c < void else used[c - 1])
    # The stretches' octets, from the first read's one-place rows (every read holds the same held stretches).
    places = {}
    for line in open(reads[0][1] + "/cavity.tsv"):
        f = line.rstrip("\n").split("\t")
        if f[0] == "P":
            places.setdefault((f[1], int(f[2])), {})[int(f[3])] = int(f[4])
    codes = []
    for _, d in reads:
        rows = {}
        for line in open(d + "/frontier.tsv"):
            f = line.rstrip("\n").split("\t")
            if f[0] == kind:
                rows[(f[1], int(f[2]), int(f[3]))] = int(f[5]) / G * LN2
        codes.append(rows)
    slices = sorted({k[0] for k in places})
    # A bin: its places, the count's code at each k from 0 to kmax, then each read's code.
    total = [[0] + [0.0] * (kmax + 1 + len(reads)) for _ in NAMES]
    for sl in slices:
        model = fit(open(f"{store}/DOCS_{sl}.bin", "rb").read(train_n), kmax)
        bins = [[0] + [0.0] * (kmax + 1 + len(reads)) for _ in NAMES]
        for (s, stretch), st in places.items():
            if s != sl:
                continue
            n = max(st) + 1
            seq = [octet(st.get(t, void)) for t in range(n)]
            # (a void octet stands in a context as an octet the fit never met)
            raw = bytes(255 if b is None else b for b in seq)
            for t in range(1, n):
                key = (sl, stretch, t)
                if seq[t] is None or any(key not in rows for rows in codes):
                    continue
                by_k = news(model, raw, t, kmax)
                b = sum(1 for e in EDGES if by_k[kmax] >= e)
                bins[b][0] += 1
                for k, c in enumerate(by_k):
                    bins[b][1 + k] += c
                for r, rows in enumerate(codes):
                    bins[b][2 + kmax + r] += rows[key]
        count = sum(b[0] for b in bins)
        if count == 0:
            continue
        for b, tb in zip(bins, total):
            for i, v in enumerate(b):
                tb[i] += v
        report(sl, bins, count, reads, kind, train_n, kmax)
    report("all", total, sum(b[0] for b in total), reads, kind, train_n, kmax)

def report(sl, bins, count, reads, kind, train_n, kmax):
    at = 1 + kmax
    whole = [sum(b[i] for b in bins) / count for i in range(1, 2 + kmax + len(reads))]
    print(f"EXCESS slice={sl} kind={kind} places={count} train_octets={train_n} k={kmax} count={whole[kmax]:.4f} " + " ".join(f"{n}={w:.4f}" for (n, _), w in zip(reads, whole[kmax + 1:]))
          + " counts_by_k: " + " ".join(f"{k}={whole[k]:.3f}" for k in range(kmax + 1)), flush=True)
    for name, b in zip(NAMES, bins):
        if b[0] == 0:
            continue
        print(f"EXCESS slice={sl} news={name!r} share={b[0] / count:.3f} count={b[at] / b[0]:.3f} " + " ".join(f"{n}={b[at + 1 + r] / b[0]:.3f}" for r, (n, _) in enumerate(reads))
              + " excess_of_all_places: " + " ".join(f"{n}={(b[at + 1 + r] - b[at]) / count:+.4f}" for r, (n, _) in enumerate(reads))
              + " counts_by_k: " + " ".join(f"{k}={b[1 + k] / b[0]:.3f}" for k in range(kmax + 1)), flush=True)

if __name__ == "__main__":
    main()
