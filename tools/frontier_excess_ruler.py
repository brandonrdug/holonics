#!/usr/bin/env -S python3 -I
"""A ruler: where the frontier's excess over a count of the places before stands, by how open the place is under the count (the lead,
November 18; the store line's form of the reading of November 17, atlas `deposition.excess-inside-units`).

Each held stretch of a `read-cavity` output is rebuilt as octets from its one-place rows (`P` rows of `cavity.tsv`, a class an octet by
the codec). A Witten-Bell count of at most KMAX places before a place within its stretch, fitted on the first TRAIN octets of the
slice's training documents, gives each place a face over the octets. A place's bin is that face's entropy, the news the count
expects there: a property of what stands before the place alone. (The first form of this ruler binned a place by the count's code of
the symbol that arrived. That selects, in the bins of little news, the places where the count gave the arriving symbol most of its mass, and in the bins of much
news the places where it gave it little, so each bin's comparison leaned the count's way or the machine's by its own selection; the
caution is the Codex thread's letter of November 18. The codes over all places were never touched by it.) The frontier rows of
KIND (`F` the law's, `K` a known stream's, `S` two streams') of each named read are set beside the count's code at the same places,
bin by bin, with the count's code at every k from 0 (the count of octets) to KMAX, so a read's code in a bin can be set against the
order of count that stands level with it there. Beside each code stands the mean mass the face gives the symbol that arrived
(`draw_agrees`): the share of draws from the face that would write the passage's own symbol at the place, which is what a write of
a word turns on (a word is written whole only if the draw agrees at each of its places), where a code weighs a place by its
logarithm. Nats a place; codes, masses and counts only.

A cavity's codes are on 2^-20 bits. Outside the machine; a count table enters no law.

Usage: frontier_excess_ruler.py STORE CODEC TRAIN_OCTETS KMAX KIND NAME=DIR [NAME=DIR ...]"""
import math, sys

G = float(1 << 20)
LN2 = math.log(2)
EDGES = [0.25, 0.5, 1.0, 2.0]
NAMES = ["under 0.25", "0.25 to 0.5", "0.5 to 1", "1 to 2", "over 2"]

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
    """The place's code under the count of at most k places before, for every k from 0 to kmax, and the entropy of the count's face
    at kmax (the news the count expects at the place, whatever arrives)."""
    uni, counts, totals = model
    tot, seen = sum(uni), sum(1 for v in uni if v)
    face = [(u + seen / 256.0) / (tot + seen) for u in uni]
    c = seq[i]
    out = [-math.log(face[c])]
    for k in range(1, kmax + 1):
        t = totals[k].get(seq[i - k:i]) if k <= i else None
        if t is not None:
            ctx, cn, scale = seq[i - k:i], counts[k], 1.0 / (t[0] + t[1])
            face = [(cn.get(ctx + bytes((a,)), 0) + t[1] * face[a]) * scale for a in range(256)]
        out.append(-math.log(face[c]))
    return out, -sum(q * math.log(q) for q in face if q > 0)

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
    total_mass = [[0.0] * (1 + len(reads)) for _ in NAMES]
    for sl in slices:
        model = fit(open(f"{store}/DOCS_{sl}.bin", "rb").read(train_n), kmax)
        bins = [[0] + [0.0] * (kmax + 1 + len(reads)) for _ in NAMES]
        mass = [[0.0] * (1 + len(reads)) for _ in NAMES]
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
                by_k, expected = news(model, raw, t, kmax)
                b = sum(1 for e in EDGES if expected >= e)
                bins[b][0] += 1
                for k, c in enumerate(by_k):
                    bins[b][1 + k] += c
                mass[b][0] += math.exp(-by_k[kmax])
                for r, rows in enumerate(codes):
                    bins[b][2 + kmax + r] += rows[key]
                    mass[b][1 + r] += math.exp(-rows[key])
        count = sum(b[0] for b in bins)
        if count == 0:
            continue
        for b, tb in zip(bins, total):
            for i, v in enumerate(b):
                tb[i] += v
        for m, tm in zip(mass, total_mass):
            for i, v in enumerate(m):
                tm[i] += v
        report(sl, bins, mass, count, reads, kind, train_n, kmax)
    report("all", total, total_mass, sum(b[0] for b in total), reads, kind, train_n, kmax)

def report(sl, bins, mass, count, reads, kind, train_n, kmax):
    at = 1 + kmax
    whole = [sum(b[i] for b in bins) / count for i in range(1, 2 + kmax + len(reads))]
    agrees = [sum(m[i] for m in mass) / count for i in range(1 + len(reads))]
    print(f"EXCESS slice={sl} kind={kind} places={count} train_octets={train_n} k={kmax} count={whole[kmax]:.4f} " + " ".join(f"{n}={w:.4f}" for (n, _), w in zip(reads, whole[kmax + 1:]))
          + f" draw_agrees: count={agrees[0]:.3f} " + " ".join(f"{n}={a:.3f}" for (n, _), a in zip(reads, agrees[1:]))
          + " counts_by_k: " + " ".join(f"{k}={whole[k]:.3f}" for k in range(kmax + 1)), flush=True)
    for (name, b), m in zip(zip(NAMES, bins), mass):
        if b[0] == 0:
            continue
        print(f"EXCESS slice={sl} expected_news={name!r} draw_agrees: count={m[0] / b[0]:.3f} " + " ".join(f"{n}={m[1 + r] / b[0]:.3f}" for r, (n, _) in enumerate(reads)), flush=True)
        print(f"EXCESS slice={sl} expected_news={name!r} share={b[0] / count:.3f} count={b[at] / b[0]:.3f} " + " ".join(f"{n}={b[at + 1 + r] / b[0]:.3f}" for r, (n, _) in enumerate(reads))
              + " excess_of_all_places: " + " ".join(f"{n}={(b[at + 1 + r] - b[at]) / count:+.4f}" for r, (n, _) in enumerate(reads))
              + " counts_by_k: " + " ".join(f"{k}={b[1 + k] / b[0]:.3f}" for k in range(kmax + 1)), flush=True)

if __name__ == "__main__":
    main()
