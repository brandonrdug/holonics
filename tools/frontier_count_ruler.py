#!/usr/bin/env -S python3 -I
"""A plain yardstick for the frontier (the lead, November 18): a count of the k places before a place, fitted on the first TRAIN
octets of a slice's training documents and read on its held documents, Witten-Bell backing off from k places before to k - 1 down to
the slice's count of bytes. It is the frontier's own question (a place's code given what stands before it) asked of a count table,
as `cloze_count_ruler.py` asks the one-place receiver's. Beside each k it prints the entries the table holds through that k (its
distinct contexts with a symbol, every shorter context's included), so a reading of the machine can be set against the count of
entries a table needs to stand at the same code. A host instrument; a count table enters no law.

Held places are read from place SKIP of the held documents on, one in every STEP places, so each has at least SKIP places before it.

Usage: frontier_count_ruler.py STORE SLICE TRAIN_OCTETS HELD_PLACES KMAX [SKIP]"""
import math, sys

def main():
    store, name, train_n, held_n, kmax = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    skip = int(sys.argv[6]) if len(sys.argv) > 6 else 64
    train = open(f"{store}/DOCS_{name}.bin", "rb").read(train_n)
    held = open(f"{store}/HELD_{name}.bin", "rb").read()
    uni = [0] * 256
    for c in train:
        uni[c] += 1
    tot = sum(uni)
    seen = sum(1 for v in uni if v)
    counts = [dict() for _ in range(kmax + 1)]   # counts[k][ctx + bytes([c])] = n (k from 1; the count of bytes is `uni`)
    totals = [dict() for _ in range(kmax + 1)]   # totals[k][ctx] = [n, distinct]
    for k in range(1, kmax + 1):
        cn, tt = counts[k], totals[k]
        for i in range(k, len(train)):
            ctx = train[i - k:i]
            key = train[i - k:i + 1]
            v = cn.get(key, 0)
            cn[key] = v + 1
            t = tt.get(ctx)
            if t is None:
                tt[ctx] = [1, 1]
            else:
                t[0] += 1
                if v == 0:
                    t[1] += 1
    first = max(skip, kmax)
    step = max(1, (len(held) - first) // held_n)
    sums = [0.0] * (kmax + 1)
    n = 0
    for i in range(first, len(held), step):
        c = held[i]
        p = (uni[c] + seen / 256.0) / (tot + seen)       # the count of bytes, with a share left for bytes not met
        sums[0] -= math.log(p)
        for k in range(1, kmax + 1):
            t = totals[k].get(held[i - k:i])
            if t is not None:
                p = (counts[k].get(held[i - k:i + 1], 0) + t[1] * p) / (t[0] + t[1])
            sums[k] -= math.log(p)
        n += 1
    entries, through = [seen], [seen]
    for k in range(1, kmax + 1):
        entries.append(len(counts[k]))
        through.append(through[-1] + len(counts[k]))
    print(f"FRONTIER_COUNT slice={name} train_octets={len(train)} held_places={n} skip={first} count_of_bytes={sums[0] / n:.4f} "
          + " ".join(f"{k}_before={sums[k] / n:.4f}" for k in range(1, kmax + 1)), flush=True)
    print(f"FRONTIER_COUNT_ENTRIES slice={name} train_octets={len(train)} " + " ".join(f"through_{k}={through[k]}" for k in range(0, kmax + 1)), flush=True)

if __name__ == "__main__":
    main()
