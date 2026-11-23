#!/usr/bin/env -S python3 -I
"""The writer's plain yardstick (the lead, November 23; the cloze ruler of November 17 read one-sided): a count of the r places before
a place, fitted on the first TRAIN octets of a slice's training documents and read on its held documents. Witten-Bell backing off from
r places before to r - 1 down to the slice's count of bytes. The question the writer's regime asks (each place at its own frontier),
asked of a count table. A host instrument; a count table enters no law.

Usage: before_count_ruler.py STORE SLICE TRAIN_OCTETS HELD_PLACES RMAX [split]

With `split`, the code at RMAX places before is also given apart at a word's first letter (after a space or a line feed), inside a word
(after a letter) and at every other place, the partition the writer's own code is read by."""
import math, sys

def main():
    store, name, train_n, held_n, rmax = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    train = open(f"{store}/DOCS_{name}.bin", "rb").read(train_n)
    held = open(f"{store}/HELD_{name}.bin", "rb").read()
    uni = [0] * 256
    for c in train:
        uni[c] += 1
    tot = sum(uni)
    seen = sum(1 for v in uni if v)
    counts = [None] + [dict() for _ in range(rmax)]   # counts[r][ctx + bytes([c])] = n
    totals = [None] + [dict() for _ in range(rmax)]   # totals[r][ctx] = [n, distinct]
    for r in range(1, rmax + 1):
        cn, tt = counts[r], totals[r]
        for i in range(r, len(train) - r):
            ctx = train[i - r:i]
            key = ctx + train[i:i + 1]
            v = cn.get(key, 0)
            cn[key] = v + 1
            t = tt.get(ctx)
            if t is None:
                tt[ctx] = [1, 1]
            else:
                t[0] += 1
                if v == 0:
                    t[1] += 1
    step = max(1, (len(held) - 2 * rmax) // held_n)
    sums = [0.0] * (rmax + 1)
    n = 0
    split = len(sys.argv) > 6 and sys.argv[6] == 'split'
    parts = {'start': [0.0, 0], 'inside': [0.0, 0], 'other': [0.0, 0]}
    letter = lambda b: 65 <= b <= 90 or 97 <= b <= 122
    for i in range(rmax, len(held) - rmax, step):
        c = held[i]
        p = (uni[c] + seen / 256.0) / (tot + seen)       # the count of bytes, with a share left for bytes not met
        sums[0] -= math.log(p)
        for r in range(1, rmax + 1):
            ctx = held[i - r:i]
            t = totals[r].get(ctx)
            if t is not None:
                p = (counts[r].get(ctx + held[i:i + 1], 0) + t[1] * p) / (t[0] + t[1])
            sums[r] -= math.log(p)
        if split:
            prev = held[i - 1]
            kind = 'start' if prev in (32, 10) and letter(c) else 'inside' if letter(prev) and letter(c) else 'other'
            parts[kind][0] -= math.log(p)
            parts[kind][1] += 1
        n += 1
    print(f"BEFORE_COUNT slice={name} train_octets={len(train)} held_places={n} count_of_bytes={sums[0] / n:.4f} " + " ".join(f"{r}_before={sums[r] / n:.4f}" for r in range(1, rmax + 1)) + ("" if not split else " | at " + str(rmax) + " before: " + " ".join(f"{k}={v[0] / max(1, v[1]):.3f}({v[1]})" for k, v in parts.items())), flush=True)

if __name__ == "__main__":
    main()
