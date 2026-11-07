#!/usr/bin/env python3
"""settle135 (theory, November 7, 04:20): the 55 squares' central readings at a letter's weight over 16, 32 and 64 on the
card, beside energy133's host read at /16, /8 and /4. Each reading (bits raw, +eps less -eps) is scaled by 16/step so a
linear reading stays put; per square the linear end, the other end, and their ratio (other/linear) at each step. Sharp G:
the bent end approaches the linear within 20% by /64; a term: they stay apart while the linear end keeps halving."""
import csv, sys
card = {(r["problem"], r["band"], r["i"], r["j"]): r for r in csv.DictReader(open(sys.argv[1]), delimiter="\t")}
host = {(r["problem"], r["band"], r["i"], r["j"]): r for r in csv.DictReader(open(sys.argv[2]), delimiter="\t")}
chosen = list(csv.DictReader(open(sys.argv[3]), delimiter="\t"))
B = 1 << 20
equal = sum(1 for k in card if k in host and card[k]["c16_i"] == host[k]["c16_i"] and card[k]["c16_j"] == host[k]["c16_j"])
print(f"# the card's /16 against energy133's host /16: {equal}/{len(card)} squares bit-equal")
print("problem\tband\ti\tj\tlinear\t" + "\t".join(f"{s}: linear other ratio" for s in ("/4h", "/8h", "/16", "/32", "/64")))
close, apart, rest = 0, 0, 0
for c in chosen:
    k = (c["problem"], c["band"], c["i"], c["j"])
    if k not in card:
        print("\t".join(k) + "\tmissing")
        continue
    lin, oth = (c["linear_end"], "j" if c["linear_end"] == "i" else "i")
    cells = []
    ratios = {}
    for name, src, col, scale in (("/4h", host, "c4", 0.25), ("/8h", host, "c8", 0.5), ("/16", card, "c16", 1), ("/32", card, "c32", 2), ("/64", card, "c64", 4)):
        a = int(src[k][f"{col}_{lin}"]) / B * scale
        b = int(src[k][f"{col}_{oth}"]) / B * scale
        r = b / a if a else float("nan")
        ratios[name] = r
        cells.append(f"{a:.2f} {b:.2f} {r:.3f}")
    r64 = ratios["/64"]
    if abs(r64 - 1) <= 0.2:
        close += 1
    elif abs(r64 - 1) >= abs(ratios["/16"] - 1) * 0.8:
        apart += 1
    else:
        rest += 1
    print("\t".join(k) + f"\t{lin}\t" + "\t".join(cells))
print(f"# within 20% at /64: {close}; still apart (no closer than 80% of the /16 gap): {apart}; closing but not within 20%: {rest}")
