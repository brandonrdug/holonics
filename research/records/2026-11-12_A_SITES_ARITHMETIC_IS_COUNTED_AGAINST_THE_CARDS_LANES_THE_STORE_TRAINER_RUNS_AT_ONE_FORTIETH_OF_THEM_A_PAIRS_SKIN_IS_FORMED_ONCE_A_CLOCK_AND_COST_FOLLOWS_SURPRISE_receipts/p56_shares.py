"""P56 item 1 (G128 a), a ruler on the bits ruler's whole histograms (FIELD_BITS_HIST): a met pair's share of its row's mass, on 2^-63, by its bit
length; the shares of met pairs at bit lengths 26, 31, 39, 47 and 55 or under (a share under 2^-37, 2^-32, 2^-24, 2^-16, 2^-8) and the median bit
length, by clock, pooled over the clocks, and for e by head and the receiver's kind. Numbers only. Argument: the read's log."""
import sys

hist = {}
for line in open(sys.argv[1]):
    if line.startswith("FIELD_BITS_HIST "):
        kv = dict(w.split("=", 1) for w in line.split()[1:])
        hist[(kv["array"], int(kv["clock"]))] = [int(c) for c in kv["counts"].split(",")]
CUTS = (26, 31, 39, 47, 55)


def summary(h):
    total = sum(h)
    acc, median = 0, 0
    for b, c in enumerate(h):
        acc += c
        if 2 * acc >= total:
            median = b
            break
    shares = [sum(h[: c + 1]) / total for c in CUTS]
    return total, shares, median


def report(label, h):
    total, shares, median = summary(h)
    cuts = " ".join(f"le{c}={s:.5f}" for c, s in zip(CUTS, shares))
    print(f"SHARES {label} pairs={total} zero={h[0]} {cuts} median_bits={median} median_share=2^{median - 63}")


for array in sorted({a for a, _ in hist}):
    clocks = sorted(k for a, k in hist if a == array)
    pooled = [0] * 65
    for k in clocks:
        report(f"array={array} clock={k}", hist[(array, k)])
        pooled = [x + y for x, y in zip(pooled, hist[(array, k)])]
    report(f"array={array} clock=pooled", pooled)
# e by the receiver's kind, pooled over the heads and the clocks
for kind in ("definite", "open"):
    pooled = [0] * 65
    for (a, k), h in hist.items():
        if a.startswith("e_share_h") and a.endswith(kind):
            pooled = [x + y for x, y in zip(pooled, h)]
    if sum(pooled):
        report(f"array=e_share_{kind} clock=pooled heads=pooled", pooled)
