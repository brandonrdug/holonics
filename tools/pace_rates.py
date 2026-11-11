#!/usr/bin/env python3 -I
"""pace_rates.py STATE CODEC: the paced heads' clock rates by class, read on the host from a saved learner state (no card, no learning; arithmetic on the
state's material line; theory's G33, November 11).

A paced head's tick rate at a site of class u is `1 + c_h[u]` (Field::paces_with: `k = one + rate`, the pace family's entry `c_h[u]` on the material's grain
2^-24; a head is paced where `h % frames >= still`, indexed in order). For each paced head: the mean of `1 + c_h[u]` by kind of class (letter, digit, space,
newline, other whitespace and control, punctuation and symbol, non-ASCII, the void), the rate of newline and of space alone, and the extremes. The class
`u` of a byte is its place in CODEC's second line (the codec's used units, bytes under founded-units-v1 0, in order); the class after them is the void, and
the pace family's last class (the alphabet's `a + 1`-th) is the extra row. Numbers only (rates on 2^-24
printed as decimals, a reading in a report).
"""
import sys

import numpy as np


def main():
    state_path, codec_path = sys.argv[1:3]
    lines = open(state_path).read().split("\n")
    words = lines[1].split(" ")
    names = ["alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes"]
    d = {k: int(w) for k, w in zip(names, words[1:11])}
    theta = np.array([int(x) for x in lines[2].split(" ")], dtype=np.int64)
    a, dw, heads, modes, still, f, frames = d["alphabet"], d["width"], d["heads"], d["modes"], d["still"], d["contacts"], d["frames"]
    m2 = 2 * heads * modes
    paced_heads = [h for h in range(heads) if h % frames >= still]
    tm = len(paced_heads) * modes
    # The families before the pace family, in Field's layout order (state_travel.py's).
    before = (a + 1) * dw * 3 + (m2 * dw + m2) * 2 + dw * m2 + dw + (f * dw + f) * 2 + dw * f + dw + dw * dw + a + (a + 1) * 2 * tm * 2 + 2 * heads + m2 * dw + m2
    width = a + 1
    codec = open(codec_path).read().split("\n")
    bytes_of = [int(x) for x in codec[1].split(" ") if x]
    assert len(bytes_of) == a - 1, (len(bytes_of), a)

    def kind(u):
        if u == len(bytes_of):
            return "void"
        if u > len(bytes_of):
            return "extra"
        b = bytes_of[u]
        if 65 <= b <= 90 or 97 <= b <= 122:
            return "letter"
        if 48 <= b <= 57:
            return "digit"
        if b == 32:
            return "space"
        if b == 10:
            return "newline"
        if b in (9, 13) or b < 32:
            return "other_whitespace_control"
        if b < 128:
            return "punctuation_symbol"
        return "non_ascii"

    kinds = ["letter", "digit", "space", "newline", "other_whitespace_control", "punctuation_symbol", "non_ascii", "void", "extra"]
    print(f"# state {state_path}; paced heads {paced_heads} (pace family at {before}, {width} classes a head); rates 1 + c_h[u] on 2^-24")
    print("head\tkind\tclasses\tmean_rate\tmin_rate\tmax_rate")
    for p, h in enumerate(paced_heads):
        c = theta[before + p * width: before + (p + 1) * width].astype(np.float64) / (1 << 24)
        rate = 1.0 + c
        for k in kinds:
            idx = [u for u in range(width) if kind(u) == k]
            if idx:
                r = rate[idx]
                print(f"{h}\t{k}\t{len(idx)}\t{r.mean():.6f}\t{r.min():.6f}\t{r.max():.6f}")
        for name, byte in (("newline", 10), ("space", 32)):
            u = bytes_of.index(byte) if byte in bytes_of else None
            print(f"{h}\t{name}_alone\t1\t{rate[u]:.6f}\t-\t-" if u is not None else f"{h}\t{name}_alone\t0\t-\t-\t-")
        print(f"{h}\tall\t{width}\t{rate.mean():.6f}\t{rate.min():.6f}\t{rate.max():.6f}")


if __name__ == "__main__":
    main()
