"""Phase 7 -- the same reading, in exact ratios. No float, no percentage.

Brandon, 2026-08-13: "stop using floats and percentages ... Floats and percentages disregard the
real expanded series that determine what the value of a float you compute in any given instant
is ... this is cancellation and it is why the machine is computationally efficient."

THE_HOLONIC_DERIVATIONS section 0 types a Ratio as "carried as a pair (num, den), NEVER DIVIDED".
Phases 1-6 divided everywhere and reported decimals. This retakes the load-bearing measurement
with the ratio kept whole.

WHY IT IS EXACT, AND WHERE THE CANCELLATION IS. A bf16 datum is exactly m * 2^e with m, e
integers. Scale a vector by 2^-min(e) and every component is an integer, so a bracket <a|b> is an
exact integer times a power of two. Then

    cos^2(a,b) = <a|b>^2 / (<a|a> <b|b>)

and the powers of two CANCEL IDENTICALLY: the numerator carries 2^(2*(ea+eb)) and the
denominator 2^(2ea) * 2^(2eb). What remains is a pure integer ratio. Nothing is approximated and
nothing is evaluated.

cos^2 rather than cos because a cosine is irrational in general while its square is not. The
squared face is the lawful exact carrier -- and it is the quotient by the sign, which is the
half turn the magnitude already discarded.

ORDERING WITHOUT EVALUATING. Two ratios compare by cross-multiplication: p/q vs r/s is p*s vs
r*q, an integer comparison. So the population can be sorted, ranked and medianed without a single
division. That is the point: the series is retained and later composition can still cancel.
"""
import json
import struct
import sys
from math import gcd

from read_map import Map


def bf16_ints(mm, base, off, n):
    """A run of bf16 as exact (mantissa, exponent) integer pairs."""
    raw = mm[base + off : base + off + n * 2]
    out = []
    for i in range(n):
        w = raw[2 * i] | (raw[2 * i + 1] << 8)
        s, E, f = (w >> 15) & 1, (w >> 7) & 0xFF, w & 0x7F
        if E == 0xFF:
            raise ValueError("inf/nan in weight material")
        m, e = (f, -133) if E == 0 else (128 + f, E - 134)
        out.append((-m if s else m, e))
    return out


def to_integer_vector(pairs):
    """Common denominator: scale by 2^-min(e) so every component is an integer.
    Returns (ints, shift) with true value = ints * 2^shift."""
    es = [e for m, e in pairs if m != 0]
    if not es:
        return [0] * len(pairs), 0
    lo = min(es)
    return [m << (e - lo) if m != 0 else 0 for m, e in pairs], lo


def bracket(a, b):
    """<a|b> as (integer, power_of_two). Exact."""
    ia, sa = a
    ib, sb = b
    return sum(x * y for x, y in zip(ia, ib)), sa + sb


def cos2(a, b):
    """cos^2 as a REDUCED (num, den) integer pair. The powers of two cancel identically."""
    nab, _ = bracket(a, b)
    naa, _ = bracket(a, a)
    nbb, _ = bracket(b, b)
    num, den = nab * nab, naa * nbb
    if den == 0:
        return (0, 1)
    g = gcd(num, den)
    return (num // g, den // g)


def cmp_ratio(p, q):
    """Order two ratios by cross-multiplication. No division ever occurs."""
    return (p[0] * q[1] > q[0] * p[1]) - (p[0] * q[1] < q[0] * p[1])


def median_ratio(rs):
    s = sorted(rs, key=_Key)
    return s[len(s) // 2]


class _Key:
    __slots__ = ("r",)

    def __init__(self, r):
        self.r = r

    def __lt__(self, o):
        return cmp_ratio(self.r, o.r) < 0


def approx(r, places=6):
    """ONLY for the reader's eye, and marked as such. The pair above is the value."""
    n, d = r
    return f"{n}/{d}" + (f"  [~{n/d:.{places}f}]" if d else "")


SP = "▁"
FAMILIES = {
    "two":  ["two", SP + "two", SP + "Two", SP + "deux", "2"],
    "four": ["four", SP + "four", SP + "Four", SP + "quatre", "4"],
    "add":  ["add", SP + "add", SP + "Add", SP + "plus", "+"],
    "king": ["king", SP + "king", SP + "King", SP + "roi"],
    "cat":  ["cat", SP + "cat", SP + "Cat", SP + "chat"],
    "red":  ["red", SP + "red", SP + "Red", SP + "rouge"],
}


def main():
    m = Map()
    vocab = json.load(open("/home/b/models/gemma-4-E4B-it/tokenizer.json"))["model"]["vocab"]
    e = m.header["model.language_model.embed_tokens.weight"]
    a0, _ = e["data_offsets"]
    V, D = e["shape"]

    fam, names, vecs = [], [], []
    for f, faces in FAMILIES.items():
        for s in faces:
            if s in vocab:
                t = vocab[s]
                vecs.append(to_integer_vector(bf16_ints(m.mm, m.base, a0 + t * D * 2, D)))
                fam.append(f)
                names.append(s)
    n = len(vecs)
    print(f"{n} faces over {len(set(fam))} holons, read as exact dyadic integer vectors\n",
          file=sys.stderr)

    within, between = [], []
    for i in range(n):
        for j in range(i + 1, n):
            r = cos2(vecs[i], vecs[j])
            (within if fam[i] == fam[j] else between).append(r)

    print("=== THE FACE, AS AN EXACT RATIO -- cos^2 = <a|b>^2 / (<a|a><b|b>) ===")
    print("    (num, den) reduced. The bracketed decimal is for the eye only; the pair is the value.\n")
    mw, mb = median_ratio(within), median_ratio(between)
    print(f"  within-holon  median cos^2 : {approx(mw)}")
    print(f"                   population : {len(within)} pairs")
    print(f"  between-holon median cos^2 : {approx(mb)}")
    print(f"                   population : {len(between)} pairs")
    print(f"\n  ordering by cross-multiplication (no division): within {'>' if cmp_ratio(mw, mb) > 0 else '<='} between")

    # the separation as an exact ratio of ratios, still never divided
    sep = (mw[0] * mb[1] - mb[0] * mw[1], mw[1] * mb[1])
    g = gcd(abs(sep[0]), sep[1]) or 1
    sep = (sep[0] // g, sep[1] // g)
    print(f"  separation (within - between) as one pair: {approx(sep)}")

    # a Winding, which is a COUNT and never a percentage
    k = sum(1 for r in within if cmp_ratio(r, mb) > 0)
    print(f"\n=== THE WINDING -- a count, not a percentage ===")
    print(f"  within-pairs exceeding the between-median: {k} of {len(within)}")
    print(f"  carried as a ratio pair: ({k}, {len(within)})")

    print("\n=== THE CANCELLATION, EXHIBITED ===")
    a, b = vecs[0], vecs[1]
    nab, sab = bracket(a, b)
    naa, saa = bracket(a, a)
    nbb, sbb = bracket(b, b)
    print(f"  <a|b> = {nab} * 2^{sab}")
    print(f"  <a|a> = {naa} * 2^{saa}")
    print(f"  <b|b> = {nbb} * 2^{sbb}")
    print(f"  numerator   carries 2^{2*sab}")
    print(f"  denominator carries 2^{saa + sbb}   -> difference {2*sab - (saa + sbb)}")
    print(f"  the powers of two cancel identically; cos^2 is a pure integer ratio.")
    print(f"  cos^2({names[0]!r},{names[1]!r}) = {approx(cos2(a, b))}")


if __name__ == "__main__":
    main()
