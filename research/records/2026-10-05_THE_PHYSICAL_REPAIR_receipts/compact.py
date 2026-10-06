#!/usr/bin/env python3
"""Compact a physical-repair sections listing for the record's receipts (exterior, exact).

Every passage keeps its four cell lines whole and its opening's work exactly. The word's energies
(open, end, dissipation, residual), exact rationals of up to some 19,000 bits after 48 crossings,
are read at the grain 2^16: carry n, phase class k and the fibre's bound, v = n + k/2^16 + e with
0 <= e < 2^-16, each with the exact value's numerator and denominator bit lengths. Integer
arithmetic only (fractions.Fraction); nothing is rounded except into the stated grain cell. The
SHA-256 of the full listing is printed so the exact values stay bound to the receipt.
"""
import hashlib
import re
import sys
from fractions import Fraction

GRAIN = 1 << 16


def cell(text):
    value = Fraction(text)
    carry = value.numerator // value.denominator
    phase = ((value - carry) * GRAIN).numerator // ((value - carry) * GRAIN).denominator
    return f"{carry} + {phase}/2^16 + e (num {value.numerator.bit_length()} bits, den {value.denominator.bit_length()} bits)"


def main(path, out):
    raw = open(path, "rb").read()
    lines = raw.decode().splitlines()
    pattern = re.compile(r"word: open (\S+) end (\S+) dissipation (\S+) residual (\S+); carry at (\d+)")
    with open(out, "w") as sink:
        sink.write(f"# compacted from a listing of {len(raw)} bytes, sha256 {hashlib.sha256(raw).hexdigest()}\n")
        for line in lines:
            match = pattern.search(line)
            if not match:
                sink.write(line + "\n")
                continue
            head = line[: line.index("; word:")]
            open_, end, dissipation, residual, carry = match.groups()
            sink.write(head + "\n")
            sink.write(f"  word: open {open_}; end {cell(end)}; dissipation {cell(dissipation)}; residual {residual}; carry at {carry}\n")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
