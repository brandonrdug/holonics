#!/usr/bin/env python3
"""The gaps of a helix of fifths, read exactly in the ratio chart (no logarithm, no float).

The j-th fifth reduced into the octave is 3^j / 2^e_j with e_j the largest e such that 2^e <= 3^j.
Sorting these N ratios around the octave and taking successive quotients (the last wraps to 2 times
the first) gives the gap ratios. The three-distance theorem (Steinhaus; Sós, Świerczkowski, Surányi)
says there are at most three, and when three occur the largest is the product of the other two
(the sum, in the additive chart). Every ratio is printed with its factorization.
"""
from fractions import Fraction
from collections import Counter

def factor(q):
    out = []
    for part, sign in ((q.numerator, 1), (q.denominator, -1)):
        n, p = part, 2
        while n > 1:
            while n % p == 0:
                out.append((p, sign)); n //= p
            p += 1
    c = Counter()
    for p, s in out: c[p] += s
    num = '·'.join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in sorted(c.items()) if e > 0) or '1'
    den = '·'.join(f"{p}^{-e}" if -e > 1 else f"{p}" for p, e in sorted(c.items()) if e < 0) or '1'
    return f"{num} : {den}"

def reduced_fifth(j):
    e = 0
    while 2 ** (e + 1) <= 3 ** j:
        e += 1
    return Fraction(3 ** j, 2 ** e)

for N in (5, 7, 12, 41, 53):
    pts = sorted(reduced_fifth(j) for j in range(N))
    gaps = [pts[i + 1] / pts[i] for i in range(N - 1)] + [2 * pts[0] / pts[-1]]
    kinds = Counter(gaps)
    print(f"N = {N}: {len(kinds)} gap ratios")
    for g, m in sorted(kinds.items()):
        print(f"   {m:3d} × {g.numerator} : {g.denominator}   = {factor(g)}")
    ks = sorted(kinds)
    assert len(ks) <= 3
    if len(ks) == 3:
        assert ks[2] == ks[0] * ks[1], "largest gap is the product of the other two"
        print("   largest = product of the other two: verified exactly")
    if len(ks) == 2:
        print(f"   larger / smaller = {(ks[1]/ks[0]).numerator} : {(ks[1]/ks[0]).denominator}   = {factor(ks[1]/ks[0])}")
