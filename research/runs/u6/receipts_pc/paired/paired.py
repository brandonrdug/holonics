"""paired.py <newer sections> <older sections>: the paired sign test on the same held-out station
cells. Each sections file (written by `hnn_prediction -- executed evaluate`) holds one line per
request, `<request> | target [..] | released [..] | locks [..]`, in the same request order. b counts
cells right at the newer state and wrong at the older, c the reverse; the one-sided tail is
P[X >= b | X ~ Bin(b + c, 1/2)], exact."""
import re, sys
from fractions import Fraction
from math import comb

def cells(path):
    out = []
    for line in open(path):
        m = re.search(r"target \[([0-9, ]*)\] \| released \[([0-9, ]*)\]", line)
        if m:
            t = [int(x) for x in m.group(1).split(',')]
            r = [int(x) for x in m.group(2).split(',')]
            out.append((line.split('|')[0].strip(), [int(a == b) for a, b in zip(t, r)]))
    return out

new, old = cells(sys.argv[1]), cells(sys.argv[2])
assert len(new) == len(old) and all(a[0] == b[0] for a, b in zip(new, old)), "the same requests in order"
b = sum(x == 1 and y == 0 for (_, u), (_, v) in zip(new, old) for x, y in zip(u, v))
c = sum(x == 0 and y == 1 for (_, u), (_, v) in zip(new, old) for x, y in zip(u, v))
n = b + c
tail = Fraction(sum(comb(n, k) for k in range(b, n + 1)), 2 ** n) if n else Fraction(1)
right = lambda s: sum(sum(v) for _, v in s)
print(f"newer right {right(new)}, older right {right(old)}, requests {len(new)}; b = {b}, c = {c}; "
      f"P[X >= b | X ~ Bin({n}, 1/2)] = {tail.numerator}/{tail.denominator}")
k = (tail * 4096).numerator // (tail * 4096).denominator
print(f"the tail lies in [{k}/4096, {k + 1}/4096); at most 1/64: {tail <= Fraction(1, 64)}")
