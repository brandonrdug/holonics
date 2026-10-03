"""paired.py <newer sections> <older sections> [--station]: the paired sign test on the same held-out
requests. Each sections file (written by `hnn_prediction -- executed evaluate`) holds one line per
request, `<request> | target [..] | released [..] | locks [..]`, in the same request order.

The unit is the request (the default, and the grade's unit from October 3): a request's eight station
targets follow from its last two cells and its classes come from one joint release, so its stations
are not independent trials; the requests are independent draws read from the same stored states.
For each request d = stations right at the newer state minus at the older; b counts d > 0, c counts
d < 0, ties are dropped, and the one-sided tail is P[X >= b | X ~ Bin(b + c, 1/2)], exact.

The station counts are printed beside it as description. `--station` also prints the station tail
(b and c counted over the stations as if independent), which no grade uses."""
import re, sys
from fractions import Fraction
from math import comb

def cells(path):
    out = []
    for line in open(path):
        m = re.search(r"target \[([0-9, ]*)\] \| (?:released|held) \[([0-9, ]*)\]", line)
        if m:
            t = [int(x) for x in m.group(1).split(',')]
            r = [int(x) for x in m.group(2).split(',')]
            out.append((line.split('|')[0].strip(), [int(a == b) for a, b in zip(t, r)]))
    return out

def tail(b, c):
    n = b + c
    return Fraction(sum(comb(n, k) for k in range(b, n + 1)), 2 ** n) if n else Fraction(1)

def cell(t, bits):
    k = (t * 2 ** bits).numerator // (t * 2 ** bits).denominator
    return f"[{k}/2^{bits}, {k + 1}/2^{bits})"

args = [a for a in sys.argv[1:] if a != "--station"]
new, old = cells(args[0]), cells(args[1])
assert len(new) == len(old) and all(a[0] == b[0] for a, b in zip(new, old)), "the same requests in order"
right = lambda s: sum(sum(v) for _, v in s)
d = [sum(u) - sum(v) for (_, u), (_, v) in zip(new, old)]
b, c = sum(x > 0 for x in d), sum(x < 0 for x in d)
t = tail(b, c)
print(f"newer right {right(new)}, older right {right(old)}, requests {len(new)}; per request "
      f"ahead {b}, behind {c}, tied {len(d) - b - c}; P[X >= {b} | X ~ Bin({b + c}, 1/2)] = "
      f"{t.numerator}/{t.denominator}")
print(f"the request tail lies in {cell(t, 12)} and {cell(t, 20)}; at most 1/64: {t <= Fraction(1, 64)}")
sb = sum(x == 1 and y == 0 for (_, u), (_, v) in zip(new, old) for x, y in zip(u, v))
sc = sum(x == 0 and y == 1 for (_, u), (_, v) in zip(new, old) for x, y in zip(u, v))
print(f"stations (described): b = {sb}, c = {sc}")
if "--station" in sys.argv:
    st = tail(sb, sc)
    print(f"station tail (stations as independent; no grade uses it) in {cell(st, 12)}")
