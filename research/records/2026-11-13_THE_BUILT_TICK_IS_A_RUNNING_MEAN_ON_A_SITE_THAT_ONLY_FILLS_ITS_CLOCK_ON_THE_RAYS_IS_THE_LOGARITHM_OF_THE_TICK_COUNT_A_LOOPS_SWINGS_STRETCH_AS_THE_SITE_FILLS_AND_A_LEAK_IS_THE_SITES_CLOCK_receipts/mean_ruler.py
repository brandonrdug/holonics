#!/usr/bin/env python3
"""mean_ruler: is the free ring's decay a running mean's? (a host ruler on public receipts; numbers only)

usage: python3 -I mean_ruler.py RECEIPT...

Reads the two series a receipt prints for a line: the length of each tick's change of an opened place's chart, and the cosine of two
successive changes. Two layouts are read:

  a read-depth receipt (G149: each held place open alone, 16 ticks on a field trained at 4): under `DEPTH out_NAME`, `change_norm t1..tK`
  (the mean length a place) and `successive_cos t2..tK` (the mean cosine a place);
  a read-ring receipt (G162: 280 seen places open alone, 16 ticks, the read's mirror at a strength in every head): under `RING PATH/NAME`,
  `change s2..sK` (the root of the mean squared change a place) and `cosine s3..sK` (pooled, sum of inner products over the root of the
  product of the summed squares).

The built tick adds to a site's state and every reader takes the state's ray (the chart at unit power), so the ray is the ray of a mean over
ticks. For a current that keeps its direction, with the opening weighing `a` ticks of it, the change of the ray at tick k goes as
1/((k + a)(k + a - 1)): a power of the tick count, with no rate on the ticks. The ruler prints, from tick 5 on (the ticks past the trained
four):

  ratio            c_k / c_(k-1), beside the running mean's (k + a - 2)/(k + a) at a = 1, which is (k - 1)/(k + 1)
  rate_on_ticks    -ln(ratio): constant if the decay were exponential in the tick count (a spectral gap on the ticks)
  power_on_log     -ln(ratio)/ln(k/(k - 1)): constant if the decay is a power of the tick count; 2 for a fixed current
  bend_per_efold   arccos(successive_cos_k) * k: the turn of the change's direction per e-fold of ticks, in radians;
                   level for a turn on the logarithmic clock, falling where a mixture of real modes settles

and, over ticks 5 to K: how far each of rate_on_ticks and power_on_log moves (first over last), the `a` that makes
c_k (k + a)(k + a - 1) most level and its largest over its least, and the opening's share a/(k + a) at the trained
tick count and at the last tick; and, from the successive cosines of ticks 9 to K, the two ends between which a cosine of the change at
tick K against the change at tick 8 would fall: `one_plane`, the cosine of the summed angles (every step's turn in one plane and one sense),
and `unlike_planes`, the product of the cosines (every step's turn in a direction unlike the ones before it).
"""
import math
import re
import sys


def series(line, mark):
    return {int(k): float(v) for k, v in re.findall(mark + r"(\d+)=(-?[0-9.]+)", line)}


def level(c, a, first, last):
    vals = [c[k] * (k + a) * (k + a - 1) for k in range(first, last + 1)]
    return max(vals) / min(vals)


def report(name, change, cos):
    ticks = max(change)
    print("MEAN_RULER line=%s ticks=%d" % (name, ticks))
    rates, powers = [], []
    for k in range(5, ticks + 1):
        r = change[k] / change[k - 1]
        rate = -math.log(r)
        power = rate / math.log(k / (k - 1))
        bend = math.acos(cos[k]) * k
        rates.append(rate)
        powers.append(power)
        print("  tick=%d ratio=%.4f mean_at_a1=%.4f rate_on_ticks=%.4f power_on_log=%.3f bend_per_efold=%.3f" % (k, r, (k - 1) / (k + 1), rate, power, bend))
    print("  rate_on_ticks first_over_last=%.2f power_on_log first_over_last=%.2f" % (rates[0] / rates[-1], powers[0] / powers[-1]))
    grid = [i / 20 for i in range(-10, 81)]
    best = min(grid, key=lambda a: level(change, a, 5, ticks))
    print("  most_level a=%.2f largest_over_least=%.4f opening_share tick4=%.3f tick%d=%.3f" % (best, level(change, best, 5, ticks), best / (4 + best), ticks, best / (ticks + best)))
    print("  at a=1 largest_over_least=%.4f" % level(change, 1.0, 5, ticks))
    print("  log_clock ln(%d)/ln(5)=%.3f (the last tick against the fourth at a=1)" % (ticks + 1, math.log(ticks + 1) / math.log(5)))
    angles = [math.acos(cos[k]) for k in range(9, ticks + 1)]
    print("  lag tick%d against tick8: turn_sum=%.3f one_plane=%.3f unlike_planes=%.3f" % (ticks, sum(angles), math.cos(sum(angles)), math.prod(cos[k] for k in range(9, ticks + 1))))


def main(paths):
    for path in paths:
        name, change, mark = None, None, None
        for line in open(path, encoding="utf-8"):
            m = re.match(r"DEPTH (out_\w+)", line)
            if m:
                name, change, mark = m.group(1), None, ("change_norm", "successive_cos", "t")
            m = re.match(r"RING \S*?(ring_s-?\d+) ", line)
            if m:
                name, change, mark = m.group(1), None, ("change ", "cosine ", "s")
            if name and change is None and mark[0] in line:
                change = series(line, mark[2])
            elif name and change and mark[1] in line:
                report(name, change, series(line, mark[2]))
                name, change = None, None


if __name__ == "__main__":
    main(sys.argv[1:])
