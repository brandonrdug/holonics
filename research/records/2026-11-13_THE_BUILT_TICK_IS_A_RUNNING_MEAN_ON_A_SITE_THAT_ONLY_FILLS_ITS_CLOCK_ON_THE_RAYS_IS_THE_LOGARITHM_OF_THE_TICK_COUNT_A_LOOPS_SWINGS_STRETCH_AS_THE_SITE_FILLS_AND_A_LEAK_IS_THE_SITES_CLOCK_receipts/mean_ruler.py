#!/usr/bin/env python3
"""mean_ruler: is the free ring's decay a running mean's? (a host ruler on a public receipt; numbers only)

usage: python3 -I mean_ruler.py g149_depth.txt

Reads the two series a read-depth receipt prints for a line (G149: each held place open alone, 16 ticks on a field
trained at 4): change_norm t1..tK, the mean length of each tick's change of an opened place's chart, and
successive_cos t2..tK, the mean cosine of two successive changes.

The built tick adds to a site's state and every reader takes the state's ray (the chart at unit power), so the ray is
the ray of a mean over ticks. For a current that keeps its direction, with the opening weighing `a` ticks of it, the
change of the ray at tick k goes as 1/((k + a)(k + a - 1)): a power of the tick count, with no rate on the ticks. The
ruler prints, from tick 5 on (the ticks past the trained four):

  ratio            c_k / c_(k-1), beside the running mean's (k + a - 2)/(k + a) at a = 1, which is (k - 1)/(k + 1)
  rate_on_ticks    -ln(ratio): constant if the decay were exponential in the tick count (a spectral gap on the ticks)
  power_on_log     -ln(ratio)/ln(k/(k - 1)): constant if the decay is a power of the tick count; 2 for a fixed current
  bend_per_efold   arccos(successive_cos_k) * k: the turn of the change's direction per e-fold of ticks, in radians;
                   level for a turn on the logarithmic clock, falling where a mixture of real modes settles

and, over ticks 5 to K: how far each of rate_on_ticks and power_on_log moves (first over last), the `a` that makes
c_k (k + a)(k + a - 1) most level and its largest over its least, and the opening's share a/(k + a) at the trained
tick count and at the last tick.
"""
import math
import re
import sys


def series(line):
    return [float(v) for v in re.findall(r"t\d+=([0-9.]+)", line)]


def level(c, a, first):
    vals = [c[k - 1] * (k + a) * (k + a - 1) for k in range(first, len(c) + 1)]
    return max(vals) / min(vals)


def main(path):
    name, change = None, None
    for line in open(path, encoding="utf-8"):
        m = re.match(r"DEPTH (out_\w+)", line)
        if m:
            name, change = m.group(1), None
        if name and "change_norm" in line:
            change = series(line)
        if name and change and "successive_cos" in line:
            cos = series(line)  # cos[0] is tick 2
            ticks = len(change)
            print("MEAN_RULER line=%s ticks=%d" % (name, ticks))
            rates, powers = [], []
            for k in range(5, ticks + 1):
                r = change[k - 1] / change[k - 2]
                rate = -math.log(r)
                power = rate / math.log(k / (k - 1))
                bend = math.acos(cos[k - 2]) * k
                rates.append(rate)
                powers.append(power)
                print("  tick=%d ratio=%.4f mean_at_a1=%.4f rate_on_ticks=%.4f power_on_log=%.3f bend_per_efold=%.3f" % (k, r, (k - 1) / (k + 1), rate, power, bend))
            print("  rate_on_ticks first_over_last=%.2f power_on_log first_over_last=%.2f" % (rates[0] / rates[-1], powers[0] / powers[-1]))
            grid = [i / 20 for i in range(-10, 81)]
            best = min(grid, key=lambda a: level(change, a, 5))
            print("  most_level a=%.2f largest_over_least=%.4f opening_share tick4=%.3f tick%d=%.3f" % (best, level(change, best, 5), best / (4 + best), ticks, best / (ticks + best)))
            print("  at a=1 largest_over_least=%.4f" % level(change, 1.0, 5))
            print("  log_clock ln(%d)/ln(5)=%.3f (the last tick against the fourth at a=1)" % (ticks + 1, math.log(ticks + 1) / math.log(5)))
            name, change = None, None


if __name__ == "__main__":
    main(sys.argv[1])
