#!/usr/bin/env python3
"""What a pass keeps of its opening at rest: the built tick, a leak of the whole lane, and a leak of the currents alone.

A planted lane on the host, no state of the machine. The write is computed from the lane's ray, g = A r(x), r(x) = x/|x|,
with A r* = r* on a fixed ray and A v = nu v on one mode across it. The opening is x0 = a r* + s v. Three passes from it:
  built    x <- x + g
  leaked   x <- (1 - delta) x + g
  held     x <- x0 + (1 - delta)(x - x0) + g
The mode's place is u = <x, v>/<x, r*>. The record's §12 gives the held pass's rest as u = delta s/(1 - nu + delta a)
(Lean: held_rest_imprint), the leaked pass's as 0 (leak_rest_imprint) and the built pass's as a power of its fill.
Run: python3 opening.py > opening.txt   (under a second, one host thread)
"""
import math


def run(kind, delta, nu, a, s, ticks):
    x0 = (a, s)
    x = x0
    for _ in range(ticks):
        n = math.hypot(*x)
        r = (x[0] / n, x[1] / n)
        g = (r[0], nu * r[1])
        if kind == "built":
            x = (x[0] + g[0], x[1] + g[1])
        elif kind == "leaked":
            x = ((1 - delta) * x[0] + g[0], (1 - delta) * x[1] + g[1])
        else:
            x = (x0[0] + (1 - delta) * (x[0] - x0[0]) + g[0], x0[1] + (1 - delta) * (x[1] - x0[1]) + g[1])
    return x[1] / x[0]


def main():
    a, s = 0.12, 0.10  # an opening about a sixth of one late write: an estimate from the residual probe's pooled ratios
    print(f"opening a={a} s={s} (in units of one write); place u = <x,v>/<x,r*>; opening's own place s/a = {s / a:.4f}")
    print("pass     delta   nu      u at 8 ticks  u at 17      u at 400     law at rest")
    for nu in (-0.54, 0.19, 0.9):
        for delta in (0.25, 0.5, 0.851, 1.0):
            law = delta * s / (1 - nu + delta * a)
            for kind in ("leaked", "held"):
                u8, u17, u400 = (run(kind, delta, nu, a, s, t) for t in (8, 17, 400))
                rest = law if kind == "held" else 0.0
                print(f"{kind:8s} {delta:5.3f}  {nu:+.2f}   {u8:+.6f}     {u17:+.6f}    {u400:+.6f}    {rest:+.6f}")
        u8, u17, u400 = (run("built", 0.0, nu, a, s, t) for t in (8, 17, 400))
        print(f"built    0.000  {nu:+.2f}   {u8:+.6f}     {u17:+.6f}    {u400:+.6f}    +0.000000 (as fill^-(1-nu))")


if __name__ == "__main__":
    main()
