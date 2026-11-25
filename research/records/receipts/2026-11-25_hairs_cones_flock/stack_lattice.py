#!/usr/bin/env python3
"""Counts the primes in each stack of a lattice of the natural numbers laid in slices of W by H places.

    python3 stack_lattice.py [W H [DEPTH]]      (default 3 5 1000000)

A place n stands at depth n // (W H) in the stack n % (W H). Read by two crossing rings the stack is (n % W, n % H); read as a
raster W wide it is (stack % W, stack // W). Printed:

  STACKS   at each depth 10, 100, ... the count of primes in every stack, the mean of the live stacks (those coprime to W H), their
           spread, and the mean of the live stacks that hold squares beside the mean of those that hold none;
  READING  the stack at (2, 1) under the four readings (two rings W, H and H, W; a raster W wide and H wide), with its count;
  WHEEL    for slices that are the product of the first primes, the share of live stacks beside Mertens' e^(-gamma) / ln p;
  CONE     primes on a winding whose turns grow: n = k^2 + k + c for k < K, a count a stack c, beside the count the same sizes
           of number would hold at random (sum of 1 / ln n).

A ruler of arithmetic: a sieve and counts. It holds no law of the engine.
"""
import math
import sys


def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return s


def main():
    w, h = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (3, 5)
    deep = int(sys.argv[3]) if len(sys.argv) > 3 else 1000000
    m = w * h
    s = sieve(m * deep)
    live = [a for a in range(m) if math.gcd(a, m) == 1]
    squares = sorted({(a * a) % m for a in live})
    plain = [a for a in live if a not in squares]
    print(f"LATTICE w={w} h={h} slice={m} live={len(live)} of {m} live_stacks={live} square_stacks={squares}")
    count = [0] * m
    done = 0
    z = 10
    while z <= deep:
        for n in range(done, m * z):
            if s[n]:
                count[n % m] += 1
        done = m * z
        lv = [count[a] for a in live]
        mean = sum(lv) / len(lv)
        sq = sum(count[a] for a in squares) / len(squares)
        pl = sum(count[a] for a in plain) / len(plain) if plain else float("nan")
        print(f"STACKS depth<{z} below={m * z} " + " ".join(f"{a}:{count[a]}" for a in range(m)))
        print(f"STACKS depth<{z} live_mean={mean:.1f} least={min(lv)} most={max(lv)} spread_share={(max(lv) - min(lv)) / mean:.4f} square_mean={sq:.1f} plain_mean={pl:.1f} lag={pl - sq:.1f} primes_below_root={sum(s[: int((m * z) ** 0.5) + 1])}")
        z *= 10
    readings = {
        f"rings ({w},{h})": [a for a in range(m) if a % w == 2 % w and a % h == 1 % h],
        f"rings ({h},{w})": [a for a in range(m) if a % h == 2 % h and a % w == 1 % w],
        f"raster {w} wide": [2 + w * 1] if 2 < w and 1 < h else [],
        f"raster {h} wide": [2 + h * 1] if 2 < h and 1 < w else [],
    }
    for name, stacks in readings.items():
        for a in stacks:
            print(f"READING {name}: stack {a} gcd_with_slice={math.gcd(a, m)} primes={count[a]} first={[n for n in range(a, a + 12 * m, m) if s[n]][:6]}")
    gamma = 0.5772156649015329
    prod, share = 1, 1.0
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23):
        prod *= p
        share *= 1 - 1 / p
        print(f"WHEEL through={p} slice={prod} live_share={share:.4f} mertens={math.exp(-gamma) / math.log(p):.4f}")
    big = 20000
    top = big * big + big + 200
    t = sieve(top)
    for c in (41, 17, 11, 5, 3, 2, 1, 7, 13, 19, 23):
        got = sum(1 for k in range(big) if t[k * k + k + c])
        at_random = sum(1 / math.log(k * k + k + c) for k in range(1, big))
        print(f"CONE c={c} k<{big} primes={got} at_random={at_random:.0f} ratio={got / at_random:.2f}")


main()
