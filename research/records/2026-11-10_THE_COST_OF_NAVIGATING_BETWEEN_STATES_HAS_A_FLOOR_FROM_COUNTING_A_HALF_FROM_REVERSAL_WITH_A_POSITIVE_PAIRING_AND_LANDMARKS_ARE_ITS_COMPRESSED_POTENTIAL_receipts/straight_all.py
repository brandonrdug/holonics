#!/usr/bin/env python3
"""straight_all.py P: the straight walk at the wall for EVERY state of the prime wheel (wheel.py's walk, vectorized; public arithmetic).
The 5,000-state sample of wheel.py misses the rare states whose short pair has one long quotient; this reads all of them.
For each x: Euclid on (p, x) to the first remainder under sqrt(p) gives the pair (u, v) with u = x v (mod p) and its predecessor;
the walk divides (nearest quotient), steps |q| units, inverts, until infinity; its cost is the unit steps plus the inversions;
the state's cost is the lesser of the two pairs'. Compared with the shortest distance (breadth first) state by state."""
import math
import sys
import time

import numpy as np

from wheel import distances, euclid_pairs, walk, wheel


def cost(u, v):
    u, v = u.copy(), v.copy()
    units = np.zeros(len(u), dtype=np.int64)
    inv = np.zeros(len(u), dtype=np.int64)
    divs = np.zeros(len(u), dtype=np.int64)
    live = v != 0
    while live.any():
        uu, vv = u[live], v[live]
        q = uu // vv
        r = uu - q * vv
        up = 2 * np.abs(r) > np.abs(vv)
        q = q + up
        r = uu - q * vv
        units[live] += np.abs(q)
        divs[live] += q != 0
        inv[live] += 1
        u[live], v[live] = -vv, r
        live = v != 0
    return units + inv, divs


def main():
    p = int(sys.argv[1])
    t0 = time.time()
    tp, tm, s = wheel(p)
    dist, _ = distances(p, tp, tm, s)
    root = math.isqrt(p)
    x = np.arange(1, p, dtype=np.int64)
    r0 = np.full(p - 1, p, dtype=np.int64)
    r1 = x.copy()
    t0_ = np.zeros(p - 1, dtype=np.int64)
    t1 = np.ones(p - 1, dtype=np.int64)
    live = r1 >= root
    while live.any():
        a, b, c, d = r0[live], r1[live], t0_[live], t1[live]
        q = a // b
        r0[live], r1[live], t0_[live], t1[live] = b, a - q * b, d, c - q * d
        live = r1 >= root
    assert np.all((r1 - x * t1) % p == 0) and np.all((r0 - x * t0_) % p == 0)
    ca, da = cost(r1, t1)
    has_prev = t0_ != 0
    cb, db = cost(np.where(has_prev, r0, r1), np.where(has_prev, t0_, t1))
    c = np.minimum(ca, cb)
    dv = np.where(ca <= cb, da, db)
    d = dist[1:p].astype(np.int64)
    assert np.all(c >= d), "a walk shorter than the shortest distance"
    # the vectorized cost against the executed walk on a few states
    for xx in (1, 2, p // 3, p // 2, p - 1, 12345 % p or 7):
        pts, _ = euclid_pairs(p, xx)
        i = next((k for k, (r, _) in enumerate(pts) if r < root), len(pts) - 1)
        got = min(sum(walk(u, v, p, xx, tp, tm, s)[:2]) for (u, v) in ([pts[i]] + ([pts[i - 1]] if i > 0 else [])))
        assert got == c[xx - 1], (xx, got, c[xx - 1])
    ratio = c / d
    qs = np.quantile(ratio, [0.5, 0.9, 0.99, 0.999])
    big = c > 2 * d
    print(f"STRAIGHT_ALL p={p} states={p - 1} shortest_mean={d.mean():.4f} straight_mean={c.mean():.4f} ratio_of_means={c.mean() / d.mean():.4f} mean_ratio={ratio.mean():.4f} share_straight_is_shortest={(c == d).mean():.4f} divisions={dv.mean():.3f} ratio_quantiles_50_90_99_99.9={' '.join(f'{v:.2f}' for v in qs)} worst={ratio.max():.1f} share_over_twice={big.mean():.5f} their_share_of_the_straight_cost={c[big].sum() / c.sum():.4f} (ln p)^2={math.log(p) ** 2:.2f} s={time.time() - t0:.1f}", flush=True)


if __name__ == "__main__":
    main()
