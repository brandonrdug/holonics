#!/usr/bin/env python3
"""wheel.py P [SAMPLES]: the prime wheel as a navigation problem (public arithmetic; a host ruler, never machinery).

States: the projective line over F_p (the p residues and the point at infinity). Moves: the unit step x+1, its inverse x-1, and the
inversion x -> -1/x (the modular group's two generators read on the wheel). Reads:
  1. the shortest distance from infinity to every state (breadth first), its mean and its farthest;
  2. the floor: the same moves on the rationals (no wheel reaches more states in r moves than the free count);
  3. the straight walk at the wall: Euclid's divisions (nearest quotients) on a short pair (u, v) with u = x v (mod p), unit steps counted,
     each walk executed on the wheel and checked to arrive;
  4. the largest nontrivial modes of the wheel's adjacency (Lanczos, constants removed) and the free walk's radius from closed-walk counts;
  5. Euclid's division count on (p, x) against (12 ln 2 / pi^2) ln p + 1.467.
Floats appear in the reads (means, modes), never in the walk.
"""
import math
import sys
import time

import numpy as np


def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def inverses(p):
    x = np.arange(p, dtype=np.int64)
    r = np.ones(p, dtype=np.int64)
    b = x.copy()
    e = p - 2
    while e:
        if e & 1:
            r = r * b % p
        b = b * b % p
        e >>= 1
    r[0] = 0
    return r


def wheel(p):
    """The three move tables on p + 1 states; index p is the point at infinity."""
    x = np.arange(p, dtype=np.int64)
    tp = np.concatenate([(x + 1) % p, [p]])
    tm = np.concatenate([(x - 1) % p, [p]])
    inv = inverses(p)
    s = (p - inv) % p
    s[0] = p
    s = np.concatenate([s, [0]])
    assert np.array_equal(s[s], np.arange(p + 1)), "the inversion is an involution"
    assert np.array_equal(tm[tp], np.arange(p + 1))
    return tp, tm, s


def distances(p, tp, tm, s):
    dist = np.full(p + 1, -1, dtype=np.int16)
    dist[p] = 0
    front = np.array([p], dtype=np.int64)
    shells = [1]
    r = 0
    while front.size:
        r += 1
        nb = np.concatenate([tp[front], tm[front], s[front]])
        nb = np.unique(nb[dist[nb] < 0])
        dist[nb] = r
        front = nb
        if nb.size:
            shells.append(int(nb.size))
    return dist, shells


def free_shells(limit):
    """Shell sizes of the same moves on the rationals from infinity = (1, 0), until the ball passes `limit`.
    A state is a coprime pair (a, b), b >= 0, (1, 0) for infinity; a neighbour of shell r lies in shells r - 1, r, r + 1."""
    off, m = 1 << 30, 1 << 31

    def key(a, b):
        return (a + off) * m + b

    def norm(a, b):
        neg = (b < 0) | ((b == 0) & (a < 0))
        return np.where(neg, -a, a), np.where(neg, -b, b)

    a = np.array([1], dtype=np.int64)
    b = np.array([0], dtype=np.int64)
    prev = np.array([], dtype=np.int64)
    cur = key(a, b)
    shells = [1]
    total = 1
    while total < limit:
        na = np.concatenate([a + b, a - b, -b])
        nb = np.concatenate([b, b, a])
        na, nb = norm(na, nb)
        k = key(na, nb)
        k, idx = np.unique(k, return_index=True)
        na, nb = na[idx], nb[idx]
        keep = ~np.isin(k, cur) & ~np.isin(k, prev)
        k, na, nb = k[keep], na[keep], nb[keep]
        prev, cur, a, b = cur, k, na, nb
        shells.append(int(k.size))
        total += int(k.size)
    return shells


def floor_mean(shells, n):
    """The mean distance if n states filled the free shells in order."""
    left, acc = n, 0
    r_last = 0
    for r, f in enumerate(shells):
        take = min(f, left)
        acc += r * take
        left -= take
        r_last = r
        if left == 0:
            break
    assert left == 0, "the free count was not carried far enough"
    return acc / n, r_last


def euclid_pairs(p, x):
    """The lattice points (r_i, t_i) of Euclid on (p, x): r_i = t_i x (mod p). Returns them all, and the division count."""
    r0, r1, t0, t1 = p, x, 0, 1
    pts = [(r1, t1)]
    steps = 0
    while r1:
        q = r0 // r1
        r0, r1, t0, t1 = r1, r0 - q * r1, t1, t0 - q * t1
        steps += 1
        if r1:
            pts.append((r1, t1))
    return pts, steps


def walk(u, v, p, x, tp, tm, s):
    """The straight walk: the state is u / v (mod p); divide (nearest quotient), step |q| units, invert; until infinity.
    Returns the unit steps, the inversions, the divisions; executes every move on the wheel and checks the arrival."""
    state = x
    units = inversions = divisions = 0
    assert (u - x * v) % p == 0
    while True:
        if v == 0:
            break
        q = round_div(u, v)
        if q:
            divisions += 1
            units += abs(q)
            # |q| unit steps x -> x - sign(q): the tables' own arithmetic (tm[x] = x - 1, tp[x] = x + 1 mod p; infinity is fixed)
            if state != p:
                state = (state - q) % p
            u -= q * v
        # now |u| <= |v| / 2; invert: -1/(u/v) = -v/u
        state = int(s[state])
        inversions += 1
        u, v = -v, u
    assert state == p, "the walk did not arrive at infinity"
    return units, inversions, divisions


def round_div(u, v):
    """The nearest integer to u / v (ties toward zero), integers only."""
    q, r = divmod(u, v)  # u = q v + r, r has the sign of v, |r| < |v|
    if 2 * abs(r) > abs(v):
        q += 1
    return q


def lanczos_top(n, apply, k, seed):
    """The extreme Ritz values of a symmetric operator on the complement of the constants (full reorthogonalization)."""
    rng = np.random.default_rng(seed)
    v = rng.standard_normal(n)
    v -= v.mean()
    v /= np.linalg.norm(v)
    basis = [v]
    alpha, beta = [], []
    w_prev, b_prev = None, 0.0
    for j in range(k):
        w = apply(basis[-1])
        w -= w.mean()
        a = float(w @ basis[-1])
        alpha.append(a)
        w -= a * basis[-1]
        if j:
            w -= b_prev * basis[-2]
        for u in basis:
            w -= (w @ u) * u
        b = float(np.linalg.norm(w))
        if b < 1e-12:
            break
        beta.append(b)
        b_prev = b
        basis.append(w / b)
    t = np.diag(alpha) + np.diag(beta[: len(alpha) - 1], 1) + np.diag(beta[: len(alpha) - 1], -1)
    ev = np.linalg.eigvalsh(t)
    return ev[-3:][::-1], ev[:2]


def main():
    p = int(sys.argv[1])
    samples = int(sys.argv[2]) if len(sys.argv) > 2 else 5000
    assert is_prime(p)
    t0 = time.time()
    tp, tm, s = wheel(p)
    n = p + 1
    dist, shells = distances(p, tp, tm, s)
    assert dist.min() >= 0, "connected"
    mean, far = float(dist.mean()), int(dist.max())
    free = free_shells(2 * n)
    fmean, fr = floor_mean(free, n)
    growth = [free[r + 1] / free[r] for r in range(len(free) - 6, len(free) - 1)]
    print(f"WHEEL p={p} states={n} mean={mean:.4f} farthest={far} floor_mean={fmean:.4f} floor_radius={fr} mean/floor={mean / fmean:.4f} farthest/mean={far / mean:.4f} ln_p={math.log(p):.4f} mean/ln_p={mean / math.log(p):.4f} s={time.time() - t0:.1f}", flush=True)
    print("  free shells " + " ".join(map(str, free[:14])) + f" ... last growth ratios {' '.join(f'{g:.4f}' for g in growth)}")
    print("  wheel shells " + " ".join(map(str, shells)))
    # the straight walk
    rng = np.random.default_rng(p)
    xs = rng.integers(1, p, size=samples)
    half, best, strides, divs, bfs, half_div = [], [], [], [], [], []
    root = math.isqrt(p)
    for x in map(int, xs):
        pts, steps = euclid_pairs(p, x)
        divs.append(steps)
        costs = []
        for (u, v) in pts:
            un, inv, dv = walk(u, v, p, x, tp, tm, s)
            costs.append((un + inv, dv))
        # the two lattice points around sqrt(p): the last with r >= sqrt(p) and the first with r < sqrt(p)
        i = next(k for k, (r, _) in enumerate(pts) if r < root) if any(r < root for r, _ in pts) else len(pts) - 1
        mid = [costs[i]] + ([costs[i - 1]] if i > 0 else [])
        c = min(mid)
        half.append(c[0])
        half_div.append(c[1])
        best.append(min(costs)[0])
        bfs.append(int(dist[x]))
    half, best, bfs, divs, half_div = map(np.array, (half, best, bfs, divs, half_div))
    print(f"  STRAIGHT samples={samples} shortest_mean={bfs.mean():.4f} straight_mean={half.mean():.4f} ratio_of_means={half.mean() / bfs.mean():.4f} mean_ratio={(half / bfs).mean():.4f} best_pair_mean={best.mean():.4f} best/shortest={best.mean() / bfs.mean():.4f} share_straight_is_shortest={(half == bfs).mean():.4f} divisions_on_the_walk={half_div.mean():.3f} worst_ratio={(half / bfs).max():.2f}")
    all_divs = None
    if p <= 2_000_000:
        # the division count over every x (known theorem: (12 ln 2 / pi^2) ln p + 1.467)
        r0 = np.full(p - 1, p, dtype=np.int64)
        r1 = np.arange(1, p, dtype=np.int64)
        cnt = np.zeros(p - 1, dtype=np.int64)
        live = r1 > 0
        while live.any():
            q0 = r0[live] % r1[live]
            r0[live] = r1[live]
            r1[live] = q0
            cnt[live] += 1
            live = r1 > 0
        all_divs = cnt.mean()
    pred = 12 * math.log(2) / math.pi ** 2 * math.log(p) + 1.467
    print(f"  EUCLID divisions mean over sample {divs.mean():.4f}" + (f" over all x {all_divs:.4f}" if all_divs is not None else "") + f" theorem {pred:.4f}")
    # modes
    apply = lambda v: v[tp] + v[tm] + v[s]
    if n <= 1_100_000:
        top, bottom = lanczos_top(n, apply, 140, 1)
        print(f"  MODES top {' '.join(f'{e:.5f}' for e in top)} bottom {' '.join(f'{e:.5f}' for e in bottom)} s={time.time() - t0:.1f}", flush=True)
    # closed walks of the free walk, read on the wheel away from the constants: m_2k = |A^k v|^2 / n for random signs v
    if n >= 1_000_000:
        v = rng.choice([-1.0, 1.0], size=n)
        v -= v.mean()
        v /= np.linalg.norm(v)
        out = []
        for k in range(1, 31):
            v = apply(v)
            v -= v.mean()
            raw = float(np.linalg.norm(v))  # |A^k v| / |A^(k-1) v|
            est = raw * (k / (k - 1)) ** 0.75 if k > 1 else float("nan")
            out.append((k, 0.0, raw, est))
            v /= raw
        print("  CLOSED WALKS k | (|A^k v|/|A^(k-1) v|) | with the k^(3/2) correction")
        for k, _, raw, est in out:
            if k in (2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30):
                print(f"    {k:3d} {raw:.5f} {est:.5f}")
    print(f"DONE p={p} s={time.time() - t0:.1f}", flush=True)


if __name__ == "__main__":
    main()
