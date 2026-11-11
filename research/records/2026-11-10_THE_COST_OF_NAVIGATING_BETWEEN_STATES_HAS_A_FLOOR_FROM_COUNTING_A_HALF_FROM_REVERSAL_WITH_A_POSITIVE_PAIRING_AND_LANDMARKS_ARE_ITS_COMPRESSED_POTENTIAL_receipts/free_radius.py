#!/usr/bin/env python3
"""free_radius.py K: the free walk's radius for the prime wheel's moves (public arithmetic; a host ruler, never machinery).

The wheel's moves x+1, x-1, -1/x are the images of T, T^-1, S in PSL2(Z). The free object is the group itself: the walk
A = S + T + T^-1 on its elements. m_2k = the number of words of length 2k in {S, T, T^-1} that equal the identity
= sum over elements g of (the number of words of length k that equal g)^2, because the move set is closed under inverses.
Every relator (S^2, (ST)^3) has even length, so m_odd = 0 and the spectrum is symmetric.
The radius is lim m_2k^(1/2k). Elements are integer matrices up to sign; counts are integers; floats appear only in the read.
"""
import sys
import time

import numpy as np

OFF = 1 << 30
M = 1 << 31


def norm(a, b, c, d):
    neg = (a < 0) | ((a == 0) & (b < 0))
    s = np.where(neg, -1, 1)
    return a * s, b * s, c * s, d * s


def step(a, b, c, d, n):
    na = np.concatenate([a, a, b])
    nb = np.concatenate([a + b, b - a, -a])
    nc = np.concatenate([c, c, d])
    nd = np.concatenate([c + d, d - c, -c])
    nn = np.concatenate([n, n, n])
    na, nb, nc, nd = norm(na, nb, nc, nd)
    k1 = (na + OFF) * M + (nb + OFF)
    k2 = (nc + OFF) * M + (nd + OFF)
    order = np.lexsort((k2, k1))
    k1, k2, na, nb, nc, nd, nn = k1[order], k2[order], na[order], nb[order], nc[order], nd[order], nn[order]
    first = np.ones(len(k1), dtype=bool)
    first[1:] = (k1[1:] != k1[:-1]) | (k2[1:] != k2[:-1])
    idx = np.flatnonzero(first)
    return na[idx], nb[idx], nc[idx], nd[idx], np.add.reduceat(nn, idx)


def sum_sq(v):
    """The sum of squares of nonnegative integers under 2^31, as a Python integer (16-bit limbs keep every partial sum in int64)."""
    return sum_prod(v, v)


def sum_prod(u, v):
    a0, a1 = u & 0xFFFF, u >> 16
    b0, b1 = v & 0xFFFF, v >> 16
    tot = 0
    for x, y, sh in ((a0, b0, 0), (a0, b1, 16), (a1, b0, 16), (a1, b1, 32)):
        p = x * y  # under 2^32 each
        acc = 0
        for i in range(0, len(p), 1 << 20):
            acc += int(p[i:i + (1 << 20)].sum())
        tot += acc << sh
    return tot


def jacobi(m):
    """The recurrence coefficients b_n^2 of the walk's spectral measure at the identity from its even moments (rationals throughout).
    p_(n+1) = x p_n - b_n^2 p_(n-1); b_n^2 = <p_n, p_n> / <p_(n-1), p_(n-1)>; odd moments vanish."""
    from fractions import Fraction
    mom = lambda j: Fraction(m[j // 2]) if j % 2 == 0 else Fraction(0)
    ip = lambda p, q: sum(a * b * mom(i + j) for i, a in enumerate(p) for j, b in enumerate(q) if a and b)
    pm, p = [Fraction(0)], [Fraction(1)]
    nm = Fraction(1)
    out = []
    for n in range(1, len(m)):
        xp = [Fraction(0)] + p
        if n == 1:
            q = xp
        else:
            q = [a - out[-1] * (pm[i] if i < len(pm) else 0) for i, a in enumerate(xp)]
        nq = ip(q, q)
        out.append(nq / nm)
        pm, p, nm = p, q, nq
    return out


def main():
    kmax = int(sys.argv[1])
    t0 = time.time()
    a = np.array([1], dtype=np.int64)
    b = np.array([0], dtype=np.int64)
    c = np.array([0], dtype=np.int64)
    d = np.array([1], dtype=np.int64)
    n = np.array([1], dtype=np.int64)
    m = [1]
    print("  k | elements reached by words of length k | m_2k (an integer) | m_2k / m_2k-2 | its root | root with the k^(3/2) correction")
    for k in range(1, kmax + 1):
        a, b, c, d, n = step(a, b, c, d, n)
        assert int(n.sum()) == 3 ** k
        assert np.all(a * d - b * c == 1)
        hi, lo = n >> 31, n & ((1 << 31) - 1)  # n = hi 2^31 + lo, each part under 2^31: the three sums are integers
        m2k = (sum_sq(hi) << 62) + (sum_prod(hi, lo) << 32) + sum_sq(lo)
        m.append(m2k)
        r = m[k] / m[k - 1]
        corr = r * (k / (k - 1)) ** 1.5 if k > 1 else float("nan")
        print(f"{k:4d} {len(n):10d} {m2k:d} {r:.6f} {r ** 0.5:.6f} {corr ** 0.5 if k > 1 else float('nan'):.6f}  s={time.time() - t0:.1f}", flush=True)
    # the read: m_2k ~ C rho^(2k) k^(-3/2) (1 + c1/k + c2/k^2): fit ln m_2k on the last terms
    ks = np.arange(1, kmax + 1, dtype=float)
    y = np.log(np.array(m[1:], dtype=float))
    for lo in (kmax - 6, kmax - 9, kmax - 12):
        if lo < 3:
            continue
        sel = ks >= lo
        for terms in (1, 2):
            cols = [np.ones(sel.sum()), ks[sel]] + [ks[sel] ** -j for j in range(1, terms + 1)]
            x = np.stack(cols, axis=1)
            coef, *_ = np.linalg.lstsq(x, y[sel] + 1.5 * np.log(ks[sel]), rcond=None)
            print(f"  fit k >= {lo} with {terms} correction term(s): radius {np.exp(coef[1] / 2):.5f}")
    # the read that converges: the recurrence coefficients of the spectral measure at the identity.
    b2 = jacobi(m)
    print("  n | b_n^2 | 2 b_n")
    for i, v in enumerate(b2, 1):
        print(f"{i:4d} {float(v):.8f} {2 * float(v) ** 0.5:.6f}")
    # the coefficients alternate: two bands, [-(b_odd + b_even), -|b_odd - b_even|] and its mirror. Each parity is read against 1/n^2.
    nn = np.arange(1, len(b2) + 1, dtype=float)
    bb = np.array([float(v) for v in b2]) ** 0.5
    for lo in (8, 12, 16, 20):
        lim = []
        for parity in (1, 0):
            sel = (nn >= lo) & (nn % 2 == parity)
            if sel.sum() < 4:
                break
            x = np.stack([np.ones(sel.sum()), nn[sel] ** -2.0], axis=1)
            coef, *_ = np.linalg.lstsq(x, bb[sel], rcond=None)
            lim.append(coef[0])
        if len(lim) == 2:
            print(f"  from n = {lo}: b_odd {lim[0]:.5f} b_even {lim[1]:.5f}: outer edge (the radius) {lim[0] + lim[1]:.5f}, inner edge {abs(lim[0] - lim[1]):.5f}")
    tail = bb[-8:]
    print(f"  last eight, no fit: b_odd mean {tail[len(bb) % 2::2].mean():.5f} b_even mean {tail[1 - len(bb) % 2::2].mean():.5f}; sum of the last two {bb[-1] + bb[-2]:.5f}")
    print(f"DONE s={time.time() - t0:.1f}")


if __name__ == "__main__":
    main()
