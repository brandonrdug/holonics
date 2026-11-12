"""The field's ring faces by the code's route (the angle rounded on 2^-30 from pi on 2^-46, then the exponential's
series, field.rs turn_phasor and tower.rs exp_series) against the nearest faces of the roots of unity themselves
(cos and sin of 2 pi c/n at 400 bits, rounded once). A host ruler: it reads the faces, it is not the code."""
from fractions import Fraction
from pi_cuts import half_turn, release, div_nearest, nearest, PI, periods, reach

MOVE = 30

def exp_series(a, b):
    term = (1 << MOVE, 0)
    s = term
    k = 1
    while True:
        re = release(term[0] * a - term[1] * b, MOVE)
        im = release(term[0] * b + term[1] * a, MOVE)
        term = (div_nearest(re, k), div_nearest(im, k))
        if term == (0, 0):
            return s
        s = (s[0] + term[0], s[1] + term[1])
        k += 1

def cos_sin(x, terms=90):
    """cos and sin of the Fraction x by their series (x within a half turn), to far past 2^-30."""
    c, s, t = Fraction(0), Fraction(0), Fraction(1)
    for k in range(terms):
        if k % 4 == 0: c += t
        elif k % 4 == 1: s += t
        elif k % 4 == 2: c -= t
        else: s -= t
        t = t * x / (k + 1)
    return c, s

if __name__ == "__main__":
    pi46 = half_turn(46, 16)
    diff = {0: 0, 1: 0, 2: 0}
    by_ring = {}
    total = 0
    for n in periods:
        for r in range(min(n, reach)):
            c = r - n if 2 * r > n else r
            if c == 0 or 2 * c == n or 4 * c == n or 4 * c == -n:
                continue
            total += 1
            theta30 = release(div_nearest(2 * pi46 * c, n), 16)
            got = exp_series(0, theta30)
            x = Fraction(2 * c, n) * PI
            # the series' terms grouped by k mod 4 give cos and sin; truncated far below the grain
            cs, sn = cos_sin(Fraction(round(x * (1 << 120)), 1 << 120))
            want = (nearest(cs * (1 << MOVE)), nearest(sn * (1 << MOVE)))
            d = max(abs(got[0] - want[0]), abs(got[1] - want[1]))
            diff[min(d, 2)] += 1
            if d:
                by_ring[n] = by_ring.get(n, 0) + 1
    print(f"RING_ROUTE faces={total} equal_to_the_roots_nearest={diff[0]} one_unit_off={diff[1]} two_or_more_off={diff[2]}")
    print("RING_ROUTE_BY_RING", " ".join(f"{n}:{by_ring.get(n, 0)}/{min(n, reach)}" for n in periods))
