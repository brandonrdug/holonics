"""The turn's series read against its own value (a host ruler; integers only, no floats in the law's side).

The engine's `exp_series` (crates/engine/src/ratio.rs) sums e^(i theta) on 2^(-30), every product released to the
grain before it enters the sum, and halts when a term releases to zero. This ruler reads, over every angle the engine's
rings take (turn_phasor at whole clocks, periods of the towers of 2 and 3 to the reach), how far the built face stands
from the nearest face of the true value, and how far it stands when the same series runs g places finer and is
released once (the guard), with and without the angle folded to an octant.
"""
import sys
from fractions import Fraction

MOVE, PACE = 30, 24

def release(x, bits):
    if bits == 0:
        return x
    half = 1 << (bits - 1)
    return (x + half) >> bits if x >= 0 else -((-x + half) >> bits)

def div_nearest(x, k):
    return (x + k // 2) // k if x >= 0 else -((-x + k // 2) // k)

def half_turn(bits, guard=16):
    one = 1 << (bits + guard)
    def atan_inverse(k):
        power, s, n = one // k, 0, 0
        while power != 0:
            term = power // (2 * n + 1)
            s += term if n % 2 == 0 else -term
            power //= k * k
            n += 1
        return s
    return release(16 * atan_inverse(5) - 4 * atan_inverse(239), guard)

def exp_series(a, b, grain=MOVE):
    term = (1 << grain, 0)
    s = term
    k = 1
    while True:
        re = release(term[0] * a - term[1] * b, grain)
        im = release(term[0] * b + term[1] * a, grain)
        term = (div_nearest(re, k), div_nearest(im, k))
        if term == (0, 0):
            return s, k
        s = (s[0] + term[0], s[1] + term[1])
        k += 1

PI_WIDE = half_turn(200, 32)          # pi on 2^(-200), the ruler's reference

def true_face(c, n, wide=200):
    """e^(2 pi i c/n) on 2^(-wide) as integers, by the series at a width no face of the read reaches."""
    theta = div_nearest(2 * PI_WIDE * c, n)
    (re, im), _ = exp_series(0, theta, wide)
    return re, im

def built(c, n, pi46):
    period = n << PACE
    cc = c << PACE
    theta = div_nearest(2 * pi46 * cc, period)
    (re, im), k = exp_series(0, release(theta, 16))
    return re, im, k

def guarded(c, n, g, fold):
    """The same series g places finer, the angle on 2^(-(30+g)), released once; fold: the angle taken to an octant first."""
    grain = MOVE + g
    pi = half_turn(grain + 16)
    q = 0
    num, den = c, n                      # the turn c/n
    if fold:
        # e^(2 pi i c/n) = i^q e^(2 pi i r), |r| <= 1/8 of a turn
        t = Fraction(c, n)
        q = round(t * 4)
        t -= Fraction(q, 4)
        num, den = t.numerator, t.denominator
    theta = div_nearest(2 * pi * num, den << 16)   # pi on 2^-(grain+16)
    (re, im), k = exp_series(0, theta, grain)
    for _ in range(q % 4):
        re, im = -im, re
    return release(re, g), release(im, g), k

def towers(reach=3771):
    out = set()
    for b in (2, 3):
        p = b
        while p <= 2 * reach:
            out.add(p)
            p *= b
    return sorted(out)

def main():
    pi46 = half_turn(46)
    periods = [2, 3, 4, 9, 16, 27, 32, 81, 128, 243, 256, 729, 1024, 2187, 4096, 6561]
    wide = 200
    rows = {}
    def score(key, re, im, tre, tim, k):
        # distance from the true value, in grains of 2^-30, as a fraction
        dre = abs(Fraction(re) - Fraction(tre, 1 << (wide - MOVE)))
        dim = abs(Fraction(im) - Fraction(tim, 1 << (wide - MOVE)))
        d = max(dre, dim)
        r = rows.setdefault(key, [0, Fraction(0), 0, 0])
        r[0] += 1
        r[1] = max(r[1], d)
        r[2] += d > Fraction(1, 2)            # off the nearest face
        r[3] = max(r[3], k)
    angles = 0
    for n in periods:
        for c in range(-(n - 1) // 2, n // 2 + 1):
            if c == 0 or 2 * c == n or 4 * c == n or 4 * c == -n:
                continue
            angles += 1
            tre, tim = true_face(c, n, wide)
            re, im, k = built(c, n, pi46)
            score('built (grain 2^-30, no guard, whole turn)', re, im, tre, tim, k)
            for g in (2, 3, 4, 6, 8):
                re, im, k = guarded(c, n, g, False)
                score(f'guard {g}, whole turn', re, im, tre, tim, k)
            for g in (0, 1, 2, 3, 4):
                re, im, k = guarded(c, n, g, True)
                score(f'guard {g}, folded to an octant', re, im, tre, tim, k)
    print(f'angles read {angles} over periods {periods}')
    print('route\tangles\tlargest distance (grains of 2^-30)\toff the nearest face\tmost terms')
    for key, (cnt, d, off, k) in rows.items():
        print(f'{key}\t{cnt}\t{float(d):.3f}\t{off}\t{k}')

main()
