"""The ring faces' attainment error by its source: the angle's rounding alone (the exact exponential of the rounded
angle, rounded once) against the series' own term rounding; the largest error and the faces outside the unit disk."""
from fractions import Fraction
from pi_cuts import half_turn, release, div_nearest, nearest, PI, periods, reach
from ring_route import exp_series, cos_sin, MOVE

pi46 = half_turn(46, 16)
worst, outside, angle_only_off, hist = 0, 0, 0, {}
for n in periods:
    for r in range(min(n, reach)):
        c = r - n if 2 * r > n else r
        if c == 0 or 2 * c == n or 4 * c == n or 4 * c == -n:
            continue
        theta30 = release(div_nearest(2 * pi46 * c, n), 16)
        got = exp_series(0, theta30)
        cs, sn = cos_sin(Fraction(round(Fraction(2 * c, n) * PI * (1 << 120)), 1 << 120))
        want = (nearest(cs * (1 << MOVE)), nearest(sn * (1 << MOVE)))
        ca, sa = cos_sin(Fraction(theta30, 1 << MOVE))          # the rounded angle's exact exponential
        at_angle = (nearest(ca * (1 << MOVE)), nearest(sa * (1 << MOVE)))
        d = max(abs(got[0] - want[0]), abs(got[1] - want[1]))
        hist[d] = hist.get(d, 0) + 1
        worst = max(worst, d)
        if at_angle != want:
            angle_only_off += 1
        if got[0] ** 2 + got[1] ** 2 > 1 << (2 * MOVE):
            outside += 1
print("RING_ERR units_off:count", " ".join(f"{k}:{v}" for k, v in sorted(hist.items())), f"largest={worst}")
print(f"RING_ERR off_by_the_angle_rounding_alone={angle_only_off} outside_the_unit_disk={outside}")
