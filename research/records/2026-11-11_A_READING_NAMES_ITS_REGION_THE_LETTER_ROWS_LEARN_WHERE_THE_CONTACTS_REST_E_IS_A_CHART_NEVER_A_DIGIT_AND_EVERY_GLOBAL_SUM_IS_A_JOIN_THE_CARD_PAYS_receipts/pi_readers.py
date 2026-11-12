"""How wide pi must be for the field's readers: the closest cut among the ring angles, and the least width of pi
(held at its nearest on 2^-(30+k)) at which every angle face on 2^-30 is still the nearest. A host ruler."""
import math
from fractions import Fraction
from pi_cuts import half_turn, release, div_nearest, nearest, PI, periods, reach

gaps = []
faces = []
for n in periods:
    for r in range(min(n, reach)):
        c = r - n if 2 * r > n else r
        if c == 0 or 2 * c == n or 4 * c == n or 4 * c == -n:
            continue
        q = Fraction(2 * c, n) * PI * (1 << 30)
        f = q - (q.numerator // q.denominator)
        gaps.append((abs(f - Fraction(1, 2)), n, r))
        faces.append((n, c, nearest(q)))
gaps.sort()
g, n, r = gaps[0]
print(f"ANGLE_CLOSEST gap_from_half={float(g):.3e} of a unit of 2^-30 ({-math.log2(float(g)):.1f} bits) at ring {n} residue {r}; next {float(gaps[1][0]):.3e} at ring {gaps[1][1]}")
for k in range(0, 17):
    pik = nearest(PI * (1 << (30 + k)))          # pi held at its nearest on 2^-(30+k)
    bad = sum(1 for (n, c, t) in faces if release(div_nearest(2 * pik * c, n), k) != t)
    print(f"PI_WIDTH extra_bits={k} angle_faces_not_nearest={bad} of {len(faces)}")
    if bad == 0:
        break
