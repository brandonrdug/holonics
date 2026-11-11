#!/usr/bin/env python3
"""Check: the skin's exponent across a variation is a difference of two site addresses with one carry.

The law (the host's skin_of):  bits(i, j) = div_nearest(2 pi |sigma_i - sigma_j|, k),  k = n ln2 2^24,
div_nearest(x, k) = (x + k // 2) // k for x >= 0.
The site form:  2 pi sigma_x = q_x k + r_x, 0 <= r_x < k (once a site);  for sigma_i >= sigma_j:
Q = q_i - q_j, R = r_i - r_j;  R < 0: Q -= 1, R += k;  bits = Q + (R + k // 2 >= k).
Integers only; any positive pi and k."""
import random

def law(pi, k, si, sj):
    return (2 * pi * abs(si - sj) + k // 2) // k

def site(pi, k, s):
    return divmod(2 * pi * s, k)          # floor division: 0 <= r < k for a signed s

def pair(k, a, b, si, sj):
    if si < sj:
        a, b = b, a
    Q, R = a[0] - b[0], a[1] - b[1]
    if R < 0:
        Q, R = Q - 1, R + k
    return Q + (1 if R + k // 2 >= k else 0)

random.seed(7)
PI = round(3.141592653589793238462643 * 2 ** 46)
LN2 = round(0.693147180559945309417232 * 2 ** 30)
checked = 0
for trial in range(400000):
    if trial % 4 == 0:
        pi, k = random.randrange(1, 2 ** 50), random.randrange(1, 2 ** 64)
    else:
        pi, k = PI, (random.choice([2, 3, 5, 7, 11, 16, 33, 77, 231, 2541, random.randrange(2, 4096)]) * LN2) << 24
    span = random.choice([2 ** 10, 2 ** 24, 2 ** 30, 2 ** 40, 2 ** 44])
    si, sj = random.randrange(-span, span), random.randrange(-span, span)
    if trial % 50 == 0:
        sj = si
    if trial % 53 == 0:                    # ties and near-ties of the rounding
        m = random.randrange(0, 2 ** 20)
        si, sj = m, 0
    assert law(pi, k, si, sj) == pair(k, site(pi, k, si), site(pi, k, sj), si, sj), (pi, k, si, sj)
    checked += 1
# exhaustive on small numbers (every tie)
for pi in range(1, 7):
    for k in range(1, 40):
        for si in range(-30, 31):
            for sj in range(-30, 31):
                assert law(pi, k, si, sj) == pair(k, site(pi, k, si), site(pi, k, sj), si, sj)
                checked += 1
print("pairs checked", checked, "all equal")
