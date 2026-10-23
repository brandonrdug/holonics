"""Exact checks of the local fluid reading (rational arithmetic).
1. z -> a z + b conj(z) as a real 2x2 matrix M: tr(M^T M) = 2(|a|^2 + |b|^2) and
   det(M^T M) = (|a|^2 - |b|^2)^2, so its singular values are |a| + |b| and ||a| - |b||.
2. A velocity gradient J = [[u_x, u_y], [v_x, v_y]] has direct part a = (div + i w)/2 and reflected
   part b = (s_n + i s_s)/2 with J = matrix of z -> a z + b conj(z); with no divergence
   det J = -W/4, W = s_n^2 + s_s^2 - w^2 (Okubo-Weiss).
3. The Swing's generators: rotation W < 0, squeeze W > 0, shear W = 0.
4. The look L(h) = a h + b conj(h) + c with |a| + |b| < 1 reaches its fixed point: the distance after
   each lap is at most rho times the distance before."""
from fractions import Fraction as F
import itertools, json

def mat(a, b):  # a, b as (re, im); z = x + i y
    ar, ai = a; br, bi = b
    return [[ar + br, -ai + bi], [ai + bi, ar - br]]
def mul(A, B): return [[sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def T(A): return [[A[j][i] for j in range(2)] for i in range(2)]
def det(A): return A[0][0] * A[1][1] - A[0][1] * A[1][0]
def n2(a): return a[0] ** 2 + a[1] ** 2

vals = [F(n, 3) for n in range(-4, 5)]
checks1 = 0
for ar, ai, br, bi in itertools.product(vals, repeat=4):
    M = mat((ar, ai), (br, bi)); G = mul(T(M), M)
    assert G[0][0] + G[1][1] == 2 * (n2((ar, ai)) + n2((br, bi)))
    assert det(G) == (n2((ar, ai)) - n2((br, bi))) ** 2
    assert det(M) == n2((ar, ai)) - n2((br, bi))
    checks1 += 1

checks2 = 0
for ux, uy, vx, vy in itertools.product(vals, repeat=4):
    div, w = ux + vy, vx - uy; sn, ss = ux - vy, vx + uy
    a, b = (div / 2, w / 2), (sn / 2, ss / 2)
    assert mat(a, b) == [[ux, uy], [vx, vy]]
    if div == 0:
        assert det([[ux, uy], [vx, vy]]) == -(sn ** 2 + ss ** 2 - w ** 2) / 4
    checks2 += 1

def W(J):
    ux, uy, vx, vy = J[0][0], J[0][1], J[1][0], J[1][1]
    return (ux - vy) ** 2 + (vx + uy) ** 2 - (vx - uy) ** 2
swing = {"rotation (turn)": W([[0, -1], [1, 0]]), "squeeze (boost)": W([[1, 0], [0, -1]]),
         "shear (free fall)": W([[0, 1], [0, 0]])}

# 4. the look settles: exact rational iteration on a contracting word
def L(h, a, b, c):
    (hr, hi), (ar, ai), (br, bi), (cr, ci) = h, a, b, c
    return (ar * hr - ai * hi + br * hr + bi * hi + cr, ai * hr + ar * hi + bi * hr - br * hi + ci)
a, b, c = (F(1, 2), F(1, 4)), (F(1, 8), F(-1, 8)), (F(3), F(-2))
# rho = |a| + |b| < 1: |a|^2 = 5/16, |b|^2 = 1/32, so |a| + |b| < 0.56 + 0.18 < 1
M = mat(a, b); I = [[1, 0], [0, 1]]
A = [[I[i][j] - M[i][j] for j in range(2)] for i in range(2)]; d = det(A)
hstar = ((A[1][1] * c[0] - A[0][1] * c[1]) / d, (-A[1][0] * c[0] + A[0][0] * c[1]) / d)
assert L(hstar, a, b, c) == hstar
h = (F(0), F(0)); dist2 = []
for _ in range(12):
    dist2.append((h[0] - hstar[0]) ** 2 + (h[1] - hstar[1]) ** 2); h = L(h, a, b, c)
rho2_bound = (n2(a) + n2(b)) * 2  # (|a| + |b|)^2 <= 2(|a|^2 + |b|^2)
assert all(dist2[k + 1] <= rho2_bound * dist2[k] for k in range(11))
out = dict(singular_value_checks=checks1, velocity_gradient_checks=checks2,
           swing_okubo_weiss={k: str(v) for k, v in swing.items()},
           look_fixed_point=[str(hstar[0]), str(hstar[1])],
           look_distance_squared=[str(x) for x in dist2], rho_squared_bound=str(rho2_bound))
print(json.dumps(out, indent=1))
json.dump(out, open('look.json', 'w'), indent=1)
