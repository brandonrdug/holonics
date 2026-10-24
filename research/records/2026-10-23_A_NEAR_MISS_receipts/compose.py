"""Exact checks of the two composition identities in Epime's note, on rational data.

1. Defect composition. With a coarse reading q, fine operators T_a, T_b and coarse operators
   S_a, S_b, the defect D_a = q T_a - S_a q composes as
   q T_b T_a - S_b S_a q = D_b T_a + S_b D_a  (an identity of the matrix ring).
   Its additive instance (q = winding, T_a = +a, S_a = +floor(a/n)) is the carry cocycle
   carry(x, a) + carry(x + a, b) = carry(a, b) + carry(x, a + b)  (winding.carry-cocycle).
2. Learned-face return. A face mixture m = sum_i p_i phi_i with p on the simplex returns
   dz_i = p_i Re<g, phi_i - m>, which is norm.laplacian-return J delta with delta_i = Re<g, phi_i>.
Fractions throughout; complex values are Gaussian rationals (pairs).
"""
from fractions import Fraction as Fr
import itertools, json

def mat(rows): return [[Fr(x) for x in r] for r in rows]
def mul(A, B): return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def sub(A, B): return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]
def add(A, B): return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]

# deterministic rational data (no RNG): a 2-from-4 reading and two non-commuting fine operators
q  = mat([[1, 1, 0, 0], [0, 0, 1, 1]])
Ta = mat([[1, 2, 0, 1], [0, 1, 3, 0], [1, 0, 1, 2], [2, 1, 0, 1]])
Tb = mat([[0, 1, 1, 0], [1, 0, 0, 2], [3, 1, 1, 0], [0, 2, 1, 1]])
Sa = mat([[Fr(3, 2), Fr(1, 2)], [Fr(1, 2), Fr(5, 2)]])
Sb = mat([[1, Fr(3, 2)], [Fr(5, 2), Fr(3, 2)]])
Da = sub(mul(q, Ta), mul(Sa, q))
Db = sub(mul(q, Tb), mul(Sb, q))
lhs = sub(mul(q, mul(Tb, Ta)), mul(mul(Sb, Sa), q))
rhs = add(mul(Db, Ta), mul(Sb, Da))
out = {"defect composition holds": lhs == rhs, "Da nonzero": any(any(r) for r in Da)}

# carry cocycle over every x, a, b in 0..99, n = 10
n = 10
carry = lambda x, y: (x % n + y % n) // n
out["carry cocycle holds (0..99)^3"] = all(
    carry(x, a) + carry(x + a, b) == carry(a, b) + carry(x, a + b)
    for x, a, b in itertools.product(range(100), repeat=3))
# and the composite carry: floor((x+a+b)/n) = floor(x/n) + floor(a/n) + floor(b/n) + carry(x,a) + carry(x+a,b)
out["carry composes along the passage"] = all(
    (x + a + b) // n == x // n + a // n + b // n + carry(x, a) + carry(x + a, b)
    for x, a, b in itertools.product(range(100), repeat=3))

# learned-face return on Gaussian rationals
def cmul_conj_re(g, z):  # Re<g, z> = Re(conj(g) z)
    return g[0] * z[0] + g[1] * z[1]
p   = [Fr(1, 6), Fr(1, 3), Fr(1, 2)]
phi = [(Fr(1), Fr(0)), (Fr(0), Fr(1)), (Fr(-1), Fr(1, 2))]
g   = (Fr(2, 3), Fr(-1, 4))
m = (sum(pi * f[0] for pi, f in zip(p, phi)), sum(pi * f[1] for pi, f in zip(p, phi)))
ret = [pi * cmul_conj_re(g, (f[0] - m[0], f[1] - m[1])) for pi, f in zip(p, phi)]
delta = [cmul_conj_re(g, f) for f in phi]
Ep = sum(pi * d for pi, d in zip(p, delta))
lap = [pi * (d - Ep) for pi, d in zip(p, delta)]
out["face return = Laplacian return"] = ret == lap
out["face return sums to zero (gauge)"] = sum(ret) == 0
out["face return"] = [str(r) for r in ret]
print(json.dumps(out, indent=1))
