# C2: once the change is released at every word's end, what accumulates bits across words is the
# deposited constitution.  Exact per-locus normal law  H += f f*,  B += (W f + gamma g) f*,  W H = B,
# unit prior H0 = I, B0 = 0.  The word is a fixed exact rational operator T (its denominators are
# those of the Cayley and contact solves); sources are integer counts m; targets one-hot.
#  (i)  the receiving map R deposited, features f = T E m (R is not an operand of its own feature)
#  (ii) the source port E deposited, features m (E is an operand of the word that makes its covector)
import random
from fractions import Fraction as F

def bits(x): return x.numerator.bit_length() + x.denominator.bit_length()
def mbits(M): return max(bits(x) for r in M for x in r)
def solve(A, b):
    n = len(A); M = [list(r) + [b[i]] for i, r in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0); M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                q = M[r][c] / M[c][c]; M[r] = [a - q * bb for a, bb in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]
def right_solve(B, H):  # W with W H = B  (H symmetric)
    return [solve(H, row) for row in B]
def mv(A, x): return [sum(a * b for a, b in zip(r, x)) for r in A]
def mt(A): return [list(c) for c in zip(*A)]

rng = random.Random(3)
A_, d, o = 3, 4, 3                      # alphabet, ring width, receiver outputs
T = [[F(rng.randint(-5, 5), rng.choice([7, 9, 13, 16, 25])) for _ in range(d)] for _ in range(d)]
E0 = [[F(rng.randint(-2, 2), rng.randint(1, 3)) for _ in range(A_)] for _ in range(d)]
R0 = [[F(rng.randint(-2, 2), rng.randint(1, 3)) for _ in range(d)] for _ in range(o)]
samples = []
for _ in range(256):
    m = [F(rng.randint(0, 4)) for _ in range(A_)]
    q = [F(0)] * o; q[rng.randrange(o)] = F(1)
    samples.append((m, q))

def deposit_R(gamma):
    H = [[F(1) if i == j else F(0) for j in range(d)] for i in range(d)]
    B = [[F(0)] * d for _ in range(o)]
    R = [row[:] for row in R0]; out = {}
    for n, (m, q) in enumerate(samples, 1):
        f = mv(T, mv(E0, m)); y = mv(R, f); g = [qi - yi for qi, yi in zip(q, y)]
        H = [[H[i][j] + f[i] * f[j] for j in range(d)] for i in range(d)]
        t = [y[i] + gamma * g[i] for i in range(o)]
        B = [[B[i][j] + t[i] * f[j] for j in range(d)] for i in range(o)]
        R = right_solve(B, H)
        if n in (8, 32, 128, 256): out[n] = (mbits(R), mbits(H))
    return out

def deposit_E(gamma):
    H = [[F(1) if i == j else F(0) for j in range(A_)] for i in range(A_)]
    B = [[F(0)] * A_ for _ in range(d)]
    E = [row[:] for row in E0]; out = {}
    RT = [mv(mt(T), r) for r in R0]          # rows of R T
    for n, (m, q) in enumerate(samples, 1):
        x = mv(E, m); y = mv(R0, mv(T, x)); gy = [qi - yi for qi, yi in zip(q, y)]
        gx = [sum(RT[k][i] * gy[k] for k in range(o)) for i in range(d)]   # (R T)^T g at E's output
        H = [[H[i][j] + m[i] * m[j] for j in range(A_)] for i in range(A_)]
        t = [x[i] + gamma * gx[i] for i in range(d)]
        B = [[B[i][j] + t[i] * m[j] for j in range(A_)] for i in range(d)]
        E = right_solve(B, H)
        if n in (8, 32, 128): out[n] = (mbits(E), mbits(H))
        if n == 128: break
    return out

for gamma in (F(1), F(1, 2)):
    print(f"(i)  receiving map R, gamma={gamma}: (bits of R, bits of H) after 8, 32, 128, 256 deposits:", deposit_R(gamma))
for gamma in (F(1), F(1, 2)):
    print(f"(ii) source port E,   gamma={gamma}: (bits of E, bits of H) after 8, 32, 128 deposits:", deposit_E(gamma), flush=True)
