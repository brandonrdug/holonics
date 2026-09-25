# C2(a): the first design's case (5) under the projector it actually stated: the spectral (Bezout)
# projector onto the critical invariant subspace along the stable one.  Computed independently of
# the review's Sylvester solve: P_crit = b(T) chi_S(T), with a chi_P + b chi_S = 1 over Q[x].
from fractions import Fraction as F
import random

def bits(x): return x.numerator.bit_length() + x.denominator.bit_length()

# polynomials: lists of coefficients, lowest degree first
def trim(p):
    while len(p) > 1 and p[-1] == 0: p = p[:-1]
    return p
def padd(p, q):
    n = max(len(p), len(q)); return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])
def pmul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q): r[i + j] += a * b
    return trim(r)
def pdivmod(p, q):
    p = trim([F(x) for x in p]); q = trim([F(x) for x in q]); out = [F(0)] * max(1, len(p) - len(q) + 1)
    while len(p) >= len(q) and any(p):
        c = p[-1] / q[-1]; d = len(p) - len(q); out[d] = c
        p = trim(padd(p, [0] * d + [-c * x for x in q]))
        if len(p) < len(q): break
    return trim(out), p
def egcd(a, b):  # returns (g, s, t) with s a + t b = g
    r0, r1, s0, s1, t0, t1 = a, b, [F(1)], [F(0)], [F(0)], [F(1)]
    while any(r1):
        q, r = pdivmod(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, padd(s0, [-x for x in pmul(q, s1)])
        t0, t1 = t1, padd(t0, [-x for x in pmul(q, t1)])
    c = r0[-1]
    return [x / c for x in r0], [x / c for x in s0], [x / c for x in t0]

n = 7
Pm = [[1 if j == (i + 1) % 5 else 0 for j in range(5)] for i in range(5)]
S = [[F(1, 3), F(1, 4)], [F(-1, 4), F(1, 3)]]
C = [[F(1, 2), 0, 0, 0, 0], [0, 0, F(1, 2), 0, 0]]
T = [[F(0)] * n for _ in range(n)]
for i in range(5):
    for j in range(5): T[i][j] = F(Pm[i][j])
for i in range(2):
    for j in range(5): T[5 + i][j] = F(C[i][j])
    for j in range(2): T[5 + i][5 + j] = S[i][j]
chiP = [F(-1), 0, 0, 0, 0, F(1)]                                   # x^5 - 1
tr = S[0][0] + S[1][1]; det = S[0][0] * S[1][1] - S[0][1] * S[1][0]
chiS = [det, -tr, F(1)]
g, a, b = egcd(chiP, chiS)
assert g == [F(1)]
def mat_mul(A, B): return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def poly_at(p):
    R = [[F(0)] * n for _ in range(n)]; Pw = [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]
    for c in p:
        R = [[R[i][j] + c * Pw[i][j] for j in range(n)] for i in range(n)]; Pw = mat_mul(Pw, T)
    return R
Pc = poly_at(pmul(b, chiS))
assert mat_mul(Pc, Pc) == Pc and mat_mul(Pc, T) == mat_mul(T, Pc)
print("Bezout projector: idempotent, commutes with T; max entry bits", max(bits(x) for r in Pc for x in r))

def step(x): return [sum(T[i][j] * x[j] for j in range(n)) for i in range(n)]
def run(mode, epochs=256, aeon=8):
    random.seed(7); x = [F(0)] * n; rec = []
    for e in range(1, epochs + 1):
        x = step(x); x[random.randint(0, 4)] += 1; x[5] += F(1)
        if aeon and e % aeon == 0 and mode == 'bezout':
            x = [sum(Pc[i][j] * x[j] for j in range(n)) for i in range(n)]
        rec.append(max(bits(v) for v in x))
    return rec
for mode in ('none', 'bezout'):
    r = run(mode)
    print(mode, "max bits at epochs 8, 32, 128, 256:", [r[i - 1] for i in (8, 32, 128, 256)], " max over run:", max(r))
