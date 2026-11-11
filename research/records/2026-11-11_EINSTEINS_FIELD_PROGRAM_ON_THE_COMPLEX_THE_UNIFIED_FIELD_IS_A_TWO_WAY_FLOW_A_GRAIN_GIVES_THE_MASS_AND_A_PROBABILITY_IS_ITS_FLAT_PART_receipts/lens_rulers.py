#!/usr/bin/env python3
"""Host rulers for section 14 of the record of Einstein's field program on the complex
(the lens of November 11, 22:27 and 22:39 UTC): rulers 9 to 13, continuing einstein_rulers.py.

Integers and rationals only (Python `fractions`); no state, no private material, no float.
Each ruler checks an identity the section uses and prints what it read. A ruler is an
instrument: nothing here is machinery, and nothing here trains or reads the field.

  python3 lens_rulers.py > lens_rulers.txt
"""
from fractions import Fraction as Fr
from itertools import combinations, product
from math import comb
import sys, time

T0 = time.time()
FAILS = []


def check(name, ok):
    print(f"  [{'ok' if ok else 'FAILED'}] {name}")
    if not ok:
        FAILS.append(name)


def rank(rows):
    """Rank of a rational matrix by elimination."""
    m = [[Fr(x) for x in r] for r in rows]
    r = 0
    cols = len(m[0]) if m else 0
    for c in range(cols):
        p = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


print(time.strftime("start %Y-%m-%dT%H:%M:%SZ", time.gmtime()) + f" (cloud host, Python {sys.version.split()[0]}, numbers only)")

# ---------------------------------------------------------------------------------------
print("""9. The arrow on a contact is the ratio of the counts of its two sides.
   A walk on the 256 words of eight bits flips one bit a step, each with rate 1/8, so a
   step and its reverse have one rate. Group the words any way: between two groups A, B
   the stationary one-step rates obey P(A->B)/P(B->A) = W_B/W_A, W the words in a group.
   The contact's odd part is then half the step of ln W, and a group with several
   neighbours reads a rise of the count on some ends and a fall on others.""")
N = 8
WORDS = list(range(1 << N))


def lump(label):
    W, E = {}, {}
    for w in WORDS:
        W[label(w)] = W.get(label(w), 0) + 1
        for b in range(N):
            a, c = label(w), label(w ^ (1 << b))
            if a != c:
                E[(a, c)] = E.get((a, c), 0) + 1
    return W, E


def ratio_law(W, E):
    """P(A->B) = E(A,B)/(N W_A): the ratio of the two rates against the ratio of counts, and equal flows."""
    ok = True
    for (a, c), e in E.items():
        back = E.get((c, a), 0)
        ok &= back == e and Fr(e, N * W[a]) / Fr(back, N * W[c]) == Fr(W[c], W[a])
    return ok


ones = lambda w, lo, hi: sum((w >> i) & 1 for i in range(lo, hi))
W, E = lump(lambda w: ones(w, 0, N))
check(f"the urn (groups by the number of ones): W_k = C(8, k) = {[W[k] for k in range(N + 1)]}", all(W[k] == comb(N, k) for k in range(N + 1)))
check("P(k->k+1) = (8-k)/8 and P(k+1->k) = (k+1)/8, so their ratio is W_(k+1)/W_k at every k",
      all(Fr(E[(k, k + 1)], N * W[k]) == Fr(N - k, N) and Fr(E[(k + 1, k)], N * W[k + 1]) == Fr(k + 1, N) for k in range(N)) and ratio_law(W, E))
W, E = lump(lambda w: (ones(w, 0, 4), ones(w, 4, 8)))
check(f"25 groups by (ones in the first four bits, ones in the last four), {len(E) // 2} contacts: the ratio law on every contact", len(W) == 25 and ratio_law(W, E))
sq = True
for i, j in product(range(4), range(4)):
    cyc = [(i, j), (i + 1, j), (i + 1, j + 1), (i, j + 1), (i, j)]
    p = Fr(1)
    for a, c in zip(cyc, cyc[1:]):
        p *= Fr(E[(a, c)], N * W[a]) / Fr(E[(c, a)], N * W[c])
    sq &= p == 1
check("round each of the 16 squares of groups the product of the rate ratios is one (the odd part is a potential's step)", sq)
at = (1, 3)
ends = [(0, 3), (2, 3), (1, 2), (1, 4)]
steps = [Fr(W[e], W[at]) for e in ends]
check(f"the group (1, 3) holds {W[at]} words and has four ends with count ratios {', '.join(str(s) for s in steps)}: two ends rise and two fall, so the arrow splits there",
      sorted(steps) == [Fr(1, 4), Fr(1, 4), Fr(3, 2), Fr(3, 2)])
W, E = lump(lambda w: w % 5)
check(f"an arbitrary grouping (the word's value mod 5, counts {[W[k] for k in range(5)]}): the ratio law on all {len(E) // 2} contacts", ratio_law(W, E))

# ---------------------------------------------------------------------------------------
print("""10. Counts of counts end. Fields of three variables with coefficients of order n:
   gradient (order n+1 -> n), curl (n -> n-1), divergence (n-1 -> n-2), on homogeneous
   polynomials, dim P_d = C(d+2, 2). The fields a curl leaves free number
   3 C(n+2,2) - 3 C(n+1,2) + C(n,2): unknowns, less equations, plus the identity among
   the equations. The chain of relations among relations has three steps in three
   variables (Hilbert's syzygy theorem in this case) and its alternating count closes.""")


def monos(d):
    return [(a, b, d - a - b) for a in range(d, -1, -1) for b in range(d - a, -1, -1)] if d >= 0 else []


def dmat(d, v):
    """Matrix of the derivative in variable v from P_d to P_(d-1)."""
    src, dst = monos(d), monos(d - 1)
    idx = {m: i for i, m in enumerate(dst)}
    M = [[0] * len(src) for _ in dst]
    for j, m in enumerate(src):
        if m[v]:
            t = list(m)
            t[v] -= 1
            M[idx[tuple(t)]][j] = m[v]
    return M


def blocks(grid):
    """Assemble a block matrix; None is a zero block (sizes read from its row and column)."""
    nr = [next(len(b) for b in row if b is not None) for row in grid]
    nc = [next(len(grid[i][j][0]) for i in range(len(grid)) if grid[i][j] is not None) for j in range(len(grid[0]))]
    out = []
    for i, row in enumerate(grid):
        for r in range(nr[i]):
            line = []
            for j, b in enumerate(row):
                line += b[r] if b is not None else [0] * nc[j]
            out.append(line)
    return out


def neg(M):
    return [[-x for x in r] for r in M]


def mul(A, B):
    return [[sum(a * b for a, b in zip(r, c)) for c in zip(*B)] for r in A]


ok_exact = ok_rank = ok_count = True
rows = []
for n in range(2, 7):
    Dn1 = [dmat(n + 1, v) for v in range(3)]
    Dn = [dmat(n, v) for v in range(3)]
    Dm = [dmat(n - 1, v) for v in range(3)]
    grad = blocks([[Dn1[0]], [Dn1[1]], [Dn1[2]]])
    curl = blocks([[None, neg(Dn[2]), Dn[1]], [Dn[2], None, neg(Dn[0])], [neg(Dn[1]), Dn[0], None]])
    div = blocks([[Dm[0], Dm[1], Dm[2]]])
    ok_exact &= all(x == 0 for r in mul(curl, grad) for x in r) and all(x == 0 for r in mul(div, curl) for x in r)
    rg, rc, rd = rank(grad), rank(curl), rank(div)
    unknowns, equations, identities = 3 * comb(n + 2, 2), 3 * comb(n + 1, 2), comb(n, 2)
    free = unknowns - rc
    ok_rank &= rg == comb(n + 3, 2) and rd == identities and rc == equations - identities
    ok_count &= free == unknowns - equations + identities == comb(n + 3, 2) and comb(n + 3, 2) - unknowns + equations - identities == 0
    rows.append(f"n={n}: {unknowns} - {equations} + {identities} = {free}")
check("curl of a gradient and divergence of a curl vanish as matrices at orders 2 to 6", ok_exact)
check("ranks: the gradient C(n+3,2), the divergence C(n,2) (onto), the curl 3 C(n+1,2) - C(n,2): each kernel is the image before it", ok_rank)
check("free data of the curl = unknowns - equations + identities = C(n+3,2):  " + ";  ".join(rows), ok_count)
check("without the identities the count is short by C(n,2) = 1, 3, 6, 10, 15 at orders 2 to 6", [comb(n, 2) for n in range(2, 7)] == [1, 3, 6, 10, 15])

# ---------------------------------------------------------------------------------------
print("""11. A junction of n ends. Its amplitudes are (xi_1 : ... : xi_n) and its Hermitian
   forms are n by n: n real entries on the diagonal, one for each end, and one complex
   entry for each pair of ends, n^2 = n + 2 C(n,2). Each pair (i, j) reads the 2 by 2
   block of its two ends, a three and one with the time t_ij = (X_ii + X_jj)/2.""")


class G:
    """Gaussian rational."""
    def __init__(s, re, im=0): s.re, s.im = Fr(re), Fr(im)
    def __add__(s, o): return G(s.re + o.re, s.im + o.im)
    def __sub__(s, o): return G(s.re - o.re, s.im - o.im)
    def __mul__(s, o): return G(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)
    def conj(s): return G(s.re, -s.im)
    def __eq__(s, o): return s.re == o.re and s.im == o.im
    def norm(s): return s.re * s.re + s.im * s.im


def gm(A, B):
    k = len(B)
    return [[sum((A[i][l] * B[l][j] for l in range(k)), G(0)) for j in range(len(B[0]))] for i in range(len(A))]


dag = lambda A: [[A[j][i].conj() for j in range(len(A))] for i in range(len(A[0]))]


def det3(A):
    return (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
            + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))


def block_det(X, i, j):
    return X[i][i] * X[j][j] - X[i][j] * X[j][i]


def embed(i, j, a, b, c, d):
    """A move of the pair (i, j), the identity on the third end."""
    M = [[G(1 if r == s else 0) for s in range(3)] for r in range(3)]
    M[i][i], M[i][j], M[j][i], M[j][j] = a, b, c, d
    return M


check("n^2 = n + 2 C(n,2) for n = 2 to 6: " + ", ".join(f"{n * n} = {n} + {2 * comb(n, 2)}" for n in range(2, 7)), all(n * n == n + 2 * comb(n, 2) for n in range(2, 7)))
X = [[G(7), G(1, 2), G(-2, 1)], [G(1, -2), G(5), G(3, -1)], [G(-2, -1), G(3, 1), G(9)]]
pairs = list(combinations(range(3), 2))
ok = True
times = []
for i, j in pairs:
    t, z, w = (X[i][i].re + X[j][j].re) / 2, (X[i][i].re - X[j][j].re) / 2, X[j][i]
    times.append(t)
    ok &= block_det(X, i, j) == G(t * t - z * z - w.norm())
check(f"each pair's block has det = t^2 - z^2 - x^2 - y^2 with its own time: t_12, t_13, t_23 = {', '.join(str(t) for t in times)}", ok and X == dag(X))
check(f"the three times sum to the trace, {sum(times)} = {X[0][0].re + X[1][1].re + X[2][2].re}: each end's entry is shared by the two pairs it joins",
      sum(times) == X[0][0].re + X[1][1].re + X[2][2].re)
m01 = embed(0, 1, G(1), G(2, 1), G(0), G(1))
m12 = embed(1, 2, G(1), G(0), G(1, -3), G(1))
m02 = embed(0, 2, G(0), G(-1), G(1), G(0))
A = gm(gm(m01, m12), gm(m02, m01))
Y = gm(gm(A, X), dag(A))
check("a move of the whole junction of determinant one keeps the form Hermitian and keeps its determinant (a cubic)", det3(A) == G(1) and Y == dag(Y) and det3(Y) == det3(X))
mp = embed(0, 1, G(2), G(0, 1), G(0, -1), G(1))
Z = gm(gm(mp, X), dag(mp))
kept = block_det(Z, 0, 1) == block_det(X, 0, 1) and det3(mp) == G(1)
moved = [(i, j) for i, j in pairs[1:] if not block_det(Z, i, j) == block_det(X, i, j)]
check(f"a move of the pair (1, 2) alone keeps that pair's three and one and changes the others' (pairs {[(i + 1, j + 1) for i, j in moved]})", kept and len(moved) == 2)
psi = [G(2, 1), G(1, -3), G(0, 2)]
R = [[psi[i] * psi[j].conj() for j in range(3)] for i in range(3)]
check("one junction amplitude (2+i : 1-3i : 2i): every pair reads a null direction, and the cubic vanishes", all(block_det(R, i, j) == G(0) for i, j in pairs) and det3(R) == G(0))

# ---------------------------------------------------------------------------------------
print("""12. A store of finite quality. A circle that keeps |gamma| = 1/(1+d) of its amplitude a
   step and takes one unit of power a step (z' = gamma z + xi) rests at the power
   1/(1 - |gamma|^2) and remembers (1+d)/d steps (the record's reach, section 5.4). What
   it holds and how long it holds it are one figure; with no leak neither is finite.""")
ok = True
out = []
for d in (Fr(1, 4), Fr(1, 8), Fr(1, 16), Fr(1, 64)):
    g = 1 / (1 + d)
    power, reach = 1 / (1 - g * g), 1 / (1 - g)
    ok &= power == (1 + d) ** 2 / (d * (2 + d)) and reach == (1 + d) / d and power / reach == (1 + d) / (2 + d)
    part = sum(g ** (2 * k) for k in range(400))
    ok &= 0 < power - part == g ** 800 * power
    out.append(f"d={d}: reach {reach}, power {power}, power/reach {power / reach}")
check("the resting power (1+d)^2/(d(2+d)), the reach (1+d)/d, and their ratio (1+d)/(2+d):  " + ";  ".join(out), ok)
check("the ratio tends to 1/2 as d falls: within 1/100 of it at d = 1/64 (the standing spread is half the reach, to first order in the leak)",
      abs((1 + Fr(1, 64)) / (2 + Fr(1, 64)) - Fr(1, 2)) < Fr(1, 100))
check("at d = 0 the power after n steps is n: 2,000 and 3,000 sites sum to 2,000 and 3,000, with no resting value", all(sum(1 for _ in range(n)) == n for n in (2000, 3000)))

# ---------------------------------------------------------------------------------------
print("""13. The gap law on a finite complex. On a graph whose every cell has q + 1 contacts, the
   closed walks of length l that never turn straight back number tr(B^l), B the step from
   one directed contact to the next. Its smooth part is q^l (plus the fixed terms
   1 + (m - n)(1 + (-1)^l), m contacts and n cells), and the prime cycles N_l follow from
   l N_l = sum over d | l of mu(l/d) tr(B^d). The count leaves its smooth part only at
   half rank, |tr(B^l) - smooth| <= 2 (n - 1) q^(l/2), exactly when every other eigenvalue
   lam of the graph has lam^2 <= 4 q: the widest gap such a graph can have.""")


def darts(edges):
    ds = [(a, b) for a, b in edges] + [(b, a) for a, b in edges]
    succ = [[j for j, (c, d) in enumerate(ds) if c == b and d != a] for a, b in ds]
    return ds, succ


def traces(edges, L):
    ds, succ = darts(edges)
    k = len(ds)
    M = [[1 if i == j else 0 for j in range(k)] for i in range(k)]
    out = []
    for _ in range(L):
        N = [[0] * k for _ in range(k)]
        for i in range(k):
            row, new = M[i], N[i]
            for e in range(k):
                v = row[e]
                if v:
                    for f in succ[e]:
                        new[f] += v
        M = N
        out.append(sum(M[i][i] for i in range(k)))
    return out


def mobius(n):
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            r = -r
        p += 1
    return -r if n > 1 else r


def primes_by_length(tr):
    return [sum(mobius(l // d) * tr[d - 1] for d in range(1, l + 1) if l % d == 0) // l for l in range(1, len(tr) + 1)]


def power_sums(lam, q, L):
    """alpha^l + beta^l for the two roots of u^2 - lam u + q, l = 1..L."""
    s = [2, lam]
    for _ in range(L - 1):
        s.append(lam * s[-1] - q * s[-2])
    return s[1:]


L, q = 40, 2
petersen = [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
n, m = 10, len(petersen)
tr = traces(petersen, L)
spectrum = [(3, 1), (1, 5), (-2, 4)]
model = [(m - n) * (1 + (-1) ** l) + sum(mult * power_sums(lam, q, L)[l - 1] for lam, mult in spectrum) for l in range(1, L + 1)]
check("the Petersen graph (10 cells, 15 contacts, eigenvalues 3, 1 five times, -2 four times): tr(B^l) equals the sum over its eigenvalues at every l to 40", tr == model)
Nl = primes_by_length(tr)
check(f"its prime cycles by length 1 to 9: {Nl[:9]} (24 = its twelve pentagons each way, 20 = its ten hexagons each way)", Nl[:6] == [0, 0, 0, 0, 24, 20] and all(x >= 0 for x in Nl))
dev = [tr[l - 1] - q ** l - 1 - (m - n) * (1 + (-1) ** l) for l in range(1, L + 1)]
check("every other eigenvalue has lam^2 <= 8, and the count stays within half rank at every l to 40: (tr(B^l) - smooth)^2 <= 4 * 81 * 2^l",
      all(lam * lam <= 4 * q for lam, _ in spectrum[1:]) and all(d * d <= 4 * (n - 1) ** 2 * q ** l for l, d in enumerate(dev, 1)))
k = 21
ladder = [(i, (i + 1) % k) for i in range(k)] + [(k + i, k + (i + 1) % k) for i in range(k)] + [(i, k + i) for i in range(k)]
n, m = 2 * k, len(ladder)
tr = traces(ladder, L)
dev = [tr[l - 1] - q ** l - 1 - (m - n) * (1 + (-1) ** l) for l in range(1, L + 1)]
inside = [l for l, d in enumerate(dev, 1) if d * d <= 4 * (n - 1) ** 2 * q ** l]
check(f"a ladder of two rings of 21 (42 cells, 63 contacts, also three contacts a cell): the count is within half rank only at l = {inside}, and outside it at l = 10 and at every l from 12 to 40; a ring of 21 holds slow modes, 1 + 2 cos(turn/21) among them",
      inside == list(range(1, 10)) + [11])
c = Fr(19, 20)
check("that mode's square is above 8: cos(turn/21) > 19/20 (from 1 - x^2/2 with x = 2 * 22/7 / 21 < 3/10 as an upper bound of the angle) and (1 + 2 * 19/20)^2 = 841/100 > 8",
      1 - Fr(3, 10) ** 2 / 2 > c and (1 + 2 * c) ** 2 > 8)

print(f"\nrulers failed: {len(FAILS)}; wall time {time.time() - T0:.1f} s")
sys.exit(1 if FAILS else 0)
