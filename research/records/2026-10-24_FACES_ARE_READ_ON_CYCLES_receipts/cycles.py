#!/usr/bin/env python3
"""Exact census for the record 2026-10-24 "faces are read on cycles".

Integers and Fractions only. Every test field is a declared integer formula; nothing is drawn.
Sections: A the carry is the Bockstein of the phase (ring and bits); B the seam class of language;
C the four blocks as Kunneth summands and the interaction rank of each face table; D the Hodge split
on a torus grid and viscosity keeping the harmonic part; E the HPP lattice gas, bitwise; F the
replicator's gradient and cycling parts.
"""
import json
import sys
from fractions import Fraction as Fr
from itertools import product

out = {}


def rank(rows):
    """Rank over Q by exact elimination."""
    m = [[Fr(v) for v in r] for r in rows]
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


# ---------------- A. the carry is the Bockstein of the phase ----------------
A = {}
for n in (2, 3, 10):
    G = range(n)
    car = lambda a, b: (a + b) // n
    cocycle = all(car(a, b) + car((a + b) % n, c) == car(b, c) + car(a, (b + c) % n)
                  for a in G for b in G for c in G)
    lap = sum(car(a, 1) for a in G)  # the binding read on the cycle a -> a + 1
    rational_coboundary = all(Fr(a, n) + Fr(b, n) - Fr((a + b) % n, n) == car(a, b) for a in G for b in G)
    n_times_integer_coboundary = all(a + b - (a + b) % n == n * car(a, b) for a in G for b in G)
    # every integer coboundary reads a multiple of n on the lap (checked over all b in {-1,0,1}^n for n <= 10)
    lap_of_coboundaries = set()
    for bvec in product((-1, 0, 1), repeat=n):
        lap_of_coboundaries.add(sum(bvec[a] + bvec[1] - bvec[(a + 1) % n] for a in G) - n * bvec[1])
    A[str(n)] = dict(cocycle=cocycle, lap=lap, rational_coboundary_of_phase=rational_coboundary,
                     n_times_carry_is_integer_coboundary=n_times_integer_coboundary,
                     integer_coboundary_lap_minus_n_b1=sorted(lap_of_coboundaries),
                     class_order=n if lap == 1 else None)

bits = {}
B8 = range(256)
maj = lambda x, y, z: (x & y) | (x & z) | (y & z)
bits["split_plus_twice_cocycle"] = all(a + b == (a ^ b) + 2 * (a & b) for a in B8 for b in B8)
ok = True
for a in B8:
    for b in B8:
        c, s = 0, 0
        for i in range(9):
            ai, bi = (a >> i) & 1, (b >> i) & 1
            s |= (ai ^ bi ^ c) << i
            c = maj(ai, bi, c)
        ok &= (s == a + b)
bits["ripple_with_majority_carry"] = ok
bits["pairs"] = 256 * 256


def plural_faces(op, k):
    seen = {}
    for a in B8:
        for b in B8:
            key = ((a >> k) & 1, (b >> k) & 1)
            seen.setdefault(key, set()).add((op(a, b) >> k) & 1)
    return sum(1 for v in seen.values() if len(v) > 1)


bits["bit_k_of_xor_plural"] = [plural_faces(lambda a, b: a ^ b, k) for k in range(8)]
bits["bit_k_of_sum_plural"] = [plural_faces(lambda a, b: a + b, k) for k in range(8)]
A["bits"] = bits
out["A_carry_bockstein"] = A

# ---------------- B. the seam class of language ----------------
L = "tha"
M = [None] + [(f, l) for f in L for l in L]


def mul(x, y):
    if x is None:
        return y
    if y is None:
        return x
    return (x[0], y[1])


def seam(x, y):
    return 1 if (x is not None and y is not None and x[1] == "t" and y[0] == "h") else 0


def face(w):
    return None if w == "" else (w[0], w[-1])


def count_th(w):
    return sum(1 for i in range(len(w) - 1) if w[i:i + 2] == "th")


words = [""] + ["".join(p) for k in range(1, 5) for p in product(L, repeat=k)]
Bres = {}
Bres["face_monoid_size"] = len(M)
Bres["cocycle_on_faces"] = all(seam(x, y) + seam(mul(x, y), z) == seam(y, z) + seam(x, mul(y, z))
                               for x in M for y in M for z in M)
Bres["count_identity_pairs"] = len(words) ** 2
Bres["count_th(xy) = count_th(x) + count_th(y) + seam(face x, face y)"] = all(
    count_th(x + y) == count_th(x) + count_th(y) + seam(face(x), face(y)) for x in words for y in words)
# is seam = delta b on the face monoid, delta b(x, y) = b(xy) - b(x) - b(y), b rational?
idx = {m: i for i, m in enumerate(M)}
Amat, rhs = [], []
for x in M:
    for y in M:
        row = [0] * len(M)
        row[idx[mul(x, y)]] += 1
        row[idx[x]] -= 1
        row[idx[y]] -= 1
        Amat.append(row)
        rhs.append(seam(x, y))
rA = rank(Amat)
rAc = rank([r + [c] for r, c in zip(Amat, rhs)])
Bres["rank_coboundary_system"] = rA
Bres["rank_augmented"] = rAc
Bres["seam_is_rational_coboundary_on_faces"] = (rA == rAc)
cert = {(("a", "t"), ("h", "a")): 1, (("a", "a"), ("a", "a")): 1,
        (("a", "t"), ("a", "t")): -1, (("h", "a"), ("h", "a")): -1}
comb = [0] * len(M)
val = 0
for (x, y), k in cert.items():
    i = M.index(x) * len(M) + M.index(y)
    comb = [c + k * v for c, v in zip(comb, Amat[i])]
    val += k * rhs[i]
Bres["certificate_cycle"] = "[at|ha] + [aa|aa] - [at|at] - [ha|ha] (faces as first,last letter)"
Bres["certificate_kills_every_coboundary"] = all(c == 0 for c in comb)
Bres["seam_read_on_certificate"] = val
# upstairs: on words the seam is the coboundary of the count itself (checked above); on the faces it is not
out["B_language_seam_class"] = Bres

# ---------------- C. the four blocks are the Kunneth summands; interaction rank ----------------


def interaction(table):
    R, C = len(table), len(table[0])
    t = [[Fr(v) for v in r] for r in table]
    rm = [sum(r) / C for r in t]
    cm = [sum(t[i][j] for i in range(R)) / R for j in range(C)]
    gm = sum(rm) / R
    return [[t[i][j] - rm[i] - cm[j] + gm for j in range(C)] for i in range(R)]


def unit_four_cycles_zero(table):
    R, C = len(table), len(table[0])
    return all(table[i][j] - table[i][j + 1] - table[i + 1][j] + table[i + 1][j + 1] == 0
               for i in range(R - 1) for j in range(C - 1))


def census(table):
    I = interaction(table)
    zero = all(v == 0 for r in I for v in r)
    return dict(interaction_rank=rank(I), interaction_zero=zero,
                unit_four_cycles_zero=unit_four_cycles_zero(table),
                agree=(zero == unit_four_cycles_zero(table)))


Cres = {}
R10 = range(10)
Cres["carry mod 10"] = census([[(a + b) // 10 for b in R10] for a in R10])
Cres["last digit of sum, integer chart"] = census([[(a + b) % 10 for b in R10] for a in R10])
Cres["last digit of product"] = census([[(a * b) % 10 for b in R10] for a in R10])
Cres["product 0..9"] = census([[a * b for b in R10] for a in R10])
Cres["sum 0..9 (no wrap)"] = census([[a + b for b in R10] for a in R10])
mats = list(product((-1, 0, 1), repeat=4))
tr = lambda A_, B_: A_[0] * B_[0] + A_[1] * B_[2] + A_[2] * B_[1] + A_[3] * B_[3]
det = lambda A_: A_[0] * A_[3] - A_[1] * A_[2]
Cres["trace of product, 81 matrices"] = census([[tr(x, y) for y in mats] for x in mats])
Cres["det of product, 81 matrices"] = census([[det(x) * det(y) for y in mats] for x in mats])
thfree = [w for w in words if 1 <= len(w) <= 2 and "th" not in w]
Cres["contains th, th-free words of length 1-2"] = census(
    [[1 if "th" in x + y else 0 for y in thfree] for x in thfree])
short = [w for w in words if len(w) <= 2]
Cres["count of th, words of length 0-2"] = census([[count_th(x + y) for y in short] for x in short])
out["C_kunneth_interaction_rank"] = Cres

# ---------------- D. the Hodge split on a torus grid; viscosity keeps the harmonic part ----------------
N = 6
V = [(i, j) for j in range(N) for i in range(N)]
vi = {v: k for k, v in enumerate(V)}
E = [("h", i, j) for j in range(N) for i in range(N)] + [("v", i, j) for j in range(N) for i in range(N)]
ei = {e: k for k, e in enumerate(E)}


def d0(phi):
    u = [Fr(0)] * len(E)
    for (k, i, j), n_ in ei.items():
        a = vi[(i, j)]
        b = vi[((i + 1) % N, j)] if k == "h" else vi[(i, (j + 1) % N)]
        u[n_] = phi[b] - phi[a]
    return u


def d0T(u):
    phi = [Fr(0)] * len(V)
    for (k, i, j), n_ in ei.items():
        a = vi[(i, j)]
        b = vi[((i + 1) % N, j)] if k == "h" else vi[(i, (j + 1) % N)]
        phi[b] += u[n_]
        phi[a] -= u[n_]
    return phi


def d1(u):  # circulation around each unit square: the field's four-cycle (its curl)
    return [u[ei[("h", i, j)]] + u[ei[("v", (i + 1) % N, j)]] - u[ei[("h", i, (j + 1) % N)]] - u[ei[("v", i, j)]]
            for j in range(N) for i in range(N)]


def d1T(w):
    u = [Fr(0)] * len(E)
    for j in range(N):
        for i in range(N):
            f = w[j * N + i]
            u[ei[("h", i, j)]] += f
            u[ei[("v", (i + 1) % N, j)]] += f
            u[ei[("h", i, (j + 1) % N)]] -= f
            u[ei[("v", i, j)]] -= f
    return u


def lap1(u):
    return [a + b for a, b in zip(d0(d0T(u)), d1T(d1(u)))]


def harmonic_part(u):
    mh = sum(u[ei[("h", i, j)]] for i in range(N) for j in range(N)) / (N * N)
    mv = sum(u[ei[("v", i, j)]] for i in range(N) for j in range(N)) / (N * N)
    return [mh if e[0] == "h" else mv for e in E]


def solve_poisson(rhs_):
    # graph Laplacian L = d0T d0 on the torus vertices, phi(0) = 0
    cols = len(V)
    rows = []
    for k in range(cols):
        e = [Fr(0)] * cols
        e[k] = Fr(1)
        rows.append(d0T(d0(e)))
    Lm = [[rows[c][r] for c in range(cols)] for r in range(cols)]  # Lm[r][c]
    Lm = [r[1:] for r in Lm]
    aug = [r + [b] for r, b in zip(Lm, rhs_)]
    m = [row[:] for row in aug]
    nvar = cols - 1
    piv = []
    rr = 0
    for c in range(nvar):
        p = next((i for i in range(rr, len(m)) if m[i][c] != 0), None)
        if p is None:
            continue
        m[rr], m[p] = m[p], m[rr]
        m[rr] = [v / m[rr][c] for v in m[rr]]
        for i in range(len(m)):
            if i != rr and m[i][c] != 0:
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[rr])]
        piv.append(c)
        rr += 1
    sol = [Fr(0)] * nvar
    for k, c in enumerate(piv):
        sol[c] = m[k][-1]
    return [Fr(0)] + sol


def split(u):
    h = harmonic_part(u)
    phi = solve_poisson(d0T(u))
    ex = d0(phi)
    co = [a - b - c for a, b, c in zip(u, ex, h)]
    return ex, co, h


dot = lambda x, y: sum(a * b for a, b in zip(x, y))
u = [Fr(((3 * i + 5 * j + i * j) % 7) - 3) if k == "h" else Fr(((2 * i + 7 * j + 2 * i * j) % 5) - 2)
     for (k, i, j) in E]
ex, co, h = split(u)
Dres = {}
Dres["grid"] = f"{N}x{N} torus, {len(V)} vertices, {len(E)} edges, {N * N} squares"
basis_lap = []
for k in range(len(E)):
    e = [Fr(0)] * len(E)
    e[k] = Fr(1)
    basis_lap.append(lap1(e))
Dres["dim_harmonic = edges - rank(Hodge Laplacian)"] = len(E) - rank(basis_lap)
Dres["sum_is_field"] = all(a + b + c == x for a, b, c, x in zip(ex, co, h, u))
Dres["pairwise_orthogonal"] = (dot(ex, co) == 0 and dot(ex, h) == 0 and dot(co, h) == 0)
Dres["coexact_is_coclosed"] = all(v == 0 for v in d0T(co))
Dres["exact_has_zero_curl"] = all(v == 0 for v in d1(ex))
Dres["harmonic_is_closed_and_coclosed"] = all(v == 0 for v in d1(h)) and all(v == 0 for v in d0T(h))
Dres["energies_step0"] = dict(exact=str(dot(ex, ex)), coexact=str(dot(co, co)), harmonic=str(dot(h, h)))
nu = Fr(1, 8)
row_circ0 = [sum(u[ei[("h", i, j)]] for i in range(N)) for j in range(N)]
cur = u
steps = []
for s in range(1, 7):
    Lu = lap1(cur)
    cur = [a - nu * b for a, b in zip(cur, Lu)]
    e2, c2, h2 = split(cur)
    steps.append(dict(step=s, harmonic_unchanged=(h2 == h), exact=str(dot(e2, e2)), coexact=str(dot(c2, c2))))
Dres["viscosity_nu"] = "1/8"
Dres["steps"] = steps
row_circ6 = [sum(cur[ei[("h", i, j)]] for i in range(N)) for j in range(N)]
Dres["row_loop_circulations_changed"] = sum(1 for a, b in zip(row_circ0, row_circ6) if a != b)
Dres["mean_row_loop_circulation_step0_step6"] = [str(sum(row_circ0) / N), str(sum(row_circ6) / N)]
energies = [(Fr(steps[k]["exact"]), Fr(steps[k]["coexact"])) for k in range(len(steps))]
prev = (dot(ex, ex), dot(co, co))
dec = True
for e_, c_ in energies:
    dec &= (e_ < prev[0]) and (c_ < prev[1])
    prev = (e_, c_)
Dres["exact_and_coexact_strictly_decrease"] = dec
out["D_torus_hodge_viscosity"] = Dres

# ---------------- E. HPP lattice gas: bitwise collision and streaming conserve mass and momentum ----------------
NG = 16
mask = (1 << NG) - 1
pc = lambda r: bin(r).count("1")


def collide(e, n, w, s):
    ew = e & w & ~n & ~s & mask
    ns = n & s & ~e & ~w & mask
    return ((e & ~ew) | ns) & mask, ((n & ~ns) | ew) & mask, ((w & ~ew) | ns) & mask, ((s & ~ns) | ew) & mask


rot_l = lambda r: ((r << 1) | (r >> (NG - 1))) & mask
rot_r = lambda r: ((r >> 1) | ((r & 1) << (NG - 1))) & mask
planes = []
for d in range(4):
    rows_ = []
    for y in range(NG):
        r = 0
        for x in range(NG):
            if ((x * 7 + y * 13 + d * 5 + x * y) % 11) < 4:
                r |= 1 << x
        rows_.append(r)
    planes.append(rows_)


def invariants(pl):
    e, n, w, s = pl
    E_, N_, W_, S_ = (sum(pc(r) for r in p) for p in (e, n, w, s))
    return (E_ + N_ + W_ + S_, E_ - W_, N_ - S_)


site_ok = True
site_changed = 0
for e, n, w, s in product((0, 1), repeat=4):
    e2, n2, w2, s2 = collide(e, n, w, s)
    site_ok &= (e + n + w + s == e2 + n2 + w2 + s2) and (e - w == e2 - w2) and (n - s == n2 - s2)
    site_ok &= collide(e2, n2, w2, s2) == (e, n, w, s)
    site_changed += (e, n, w, s) != (e2, n2, w2, s2)
inv0 = invariants(planes)
ok_all = True
moved = 0
for step in range(64):
    e, n, w, s = planes
    cols_ = [collide(e[y], n[y], w[y], s[y]) for y in range(NG)]
    e = [c[0] for c in cols_]
    n = [c[1] for c in cols_]
    w = [c[2] for c in cols_]
    s = [c[3] for c in cols_]
    e = [rot_l(r) for r in e]
    w = [rot_r(r) for r in w]
    n = [n[(y - 1) % NG] for y in range(NG)]
    s = [s[(y + 1) % NG] for y in range(NG)]
    new = [e, n, w, s]
    moved += sum(pc(a ^ b) for p, q in zip(planes, new) for a, b in zip(p, q))
    planes = new
    ok_all &= invariants(planes) == inv0
out["E_hpp_lattice_gas"] = dict(torus=f"{NG}x{NG}", steps=64, invariants_mass_px_py=list(inv0),
                                conserved_every_step=ok_all,
                                per_site_conserves_and_is_involution=site_ok,
                                site_states_changed_by_collision=site_changed,
                                bits_flipped_over_run=moved)

# ---------------- F. replicator: the gradient part and the cycling part ----------------
K = [[0, -1, 1], [1, 0, -1], [-1, 1, 0]]
S = [[1, 2, 0], [2, 0, 1], [0, 1, 3]]
mv = lambda Mx, x: [sum(Fr(Mx[i][j]) * x[j] for j in range(3)) for i in range(3)]
pts = [[Fr(1, 2), Fr(1, 3), Fr(1, 6)], [Fr(1, 5), Fr(2, 5), Fr(2, 5)], [Fr(3, 7), Fr(1, 7), Fr(3, 7)]]
Fres = {"column_sums_of_K_zero": all(sum(K[i][j] for i in range(3)) == 0 for j in range(3))}
cyc, fisher = True, True
for x in pts:
    Kx = mv(K, x)
    phiK = sum(a * b for a, b in zip(x, Kx))
    xdot = [x[i] * (Kx[i] - phiK) for i in range(3)]
    cyc &= (phiK == 0) and (sum(xdot[i] / x[i] for i in range(3)) == 0)  # d/dt sum log x_i = 0
    Sx = mv(S, x)
    phiS = sum(a * b for a, b in zip(x, Sx))
    ydot = [x[i] * (Sx[i] - phiS) for i in range(3)]
    dmean = 2 * sum(a * b for a, b in zip(ydot, Sx))  # d/dt x^T S x, S symmetric
    fisher &= dmean == 2 * sum(x[i] * (Sx[i] - phiS) ** 2 for i in range(3))
Fres["cycling_part_conserves_sum_log_x"] = cyc
Fres["gradient_part_mean_fitness_rate_is_twice_variance"] = fisher
Fres["points"] = len(pts)
out["F_replicator_parts"] = Fres

json.dump(out, sys.stdout, indent=1, ensure_ascii=False)
print()
