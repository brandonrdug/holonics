"""Founding when no present face carries the remainder (exact).

F1. A conjunction: the arrival is the product of two signs. Each sign, and both read additively,
    carry nothing (M = 0); their product carries the whole tension. The XOR table's four-cycle is
    nonzero, so no additive face separates it.
F2. The price of choosing: on tension.py's eight line starts, every ±1 pattern of the eight cells
    as a candidate face. The mean drop, the largest drop, and the held mode's code saving against
    the number of candidates it was chosen from: all 256 patterns, or the 14 square-wave clocks of
    periods 2, 4 and 8 (every phase).
F2b. The same choice with the material charged: a sequential Krichevsky–Trofimov code per group
    (each cell coded before its group's counts take it) pays for the group frequencies that F2's
    optima leave free. The held mode on the eight cells and on the eight repeated two to four times,
    against the clocks of every period up to the passage at every phase; the best ±1 pattern.
F3. A pool whose coordinates are correlated: c₁ = held mode + alternation, c₂ = alternation. The
    pool's drop tr M Q⁺ Mᵀ (the sum of its generalized eigenvalues), each coordinate's drop, and the
    combinations c₁ + s c₂: the best face in a pool is a combination and carries more than either
    coordinate.
F4. A pool that is a function of a finite context (here the last two symbols, encoded by E into two
    coordinates each). One pass keeps, per occurring context p, the count n_p, the summed covector
    τ_p and the summed face φ_p. From that table alone: the moments of the product pool E(s_k)⊗E(s_k−1)
    and of a half-step pool x·(bᵀy) equal the cells'; the tension after every function of the context
    is the within-context tension T_w − B_w H_w⁺ B_wᵀ (X_w = X − Σ_p sums_p sums_pᵀ / n_p), the ceiling
    of every pool of the context; the joint regression's fit at a cell of context p is
    G_w f̄ + a_p, a_p = (τ_p − G_w φ_p)/n_p with G_w = B_w H_w⁺ (fitted values; the constant's
    coefficient is gauge, since the context's indicators span it); the generalized eigenvalues of (MᵀM, Q) are the
    eigenvalues of the class-side M Q⁺ Mᵀ (Sylvester: the characteristic polynomials agree up to μ);
    and a rational output step w = Q⁺ Mᵀ v, v' = M w, never lowers the exact drop of the face wᵀc.
"""
from fractions import Fraction as F
from itertools import product
import json, sys

def mat(r, c, v=F(0)): return [[v] * c for _ in range(r)]
def T_(A): return [list(x) for x in zip(*A)]
def mul(A, B): return [[sum((A[i][k] * B[k][j] for k in range(len(B))), F(0)) for j in range(len(B[0]))] for i in range(len(A))]
def sub(A, B): return [[a - b for a, b in zip(r, s)] for r, s in zip(A, B)]
def add(A, B): return [[a + b for a, b in zip(r, s)] for r, s in zip(A, B)]
def outer(u, v): return [[a * b for b in v] for a in u]
def gram(xs, ys):
    G = mat(len(xs[0]), len(ys[0]))
    for x, y in zip(xs, ys): G = add(G, outer(x, y))
    return G

def pinv_solve(H, Bt):
    n = len(H); m = len(Bt[0])
    A = [H[i][:] + Bt[i][:] for i in range(n)]
    piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, n) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]; A[r] = [x / pv for x in A[r]]
        for i in range(n):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c); r += 1
    for i in range(r, n): assert all(x == 0 for x in A[i][n:]), "right side outside range(H)"
    X = mat(n, m)
    for i, c in enumerate(piv): X[c] = A[i][n:]
    return X

def tension(faces, covs):
    H = gram(faces, faces); B = gram(covs, faces); Tm = gram(covs, covs)
    return sub(Tm, mul(B, pinv_solve(H, T_(B))))

def tr(A): return sum(A[i][i] for i in range(len(A)))
def drop(faces, covs, cs):
    """M Q⁺ Mᵀ for the pool cs (one list of coordinates per cell) beside the faces."""
    H = gram(faces, faces); B = gram(covs, faces)
    K = gram(covs, cs); L = gram(faces, cs); C = gram(cs, cs)
    M = sub(K, mul(B, pinv_solve(H, L)))
    Q = sub(C, mul(T_(L), pinv_solve(H, L)))
    return mul(M, pinv_solve(Q, T_(M)))

fr = str
out = {}
one = F(1)

# ---------- F1 ----------
cells = list(product((1, -1), repeat=2))                 # (a, b)
covs = [[F(1, 2) - (1 if k == (0 if a * b == 1 else 1) else 0) for k in range(2)] for a, b in cells]
const = [[one] for _ in cells]
S0 = tension(const, covs)
additive = [[F(a), F(b)] for a, b in cells]
prodc = [[F(a * b)] for a, b in cells]
four_cycle = [(1 if a * b == 1 else 0) for a, b in cells]   # class-0 indicator on the 2×2 table
out["F1"] = {
    "tension_constant_only_trace": fr(tr(S0)),
    "drop_each_sign_and_both_additively": [fr(tr(drop(const, covs, [[x[0]] for x in additive]))),
                                           fr(tr(drop(const, covs, [[x[1]] for x in additive]))),
                                           fr(tr(drop(const, covs, additive)))],
    "drop_product_face": fr(tr(drop(const, covs, prodc))),
    "four_cycle_of_the_table": four_cycle[0] - four_cycle[1] - four_cycle[2] + four_cycle[3],
}

# ---------- F2 ----------
targets = [0, 0, 0, 2, 1, 1, 1, 2]
q = [F(3, 8), F(3, 8), F(2, 8)]
covsC = [[p - (1 if a == u else 0) for a, p in enumerate(q)] for u in targets]
facesC = [[one, one] for _ in targets]
drops = {}
for pat in product((1, -1), repeat=8):
    if pat[0] == -1: continue                            # a pattern and its negation read alike
    drops[pat] = tr(drop(facesC, covsC, [[F(x)] for x in pat]))
mean = sum(drops.values(), F(0)) / len(drops)
best = max(drops.values())
best_pats = sorted("".join("+" if x == 1 else "-" for x in p) for p, d in drops.items() if d == best)
held = (1, 1, 1, 1, -1, -1, -1, -1)
def likelihood(groups):
    """Product of p(true) at each group's own optimum (its class frequencies)."""
    L = F(1)
    for g in groups:
        for u in g: L *= F(g.count(u), len(g))
    return L
merged = likelihood([targets])
ratios = {}
for pat in drops:
    plus = [u for u, x in zip(targets, pat) if x == 1]; minus = [u for u, x in zip(targets, pat) if x == -1]
    ratios[pat] = likelihood([g for g in (plus, minus) if g]) / merged
clocks = set()
for period in (2, 4, 8):
    for phase in range(period):
        w = tuple(1 if ((k + phase) % period) < period // 2 else -1 for k in range(8))
        clocks.add(w if w[0] == 1 else tuple(-x for x in w))
out["F2"] = {
    "patterns_up_to_sign": len(drops),
    "mean_drop_trace": fr(mean),
    "largest_drop_trace": fr(best), "largest_drop_patterns": best_pats,
    "held_mode_drop_trace": fr(drops[held]),
    "held_mode_code_saving_ratio": "64",                   # tension.py C: 729/65536 over 729/4194304 = 2^6
    "candidates_all_patterns": 2 ** 8,
    "candidates_square_wave_clocks_counted_with_sign": 2 * len(clocks),
    "founded_against_all_patterns": 64 > 2 ** 8,
    "founded_against_clocks": 64 > 2 * len(clocks),
    "held_mode_is_a_clock": held in clocks,
    "held_mode_saving_ratio_recomputed": fr(ratios[held]),
    "largest_drop_pattern_saving_ratio": fr(ratios[tuple(1 if ch == "+" else -1 for ch in "+++-----")]),
    "largest_saving_ratio_over_all_patterns": fr(max(ratios.values())),
    "patterns_whose_saving_exceeds_their_choice_among_256": sum(1 for r in ratios.values() if r > 256),
    "clocks_whose_saving_exceeds_their_choice_among_14": sum(1 for w in clocks if ratios[w] > 14),
}

def kt(seq, A=3):
    """Sequential Krichevsky–Trofimov probability: each cell coded before its counts take it."""
    n = [0] * A; pr = F(1); N = 0
    for u in seq:
        pr *= F(2 * n[u] + 1, 2 * N + A); n[u] += 1; N += 1
    return pr
def kt_split(seq, pat):
    g1 = [u for u, x in zip(seq, pat) if x == 1]; g2 = [u for u, x in zip(seq, pat) if x == -1]
    return kt(g1) * (kt(g2) if g2 else F(1)) / kt(seq)
f2b = {"best_pattern_saving_ratio_material_charged": fr(max(kt_split(targets, pat) for pat in drops))}
for reps in (1, 2, 3, 4):
    n = 8 * reps
    f2b[f"held_mode_{n}_cells"] = {"saving_ratio_material_charged": fr(kt_split(targets * reps, held * reps)),
                                   "clocks_counted_with_sign": sum(p for p in (2, 4, 8, 16, 32, 64) if p <= n)}
out["F2b"] = f2b

# ---------- F3 ----------
alt = (1, -1, 1, -1, 1, -1, 1, -1)
pool = [[F(h + a), F(a)] for h, a in zip(held, alt)]
D = drop(facesC, covsC, pool)
single = [tr(drop(facesC, covsC, [[c[i]] for c in pool])) for i in range(2)]
combos = {}
for sv in (F(-2), F(-1), F(-1, 2), F(0), F(1, 2), F(1)):
    combos[fr(sv)] = fr(tr(drop(facesC, covsC, [[c[0] + sv * c[1]] for c in pool])))
H = gram(facesC, facesC); B = gram(covsC, facesC)
K = gram(covsC, pool); L = gram(facesC, pool); C = gram(pool, pool)
M = sub(K, mul(B, pinv_solve(H, L))); Q = sub(C, mul(T_(L), pinv_solve(H, L)))
MtM = mul(T_(M), M)
def det2(A): return A[0][0] * A[1][1] - A[0][1] * A[1][0]
gen = {fr(mu): det2(sub(MtM, [[mu * x for x in r] for r in Q])) == 0 for mu in (F(9, 4), F(3, 4))}
out["F3"] = {"generalized_eigenvalues_9_4_and_3_4": gen, "pool_drop_trace": fr(tr(D)), "single_coordinate_drops": [fr(x) for x in single],
             "combination_c1_plus_s_c2": combos}

# ---------- F4 ----------
x_ = 20261024
def step():
    global x_
    x_ = (1103515245 * x_ + 12345) % (1 << 31)
    return x_ >> 16
syms = [step() % 4 for _ in range(64)]
E = {0: (1, 0), 1: (0, 1), 2: (1, 1), 3: (1, -1)}
cellsP, uP, gP = [], [], []
for k in range(1, len(syms)):
    a, b = syms[k], syms[k - 1]
    u = 0 if a == b else 1 + (a + b) % 2                   # a conjunction of the two symbols
    if step() % 5 == 0: u = (u + 1) % 3                    # and a fifth of the cells against it
    cellsP.append((a, b)); uP.append(u); gP.append(F(k % 3 - 1))
phat = [F(1, 2), F(1, 4), F(1, 4)]
covsP = [[pp - (1 if c == u else 0) for c, pp in enumerate(phat)] for u in uP]
facesP = [[g, one] for g in gP]
def kron(x, y): return [F(xi * yi) for xi in x for yi in y]
prodP = [kron(E[a], E[b]) for a, b in cellsP]
ctxs = sorted(set(cellsP))
nP = {p: 0 for p in ctxs}; tau = {p: [F(0)] * 3 for p in ctxs}; phi = {p: [F(0)] * 2 for p in ctxs}
for (p, t, f) in zip(cellsP, covsP, facesP):                # the one pass: count, Σt, Σf̄ per context
    nP[p] += 1; tau[p] = [a + b for a, b in zip(tau[p], t)]; phi[p] = [a + b for a, b in zip(phi[p], f)]
def table_moments(cfun):
    K = mat(3, len(cfun(ctxs[0]))); L = mat(2, len(cfun(ctxs[0]))); C = mat(len(cfun(ctxs[0])), len(cfun(ctxs[0])))
    for p in ctxs:
        c = cfun(p)
        K = add(K, outer(tau[p], c)); L = add(L, outer(phi[p], c)); C = add(C, [[nP[p] * v for v in r] for r in outer(c, c)])
    return K, L, C
Kt_, Lt_, Ct_ = table_moments(lambda p: kron(E[p[0]], E[p[1]]))
bvec = (F(1), F(2))
half = lambda p: [F(e) * (bvec[0] * E[p[1]][0] + bvec[1] * E[p[1]][1]) for e in E[p[0]]]
Kh_, Lh_, Ch_ = table_moments(half)
halfP = [half(p) for p in cellsP]
H = gram(facesP, facesP); B = gram(covsP, facesP); Tm = gram(covsP, covsP)
S = sub(Tm, mul(B, pinv_solve(H, T_(B))))
# the joint regression on (f̄, every indicator of the context), by the pseudo-inverse
ind = [[F(1 if p == q else 0) for q in ctxs] for p in cellsP]
joint = [f + i for f, i in zip(facesP, ind)]
S_joint = tension(joint, covsP)
# the within-context tension from the table
def within(X, sx, sy): return sub(X, [[sum((sx[p][i] * sy[p][j] / nP[p] for p in ctxs), F(0)) for j in range(len(sy[ctxs[0]]))] for i in range(len(sx[ctxs[0]]))])
Tw = within(Tm, tau, tau); Bw = within(B, tau, phi); Hw = within(H, phi, phi)
Gw = T_(pinv_solve(Hw, T_(Bw)))                            # one solution; the constant's coefficient is gauge
S_within = sub(Tw, mul(Bw, pinv_solve(Hw, T_(Bw))))
# the joint fit from the normal equations against the table form t̂ = G_w f̄ + a_p (fitted values are unique)
Gj = gram(joint, joint); Bj = gram(covsP, joint)
coef = T_(pinv_solve(Gj, T_(Bj)))                           # 3 × (2 + #contexts)
a_from_table = {p: [(tau[p][c] - sum(Gw[c][j] * phi[p][j] for j in range(2))) / nP[p] for c in range(3)] for p in ctxs}
fit_joint = [[sum(coef[c][j] * z[j] for j in range(len(z))) for c in range(3)] for z in joint]
fit_table = [[sum(Gw[c][j] * f[j] for j in range(2)) + a_from_table[p][c] for c in range(3)] for f, p in zip(facesP, cellsP)]
# the product pool's drop, its spectrum on the class side, and the rational output step
def MQ(faces, covs, cs):
    Hh = gram(faces, faces); Bb = gram(covs, faces)
    K = gram(covs, cs); L = gram(faces, cs); C = gram(cs, cs)
    M = sub(K, mul(Bb, pinv_solve(Hh, L))); Q = sub(C, mul(T_(L), pinv_solve(Hh, L)))
    return M, Q
Mp, Qp = MQ(facesP, covsP, prodP)
Dp = mul(Mp, pinv_solve(Qp, T_(Mp)))
def charpoly(A):
    """Faddeev–LeVerrier: coefficients of det(μI − A), highest first."""
    n = len(A); I = [[one if i == j else F(0) for j in range(n)] for i in range(n)]
    coeffs = [one]; Mk = [r[:] for r in I]
    for k in range(1, n + 1):
        AM = mul(A, Mk); ck = -tr(AM) / k; coeffs.append(ck)
        Mk = add(AM, [[ck * v for v in r] for r in I])
    return coeffs
QinvMt = pinv_solve(Qp, T_(Mp))
poly_pool = charpoly(mul(QinvMt, Mp))                       # 4 × 4: Q⁻¹ Mᵀ M
poly_class = charpoly(mul(Mp, QinvMt))                      # 3 × 3: M Q⁻¹ Mᵀ
def face_drop(w):
    Mw = [sum(Mp[i][j] * w[j] for j in range(len(w))) for i in range(3)]
    return sum(v * v for v in Mw) / sum(w[i] * Qp[i][j] * w[j] for i in range(len(w)) for j in range(len(w))), Mw
v0 = [one, -one, F(0)]
w0 = [r[0] for r in pinv_solve(Qp, mul(T_(Mp), [[v] for v in v0]))]
d0, v1 = face_drop(w0)
w1 = [r[0] for r in pinv_solve(Qp, mul(T_(Mp), [[v] for v in v1]))]
d1, v2 = face_drop(w1)
w2 = [r[0] for r in pinv_solve(Qp, mul(T_(Mp), [[v] for v in v2]))]
d2, _ = face_drop(w2)
out["F4"] = {
    "cells": len(cellsP), "occurring_contexts": len(ctxs),
    "product_pool_moments_from_table_equal_cells": [Kt_ == gram(covsP, prodP), Lt_ == gram(facesP, prodP), Ct_ == gram(prodP, prodP)],
    "half_step_pool_moments_from_table_equal_cells": [Kh_ == gram(covsP, halfP), Lh_ == gram(facesP, halfP), Ch_ == gram(halfP, halfP)],
    "tension_trace": fr(tr(S)),
    "within_context_tension_equals_joint_regression_on_every_indicator": S_within == S_joint,
    "ceiling_drop_trace": fr(tr(S) - tr(S_within)),
    "product_pool_drop_trace": fr(tr(Dp)),
    "product_pool_at_most_ceiling": tr(Dp) <= tr(S) - tr(S_within),
    "joint_fit_equals_table_form_G_w_f_plus_a_p": fit_joint == fit_table,
    "pool_side_charpoly_equals_mu_times_class_side": poly_pool == poly_class + [F(0)],
    "output_steps_drop_traces": [fr(d0), fr(d1), fr(d2)],
    "output_steps_never_lower_the_drop": d0 <= d1 <= d2 <= tr(Dp),
}

json.dump(out, sys.stdout, indent=1)
print()
