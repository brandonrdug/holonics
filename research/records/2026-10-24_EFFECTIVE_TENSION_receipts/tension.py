"""The bridge and the tension at a contact, read exactly (Fractions only).

A. The tension is the Schur complement of the joint (face, covector) Gram and is the least residual
   of the covector on the face; the remainder is orthogonal to every face, so the plain gradient
   carries none of it.
B. Two cells one face merges, asked opposite things: the tension is the four-cycle.
C. Founding: the partial regression of the remainder on a candidate face's residual; which candidate
   bridges the tension, the founded material, and the exact code saving at the optima.
D. The phase part: the ratio read through the tower's own receiving loop is gauge-free where the
   real read is not, and the quadrature separates arrivals the real face merges.
E. The tension is frame-free: a rebase of the face leaves it unchanged.
"""
from fractions import Fraction as F
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
    """Solve H X = Bt on range(H) exactly (Gauss-Jordan with free variables set to zero)."""
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
    # consistency: rows below r must be zero on the right
    for i in range(r, n): assert all(x == 0 for x in A[i][n:]), "right side outside range(H)"
    X = mat(n, m)
    for i, c in enumerate(piv): X[c] = A[i][n:]
    return X

def tension(faces, covs):
    """H = Σ f̄f̄ᵀ, B = Σ t f̄ᵀ, T = Σ t tᵀ;  S = T − B H⁺ Bᵀ;  also W* = B H⁺ (the least-squares material)."""
    H = gram(faces, faces); B = gram(covs, faces); Tm = gram(covs, covs)
    X = pinv_solve(H, T_(B))           # H X = Bᵀ, X = H⁺ Bᵀ
    S = sub(Tm, mul(B, X))
    W = T_(X)                          # W* = B H⁺
    return H, B, Tm, S, W

def fr(x): return str(x)
def frm(A): return [[fr(x) for x in r] for r in A]
out = {}

# ---------- A ----------
one = F(1)
facesA = [[F(1), F(2), one], [F(-1), F(1), one], [F(0), F(3), one], [F(2), F(-1), one], [F(1), F(1), one], [F(-2), F(0), one]]
phat = [F(1, 2), F(1, 4), F(1, 4)]
targetsA = [0, 1, 2, 0, 2, 1]
covsA = [[p - (1 if a == u else 0) for a, p in enumerate(phat)] for u in targetsA]
H, B, Tm, S, W = tension(facesA, covsA)
resid = [[t - sum(W[o][k] * f[k] for k in range(len(f))) for o, t in enumerate(c)] for f, c in zip(facesA, covsA)]
least = gram(resid, resid)
orth = gram(resid, facesA)                       # Σ r_t f̄_tᵀ, must be zero
B_from_fit = gram([[sum(W[o][k] * f[k] for k in range(len(f))) for o in range(3)] for f in facesA], facesA)
out["A"] = {
    "S_equals_least_residual_gram": S == least,
    "remainder_orthogonal_to_every_face": all(x == 0 for r in orth for x in r),
    "plain_gradient_equals_fitted_part_gradient": B == B_from_fit,
    "trace_T": fr(sum(Tm[i][i] for i in range(3))), "trace_bridged": fr(sum(Tm[i][i] - S[i][i] for i in range(3))),
    "trace_S": fr(sum(S[i][i] for i in range(3))), "S": frm(S),
}

# ---------- B ----------
facesB = [[F(1), one], [F(1), one]]
phatB = [F(1, 2), F(1, 2)]
covsB = [[p - (1 if a == u else 0) for a, p in enumerate(phatB)] for u in (0, 1)]
_, _, _, SB, _ = tension(facesB, covsB)
out["B"] = {"S": frm(SB), "four_cycle": SB[0][1] == -SB[0][0] and SB[1][0] == -SB[1][1] and SB[0][0] == SB[1][1] and SB[0][1] < 0}

# ---------- C ----------
# eight line-start cells: one face (the newline's and the constant); the medium is not in the face.
# medium P targets 0,0,0,2 ; medium L targets 1,1,1,2 (class 2 shared: a blank line).
targetsC = [0, 0, 0, 2, 1, 1, 1, 2]
facesC = [[F(1), one] for _ in targetsC]
q = [F(3, 8), F(3, 8), F(2, 8)]                  # the merged optimum the plain step reaches
covsC = [[p - (1 if a == u else 0) for a, p in enumerate(q)] for u in targetsC]
HC, BC, TC, SC, WC = tension(facesC, covsC)
cands = {
    "held_mode_carrying_the_medium": [F(1)] * 4 + [F(-1)] * 4,
    "quadrature_alternating_within_each_medium": [F(1), F(-1), F(1), F(-1)] * 2,
    "half_the_medium": [F(1), F(1), F(0), F(0), F(-1), F(-1), F(0), F(0)],
}
resC = {"S": frm(SC), "trace_S": fr(sum(SC[i][i] for i in range(3)))}
for name, c in cands.items():
    cs = [[x] for x in c]
    K = gram(covsC, cs); L = gram(facesC, cs); Cc = gram(cs, cs)
    Xl = pinv_solve(HC, L)                        # H⁺ L
    M = sub(K, mul(BC, Xl))                       # residual covector × residual candidate
    Q = sub(Cc, mul(T_(L), Xl))                   # candidate's residual Gram
    if Q[0][0] == 0:
        drop = mat(3, 3); mat_found = mat(3, 1)
    else:
        mat_found = [[m[0] / Q[0][0]] for m in M]
        drop = [[M[i][0] * M[j][0] / Q[0][0] for j in range(3)] for i in range(3)]
    # check against the joint regression on (face, candidate)
    joint = [f + [x] for f, x in zip(facesC, c)]
    _, _, _, Sj, _ = tension(joint, covsC)
    resC[name] = {"drop_trace": fr(sum(drop[i][i] for i in range(3))), "S_after_trace": fr(sum(Sj[i][i] for i in range(3))),
                  "drop_equals_joint_regression": sub(SC, drop) == Sj, "founded_material": [fr(m[0]) for m in mat_found]}
# exact code saving at the optima: product of p(true) merged vs separated by the held mode
from functools import reduce
prod = lambda xs: reduce(lambda a, b: a * b, xs, F(1))
merged = prod(q[u] for u in targetsC)
sideP = [F(3, 4), F(0), F(1, 4)]; sideL = [F(0), F(3, 4), F(1, 4)]
separated = prod((sideP if i < 4 else sideL)[u] for i, u in enumerate(targetsC))
resC["product_p_true_merged"] = fr(merged); resC["product_p_true_separated"] = fr(separated)
resC["ratio_separated_over_merged"] = fr(separated / merged)   # 2^bits saved
out["C"] = resC

# ---------- D ----------
# complex rationals as pairs; one readout row c over two modes, push vectors for two arrivals.
def cm(a, b): return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
def cadd(a, b): return (a[0] + b[0], a[1] + b[1])
def cdiv(a, b):
    d = b[0] ** 2 + b[1] ** 2
    return ((a[0] * b[0] + a[1] * b[1]) / d, (a[1] * b[0] - a[0] * b[1]) / d)
def dot(c, v): return reduce(cadd, (cm(x, y) for x, y in zip(c, v)), (F(0), F(0)))
crow = [(F(1), F(0)), (F(0), F(1))]                       # y = h1 + i h2
h = [(F(1), F(0)), (F(0), F(0))]                          # where the tower stands (λh, folded in)
push = {"a": [(F(1), F(0)), (F(1), F(0))],                # C·push = 1 + i
        "b": [(F(1), F(0)), (F(-1), F(0))]}               # C·push = 1 − i
ph = {"a": F(1, 2), "b": F(1, 2)}
exp_push = [cadd(cm((ph["a"], F(0)), pa), cm((ph["b"], F(0)), pb)) for pa, pb in zip(push["a"], push["b"])]
yH = dot(crow, [cadd(x, y) for x, y in zip(h, exp_push)])
rows = {}
for u in ("a", "b"):
    yT = dot(crow, [cadd(x, y) for x, y in zip(h, push[u])])
    R = cdiv(yT, yH)
    nu = (yT[0] - yH[0], yT[1] - yH[1])
    first = cdiv(nu, yH)
    rows[u] = {"y_T": [fr(yT[0]), fr(yT[1])], "real_face": fr(yT[0]), "R": [fr(R[0]), fr(R[1])], "first_order_turn": fr(first[1])}
# gauge: turn the readout row by the unit (3+4i)/5
g = (F(3, 5), F(4, 5))
crow_g = [cm(g, x) for x in crow]
yHg = dot(crow_g, [cadd(x, y) for x, y in zip(h, exp_push)])
gauge = {}
for u in ("a", "b"):
    yTg = dot(crow_g, [cadd(x, y) for x, y in zip(h, push[u])])
    gauge[u] = {"R_after_gauge": [fr(c) for c in cdiv(yTg, yHg)], "real_face_after_gauge": fr(yTg[0])}
out["D"] = {"y_H": [fr(yH[0]), fr(yH[1])], "arrivals": rows, "gauge_turned_row": gauge,
            "real_face_merges_a_b": rows["a"]["real_face"] == rows["b"]["real_face"],
            "phase_part_separates": rows["a"]["first_order_turn"] != rows["b"]["first_order_turn"],
            "R_gauge_free": all(gauge[u]["R_after_gauge"] == rows[u]["R"] for u in ("a", "b")),
            "real_face_gauge_dependent": any(gauge[u]["real_face_after_gauge"] != rows[u]["real_face"] for u in ("a", "b"))}
# the merged real face leaves tension; the quadrature bridges it (cells: arrival a or b, target = which arrived)
facesD = [[F(rows[u]["real_face"].split("/")[0]) if "/" not in rows[u]["real_face"] else F(rows[u]["real_face"]), one] for u in ("a", "b")]
covsD = [[F(1, 2) - (1 if k == j else 0) for k in range(2)] for j in range(2)]
_, _, _, SD, _ = tension(facesD, covsD)
quadD = [[F(1)], [F(-1)]]
_, _, _, SDq, _ = tension([f + q_ for f, q_ in zip(facesD, quadD)], covsD)
out["D"]["tension_on_real_face_trace"] = fr(SD[0][0] + SD[1][1])
out["D"]["tension_after_reading_quadrature_trace"] = fr(SDq[0][0] + SDq[1][1])

# ---------- E ----------
A = [[F(2), F(1), F(0)], [F(1), F(1), F(0)], [F(3), F(-1), F(1)]]  # invertible rebase of (x, 1)
facesE = [[sum(A[i][k] * f[k] for k in range(3)) for i in range(3)] for f in facesA]
_, _, _, SE, _ = tension(facesE, covsA)
out["E"] = {"S_unchanged_under_face_rebase": SE == S}

json.dump(out, sys.stdout, indent=1)
print()
