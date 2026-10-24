"""What closes, the shared part, and the lock's friction against the information distance (exact).

A. The covector's own size is the friction of the aligned coupling: at a committed release
   tr T = 2·#{h_k ≠ u_k} = |H| + |T| − 2·(aligned equal cells), and F* ≤ it; the soft form
   tr T = Σ|p̂|² + N − 2 Σ p̂(u).
B. The shared part between face and covector: on the sum-zero range of the covectors,
   det S / det S₀ = Π_k (1 − ρ_k²), with S₀ the tension against the constant alone (the centred
   Gram) and ρ_k the canonical correlations of covector and face; a founding drop is the same
   conditional ratio det S_after / det S. Read on tension.py's data A and C.
C. F* = |H| + |T| − 2λ against the information distance K(H|T) + K(T|H):
   1. the grain: equal F*, different shared code under one declared class code;
   2. the order: a rotation and a reversal share everything out of order;
   3. the coupling's own description: exact enumeration of λ over every pair of short strands of
      2, 3 and 4 classes, and how many couplings pay for their positions.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
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
    X = pinv_solve(H, T_(B))
    return H, B, Tm, sub(Tm, mul(B, X))

def det(A):
    A = [r[:] for r in A]; n = len(A); d = F(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None: return F(0)
        if p != c: A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]; A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return d

def range_part(M):
    """Covectors p̂ − e_u sum to zero; dropping the last class is injective on that range."""
    return [r[:-1] for r in M[:-1]]

def lcs(h, t):
    prev = [0] * (len(t) + 1)
    for a in h:
        cur = [0]
        for j, b in enumerate(t):
            cur.append(prev[j] + 1 if a == b else max(prev[j + 1], cur[j]))
        prev = cur
    return prev[-1]

fr = str
out = {}

# ---------- A ----------
pairs_ok = True; fstar_le = True
for h in product(range(2), repeat=4):
    for u in product(range(2), repeat=4):
        covs = [[(1 if a == hk else 0) - (1 if a == uk else 0) for a in range(2)] for hk, uk in zip(h, u)]
        trT = sum(x * x for c in covs for x in c)
        aligned = sum(1 for hk, uk in zip(h, u) if hk == uk)
        diag_friction = len(h) + len(u) - 2 * aligned
        pairs_ok &= trT == diag_friction
        fstar_le &= len(h) + len(u) - 2 * lcs(h, u) <= trT
late_H, late_T = "xabc", "abcy"
lam = lcs(late_H, late_T)
out["A"] = {
    "trace_T_equals_aligned_friction_all_binary_length_4": pairs_ok,
    "F_star_at_most_trace_T_all_binary_length_4": fstar_le,
    "release_one_cell_late": {"H": late_H, "T": late_T, "trace_T": 2 * sum(1 for a, b in zip(late_H, late_T) if a != b),
                              "lambda": lam, "F_star": len(late_H) + len(late_T) - 2 * lam},
}
# soft release: tr T = Σ|p̂|² + N − 2 Σ p̂(u)
phat = [F(1, 2), F(1, 4), F(1, 4)]; targets = [0, 1, 2, 0, 2, 1]
covs = [[p - (1 if a == u else 0) for a, p in enumerate(phat)] for u in targets]
out["A"]["soft_form_holds"] = sum(x * x for c in covs for x in c) == \
    len(targets) * sum(p * p for p in phat) + len(targets) - 2 * sum(phat[u] for u in targets)

# ---------- B ----------
one = F(1)
facesA = [[F(1), F(2), one], [F(-1), F(1), one], [F(0), F(3), one], [F(2), F(-1), one], [F(1), F(1), one], [F(-2), F(0), one]]
_, _, _, SA = tension(facesA, covs)
_, _, _, S0 = tension([[one] for _ in facesA], covs)   # the constant alone: the covector's centred Gram
S0r, Sr = range_part(S0), range_part(SA)
ratio = det(Sr) / det(S0r)
Kc = pinv_solve(S0r, sub(S0r, Sr))               # S₀⁻¹ (S₀ − S): its eigenvalues are ρ_k²
trK = Kc[0][0] + Kc[1][1]; detK = det(Kc)
out["B"] = {
    "A_det_S_over_det_S_constant_only": fr(ratio),
    "A_sum_rho_sq": fr(trK), "A_prod_rho_sq": fr(detK),
    "A_prod_one_minus_rho_sq_equals_ratio": 1 - trK + detK == ratio,
}
targetsC = [0, 0, 0, 2, 1, 1, 1, 2]
facesC = [[F(1), one] for _ in targetsC]
q = [F(3, 8), F(3, 8), F(2, 8)]
covsC = [[p - (1 if a == u else 0) for a, p in enumerate(q)] for u in targetsC]
_, _, TC, SC = tension(facesC, covsC)
held = [F(1)] * 4 + [F(-1)] * 4
_, _, _, SCh = tension([f + [x] for f, x in zip(facesC, held)], covsC)
alt = [F(1), F(-1), F(1), F(-1)] * 2
_, _, _, SCa = tension([f + [x] for f, x in zip(facesC, alt)], covsC)
out["B"]["C_det_S_merged"] = fr(det(range_part(SC)))
out["B"]["C_held_mode_det_S_after_over_det_S"] = fr(det(range_part(SCh)) / det(range_part(SC)))
out["B"]["C_alternating_det_S_after_over_det_S"] = fr(det(range_part(SCa)) / det(range_part(SC)))

# ---------- C ----------
# 1. the grain: a declared class code p = (1/2, 1/4, 1/8, 1/8), ℓ = (1, 2, 3, 3) bits
ell = {"a": 1, "b": 2, "c": 3, "d": 3}
def shared_bits(h, t):
    """Weighted longest coupling: the most code an order-consistent coupling shares (one side)."""
    prev = [0] * (len(t) + 1)
    for x in h:
        cur = [0]
        for j, y in enumerate(t):
            cur.append(max(prev[j] + ell[x] if x == y else 0, prev[j + 1], cur[j]))
        prev = cur
    return prev[-1]
grain = {}
for h, t in (("aac", "aad"), ("ccb", "ccd")):
    lam = lcs(h, t); sb = shared_bits(h, t)
    Lh = sum(ell[x] for x in h); Lt = sum(ell[x] for x in t)
    grain[h + "|" + t] = {"lambda": lam, "F_star": len(h) + len(t) - 2 * lam, "shared_bits_each_side": sb,
                          "L_H_plus_L_T": Lh + Lt, "conditional_sum_free_coupling_bits": Lh + Lt - 2 * sb}
# 2. the order
rot_H, rot_T = "abcdefgh", "efghabcd"
rev_H, rev_T = "abcd", "dcba"
order = {"rotation": {"H": rot_H, "T": rot_T, "lambda": lcs(rot_H, rot_T), "F_star": 16 - 2 * lcs(rot_H, rot_T),
                      "rotation_offsets": 8},
         "reversal": {"H": rev_H, "T": rev_T, "lambda": lcs(rev_H, rev_T), "F_star": 8 - 2 * lcs(rev_H, rev_T)}}
# 3. the coupling's own description, by exact enumeration of every pair of length-n strands
chance = {}
for sigma, nmax in ((2, 8), (3, 5), (4, 4)):
    for n in range(1, nmax + 1):
        strands = list(product(range(sigma), repeat=n))
        total = 0; at_least_half = 0; pays = 0; pays_full = 0; identical = 0; count = 0
        for h in strands:
            for t in strands:
                lam = lcs(h, t); total += lam; count += 1
                at_least_half += 2 * lam >= n
                # alignment code for t given h at log2(sigma) bits per cell, positions charged:
                # C(n,λ)² · σ^(n−λ) < σ^n  ⇔  C(n,λ)² < σ^λ   (λ's own value not charged)
                pays += comb(n, lam) ** 2 < sigma ** lam
                # and with λ's own value charged too (one of n + 1):
                pays_full += comb(n, lam) ** 2 * (n + 1) < sigma ** lam
                identical += h == t
        chance[f"sigma{sigma}_n{n}"] = {"pairs": count, "mean_lambda_over_n": fr(F(total, count * n)),
                                         "pairs_with_2lambda_at_least_n": at_least_half,
                                         "pairs_whose_coupling_pays_for_its_positions": pays,
                                         "pairs_whose_coupling_pays_with_lambda_charged": pays_full,
                                         "identical_pairs": identical}
out["C"] = {"grain": grain, "order": order, "chance": chance}

json.dump(out, sys.stdout, indent=1)
print()
