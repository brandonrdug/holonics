"""The leverage of a new reading (exact).

Twelve cells, each a reading x = (f, c): a face f = (1, a) and a pool c of four coordinates whose
fourth is the sum of the first two, so the joint Gram G = Σ x xᵀ has rank 5 and kernel
n = (0, 0, 1, 1, 0, −1). Two covector coordinates t per cell. Three new readings: x_in in range(G),
x_far in range(G) and far from the cells, x_out with a component along n.

A. The extension bound on the pool: Q = C − Lᵀ H⁻¹ L, M = K − B H⁻¹ L, c_res = c* − Lᵀ H⁻¹ f*.
   A founded form W_v = Q⁺ Mᵀ v has training energy W_vᵀ Q W_v = vᵀ M Q⁺ Mᵀ v (its drop along v), lies
   in range(Q), and |W_vᵀ c_res|² ≤ (vᵀ M Q⁺ Mᵀ v)(c_resᵀ Q⁺ c_res), with equality at c_res = Q W_v.
B. The bordered fraction-free elimination: append the reading as a column with a zero corner and
   eliminate as the tower's `Upper::eliminate` does (zero pivots passed over). The corner ends at
   −Δ_r h and h = Σ_k Γ_k² / (Δ_{k−1} Δ_k), Γ_k the border entry at pivot k. The same Γ_k come from
   a forward pass over the stored rows of G's own elimination, without eliminating G again.
C. Out of range: a zero pivot leaves a nonzero border entry β_p = Δ · n_pᵀ x (n_p the null vector
   that pivot exposes); in range every β is zero. In range, two pivot orders and the
   pseudo-inverse agree; out of range they differ, and ε·xᵀ(G + εI)⁻¹x tends to |(I − G G⁺)x|²
   (the honest leverage is unbounded). Training-equivalent forms (w + s n, the pivot chart's basic
   form) agree at every cell and at x_in, and spread at x_out by s·nᵀx. In each chart the bound
   holds with that chart's value and leverage; the energy is the same in every chart.
D. A rebase of the pool by an integer unimodular A: the leverage of x_in is unchanged; at x_out the
   chart's leverage and the residual's length change, and β ≠ 0 stays.
E. Joint additivity: with the faces pivoted first, the series splits into fᵀH⁻¹f (face pivots) and
   the pool part (pool pivots); in range the pool part is c_resᵀ Q⁺ c_res.
F. The charge: with a unit prior G_0 = I, the leverages h_t = x_tᵀ G_{t−1}⁻¹ x_t of the readings as
   they arrive satisfy Π (1 + h_t) = det G_N / det G_0, and the prequential residuals satisfy
   Σ r_t² / (1 + h_t) = min_β |y − Xβ|² + βᵀβ, so a reading of leverage h costs ½ log₂(1 + h) bits in
   the Gaussian chart. The cells' own leverages under G sum to rank G. Repeating the cells m times,
   det(I + mG) = Σ_k e_k(G) mᵏ has degree rank G: the charge is (rank/2) log₂ m plus a constant.
G. Prediction at a new reading, every ±1 noise pattern on six cells and the new cell (128): the
   mean square error of the fitted prediction is 1 + h* in range, for every true coefficient; out
   of range it also carries (x*ᵀ(I − G⁺G)β)², which the cells do not fix.
H. Any form, any reading, in a pivot chart K of G: v = v_s + ρ with v_s = G_{:,K} G_KK⁻¹ v_K in
   range(G) and ρ zero on K (ρ_p = β_p/Δ at each passed pivot). For every w, |wᵀv_s|² ≤
   (wᵀGw)(v_Kᵀ G_KK⁻¹ v_K), and every training-equivalent form w + s·n has the same wᵀv_s; wᵀρ is
   what the encounters leave open. GPT-6's example Q = [[1, 1], [1, 1]], w = (1, 0), c = (1, 0):
   the pseudo-inverse bound (1/4) fails for wᵀc = 1, and the chart's split holds with equality.
"""
from fractions import Fraction as F
from itertools import product
from math import log2
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
def eye(n): return [[F(int(i == j)) for j in range(n)] for i in range(n)]
def col(v): return [[F(x)] for x in v]
def dot(u, v): return sum((F(a) * b for a, b in zip(u, v)), F(0))
def mv(A, v): return [dot(r, v) for r in A]

def inv(A):
    n = len(A); M = [list(map(F, A[i])) + eye(n)[i] for i in range(n)]
    for c in range(n):
        p = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]; M[c] = [x / pv for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]; M[i] = [a - f * b for a, b in zip(M[i], M[c])]
    return [r[n:] for r in M]

def det(A):
    A = [list(map(F, r)) for r in A]; n = len(A); d = F(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None: return F(0)
        if p != c: A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]; A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return d

def independent_columns(G):
    """The first columns of G that are independent, in order."""
    basis = []; rows = []
    for j in range(len(G)):
        v = [F(G[i][j]) for i in range(len(G))]
        for piv, r in rows:
            if v[piv] != 0:
                f = v[piv] / r[piv]; v = [a - f * b for a, b in zip(v, r)]
        p = next((i for i, x in enumerate(v) if x != 0), None)
        if p is not None: rows.append((p, v)); basis.append(j)
    return basis

def pinv(G):
    """Q⁺ = V (Vᵀ Q V)⁻¹ Vᵀ for any basis V of range(Q), Q symmetric."""
    K = independent_columns(G)
    V = [[F(G[i][j]) for j in K] for i in range(len(G))]
    P = mul(mul(V, inv(mul(mul(T_(V), G), V))), T_(V))
    Gf = [list(map(F, r)) for r in G]
    assert mul(mul(Gf, P), Gf) == Gf and mul(mul(P, Gf), P) == P and mul(Gf, P) == T_(mul(Gf, P))
    return P, len(K)

def bareiss(G, order, border=None):
    """Fraction-free elimination of `order` as `Upper::eliminate` runs it, on G bordered by the
    reading (zero corner) when one is given. Returns the pivot record [(p, Δ_prev, Δ_p, Γ_p)], the
    zero pivots' border entries {p: β_p}, the stored rows {p: row at its pivot} and the corner."""
    n = len(G); b = n
    A = [list(map(int, r)) + [0] for r in G] + [[0] * (n + 1)]
    if border is not None:
        for i in range(n): A[i][b] = A[b][i] = int(border[i])
    live = [False] * (n + 1)
    for p in order: live[p] = True
    if border is not None: live[b] = True
    last = 1; record = []; beta = {}; stored = {}
    for p in order:
        live[p] = False
        pivot = A[p][p]
        column = [A[i][p] if live[i] else 0 for i in range(n + 1)]
        stored[p] = A[p][:]
        if pivot == 0:
            assert all(column[i] == 0 for i in range(n)), "a zero pivot with a nonzero row"
            if border is not None and column[b] != 0: beta[p] = column[b]
            continue
        record.append((p, last, pivot, column[b] if border is not None else None))
        for i in range(n + 1):
            if not live[i]: continue
            for j in range(n + 1):
                if not live[j]: continue
                num = pivot * A[i][j] - column[i] * column[j]
                assert num % last == 0
                A[i][j] = num // last
        last = pivot
    return record, beta, stored, (A[b][b] if border is not None else None), last

def forward(record_order, stored, zero_pivots, x):
    """The reading's border column from the stored rows alone: the same arithmetic, O(r²)."""
    xs = list(map(int, x)); corner = 0; gammas = []; beta = {}; done = set()
    for p, prev, piv in record_order:
        if piv == 0:
            if xs[p] != 0: beta[p] = xs[p]
            done.add(p); continue
        g = xs[p]; gammas.append((p, prev, piv, g)); done.add(p)
        for i in range(len(xs)):
            if i in done: continue
            num = piv * xs[i] - stored[p][i] * g
            assert num % prev == 0; xs[i] = num // prev
        num = piv * corner - g * g; assert num % prev == 0; corner = num // prev
    return gammas, beta, corner

def series(record): return sum((F(g * g, prev * piv) for _, prev, piv, g in record), F(0))

out = {}
fr = str

# ---------- the cells ----------
state = 20261024
def lcg():
    global state
    state = (6364136223846793005 * state + 1442695040888963407) % (1 << 64)
    return state >> 33
def draw(lo, hi): return lo + lcg() % (hi - lo + 1)

N = 12
cells = []
for _ in range(N):
    f = (1, draw(-1, 1))
    c0, c1, c2 = draw(-2, 2), draw(-2, 2), draw(-2, 2)
    c = (c0, c1, c2, c0 + c1)
    t = (draw(-2, 2), draw(-2, 2))
    cells.append((f, c, t))
X = [list(f) + list(c) for f, c, _ in cells]
G = [[sum(x[i] * x[j] for x in X) for j in range(6)] for i in range(6)]
Gp, rank = pinv(G)
nker = [0, 0, 1, 1, 0, -1]
assert rank == 5 and mv(G, nker) == [0] * 6
readings = {"x_in": [1, 1, 2, -1, 1, 1], "x_far": [1, -1, 5, 5, -4, 10], "x_out": [1, 1, 2, -1, 1, 3]}
for k, x in readings.items():
    assert (dot(nker, x) == 0) == (k != "x_out")
out["cells"] = {"G": G, "rank": rank, "kernel": nker, "readings": readings,
                "n_dot_x": {k: fr(dot(nker, x)) for k, x in readings.items()}}

# ---------- A ----------
fs = [list(map(F, f)) for f, _, _ in cells]; cs = [list(map(F, c)) for _, c, _ in cells]; ts = [list(map(F, t)) for _, _, t in cells]
H = gram(fs, fs); L = gram(fs, cs); C = gram(cs, cs); Bm = gram(ts, fs); Km = gram(ts, cs)
Hi = inv(H)
Q = sub(C, mul(mul(T_(L), Hi), L)); M = sub(Km, mul(mul(Bm, Hi), L))
Qp, rq = pinv(Q)
D = mul(mul(M, Qp), T_(M))
def c_res(x): return sub(col(x[2:]), mul(mul(T_(L), Hi), col(x[:2])))
A_rows = []
for v in ([1, 0], [0, 1], [1, -1]):
    W = mul(mul(Qp, T_(M)), col(v))
    energy = mul(mul(T_(W), Q), W)[0][0]
    drop_v = mul(mul([list(map(F, v))], D), col(v))[0][0]
    assert energy == drop_v and mul(mul(Q, Qp), W) == W
    row = {"v": v, "energy": fr(energy)}
    for k in ("x_in", "x_far", "x_out"):
        cr = c_res(readings[k])
        value = mul(T_(W), cr)[0][0]
        lev = mul(mul(T_(cr), Qp), cr)[0][0]
        projected = mul(T_(W), mul(mul(Q, Qp), cr))[0][0]
        assert value == projected and value * value <= energy * lev
        row[k] = {"value": fr(value), "leverage": fr(lev), "value_sq_over_energy_times_leverage": fr(value * value / (energy * lev)) if lev else None}
    ce = mul(Q, W)                                   # the reading at which the bound is tight
    lev = mul(mul(T_(ce), Qp), ce)[0][0]; value = mul(T_(W), ce)[0][0]
    assert value * value == energy * lev
    row["tight_at_Q_W"] = True
    A_rows.append(row)
out["A"] = {"Q_rank": rq, "drop_matrix": [[fr(z) for z in r] for r in D], "forms": A_rows}

# ---------- B ----------
order = list(range(6))
rec_G, beta_G, stored, _, last_G = bareiss(G, order)
B_rows = {}
for k, x in readings.items():
    rec, beta, stored_b, corner, last = bareiss(G, order, x)
    h_series = series(rec); h_corner = F(-corner, last)
    plan = []
    zero = set(p for p in order if p not in [r[0] for r in rec_G])
    for p in order:
        if p in zero: plan.append((p, None, 0))
        else:
            r = next(r for r in rec_G if r[0] == p); plan.append((p, r[1], r[2]))
    gam, beta_f, corner_f = forward(plan, stored, zero, x)
    assert [g[3] for g in gam] == [r[3] for r in rec] and beta_f == beta and corner_f == corner
    assert h_series == h_corner
    if not beta:
        assert h_series == dot(x, mv(Gp, x))
    B_rows[k] = {"pivots": [(p, prev, piv) for p, prev, piv, _ in rec], "Gamma": [g for *_, g in rec],
                 "corner": corner, "last_pivot": last, "leverage": fr(h_series), "beta": beta,
                 "terms": [fr(F(g * g, prev * piv)) for _, prev, piv, g in rec],
                 "equals_pinv": h_series == dot(x, mv(Gp, x)), "pinv_leverage": fr(dot(x, mv(Gp, x)))}
out["B"] = {"order": order, "zero_pivots": sorted(zero), "readings": B_rows,
            "forward_pass_from_stored_rows_equals_bordered_elimination": True}

# ---------- C ----------
orders = {"0..5": list(range(6)), "5..0": list(range(5, -1, -1)), "2,3,0,1,4,5": [2, 3, 0, 1, 4, 5]}
C_rows = {}
for k, x in readings.items():
    by_order = {}
    for name, o in orders.items():
        rec, beta, _, corner, last = bareiss(G, o, x)
        h = F(-corner, last)
        # β_p / Δ = n_pᵀ x, n_p = e_p − (the pivots' solve for column p)
        Kp = [r[0] for r in rec]
        for p, bp in beta.items():
            GK = [[G[i][j] for j in Kp] for i in Kp]
            a = mv(inv(GK), [G[i][p] for i in Kp])
            n_p = [F(0)] * 6; n_p[p] = F(1)
            for i, ai in zip(Kp, a): n_p[i] -= ai
            assert mv(G, n_p) == [0] * 6
            # Δ at the zero pivot is the last nonzero pivot reached before it
            reached = [r for r in rec if o.index(r[0]) < o.index(p)]
            delta = reached[-1][2] if reached else 1
            assert F(bp, delta) == dot(n_p, x)
        by_order[name] = {"leverage": fr(h), "beta": beta}
    vals = set(v["leverage"] for v in by_order.values())
    resid = [F(x[i]) - z for i, z in enumerate(mv(mul([list(map(F, r)) for r in G], Gp), x))]
    res_sq = dot(resid, resid)
    C_rows[k] = {"orders": by_order, "orders_agree": len(vals) == 1, "pinv": fr(dot(x, mv(Gp, x))),
                 "residual_sq": fr(res_sq)}
    assert (len(vals) == 1 and all(not v["beta"] for v in by_order.values())) == (k != "x_out")
# the regularized leverage of x_out
x = readings["x_out"]; xpar = mv(mul([list(map(F, r)) for r in G], Gp), x)
res_sq = F(C_rows["x_out"]["residual_sq"]); lev_par = dot(xpar, mv(Gp, xpar))
reg = []
for e in range(1, 7):
    eps = F(1, 10 ** e)
    Ge = add([list(map(F, r)) for r in G], [[eps * z for z in r] for r in eye(6)])
    lev = dot(x, mv(inv(Ge), x))
    gap = eps * lev - res_sq
    assert 0 <= gap <= eps * lev_par
    reg.append({"eps": fr(eps), "eps_times_leverage": float(eps * lev), "gap_bound": fr(eps * lev_par)})
C_reg = {"residual_sq": fr(res_sq), "steps": reg}
# training-equivalent forms: min-norm, plus s·n, and the pivot chart's basic form
v = [1, -1]
rhs = [sum(F(vv) * t[j] * xx[i] for xx, (_, _, t) in zip(X, cells) for j, vv in enumerate(v)) for i in range(6)]
w0 = mv(Gp, rhs)
Kb = [r[0] for r in rec_G]
wb_K = mv(inv([[G[i][j] for j in Kb] for i in Kb]), [rhs[i] for i in Kb])
wb = [F(0)] * 6
for i, z in zip(Kb, wb_K): wb[i] = z
forms = {"min_norm": w0, "min_norm_plus_n": [a + b for a, b in zip(w0, nker)], "min_norm_minus_2n": [a - 2 * b for a, b in zip(w0, nker)], "basic_pivot_chart": wb}
energy0 = dot(w0, mv(G, w0))
train0 = [dot(w0, xx) for xx in X]
C_forms = {}
for name, w in forms.items():
    assert [dot(w, xx) for xx in X] == train0 and dot(w, mv(G, w)) == energy0
    C_forms[name] = {k: fr(dot(w, x)) for k, x in readings.items()}
assert len(set(f["x_in"] for f in C_forms.values())) == 1 and len(set(f["x_out"] for f in C_forms.values())) > 1
# the bound in each chart: min-norm with pinv leverage, basic form with the pivot chart's leverage
for k, x in readings.items():
    v0 = dot(w0, x); assert v0 * v0 <= energy0 * dot(x, mv(Gp, x))
    rec, _, _, corner, last = bareiss(G, list(range(6)), x)
    vb = dot(wb, x); assert vb * vb <= energy0 * F(-corner, last)
out["C"] = {"readings": C_rows, "regularized_x_out": C_reg, "forms_value": C_forms, "form_energy": fr(energy0),
            "bound_holds_in_each_chart": True}

# ---------- D ----------
A = [[1, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 0, 1, -2, 0], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1]]
assert det(A) in (1, -1)
GA = [[sum(A[i][k] * G[k][l] * A[j][l] for k in range(6) for l in range(6)) for j in range(6)] for i in range(6)]
GAp, _ = pinv(GA)
D_rows = {}
for k, x in readings.items():
    xa = [sum(A[i][j] * x[j] for j in range(6)) for i in range(6)]
    h0 = dot(x, mv(Gp, x)); h1 = dot(xa, mv(GAp, xa))
    rec, beta, _, corner, last = bareiss(GA, list(range(6)), xa)
    res = [F(xa[i]) - z for i, z in enumerate(mv(mul([list(map(F, r)) for r in GA], GAp), xa))]
    D_rows[k] = {"pinv_before": fr(h0), "pinv_after": fr(h1), "pivot_chart_after": fr(F(-corner, last)),
                 "beta_after": beta, "residual_sq_after": fr(dot(res, res))}
    assert (h0 == h1) or k == "x_out"
    assert bool(beta) == (k == "x_out")
out["D"] = {"rebase": A, "readings": D_rows}

# ---------- E ----------
E_rows = {}
for k, x in readings.items():
    rec, _, _, corner, last = bareiss(G, list(range(6)), x)
    face = sum((F(g * g, prev * piv) for p, prev, piv, g in rec if p < 2), F(0))
    pool = sum((F(g * g, prev * piv) for p, prev, piv, g in rec if p >= 2), F(0))
    f = list(map(F, x[:2])); cr = c_res(x)
    assert face == dot(f, mv(Hi, f))
    pool_pinv = mul(mul(T_(cr), Qp), cr)[0][0]
    if k != "x_out": assert pool == pool_pinv
    E_rows[k] = {"face_part": fr(face), "pool_part_pivot_chart": fr(pool), "pool_part_pinv": fr(pool_pinv)}
out["E"] = E_rows

# ---------- F ----------
Gt = eye(6); prod_ = F(1); hs = []; rs = []; beta_t = [F(0)] * 6; bacc = [F(0)] * 6
ys = [F(t[0]) for _, _, t in cells]
for xx, y in zip(X, ys):
    xf = list(map(F, xx))
    Gi = inv(Gt)
    h = dot(xf, mv(Gi, xf)); hs.append(h); prod_ *= 1 + h
    pred = dot(xf, mv(Gi, bacc)); rs.append(y - pred)
    Gt = add(Gt, outer(xf, xf)); bacc = [a + y * b for a, b in zip(bacc, xf)]
ratio = det(Gt) / det(eye(6))
assert prod_ == ratio
lhs = sum((r * r / (1 + h) for r, h in zip(rs, hs)), F(0))
bvec = bacc; pen = dot(ys, ys) - dot(bvec, mv(inv(Gt), bvec))
assert lhs == pen
train_lev = [dot(list(map(F, xx)), mv(Gp, list(map(F, xx)))) for xx in X]
assert sum(train_lev) == rank
def charpoly(Am):
    n = len(Am); Mk = mat(n, n); c = [F(1)]
    for k in range(1, n + 1):
        Mk = add(mul(Am, Mk), [[c[-1] * z for z in r] for r in eye(n)])
        c.append(-sum((mul(Am, Mk)[i][i] for i in range(n)), F(0)) / k)
    return c                                          # det(λI − A) = Σ c_k λ^(n−k)
cp = charpoly([list(map(F, r)) for r in G])
e = [(-1) ** k * c for k, c in enumerate(cp)]       # e_k(G): det(I + mG) = Σ e_k m^k
for m in (1, 2, 3, 8):
    assert det(add(eye(6), [[F(m) * z for z in r] for r in G])) == sum(ek * m ** k for k, ek in enumerate(e))
assert e[6] == 0 and e[5] != 0
out["F"] = {"leverages_as_they_arrive": [fr(h) for h in hs], "product_of_one_plus_h": fr(prod_), "det_ratio": fr(ratio),
            "charge_bits": round(0.5 * log2(ratio), 4), "prequential_identity": [fr(lhs), fr(pen)],
            "training_leverages": [fr(h) for h in train_lev], "sum_training_leverages": fr(sum(train_lev)),
            "e_k_of_G": [fr(z) for z in e], "degree_of_det_I_plus_mG": max(k for k, z in enumerate(e) if z != 0)}

# ---------- G ----------
Xg = [[1, 0, 1], [0, 1, 1], [1, 1, 2], [1, -1, 0], [2, 1, 3], [0, 2, 2]]     # third column = first + second
Gg = [[sum(r[i] * r[j] for r in Xg) for j in range(3)] for i in range(3)]
Ggp, rg = pinv(Gg)
assert rg == 2
G_rows = {}
for name, xs_ in (("in_range", [1, 2, 3]), ("far_in_range", [3, -2, 1]), ("out_of_range", [1, 2, 2])):
    xs_f = list(map(F, xs_)); h = dot(xs_f, mv(Ggp, xs_f))
    proj = mv(mul([list(map(F, r)) for r in Gg], Ggp), xs_f)
    by_beta = {}
    for beta in ([1, -2, 3], [0, 0, 1], [2, 5, -1]):
        tot = F(0); mean_pred = F(0)
        for noise in product((1, -1), repeat=len(Xg) + 1):
            y = [dot(r, beta) + e_ for r, e_ in zip(Xg, noise)]
            b = [sum(F(r[i]) * yy for r, yy in zip(Xg, y)) for i in range(3)]
            yhat = dot(xs_f, mv(Ggp, b)); ystar = dot(xs_f, beta) + noise[-1]
            tot += (ystar - yhat) ** 2; mean_pred += yhat
        n_ = 2 ** (len(Xg) + 1); mse = tot / n_
        bias = dot(xs_f, beta) - dot(proj, beta)
        assert mse == 1 + h + bias * bias and mean_pred / n_ == dot(proj, beta)
        by_beta[str(beta)] = {"mse": fr(mse), "bias_sq": fr(bias * bias)}
    assert (len(set(v["mse"] for v in by_beta.values())) == 1) == (name != "out_of_range")
    G_rows[name] = {"reading": xs_, "leverage": fr(h), "one_plus_h": fr(1 + h), "by_true_coefficient": by_beta}
out["G"] = {"X": Xg, "rank": rg, "noise_patterns": 2 ** (len(Xg) + 1), "readings": G_rows}

# ---------- H ----------
def split(Gm, K, v):
    GK = [[F(Gm[i][j]) for j in K] for i in K]
    y = mv(inv(GK), [F(v[i]) for i in K])
    vs = [sum((F(Gm[i][j]) * yj for j, yj in zip(K, y)), F(0)) for i in range(len(Gm))]
    rho = [F(a) - b for a, b in zip(v, vs)]
    return vs, rho, dot([F(v[i]) for i in K], y)
Qx = [[1, 1], [1, 1]]; Qxp, _ = pinv(Qx); wx = [F(1), F(0)]; cx = [1, 0]
vs, rho, hK = split(Qx, [0], cx)
ex = {"w_dot_c": fr(dot(wx, cx)), "energy": fr(dot(wx, mv(Qx, wx))), "pinv_leverage": fr(dot(cx, mv(Qxp, cx))),
      "pinv_bound_sq": fr(dot(wx, mv(Qx, wx)) * dot(cx, mv(Qxp, cx))), "v_s": [fr(z) for z in vs], "rho": [fr(z) for z in rho],
      "chart_leverage": fr(hK), "w_dot_v_s": fr(dot(wx, vs)), "w_dot_rho": fr(dot(wx, rho))}
assert dot(wx, cx) ** 2 > dot(wx, mv(Qx, wx)) * dot(cx, mv(Qxp, cx))
assert dot(wx, vs) ** 2 == dot(wx, mv(Qx, wx)) * hK
H_rows = {}
ws = [[3, -1, 2, 0, 1, -2], [0, 1, -1, 2, 2, 1], [1, 1, 1, 1, 1, 1]]
for name, o in orders.items():
    rec, _, _, _, _ = bareiss(G, o)
    K = [r[0] for r in rec]
    for k, x in readings.items():
        vs, rho, hK = split(G, K, x)
        assert all(rho[i] == 0 for i in K) and mv(mul([list(map(F, r)) for r in G], Gp), vs) == vs
        assert (any(rho) == (k == "x_out"))
        rec_b, beta, _, corner, last = bareiss(G, o, x)
        assert F(-corner, last) == hK
        for p, bp in beta.items():
            reached = [r for r in rec_b if o.index(r[0]) < o.index(p)]
            assert F(bp, reached[-1][2] if reached else 1) == rho[p]
        for w in ws:
            wf = list(map(F, w)); en = dot(wf, mv(G, wf)); val = dot(wf, vs)
            assert val * val <= en * hK
            for s_ in (1, -3):
                assert dot([a + s_ * b for a, b in zip(wf, nker)], vs) == val
        H_rows.setdefault(k, {})[name] = {"v_s": [fr(z) for z in vs], "rho": [fr(z) for z in rho], "chart_leverage": fr(hK),
                                          "values_w": [fr(dot(list(map(F, w)), vs)) for w in ws], "open_values_w": [fr(dot(list(map(F, w)), rho)) for w in ws]}
out["H"] = {"gpt6_example": ex, "forms": ws, "readings": H_rows}

json.dump(out, sys.stdout, indent=1, default=str)
print()
