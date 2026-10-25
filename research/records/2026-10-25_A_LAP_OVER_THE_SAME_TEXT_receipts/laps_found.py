"""Laps over the same passage, read exactly (Fractions and integers; floats only in printed readings).

Every cell of {±1}^5 is met r times: x1..x4 are offered to the machine as faces, z is not (it is the
floor). A face is a monomial in x1..x4 (a product of present signs). One lap:
  1. rereads the passage at the held constitution: H = Σ f̄f̄ᵀ, B = Σ t f̄ᵀ, T = Σ t² (the tension
     record's moments), so the tension is S = T − B H⁺ Bᵀ;
  2. generates its pool from the present faces alone: every product of two present faces that the
     present faces do not already span;
  3. founds, rank by rank, the candidate with the largest drop M Q⁺ Mᵀ while its code saving
     (N/2) log2(S / (S − drop)) exceeds its charge ½ log2 N + log2 |pool|. The comparison is exact:
     (S / (S − drop))^N > N |pool|².
A lap that founds nothing is the fixed point. No lap count is chosen.

A. A reread at one constitution returns the same moments, so a lap that founds nothing changes nothing.
B. A staircase is climbed one founding lap per step, and the tension falls to the floor in steps.
C. A parity with no lower part founds nothing at any lap (dormant); a pool that offers the whole
   conjunction at once carries it, so the reach is the pool's composition, not the passage.
D. A weak first step is under its charge on a short passage and over it on a long one: the passage
   length lets the climb start, and the laps carry it.
E. Products of founded faces double the reach: two degree-2 faces found on lap 1, their degree-4
   product on lap 2.
"""
from fractions import Fraction as Fr
from itertools import product, combinations
from math import log2
import json, sys

VARS = (1, 2, 3, 4)
CELLS = list(product((1, -1), repeat=5))  # (x1, x2, x3, x4, z)


def mono_value(m, cell):
    v = 1
    for i in m:
        v *= cell[i - 1]
    return v


def name(m):
    return "1" if not m else "".join(f"x{i}" for i in sorted(m))


def solve(H, b):
    """One solution of H w = b on range(H), exactly (free variables zero)."""
    n = len(H)
    A = [H[i][:] + [b[i]] for i in range(n)]
    piv, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, n) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(n):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * x for a, x in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    w = [Fr(0)] * n
    for i, c in enumerate(piv):
        w[c] = A[i][n]
    return w


def moments(faces, target, r):
    fb = [[Fr(mono_value(m, c)) for m in faces] for c in CELLS]
    t = [target(c) for c in CELLS]
    n = len(faces)
    H = [[r * sum(fb[k][i] * fb[k][j] for k in range(len(CELLS))) for j in range(n)] for i in range(n)]
    B = [r * sum(t[k] * fb[k][i] for k in range(len(CELLS))) for i in range(n)]
    T = r * sum(x * x for x in t)
    return H, B, T


def tension(faces, target, r):
    H, B, T = moments(faces, target, r)
    w = solve(H, B)
    return T - sum(a * b for a, b in zip(B, w))


def drop(faces, cand, target, r):
    """M Q⁺ Mᵀ: what reading cand beside the faces removes from the tension (scalar covector)."""
    H, B, _ = moments(faces, target, r)
    t = [target(c) for c in CELLS]
    cv = [Fr(mono_value(cand, c)) for c in CELLS]
    fb = [[Fr(mono_value(m, c)) for m in faces] for c in CELLS]
    K = r * sum(a * b for a, b in zip(t, cv))
    L = [r * sum(fb[k][i] * cv[k] for k in range(len(CELLS))) for i in range(len(faces))]
    C = r * sum(x * x for x in cv)
    HB = solve(H, B)
    HL = solve(H, L)
    M = K - sum(a * b for a, b in zip(HB, L))
    Q = C - sum(a * b for a, b in zip(L, HL))
    return Fr(0) if Q == 0 else M * M / Q


def spanned(faces, cand):
    return cand in faces  # monomials over all cells are orthonormal, so span is membership


def pool_of(faces, degree_cap=None, direct=None):
    if direct is not None:
        return [m for m in direct if not spanned(faces, m)]
    out = set()
    for a, b in combinations([m for m in faces if m], 2):
        p = frozenset(a ^ b)
        if not spanned(faces, p):
            out.add(p)
    return sorted(out, key=lambda m: (len(m), sorted(m)))


def passes(S, S2, N, P):
    """(S / S2)^N > N P², exactly; True when the saving exceeds the charge."""
    if S2 == 0:
        return True
    q = S / S2
    return q.numerator ** N * 1 > N * P * P * q.denominator ** N


def bits(S, S2, N):
    return round(N / 2 * log2(S / S2), 3) if S2 else None


def run_laps(target, r, direct=None, max_guard=16):
    N = 32 * r
    faces = [frozenset()] + [frozenset({i}) for i in VARS]
    laps = []
    S = tension(faces, target, r)
    for lap in range(1, max_guard + 1):
        pool = pool_of(faces, direct=direct)
        P = len(pool)
        founded = []
        live = list(pool)
        while live:
            scored = [(drop(faces, c, target, r), c) for c in live]
            d, best = max(scored, key=lambda x: (x[0], -len(x[1])))
            if d == 0 or not passes(S, S - d, N, P):
                break
            founded.append({"face": name(best), "degree": len(best), "drop": str(d),
                            "tension_before": str(S), "tension_after": str(S - d),
                            "saving_bits": bits(S, S - d, N),
                            "charge_bits": round(0.5 * log2(N) + log2(P), 3)})
            faces = faces + [best]
            S = S - d
            live.remove(best)
        laps.append({"lap": lap, "pool": P, "founded": founded, "tension": str(S)})
        if not founded:
            break  # the fixed point
    return {"N": N, "laps": laps, "faces": [name(m) for m in faces], "floor": str(Fr(N))}


def mono(*idx):
    return frozenset(idx)


def stair(c):
    x1, x2, x3, x4, z = c
    return Fr(x1 + x1 * x2 + x1 * x2 * x3 + z)


def parity(c):
    x1, x2, x3, x4, z = c
    return Fr(x1 * x2 * x3 + z)


def weak(c):
    x1, x2, x3, x4, z = c
    return Fr(1, 4) * x1 * x2 + x1 * x2 * x3 + z


def double(c):
    x1, x2, x3, x4, z = c
    return Fr(x1 * x2 + x3 * x4 + x1 * x2 * x3 * x4 + z)


out = {}
fail = []

# A. reread
f0 = [frozenset()] + [frozenset({i}) for i in VARS]
m1, m2 = moments(f0, stair, 1), moments(f0, stair, 1)
out["A_reread_same_moments"] = (m1 == m2)
S_a = tension(f0, stair, 1)
out["A_tension_held_constitution"] = [str(S_a), str(tension(f0, stair, 1))]
if m1 != m2 or S_a != Fr(96):
    fail.append("A")

# B. staircase
B_ = run_laps(stair, 1)
out["B_staircase"] = B_
got = [[f["face"] for f in l["founded"]] for l in B_["laps"]]
if got != [["x1x2"], ["x1x2x3"], []] or B_["laps"][-1]["tension"] != "32":
    fail.append("B")

# C. parity and its direct foil
C_ = run_laps(parity, 1)
out["C_parity_laps"] = C_
triples = [frozenset(s) for s in combinations(VARS, 3)]
C_direct = run_laps(parity, 1, direct=triples)
out["C_parity_direct_triples"] = C_direct
if [l["founded"] for l in C_["laps"]] != [[]] or C_["laps"][0]["tension"] != "64":
    fail.append("C laps")
if [[f["face"] for f in l["founded"]] for l in C_direct["laps"]][0] != ["x1x2x3"]:
    fail.append("C direct")

# D. weak first step: least passage at which the climb starts, and the climb there
first_r = None
for r in range(1, 65):
    res = run_laps(weak, r)
    if res["laps"][0]["founded"]:
        first_r = r
        break
out["D_weak_short"] = run_laps(weak, 1)
out["D_weak_least_multiplicity"] = first_r
out["D_weak_at_least"] = run_laps(weak, first_r)
out["D_weak_one_less"] = run_laps(weak, first_r - 1)
d_short = [[f["face"] for f in l["founded"]] for l in out["D_weak_short"]["laps"]]
d_long = [[f["face"] for f in l["founded"]] for l in out["D_weak_at_least"]["laps"]]
if d_short != [[]] or d_long != [["x1x2"], ["x1x2x3"], []]:
    fail.append("D")
if [l["founded"] for l in out["D_weak_one_less"]["laps"]] != [[]]:
    fail.append("D least")

# E. doubling
E_ = run_laps(double, 1)
out["E_doubling"] = E_
e_got = [sorted(f["face"] for f in l["founded"]) for l in E_["laps"]]
if e_got != [["x1x2", "x3x4"], ["x1x2x3x4"], []]:
    fail.append("E")

out["fail"] = fail
json.dump(out, sys.stdout, indent=1)
print()
sys.exit(1 if fail else 0)
