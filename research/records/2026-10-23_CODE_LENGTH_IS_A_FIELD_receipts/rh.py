# The primes' signs through the same lens, and through the count lens. usage: python3 -I rh.py RUNDIR OUT.json
import json, sys, numpy as np
from math import lgamma, log, log2, pi, sqrt
R, out = sys.argv[1], sys.argv[2]
mu = np.fromfile(R + "/mu.bin", np.uint8).astype(np.int64) - 1
lam = np.fromfile(R + "/lam.bin", np.uint8).astype(np.int64) * 2 - 1
N = len(mu); n = np.arange(1, N + 1)
assert list(mu[:12]) == [1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0] and list(lam[:12]) == [1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1]
res = {"N": N}
octs = [2 ** k for k in range(4, 23)]
def parts(prefix, seq_cells, zero_cell=None):
    P = np.fromfile(R + "/%s.p" % prefix, "<f4").reshape(-1, 4).astype(np.float64)
    u = seq_cells
    cast = -np.log2(1 - P[:, 3])                 # the unused cell value (and 2 for the hand): the alphabet cast
    Pn = P / (1 - P[:, 3])[:, None]
    tot = -np.log2(P[np.arange(len(u)), u])
    d = {"total": tot, "cast": cast}
    if zero_cell is not None:
        isz = u == zero_cell
        zb = np.where(isz, -np.log2(Pn[:, zero_cell]), -np.log2(1 - Pn[:, zero_cell]))
        sg = np.where(isz, 0.0, -np.log2(Pn[np.arange(len(u)), u] / (1 - Pn[:, zero_cell])))
        d["zero"] = zb; d["sign"] = sg; d["isz"] = isz
    else:
        cast2 = -np.log2(1 - P[:, 2] - P[:, 3])  # the hand uses two of four cell values
        d["cast"] = cast2
        d["sign"] = -np.log2(P[np.arange(len(u)), u] / (P[:, 0] + P[:, 1]))
    assert np.allclose(tot, d["cast"] + d.get("zero", 0) + d["sign"], atol=1e-4)
    return d
def octave_table(d, mask_sign=None):
    rows = []
    lo = 0
    for hi in octs:
        s = slice(lo, hi)
        row = {"n_hi": hi}
        for k in ("total", "cast", "zero", "sign"):
            if k in d:
                if k == "sign" and mask_sign is not None:
                    m = ~mask_sign[s]; row[k] = float(d[k][s][m].mean())
                else: row[k] = float(d[k][s].mean())
        rows.append(row); lo = hi
    return rows
mu_cells = (mu + 1).astype(np.int64); lam_cells = ((lam + 1) // 2).astype(np.int64)
for name, pre, cells, zc in (("mu, no clock", "mu1", mu_cells, 1), ("mu, clock mod 4", "mu4", mu_cells, 1), ("lambda, no clock", "lam1", lam_cells, None)):
    d = parts(pre, cells, zc)
    tab = octave_table(d, d.get("isz"))
    summ = {k: float(d[k].sum()) for k in ("total", "cast", "zero", "sign") if k in d}
    if "isz" in d: summ["nonzero_cells"] = int((~d["isz"]).sum())
    # equation of state of each part on its own clock (octaves)
    for k in ("zero", "sign"):
        if k in d:
            x = d[k] if k == "zero" else (d[k][~d["isz"]] if "isz" in d else d[k])
            L = np.cumsum(x); V = np.array([2 ** j for j in range(10, 23) if 2 ** j <= len(x)])
            summ["w_" + k] = [float(-log2(L[V[i] - 1] / L[V[i - 1] - 1])) for i in range(1, len(V))]
    res[name] = {"octaves": tab, "sums": summ}
# the count lens on the hand (lambda) and on mu's signs: exact KT code against the floor
def kt_bits(a, b):  # -log2 of the KT probability of a binary sequence with a ones and b zeros
    return -(lgamma(a + .5) + lgamma(b + .5) - 2 * lgamma(.5) - lgamma(a + b + 1)) / log(2)
def h2(p): return 0.0 if p <= 0 or p >= 1 else -(p * log2(p) + (1 - p) * log2(1 - p))
count = []
Lc = np.cumsum(lam); Mc = np.cumsum(mu); Qc = np.cumsum(mu != 0)
for X in octs:
    Lx = int(Lc[X - 1]); a = (X + Lx) // 2; b = X - a
    D = X * (1 - h2(a / X)); kt = kt_bits(a, b)
    Mx = int(Mc[X - 1]); Q = int(Qc[X - 1]); am = (Q + Mx) // 2; bm = Q - am
    Dm = Q * (1 - h2(am / Q)); ktm = kt_bits(am, bm)
    count.append({"N": X, "L": Lx, "L_over_sqrtN": Lx / sqrt(X), "deficit": D, "sandwich_lo": Lx * Lx / (2 * X * log(2)),
                  "sandwich_hi": Lx * Lx / X, "kt_minus_floor": kt - X, "half_log2N": 0.5 * log2(X),
                  "M": Mx, "Q": Q, "M_over_sqrtN": Mx / sqrt(X), "mu_deficit": Dm, "mu_kt_minus_floor": ktm - Q})
    assert count[-1]["sandwich_lo"] - 1e-9 <= D <= count[-1]["sandwich_hi"] + 1e-9
res["count_lens"] = count
# the coincidence spectrum (Kasiski/Friedman) of the hand and of mu's zeros: lag correlations
lags = list(range(1, 257)) + [int(round(2 ** (k / 8))) for k in range(65, 8 * 20)]
lags = sorted(set(l for l in lags if l < N // 2))
ch = [float((lam[:-l] * lam[l:]).mean()) for l in lags]
z = (mu == 0).astype(np.float64); pz = z.mean()
zc = [float((z[:-l] * z[l:]).mean() / pz ** 2 - 1) for l in lags]
sg = np.where(mu != 0, mu, 0).astype(np.float64)
sc = [float((sg[:-l] * sg[l:]).sum() / ((mu[:-l] != 0) & (mu[l:] != 0)).sum()) for l in lags]
res["spectrum"] = {"lags": lags, "lambda_corr": ch, "mu_zero_excess": zc, "mu_sign_corr": sc, "rms_noise": 1 / sqrt(N)}
json.dump(res, open(out, "w"))
for name in ("mu, no clock", "mu, clock mod 4", "lambda, no clock"):
    s = res[name]["sums"]
    print(name, {k: (round(v / N, 5) if isinstance(v, float) else v) for k, v in s.items() if not k.startswith("w_")})
    for k in s:
        if k.startswith("w_"): print("   ", k, " ".join("%.3f" % x for x in s[k]))
    print("   per octave (n up to): " + " | ".join("%d: %s" % (r["n_hi"], ",".join("%s %.3f" % (k[0], r[k]) for k in ("zero", "sign", "cast") if k in r)) for r in res[name]["octaves"][::3]))
print("count lens on the hand (N, L/sqrtN, deficit bits, KT - floor, half log2 N):")
for c in count[::2]:
    print("  %8d %+.3f  D %.3f  kt-floor %.2f  ½log2N %.2f | mu: M/sqrtN %+.3f D %.3f kt-floor %.2f" % (c["N"], c["L_over_sqrtN"], c["deficit"], c["kt_minus_floor"], c["half_log2N"], c["M_over_sqrtN"], c["mu_deficit"], c["mu_kt_minus_floor"]))
print("hand correlation at lags 1..8:", ["%+.4f" % x for x in ch[:8]], "max |.| over all lags %.4f, 1/sqrtN %.4f" % (max(abs(x) for x in ch), 1 / sqrt(N)))
print("mu sign correlation max |.| %.4f; mu zero excess at lags 1..12:" % max(abs(x) for x in sc), ["%+.3f" % x for x in zc[:12]])
