# Code length as a field over regions and passage: equation of state, floor and learning, binding,
# the lock's offset profile, and units. usage: python3 -I analyze.py RUNDIR OUT.json
import json, sys, numpy as np
R, out = sys.argv[1], sys.argv[2]
roles = np.fromfile(R + "/roles.u8", np.uint8); fine = np.fromfile(R + "/fine.u8", np.uint8)
prob = np.fromfile(R + "/prob.u32", np.uint32)
NB = len(roles)
def per_byte(path, cells_per_byte=4):
    c = np.fromfile(path, "<f4").reshape(-1, 3).astype(np.float64)
    return c.reshape(-1, cells_per_byte, 3).sum(1)
W = per_byte(R + "/whole.f32")            # bits a byte: base, node, ring
oct_cell = np.fromfile(R + "/whole.f32.oct", np.uint8)
assert len(W) == NB
REG = ["Q", "P", "N", "M"]
NAME = {"Q": "question", "P": "answer prose", "N": "answer numbers", "M": "calculation markup"}
alone = {k: per_byte(R + "/%s.f32" % k) for k in REG}
res = {"bytes": NB, "regions": {}}
LN2 = np.log(2)

def octave_curve(code):
    """cumulative code L at V = 2^k bytes of the region's own clock, and w = -log2(L(2V)/L(V))"""
    V = np.arange(1, len(code) + 1); L = np.cumsum(code)
    ks = [k for k in range(8, 64) if 2 ** k <= len(code)]
    Vk = np.array([2 ** k for k in ks] + [len(code)])
    Lk = L[Vk - 1]
    marg = [(Lk[i] - Lk[i - 1]) / (Vk[i] - Vk[i - 1]) for i in range(1, len(Vk))]
    w = [-np.log(Lk[i] / Lk[i - 1]) / np.log(Vk[i] / Vk[i - 1]) for i in range(1, len(Vk))]
    return Vk.tolist(), Lk.tolist(), marg, w

def fit_floor(Vk, marg):
    """marginal rate per octave ~ h + c V^-alpha, V the octave's upper volume; grid alpha, least squares h, c >= 0"""
    V = np.array(Vk[1:], float); y = np.array(marg)
    best = None
    for a in np.linspace(0.02, 1.5, 149):
        X = np.stack([np.ones_like(V), V ** -a], 1)
        coef, *_ = np.linalg.lstsq(X, y, rcond=None)
        if coef[1] < 0: continue
        r = ((X @ coef - y) ** 2).sum()
        if best is None or r < best[0]: best = (r, a, coef[0], coef[1])
    if best is None: return None
    r, a, h, c = best
    return {"alpha": float(a), "h": float(h), "c": float(c), "rms": float(np.sqrt(r / len(y)))}

for k in REG:
    sel = roles == REG.index(k)
    ctx = W[sel]; al = alone[k]
    assert len(ctx) == len(al)
    reg = {"name": NAME[k], "bytes": int(sel.sum()), "share": float(sel.mean())}
    for arm, j in (("base", 0), ("node", 1)):
        for where, code in (("context", ctx[:, j]), ("alone", al[:, j])):
            Vk, Lk, marg, w = octave_curve(code)
            fit = fit_floor(Vk, marg)
            d = {"V": Vk, "L": Lk, "marginal": marg, "w": w, "fit": fit, "rate": float(code.mean())}
            if fit:
                h = fit["h"]; Vf = np.array(Vk, float); Lf = np.array(Lk)
                d["floor_share"] = (h * Vf / Lf).tolist()
            reg["%s_%s" % (arm, where)] = d
        b = al[:, j] - ctx[:, j]
        Vk, Bk, _, wb = octave_curve(np.maximum(b, -1e9))
        reg["binding_" + arm] = {"V": Vk, "B": Bk, "w": wb, "per_byte": float(b.mean()),
                                 "fraction_of_alone": float(b.sum() / al[:, j].sum())}
    res["regions"][k] = reg

# expansion and contraction per partition: 20 blocks of problems, bits a byte per fine role and region
P = int(prob.max()) + 1; NBLK = 20
blk = (prob.astype(np.int64) * NBLK) // P
FINE = ["question prose", "question digit", "separator", "answer prose", "answer digit (prose)",
        "calc markup", "calc operand digit", "calc result digit", "digit after >> (repeat of result)",
        "#### marker", "final answer digit"]
grid = {}
for fi, fn in enumerate(FINE):
    rows = []
    for b in range(NBLK):
        s = (fine == fi) & (blk == b)
        rows.append([int(s.sum()), float(W[s, 0].sum()), float(W[s, 1].sum())])
    grid[fn] = rows
for k in REG:
    rows = []
    for b in range(NBLK):
        s = (roles == REG.index(k)) & (blk == b)
        rows.append([int(s.sum()), float(W[s, 0].sum()), float(W[s, 1].sum())])
    grid["region " + NAME[k]] = rows
res["blocks"] = {"count": NBLK, "problems": P, "grid": grid}

# whole passage on the passage clock
Vk, Lk, marg, w = octave_curve(W[:, 0]); res["whole_base"] = {"V": Vk, "L": Lk, "marginal": marg, "w": w, "fit": fit_floor(Vk, marg)}
Vk, Lk, marg, w = octave_curve(W[:, 1]); res["whole_node"] = {"V": Vk, "L": Lk, "marginal": marg, "w": w, "fit": fit_floor(Vk, marg)}
tot_alone = sum(alone[k][:, 0].sum() for k in REG); tot_ctx = W[:, 0].sum()
res["multi_information_base"] = {"alone_sum": float(tot_alone), "whole": float(tot_ctx), "binding": float(tot_alone - tot_ctx)}
tot_alone1 = sum(alone[k][:, 1].sum() for k in REG); tot_ctx1 = W[:, 1].sum()
res["multi_information_node"] = {"alone_sum": float(tot_alone1), "whole": float(tot_ctx1), "binding": float(tot_alone1 - tot_ctx1)}

# the lock's offset profile ("rotation curve"): saved bits per octave of delta, per region (cells -> region of their byte)
C = np.fromfile(R + "/whole.f32", "<f4").reshape(-1, 3).astype(np.float64)
cell_role = np.repeat(roles, 4)
prof = {}
for name, s in [("all", np.ones(len(C), bool))] + [(NAME[k], cell_role == i) for i, k in enumerate(REG)]:
    o = oct_cell[s]; c = C[s]
    rows = []
    for q in range(0, 32):
        m = o == q
        if m.any(): rows.append([q, int(m.sum()), float(c[m, 0].sum() - c[m, 1].sum()), float(c[m, 0].sum())])
    prof[name] = rows
res["offset_profile"] = prof
# share drift (the cast between a region's own clock and the passage clock)
res["share_by_block"] = {NAME[k]: [float(((roles == i) & (blk == b)).sum() / (blk == b).sum()) for b in range(NBLK)] for i, k in enumerate(REG)}
json.dump(res, open(out, "w"))
# summary
for k in REG:
    r = res["regions"][k]
    print("%-20s share %.3f | ctx base %.3f node %.3f | alone base %.3f node %.3f | binding %.3f b/B (%.1f%% of alone)" % (
        r["name"], r["share"], r["base_context"]["rate"], r["node_context"]["rate"], r["base_alone"]["rate"],
        r["node_alone"]["rate"], r["binding_node"]["per_byte"], 100 * r["binding_node"]["fraction_of_alone"]))
    for where in ("context", "alone"):
        d = r["node_" + where]
        print("   node %-7s w by octave: %s" % (where, " ".join("%.3f" % x for x in d["w"])))
        print("            marginal:     %s" % " ".join("%.3f" % x for x in d["marginal"]))
        print("            fit: %s" % d["fit"])
    print("   binding w: %s" % " ".join("%.3f" % x for x in r["binding_node"]["w"]))
print("multi-information (sum alone - whole): base %.0f bits, node %.0f bits" % (res["multi_information_base"]["binding"], res["multi_information_node"]["binding"]))
print("whole node w:", " ".join("%.3f" % x for x in res["whole_node"]["w"]), res["whole_node"]["fit"])
for name, rows in prof.items():
    print("profile", name, " ".join("%d:%.0f" % (q, s) for q, n, s, b in rows))
