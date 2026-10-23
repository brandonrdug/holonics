# Motion class of each region's code flow, on its own clock, from octaves V >= 2^13 bytes:
# shear (parabolic): excess C(V) = L - hV grows by a constant per octave, marginal = h + k/(2 V ln 2)
# boost (hyperbolic): excess grows by a constant factor per octave, marginal = h + c V^-alpha, 0 < alpha < 1
# turn (on the circle): no excess, marginal = h (w = -1)
# usage: python3 -I classify.py field.json
import json, sys, numpy as np
r = json.load(open(sys.argv[1]))
def fits(V, y):
    V = np.array(V, float); y = np.array(y)
    out = {}
    X = np.stack([np.ones_like(V)], 1); c, *_ = np.linalg.lstsq(X, y, rcond=None); out["turn"] = (float(np.sqrt(((X @ c - y) ** 2).mean())), {"h": float(c[0])})
    X = np.stack([np.ones_like(V), 1 / (2 * V * np.log(2))], 1); c, *_ = np.linalg.lstsq(X, y, rcond=None); out["shear"] = (float(np.sqrt(((X @ c - y) ** 2).mean())), {"h": float(c[0]), "k": float(c[1])})
    best = None
    for a in np.linspace(0.02, 0.98, 97):
        X = np.stack([np.ones_like(V), V ** -a], 1); c, *_ = np.linalg.lstsq(X, y, rcond=None)
        e = float(np.sqrt(((X @ c - y) ** 2).mean()))
        if c[1] > 0 and (best is None or e < best[0]): best = (e, {"h": float(c[0]), "c": float(c[1]), "alpha": float(a)})
    if best: out["boost"] = best
    return out
res = {}
for k, reg in r["regions"].items():
    for where in ("context", "alone"):
        d = reg["node_" + where]
        V = d["V"][1:]; y = d["marginal"]
        sel = [i for i, v in enumerate(V) if v >= 2 ** 13]
        f = fits([V[i] for i in sel], [y[i] for i in sel])
        res[reg["name"] + " / " + where] = f
d = r["whole_node"]; V = d["V"][1:]; sel = [i for i, v in enumerate(V) if v >= 2 ** 13]
res["whole passage"] = fits([V[i] for i in sel], [d["marginal"][i] for i in sel])
for name, f in res.items():
    best = min(f, key=lambda m: f[m][0])
    print("%-36s best %-5s | " % (name, best) + " | ".join("%s rms %.4f %s" % (m, e, {a: round(b, 4) for a, b in p.items()}) for m, (e, p) in f.items()))
json.dump(res, open("classes.json", "w"))
