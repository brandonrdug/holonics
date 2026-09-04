"""Phase 2 -- read every OV circuit in the text tower, against a matched null.

336 heads (42 layers x 8 query heads). For each, the nonzero spectrum of W_OV = W_O W_V is
computed from the d x d small side, so the 2560x2560 circuit is never formed. Peak residency is
one layer's projections.

Every returned quantity is a Ratio or a Winding:
  participation ratio of |lambda|   Ratio    (scale-free effective spread)
  conjugate pair count              Winding  (how many turns the circuit carries)
  real-positive / real-negative     Winding  (no turn / half turn)
  turn quantiles                    Ratio    (pure angles)
No norms, no condition numbers, no raw magnitudes.
"""
import json
import sys

import numpy as np

from read_map import Map, participation_ratio, winding_census

rng = np.random.default_rng(20260813)


def spectrum(Wo, Wv):
    return np.linalg.eigvals((Wv @ Wo).astype(np.float64))


def faces(ev):
    w = winding_census(ev)
    a = np.abs(ev)
    return {
        "pairs": w["conjugate_pairs"],
        "real_pos": w["real_positive"],
        "real_neg": w["real_negative"],
        "pr": participation_ratio(a),
        "turns": w["turns"],
    }


def main():
    m = Map()
    species = m.layer_species()
    nq = m.text["num_attention_heads"]
    nkv = m.text["num_key_value_heads"]
    rows = []
    for L in range(m.text["num_hidden_layers"]):
        v = m.take(f"model.language_model.layers.{L}.self_attn.v_proj.weight").astype(np.float64)
        o = m.take(f"model.language_model.layers.{L}.self_attn.o_proj.weight").astype(np.float64)
        d = m.text["global_head_dim"] if species[L] == "full_attention" else m.text["head_dim"]
        sv, so = float(v.std()), float(o.std())
        for H in range(nq):
            g = H // (nq // nkv)
            Wv = v[g * d : (g + 1) * d, :]
            Wo = o[:, H * d : (H + 1) * d]
            f = faces(spectrum(Wo, Wv))
            n = faces(spectrum(rng.standard_normal((2560, d)) * so, rng.standard_normal((d, 2560)) * sv))
            rows.append({
                "layer": L, "head": H, "species": species[L], "d": d,
                "pairs": f["pairs"], "real_pos": f["real_pos"], "real_neg": f["real_neg"],
                "pr": f["pr"], "turn_med": float(np.median(f["turns"])) if f["turns"].size else None,
                "null_pairs": n["pairs"], "null_real_pos": n["real_pos"],
                "null_real_neg": n["real_neg"], "null_pr": n["pr"],
            })
        print(f"  layer {L:2} ({species[L][:8]}) done", file=sys.stderr)
    json.dump(rows, open("sweep.json", "w"))

    import statistics as S
    print("\n=== OV CIRCUIT SWEEP: 336 heads, each against its own matched null ===\n")
    for sp in ("sliding_attention", "full_attention"):
        r = [x for x in rows if x["species"] == sp]
        print(f"{sp}  (n={len(r)}, head_dim={r[0]['d']})")
        for key, nkey, label in (("pr", "null_pr", "participation ratio (Ratio)"),
                                 ("real_pos", "null_real_pos", "real-positive count (Winding)"),
                                 ("real_neg", "null_real_neg", "real-negative count (Winding)"),
                                 ("pairs", "null_pairs", "conjugate pairs   (Winding)")):
            a = [x[key] for x in r]
            b = [x[nkey] for x in r]
            print(f"   {label:32} real med {S.median(a):9.2f}   null med {S.median(b):9.2f}"
                  f"   ratio {S.median(a)/max(S.median(b),1e-9):6.3f}")
        sep = sum(1 for x in r if x["pr"] < 0.75 * x["null_pr"])
        print(f"   heads whose PR is <75% of their own null: {sep}/{len(r)}")
        print()

    print("=== the six most concentrated heads (lowest PR relative to their null) ===")
    ranked = sorted(rows, key=lambda x: x["pr"] / x["null_pr"])[:6]
    for x in ranked:
        print(f"   L{x['layer']:2} H{x['head']}  {x['species'][:8]}  PR {x['pr']:8.2f} "
              f"vs null {x['null_pr']:8.2f}  ({x['pr']/x['null_pr']:.3f})  "
              f"pairs {x['pairs']:3}  real+ {x['real_pos']:3}  real- {x['real_neg']:3}")


if __name__ == "__main__":
    main()
