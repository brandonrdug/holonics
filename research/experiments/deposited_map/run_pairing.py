"""Phase 3 -- the receiver family, which is Brandon's own (MEANING_DEFINED.md:64-69):
"'two' as a string can have a similar causal composition to '2' ... It is in the phase
distributions and calculus."

THE TEST. For each OV circuit, form the induced map on the probe family
    Phi = E_S (W_O W_V) E_S^T
which is exactly gauge-invariant and lives in the vocabulary basis the model itself supplies.
Then ask whether transport couples a digit to its WORD -- 2 <-> two -- more than to the rest of
the family.

THE OBSERVABLE IS A RATIO, as the horizon law requires:
    lift(i) = |Phi[i, pair(i)]| / median_j |Phi[i, j]|
a quotient of two quantities in one frame, so it is dimensionless and survives the horizon.
No norm, no magnitude, no cosine similarity is reported.

THREE FRAMES, and the reading is refused unless all three separate:
  real circuit + true pairing      -- the claim
  real circuit + shuffled pairing  -- kills "this head lifts everything"
  null circuit + true pairing      -- kills "this pairing lifts under any matrix"
"""
import json
import sys

import numpy as np

from read_map import Map

rng = np.random.default_rng(20260813)

DIGIT_WORD = [("0", "zero"), ("1", "one"), ("2", "two"), ("3", "three"), ("4", "four"),
              ("5", "five"), ("6", "six"), ("7", "seven"), ("8", "eight"), ("9", "nine")]
OP_WORD = [("+", "plus"), ("*", "times"), ("-", "minus"), ("=", "equals"), ("/", "divided")]


def build_probes():
    vocab = json.load(open("/home/b/models/gemma-4-E4B-it/tokenizer.json"))["model"]["vocab"]
    left, right, names = [], [], []
    for a, b in DIGIT_WORD + OP_WORD:
        for cand in (b, "▁" + b):
            if a in vocab and cand in vocab:
                left.append(vocab[a]); right.append(vocab[cand]); names.append(f"{a}<->{cand}")
                break
    return left, right, names


def lift(Phi, li, ri):
    """Ratio: paired entry over the row's own median. Scale-free by construction."""
    out = []
    for k in range(len(li)):
        row = np.abs(Phi[k, len(li):])          # this left probe against every right probe
        med = np.median(row)
        if med > 0:
            out.append(float(np.abs(Phi[k, len(li) + k]) / med))
    return float(np.median(out)) if out else float("nan")


def main():
    m = Map()
    species = m.layer_species()
    li, ri, names = build_probes()
    print(f"probe pairs ({len(names)}): {', '.join(names)}\n", file=sys.stderr)
    E = m.rows("model.language_model.embed_tokens.weight", li + ri).astype(np.float64)
    nL = len(li)
    perm = rng.permutation(nL)

    nq, nkv = m.text["num_attention_heads"], m.text["num_key_value_heads"]
    rows = []
    for L in range(m.text["num_hidden_layers"]):
        v = m.take(f"model.language_model.layers.{L}.self_attn.v_proj.weight").astype(np.float64)
        o = m.take(f"model.language_model.layers.{L}.self_attn.o_proj.weight").astype(np.float64)
        d = m.text["global_head_dim"] if species[L] == "full_attention" else m.text["head_dim"]
        sv, so = float(v.std()), float(o.std())
        for H in range(nq):
            g = H // (nq // nkv)
            Wv, Wo = v[g * d : (g + 1) * d, :], o[:, H * d : (H + 1) * d]
            Phi = (E @ Wo) @ (Wv @ E.T)
            Nv = rng.standard_normal((d, 2560)) * sv
            No = rng.standard_normal((2560, d)) * so
            PhiN = (E @ No) @ (Nv @ E.T)
            shuf = Phi[:, list(range(nL)) + [nL + int(p) for p in perm]]
            rows.append({"layer": L, "head": H, "species": species[L],
                         "real": lift(Phi, li, ri),
                         "shuffled": lift(shuf, li, ri),
                         "null": lift(PhiN, li, ri)})
        print(f"  layer {L:2} done", file=sys.stderr)
    json.dump(rows, open("pairing.json", "w"))

    import statistics as S
    print("=== PAIRING LIFT: does transport couple a digit to its word? ===")
    print("    (Ratio: paired entry / row median. 1.0 = no coupling.)\n")
    for sp in ("sliding_attention", "full_attention"):
        r = [x for x in rows if x["species"] == sp]
        print(f"  {sp}  (n={len(r)})")
        for k in ("real", "shuffled", "null"):
            vals = [x[k] for x in r if np.isfinite(x[k])]
            print(f"     {k:9} median {S.median(vals):6.3f}   p90 {np.percentile(vals,90):6.3f}"
                  f"   max {max(vals):7.3f}")
        print()
    top = sorted([x for x in rows if np.isfinite(x["real"])], key=lambda x: -x["real"])[:10]
    print("=== the ten heads with the strongest digit<->word coupling ===")
    for x in top:
        print(f"   L{x['layer']:2} H{x['head']}  {x['species'][:8]}  real {x['real']:7.3f}"
              f"   shuffled {x['shuffled']:6.3f}   null {x['null']:6.3f}"
              f"   -> lift over shuffled x{x['real']/max(x['shuffled'],1e-9):5.2f}")


if __name__ == "__main__":
    main()
