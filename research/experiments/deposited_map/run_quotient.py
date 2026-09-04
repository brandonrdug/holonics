"""Phase 6 -- the transport read as a QUOTIENT, in the dialect.

THE SPECIES (TABLET_THE_OPERATIONS, H.0476). W_V's rows are receiver bras, W_O's columns are
construction kets, so
        W_OV = sum_k sigma_k |u_k> <w_k|
is a POPULATION OF DEPOSITS, each an outer product. <t|W|s> is a FACE. What a head does to a
family of faces of one holon -- two, _two, _Two, _deux -- is not a relation we name: it
COLLAPSES them. That is a QUOTIENT, whose lawful content is the collapsed population and the
receiver that sees it. Receiver-relative, hence relativistic; and a partition can transfer
across bodies where an operator never could.

WHAT IS MEASURED. For source holon s the transport deposits the direction
        |w_s> = W_O W_V diag(g_in) |s>
Magnitude is a Rank and does not cross the horizon, so only the DIRECTION is read. The face
between two deposits is the bracket <w_a|w_b> / (||w_a|| ||w_b||) -- a pure angle, a Ratio.

ON ANGLES BEING ADMITTED HERE. Phases 1-4 refused cosine similarity. That refusal is correct
under a general GL gauge. This architecture ties its embedding to its unembedding, which reduces
the residual gauge to O(2560) -- a metric, in TABLET_THE_MANIFOLD section 16's table -- and an
orthogonal map preserves inner products. So angles between BUS vectors are invariant HERE, by a
reduction the model itself declares. The claim is architecture-specific, not general.

THE ARCHETYPE IS A RECURRING QUOTIENT. Finitely many partition types, many operators realising
each -- Berger's shape. So the return is: which quotient each head induces, and which quotients
RECUR. A quotient that recurs across independent heads is a candidate archetype; one that
appears in a single head is that head's coordinate.
"""
import json
import sys
from collections import Counter

import numpy as np

from read_map import Map

SP = "▁"

# Each family is one holon presented under several faces: segmentation, case, language, glyph.
FAMILIES = {
    "two":  ["two", SP + "two", SP + "Two", SP + "deux", "2"],
    "four": ["four", SP + "four", SP + "Four", SP + "quatre", "4"],
    "add":  ["add", SP + "add", SP + "Add", SP + "plus", "+"],
    "king": ["king", SP + "king", SP + "King", SP + "roi"],
    "cat":  ["cat", SP + "cat", SP + "Cat", SP + "chat"],
    "red":  ["red", SP + "red", SP + "Red", SP + "rouge"],
}


def main():
    m = Map()
    vocab = json.load(open("/home/b/models/gemma-4-E4B-it/tokenizer.json"))["model"]["vocab"]
    fam, names, ids = [], [], []
    for f, faces in FAMILIES.items():
        for s in faces:
            if s in vocab:
                fam.append(f); names.append(s); ids.append(vocab[s])
    fam = np.array(fam)
    print(f"{len(ids)} faces over {len(set(fam))} holons", file=sys.stderr)
    E = m.rows("model.language_model.embed_tokens.weight", ids).astype(np.float64)

    species = m.layer_species()
    nq, nkv = m.text["num_attention_heads"], m.text["num_key_value_heads"]
    same = fam[:, None] == fam[None, :]
    off = ~np.eye(len(ids), dtype=bool)

    rows = []
    for L in range(m.text["num_hidden_layers"]):
        g = m.take(f"model.language_model.layers.{L}.input_layernorm.weight").astype(np.float64)
        vw = m.take(f"model.language_model.layers.{L}.self_attn.v_proj.weight").astype(np.float64)
        ow = m.take(f"model.language_model.layers.{L}.self_attn.o_proj.weight").astype(np.float64)
        d = m.text["global_head_dim"] if species[L] == "full_attention" else m.text["head_dim"]
        Eg = E * g
        for H in range(nq):
            gq = H // (nq // nkv)
            W = (Eg @ vw[gq * d : (gq + 1) * d, :].T) @ ow[:, H * d : (H + 1) * d].T  # deposits
            n = np.linalg.norm(W, axis=1, keepdims=True)
            n[n == 0] = 1.0
            U = W / n
            G = U @ U.T                                    # the face: pure angles, a Ratio
            wi = float(G[same & off].mean())               # within-holon face
            bt = float(G[~same & off].mean())              # between-holon face
            # the induced quotient: which faces this transport actually collapses
            thr = np.percentile(G[off], 95)
            part = [tuple(sorted(np.where(G[i] >= thr)[0])) for i in range(len(ids))]
            rows.append({"layer": L, "head": H, "species": species[L],
                         "within": wi, "between": bt, "sep": wi - bt,
                         "quotient": part})
        print(f"  layer {L:2} done", file=sys.stderr)

    sep = np.array([r["sep"] for r in rows])
    print("\n=== THE QUOTIENT: does the transport collapse faces of one holon? ===")
    print(f"  within-holon minus between-holon face, over 336 transports:")
    print(f"    median {np.median(sep):+.4f}   p90 {np.percentile(sep,90):+.4f}   max {sep.max():+.4f}")
    print(f"    positive in {100*(sep>0).mean():.1f}% of transports")

    print("\n=== the ten transports that collapse faces hardest ===")
    for r in sorted(rows, key=lambda x: -x["sep"])[:10]:
        print(f"   L{r['layer']:2} H{r['head']}  {r['species'][:8]}  "
              f"within {r['within']:+.3f}  between {r['between']:+.3f}  separation {r['sep']:+.3f}")

    # A recurring quotient is an archetype; a unique one is that head's coordinate.
    print("\n=== RECURRENCE: do independent transports induce the SAME quotient? ===")
    key = Counter()
    for r in rows:
        blocks = frozenset(b for b in r["quotient"] if len(b) > 1)
        if blocks:
            key[blocks] += 1
    print(f"  distinct non-trivial quotients over 336 transports: {len(key)}")
    for q, c in key.most_common(5):
        if c < 2:
            break
        shown = sorted(q, key=len, reverse=True)[:3]
        desc = " | ".join("{" + ",".join(names[i] for i in b) + "}" for b in shown)
        print(f"    x{c:3}  {desc.replace(SP,'_')}")
    singles = sum(1 for c in key.values() if c == 1)
    print(f"  quotients appearing in exactly one transport: {singles}/{len(key)}")

    json.dump([{k: v for k, v in r.items() if k != "quotient"} for r in rows],
              open("quotient.json", "w"))


if __name__ == "__main__":
    main()
