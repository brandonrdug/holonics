"""Phase 5 -- what a transport CHARACTERISTICALLY DOES, returned as the artifact.

CLAUDE.md section 9: "Return the artifact. Counts, morphology totals, atlases, and diagnostics
are supporting receipts and never substitutes." Phases 1-4 returned diagnostics about
transports without ever returning a transport. This returns the transport.

TWO DEFECTS FROM PHASES 3-4 ARE FIXED HERE, both found by asking what inference actually does:

 1. LEXICAL FORM. Phase 3 paired bare 'two' (id 13498) with bare '2'. In running text the word
    form is SPACE-PREFIXED, U+2581 'two' (id 1156); the bare form is a word-continuation piece.
    The wrong side of the codec was being read. Both forms are carried here and reported apart.

 2. THE PRE-NORM GAIN. The operator that actually acts is not W_O W_V. RMSNorm scales the layer
    input elementwise by input_layernorm.weight before v_proj sees it, so the acting operator is
        W_eff = W_O W_V diag(g_in),      g_in = layers.L.input_layernorm.weight
    Phases 1-4 omitted diag(g_in) and therefore read an operator the model never applies.

WHAT IS STILL NOT MODELLED, and it bounds every reading here: position (RoPE is stripped, so
this is the zero-offset slice), the attention pattern itself (OV only acts on what QK selects),
the PLE per-layer injection, all prior layers' writes (so at layer L the true input is not E),
the chat template's turn structure and control tokens, and KV-cache sharing across 18 layers.
This is the DIRECT PATH at zero position with the true input gain -- a named, bounded slice.
"""
import json
import sys

import numpy as np

from read_map import Map

SPACE = "▁"


def vocab_maps():
    v = json.load(open("/home/b/models/gemma-4-E4B-it/tokenizer.json"))["model"]["vocab"]
    inv = {i: s for s, i in v.items()}
    return v, inv


def readable_sample(inv, limit=8000):
    """A readable target vocabulary: word-like pieces, so the artifact is legible."""
    out = []
    for i in range(len(inv)):
        s = inv.get(i)
        if not s or len(s) < 2:
            continue
        core = s[1:] if s.startswith(SPACE) else s
        if core.isascii() and core.isalpha() and len(core) >= 2:
            out.append(i)
        if len(out) >= limit:
            break
    return out


def main():
    m = Map()
    v, inv = vocab_maps()
    species = m.layer_species()
    targets = readable_sample(inv)
    E_t = m.rows("model.language_model.embed_tokens.weight", targets).astype(np.float64)
    print(f"target vocabulary: {len(targets)} word-like pieces\n", file=sys.stderr)

    sources = []
    for s in ["2", "two", SPACE + "two", "4", SPACE + "four", "+", SPACE + "plus",
              SPACE + "add", "=", SPACE + "equals", SPACE + "cat", SPACE + "king"]:
        if s in v:
            sources.append((s, v[s]))
    E_s = m.rows("model.language_model.embed_tokens.weight", [i for _, i in sources]).astype(np.float64)

    heads = [(0, 4, "most acyclic"), (5, 5, "most spectrally concentrated"),
             (13, 0, "pairing peak"), (17, 7, "pairing peak, global")]

    for L, H, why in heads:
        g = m.take(f"model.language_model.layers.{L}.input_layernorm.weight").astype(np.float64)
        vw = m.take(f"model.language_model.layers.{L}.self_attn.v_proj.weight").astype(np.float64)
        ow = m.take(f"model.language_model.layers.{L}.self_attn.o_proj.weight").astype(np.float64)
        d = m.text["global_head_dim"] if species[L] == "full_attention" else m.text["head_dim"]
        nq, nkv = m.text["num_attention_heads"], m.text["num_key_value_heads"]
        gq = H // (nq // nkv)
        Wv = vw[gq * d : (gq + 1) * d, :]
        Wo = ow[:, H * d : (H + 1) * d]

        print(f"\n{'='*78}")
        print(f"L{L} H{H}  ({species[L]}, head_dim {d})  -- {why}")
        print(f"{'='*78}")
        for (name, _), e in zip(sources, E_s):
            w = Wo @ (Wv @ (g * e))          # the acting operator, gain included
            logits = E_t @ w
            nrm = np.linalg.norm(logits)
            if nrm == 0:
                continue
            top = np.argsort(-logits)[:6]
            bot = np.argsort(logits)[:3]
            # Ratio: each target's share of the write, scale-free
            share = logits / nrm
            tt = " ".join(f"{inv[targets[j]].replace(SPACE,'_')}({share[j]:+.3f})" for j in top)
            bb = " ".join(f"{inv[targets[j]].replace(SPACE,'_')}({share[j]:+.3f})" for j in bot)
            print(f"  {name.replace(SPACE,'_'):10} -> {tt}")
            print(f"  {'':10}    away: {bb}")


if __name__ == "__main__":
    main()
