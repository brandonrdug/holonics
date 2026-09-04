"""Phase 4 -- does the coupling carry a hand, and does it read like a DAG?

Phi = E_S (W_O W_V) E_S^T is NOT symmetric. Phase 3 read only the digit->word block, so the
question of direction was left open. Three readings, all Ratios:

  1. PAIRED ASYMMETRY.  A(a,b) = (|Phi_ab| - |Phi_ba|) / (|Phi_ab| + |Phi_ba|)  in [-1,1].
     Dimensionless. Magnitude says how one-sided; SIGN CONSISTENCY ACROSS HEADS is what
     distinguishes a hand from noise. Half the heads pointing each way is not a direction.

  2. SYM/ANTISYM RATIO.  ||antisym|| / ||sym|| of Phi on the probe block. For a random real
     matrix this sits at ~1 (equal energy). Departure is the signal. Per TABLET_THE_MANIFOLD
     section 16: the symmetric part is O-type structure (comparison), the antisymmetric part is
     Sp-type -- "a phase area is fixed". The antisymmetric part IS the hand.

  3. HODGE DECOMPOSITION -- the DAG test proper.  The net flow F_ij = Phi_ij - Phi_ji is
     antisymmetric, i.e. a 1-cochain on the complete graph over the probe set. Decompose
         F = grad(s)  +  curl-part,        grad(s)_ij = s_j - s_i
     The gradient part is exactly a POTENTIAL: it admits a rank function, so it is acyclic --
     a DAG. The residual circulates: it is holonomy, loops that fail to return the identity.
         dag_fraction = ||grad||^2 / ||F||^2
     is a Ratio in [0,1]. 1.0 = perfectly acyclic transport. 0.0 = pure circulation.
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
                left.append(vocab[a]); right.append(vocab[cand]); names.append(f"{a}->{cand}")
                break
    return left, right, names


def paired_asymmetry(Phi, n):
    """Signed, dimensionless. Positive = left(symbol) -> right(word) dominates."""
    out = []
    for k in range(n):
        ab, ba = abs(Phi[k, n + k]), abs(Phi[n + k, k])
        if ab + ba > 0:
            out.append((ab - ba) / (ab + ba))
    return float(np.median(out)) if out else float("nan")


def sym_antisym(Phi):
    S = 0.5 * (Phi + Phi.T)
    A = 0.5 * (Phi - Phi.T)
    ns = np.linalg.norm(S)
    return float(np.linalg.norm(A) / ns) if ns > 0 else float("nan")


def hodge_dag_fraction(Phi):
    """Split the net flow into an acyclic gradient and a circulating residual.

    F_ij = Phi_ij - Phi_ji on the complete graph. Least-squares potential s solves
    min ||F - (s_j - s_i)||^2, whose normal equations are L s = div(F) with L the graph
    Laplacian. Returns ||grad||^2 / ||F||^2.
    """
    F = Phi - Phi.T
    n = F.shape[0]
    div = F.sum(axis=1)                       # div(F)_i = sum_j F_ij
    L = n * np.eye(n) - np.ones((n, n))       # Laplacian of K_n
    s = np.linalg.lstsq(L, -div, rcond=None)[0]
    G = s[None, :] - s[:, None]               # grad(s)_ij = s_j - s_i
    fF = float((F * F).sum())
    if fF == 0:
        return float("nan")
    return float((G * G).sum() / fF)


def main():
    m = Map()
    species = m.layer_species()
    li, ri, names = build_probes()
    n = len(li)
    print(f"probe pairs ({n}): {', '.join(names)}\n", file=sys.stderr)
    E = m.rows("model.language_model.embed_tokens.weight", li + ri).astype(np.float64)

    nq, nkv = m.text["num_attention_heads"], m.text["num_key_value_heads"]
    rows = []
    for L in range(m.text["num_hidden_layers"]):
        v = m.take(f"model.language_model.layers.{L}.self_attn.v_proj.weight").astype(np.float64)
        o = m.take(f"model.language_model.layers.{L}.self_attn.o_proj.weight").astype(np.float64)
        d = m.text["global_head_dim"] if species[L] == "full_attention" else m.text["head_dim"]
        sv, so = float(v.std()), float(o.std())
        for H in range(nq):
            g = H // (nq // nkv)
            Phi = (E @ o[:, H * d : (H + 1) * d]) @ (v[g * d : (g + 1) * d, :] @ E.T)
            PhiN = (E @ (rng.standard_normal((2560, d)) * so)) @ ((rng.standard_normal((d, 2560)) * sv) @ E.T)
            rows.append({
                "layer": L, "head": H, "species": species[L],
                "asym": paired_asymmetry(Phi, n), "asym_null": paired_asymmetry(PhiN, n),
                "sa": sym_antisym(Phi), "sa_null": sym_antisym(PhiN),
                "dag": hodge_dag_fraction(Phi), "dag_null": hodge_dag_fraction(PhiN),
            })
        print(f"  layer {L:2} done", file=sys.stderr)
    json.dump(rows, open("direction.json", "w"))

    import statistics as S
    A = np.array([x["asym"] for x in rows]); AN = np.array([x["asym_null"] for x in rows])
    print("=== 1. PAIRED ASYMMETRY  (symbol->word minus word->symbol, normalised) ===")
    print(f"   real  median {np.median(A):+.4f}   positive in {100*(A>0).mean():5.1f}% of 336 heads")
    print(f"   null  median {np.median(AN):+.4f}   positive in {100*(AN>0).mean():5.1f}% of 336 heads")
    k = int((A > 0).sum()); N = len(A)
    from math import comb
    p = 2 * min(sum(comb(N, i) for i in range(k, N + 1)), sum(comb(N, i) for i in range(0, k + 1))) / 2**N
    print(f"   two-sided sign test vs 50%: p = {p:.3e}")

    print("\n=== 2. ANTISYM / SYM ENERGY  (1.0 = no preferred hand) ===")
    for key, lab in (("sa", "real"), ("sa_null", "null")):
        vals = np.array([x[key] for x in rows]); vals = vals[np.isfinite(vals)]
        print(f"   {lab:5} median {np.median(vals):6.3f}   p10 {np.percentile(vals,10):6.3f}"
              f"   p90 {np.percentile(vals,90):6.3f}")

    print("\n=== 3. HODGE: acyclic (DAG) fraction of the net flow ===")
    for key, lab in (("dag", "real"), ("dag_null", "null")):
        vals = np.array([x[key] for x in rows]); vals = vals[np.isfinite(vals)]
        print(f"   {lab:5} median {np.median(vals):6.4f}   p90 {np.percentile(vals,90):6.4f}"
              f"   max {vals.max():6.4f}")
    d_real = np.array([x["dag"] for x in rows]); d_null = np.array([x["dag_null"] for x in rows])
    print(f"   real > null in {100*(d_real>d_null).mean():.1f}% of heads")

    print("\n=== by region (the layers where phase 3 found the coupling) ===")
    for lo, hi, lab in ((3, 22, "layers 3-22"), (26, 41, "layers 26-41")):
        r = [x for x in rows if lo <= x["layer"] <= hi]
        a = np.array([x["asym"] for x in r]); dd = np.array([x["dag"] for x in r])
        dn = np.array([x["dag_null"] for x in r])
        print(f"   {lab:12} asym med {np.median(a):+.4f}  pos {100*(a>0).mean():5.1f}%   "
              f"DAG med {np.median(dd):.4f}  null {np.median(dn):.4f}")

    print("\n=== the eight most acyclic heads ===")
    for x in sorted(rows, key=lambda z: -z["dag"])[:8]:
        print(f"   L{x['layer']:2} H{x['head']}  {x['species'][:8]}  DAG {x['dag']:.4f} "
              f"(null {x['dag_null']:.4f})   asym {x['asym']:+.3f}   antisym/sym {x['sa']:.3f}")


if __name__ == "__main__":
    main()
