# Athena — the dimension is declared, the rank is the file size, and no float is respected

> **CONSUMED BY THE PHOENIX CONSTRUCTION / SUBORDINATE DIMENSION AND EXPORT INSTRUMENT / NOT AN
> INDEPENDENT SCHEDULER — 2026-08-18.** ATHENA-000's exact mouths, tree chart, integer containers,
> and the dense-route refutation remain standing evidence. Native baseline, receiver-minimal
> dimension, cultivation, executable output, and inference are now specified by
> [`THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`](THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md).
> Do not resume a station here as a standalone tensor experiment.

**Date:** 2026-08-18
**Truth status:** `established-bounded` for every measured figure; `proved-standard` for the
realization theorem and the interval/light-cone equivalence; `interpretation` for the architecture,
which is posed for ratification and not built.
**Evidence:** `measured`. `crates/holonic-engine/examples/the_dimension_is_measured_before_it_is_spent.rs`,
`crates/holonic-engine/src/athena.rs`, and the real Gemma-4-E4B container's own header.
**Provenance:** Brandon, 2026-08-18:

> *"instead of linearly scaling floating point representations, you could just alter the dimensions
> of layers and heads, and it would encode the same performance while still compressing. That's
> holonic compression… We don't respect floats, but we'll reverse engineer them so they go away and
> we can work with pure integers again."*

**Plan:** sits under [`docs/plans/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md). It succeeds
[`research/records/2026-08-18_THE_ATLAS_IS_A_NAVMESH_AND_THE_TRANSITION_TO_A_TENSOR_SPLITS_INTO_A_FREE_TREE_AND_A_CYCLE_RANK.md`](../../research/records/2026-08-18_THE_ATLAS_IS_A_NAVMESH_AND_THE_TRANSITION_TO_A_TENSOR_SPLITS_INTO_A_FREE_TREE_AND_A_CYCLE_RANK.md),
which built ATHENA-000 — the tree half, emitted and read back.

---

## 0. What quantisation is, stated so the alternative is visible

Industry quantisation is `W ≈ s·(Q − z)`: an integer tensor `Q`, a float scale `s`, a zero point
`z`. Brandon's reading — *"pretty much just linear scaling with some nuances"* — is correct, and it
is affine rather than linear because of `z`. **The whole literature is about where to put the scale
boundaries**: per-tensor, per-channel, per-group of 128; AWQ, SmoothQuant and GPTQ differ in which
population shares a scale and how the error is pushed around. In this corpus's vocabulary that is
**a declared receiver family over the entries** — so even done well, quantisation is a grouping
question wearing a numerical costume.

**Two compressions, and only one is this corpus's law:**

| | quantisation | dimension |
|---|---|---|
| what shrinks | the precision of each entry | the shape |
| what is kept | the shape | every entry, exactly |
| the remainder | per-entry rounding, spread uniformly | a **cokernel** — a named subspace |
| can it be exhibited? | no: a float tail, deleted | yes: the collapsed population, with a separating word |
| needs a float? | **yes** — `s` is a float | **no** — integers throughout |

The first is the tail deletion this corpus refuses everywhere else. The second is *a codec pivot
carrying a declared decoder*, which is the compression law verbatim.

## 1. The measurement, and it sharpens the thesis rather than confirming it

Real Gemma circuits, through the dyadic mouth to exact integers, rank over two declared primes:

```text
  circuit                                      shape     rank  deficit  frames
  layers.0.self_attn.q_proj.weight          256x2560      256        0  agree
  layers.0.self_attn.k_proj.weight          256x2560      256        0  agree
  layers.0.self_attn.v_proj.weight          256x2560      256        0  agree
  layers.0.per_layer_input_gate.weight      256x2560      256        0  agree
  layers.20.self_attn.q_proj.weight         256x2560      256        0  agree
  layers.20.per_layer_input_gate.weight     256x2560      256        0  agree
  layers.41.self_attn.q_proj.weight         256x2560      256        0  agree
```

**Seven of seven are full rank.** There is no free dimension sitting in a trained weight matrix, at
any depth. So:

- **The lazy reading of the thesis is refuted.** You cannot truncate Gemma's matrices and lose
  nothing; every declared dimension is carrying something exact.
- **The real reading is sharpened, and the measurement says where the room is.** A matrix trained
  with a fixed shape and eight mantissa bits will *fill* that shape — that is what descent does.
  **Full rank is what you get when you spend precision instead of structure.**

### And the industry already compresses by dimension — in the architecture, not in the weights

Read off Gemma's own header rather than a paper:

```text
  q_proj [2048, 2560]   = 8 query heads x 256
  k_proj [ 512, 2560]   = 2 KV heads x 256      <- grouped-query: 8 sharing 2
  v_proj [ 512, 2560]
  o_proj [2560, 2048]
  embed_tokens_per_layer [262144, 10752]        = 42 layers x 256
  per_layer_input_gate   [256, 2560]
  per_layer_projection   [2560, 256]
```

- **The OV circuit is `W_O W_V`: `2560×512 · 512×2560`, so rank ≤ 512 in a 2560-dimensional stream
  by construction.** The architecture declares a rank deficit of 2,048 before a single step of
  training.
- **The QK circuit is rank ≤ 256** for the same reason.
- **Grouped-query attention is a declared structural quotient**: eight query heads share two key
  populations.
- **The per-layer embedding is the thesis already shipped.** 2.8 billion of the model's parameters
  are a `262144 × 10752` lookup injected **256 dimensions at a time per layer**, rather than
  precision spent on one wide embedding.

> **So the structure is where the rank lives, and quantisation is what is left over after the
> structural compression has already been taken.** Brandon's direction is the one the industry is
> already moving in; what it has not done is *derive* the structure rather than search for it.

### The MoE reading, and why it is evidence for the same thesis

`docs/canon/TABLET_THE_REASONING_CYCLE.md` already types it: *router → conditional transport junction*,
*expert → a distinct organ only when intervention exhibits distinct conduct*. Two consequences:

- **Top-`k` routing is a governor.** It ranks and crowns `k` of `E`. The atlas's junction returns
  the whole population with per-depth support, so the same station exists without the selection.
- **MoE's win is structural sparsity, not precision.** Most parameters are inactive per token. That
  is the largest compression lever the field has found in years and it is *entirely* a dimension
  argument — which is the thesis, validated by the industry's own results.

**And the atlas's equivalent of an expert is a subtree of the suffix-link tree.** MoE learns a
partition of an FFN and learns a router into it; the atlas *has* a partition — the tree's own
branches — and the routing is the arc, which is caused rather than trained. This repository's
version of "experts" needs no expert-assignment loss, because the material assigns them.

**Gemma-4-E4B as read here is dense, not MoE** — no expert tensors appear in its header — so the MoE
comparison above is structural and is not a claim about this container.

## 2. The derivation: what the width of an Athena file must be

ATHENA-000 answers Brandon's file-size question in the only terms that are well posed:

```text
  octets = rows x width x 2         112,604 for 3,125 x 18
```

so **the size question is the width question, and the width question is a rank question.** That is
what ATHENA-001 must settle, and it has an exact answer.

### The minimal dimension is the rank of the Hankel matrix

For a linear representation of a weighted automaton — vectors `u`, `v` and per-symbol matrices `A_a`
with `f(a₁…a_n) = uᵀ A_{a₁}…A_{a_n} v` — the **minimal dimension is exactly the rank of the Hankel
matrix** `H[x, y] = f(xy)` over contexts `x` and continuations `y`. That is Fliess–Kalman
realization theory, and it is a theorem rather than a heuristic: there is no smaller exact
representation and one of that size always exists.

**Over ℤ rather than a field the right object is the Smith normal form**, which
`rebase_invariants::smith_normal_form` already computes:

```text
  rank r            the minimal dimension, exactly
  factors d₁|…|d_r  the invariant factors
  torsion           factors above one
```

**The torsion is the part quantisation destroys silently.** A factor `d > 1` is a direction reachable
only at a multiple of `d` — `ReachableOnlyInMultiple`, which §11 and §3 already own as the cokernel
of a cycle-class map. An affine rescale of the integer grid does not preserve it; a change of basis
over ℤ does.

### And the machine already computes the automaton whose Hankel this is

`receiver_exact_compression::compress` returns the causal-state construction — the coarsest partition
whose conduct is determined by the block. That is the minimal automaton, and its state count bounds
the Hankel rank. So the pipeline is:

```text
  material -> atlas -> minimal automaton (compress) -> Hankel block -> Smith normal form
           -> r = the width, and the invariant factors = the torsion the file must carry
```

**No dimension is chosen anywhere in that chain.** The width is read off the material.

## 3. The stations, posed

### Station one — the Hankel block, and its rank

Build `H` over a declared context/continuation aperture, exactly, from the atlas. Take the Smith
normal form. **Return `r` and the invariant factors.**

*Expectation.* `r` is far below `|S| = 25,030`, because the classes are highly redundant as a linear
system even though they are distinct as a partition.
*Falsifier, and it is the one that decides the whole design:* if `r` is within a small factor of
`|S|`, there is no linear representation worth having and the tensor chart is the wrong container
for the transport half. **That would be a real negative and the station must return it as one.**
*The vacuity arm:* if the aperture is small enough that `H` is trivially low rank, the rank measures
the aperture and not the material. The aperture must be swept and the rank reported against it.

### Station two — the transport tensors, in integers, with no scale

Emit `U ∈ ℤ^{|S|×r}`, `V ∈ ℤ^{r×|S|}`, and per-germ `A_a ∈ ℤ^{r×r}`. **No `s`, no `z`, no float
anywhere in the container's semantics** — floats are the wire format only, and `round_into` already
certifies each crossing with an exact residual.

*Falsifier.* `U A_a V` must reproduce `M_a` exactly on the declared population. A single disagreement
means `r` is not the rank.

### Station three — the absolute frame is charged for, and must be rebased

ATHENA-000's widest residual was **64**, because a raw depth-first index is an absolute coordinate
and a `BF16` ulp at magnitude 16,000 is 64. Carry the **relative** interval instead — a ratio, which
crosses a horizon where a magnitude cannot.

*Expectation.* The widest residual falls toward zero.
*Falsifier.* If it does not, the absolute frame is not what the 64 was charging for and section 5 of
the ATHENA-000 record is wrong.

### Station four — a declared architecture, so the container is runnable

A declared architecture manifest naming the layer law: **layer `k` is the atlas at suffix-link height `k`**, layer count
= the tree's height (measured **8**), and the composition is the transfer-matrix product of the
per-germ `A_a`.

*Falsifier.* A run of the declared architecture on a held-out surface must reproduce the atlas's own
emanation. If it does not, the tensors do not carry the transport they claim to.

### Station five — the same reading turned on Gemma

The rank probe generalised: every circuit of a trained container, exact integer rank and invariant
factors, per layer. **This has not been done because rank is not well posed in floating point** — an
SVD returns a spectrum and a human picks a cutoff. Over integers it is a number.

*Expectation, from the seven measured today:* full rank throughout, so the compressible structure is
in the **composition** — `W_O W_V` and `W_Qᵀ W_K` — not in the factors.
*Falsifier.* Any circuit with a genuine deficit is dimension removable with a named cokernel, and
that is a direct, citable finding about a shipped model.

## 4. What is refused

- **No float in any arithmetic.** Floats are a wire format. Every crossing carries its exact
  rational residual, both directions.
- **No scale, no zero-point.** A container needing an `s` has quantised.
- **No SVD cutoff, no threshold, no tolerance.** Rank is exact or it is not being measured.
- **No top-`k` router.** A junction returns its population.
- **No dimension chosen by a human.** The width is the Hankel rank; the depth is the tree's height.
- **No claim that Athena outperforms a transformer**, and no agreement with Gemma as a criterion.

## 5. What would make this fail honestly

If the Hankel rank is large, the linear-representation route is the wrong chart for transport and
the design is refuted at station one. That is a real possibility and it is the first thing to
measure, before any emission is built on it. The tree half already stands and is unaffected either
way — it is rank 2 with zero remainder because the geometry of a laminar family is Lorentzian, not
because anything was truncated.
