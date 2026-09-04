# The Hankel rank does not saturate, so the compression is sparsity — and it is exact

**Date:** 2026-08-18
**Truth status:** `established-bounded` for every figure, each from running the named drivers today;
`proved-standard` for Fliess–Kalman; the blueprint's dense-linear route is **refuted** and withdrawn.
**Evidence:** `measured`. `soma/life/examples/the_hankel_rank_is_the_width_athena_can_have.rs`,
`crates/holonic-engine/examples/the_dimension_is_measured_before_it_is_spent.rs`,
`soma/life/examples/athena_001_the_transport_crosses_as_integers.rs`.
**Provenance:** Brandon, 2026-08-18: *"instead of linearly scaling floating point representations,
you could just alter the dimensions of layers and heads… We don't respect floats, but we'll reverse
engineer them so they go away and we can work with pure integers again."*
**Plan:** station one of
[`blueprint/ATHENA_THE_DIMENSION_IS_DECLARED_AND_THE_RANK_IS_THE_FILE_SIZE.md`](../../archive/plans/ATHENA_THE_DIMENSION_IS_DECLARED_AND_THE_RANK_IS_THE_FILE_SIZE.md).

---

## 1. Station one fired its own falsifier

The blueprint declared it: *"if `r` is within a small factor of `|S|`, there is no linear
representation worth having and the tensor chart is the wrong container for the transport half. That
would be a real negative and the station must return it as one."*

```text
  canonical order                      by standing order
  block  nonzero  rank                 block  nonzero  rank
     64       12     4                    64      761    60
    128       19     8                   128     1638   124
    256       89    21                   256     3364   247
    512      301    66                   512     6409   491
   1024      896   216                  1024    10852   927
   2048     3410   557                  2048    17132  1638
```

Both prime frames agree at every point. **Neither aperture frame saturates.**

**The canonical frame's low rank is a sparsity artifact and must not be quoted** — 3,410 nonzeros in
4,194,304 cells is 0.08% density, so the block is nearly empty and its rank measures the aperture.
That is exactly the vacuity arm the sweep was built to carry, and it fired.

**The honest frame is by-standing, and there the rank is near-full at every aperture**: 1,638 of
2,048, with the deficit shrinking as a fraction and no saturation anywhere, against 25,030 classes.

By Fliess–Kalman the minimal exact dimension of a linear representation **is** that rank. So there is
no small dense chart of this transport, and **the dense route is refuted by measurement.**

## 2. And it is the same fact as the Gemma measurement

Real Gemma-4-E4B circuits, through the dyadic mouth to exact integers, rank over two declared primes:

```text
  q_proj / k_proj / v_proj / per_layer_input_gate,  layers 0, 20, 41
  256 x 2560   ->   rank 256   deficit 0   both frames agree,  7 of 7
```

**Seven of seven full rank.** No free dimension sits in a trained weight matrix at any depth.

Those are not two results. **The material's own Hankel is near-full rank and a trained model's
circuits are full rank because the dimension is real.** Training fills the shape because the shape is
demanded. The industry is not wasting rank, and the lazy reading of *alter the dimensions* — truncate
somebody's trained matrix and lose nothing — is false.

### Where the industry does compress by dimension: in the architecture

Read off Gemma's own header rather than a paper:

- **the OV circuit is `W_O W_V`: `2560×512 · 512×2560`, hence rank ≤ 512 in a 2560-dimensional
  stream by construction** — a declared deficit of 2,048 before training begins;
- **the QK circuit is rank ≤ 256** for the same reason;
- **grouped-query attention** puts 8 query heads on 2 KV heads — a declared structural quotient;
- **`embed_tokens_per_layer [262144, 10752]`** is 2.8 billion parameters injected **256 dimensions
  at a time per layer** through `per_layer_projection [2560, 256]`.

> **The structure is where the rank lives, and quantisation is what is left over after the
> structural compression has already been taken.**

**MoE reads the same way.** `canon/TABLET_THE_REASONING_CYCLE.md` already types the router as a
conditional transport junction and refuses an expert that no intervention distinguishes. Top-`k`
routing is a governor — it ranks and crowns `k` of `E` — and MoE's win is **structural sparsity, not
precision**, which is the same thesis reached from the other side. The atlas's equivalent of an
expert is a subtree of the suffix-link tree, assigned by the material rather than by a router loss.
*(Gemma-4-E4B as read here is dense; no expert tensors appear in its header.)*

## 3. So the compression is sparsity, and `BF16` cannot carry it

`|S| = 25,030` classes, `|E| = 43,049` germ transitions, vocabulary 3,125. The transport is a
**sparse partial function**, and a dense chart of it is an *expansion*:

```text
  a dense rank-512  linear representation   3,125 germ matrices x 512²  x 2 =  1.6 GB
  a dense rank-1024                                                        =  6.6 GB
  a dense rank-2048                                                        = 26.2 GB
```

**And `BF16` cannot hold an index.** Eight significand bits means every integer above 256 is
unrepresentable. A container whose content is *structure* rather than *magnitude* therefore needs
integer dtypes — which is not a lossiness argument but a wrongness one, and it is why every
industry container is `BF16`: their content is magnitudes.

## 4. ATHENA-001, emitted and replayed

```text
  athena.transport.indptr    25,031  U32   100,124 octets
  athena.transport.germ      43,049  U16    86,098
  athena.transport.target    43,049  U32   172,196
  athena.class.standing      25,030  U32   100,120
  athena.class.suffix        25,030  U32   100,120
  CONTAINER                                559,114 octets = 546 KiB
```

**No scale, no zero point, no rounding, no residual.** Every entry is an integer that crosses exactly.

**The falsifier, and it is the whole claim:** 4,000 walks taken from the container alone — no
ecology, no corpus, no organ, only the integers that crossed — replayed against the atlas.
**0 disagreements.** The arc is in there too: when no germ is found in a class's span the replay
follows `athena.class.suffix`, which is `carry`'s law expressed in three integer arrays.

So the transport half crosses into the industry's container, in integers, and reproduces the
machine's conduct walk for walk, at **546 KiB against 1.6–26.2 GB dense.**

## 5. What is withdrawn and what is owed

**Withdrawn:** the blueprint's station-one expectation that `r` would be far below `|S|`, and station
two's dense `U`, `V`, `A_a` emission. Refuted by measurement, not abandoned.

**Retained unchanged:** the tree half. It is rank 2 with zero remainder because the geometry of a
laminar family is Lorentzian — nothing was truncated to get it, so nothing here touches it.

**Owed:**
- station three, the relative-interval rebase, which should drive ATHENA-000's widest residual of 64
  toward zero — the absolute frame being charged for;
- a declared architecture manifest so the container is runnable, with layer `k` = suffix height `k`
  and the layer count the tree's own height, measured 8;
- the rank probe generalised across every Gemma circuit, which is a citable finding about a shipped
  model and has not been done because rank is not well posed in floating point.

## 6. Falsifiers

- The container's replay must agree with the atlas on every walk. One disagreement means it does not
  carry the transport.
- The by-standing rank must stay near-full at wider apertures. If it saturates at, say, 4,096, the
  dense route reopens at that width and this record's headline is wrong.
- The canonical-order frame must stay uninformative. If its rank ever rises to meet the standing
  frame, the sparsity artifact reading is wrong.
- A `BF16` container must fail to carry a class index above 256 exactly. If it does not, the dtype
  argument is wrong.
