# The ratio crossed, the container produces, and all 168 Gemma circuits are full rank

**Date:** 2026-08-18
**Truth status:** `established-bounded` throughout; every figure from running the named drivers today.
**Evidence:** `measured`. `soma/life/examples/athena_002_the_container_generates_from_itself.rs`,
`crates/holonic-engine/examples/the_dimension_is_measured_before_it_is_spent.rs`.
**Plan:** [`blueprint/ATHENA_THE_DIMENSION_IS_DECLARED_AND_THE_RANK_IS_THE_FILE_SIZE.md`](../../archive/plans/ATHENA_THE_DIMENSION_IS_DECLARED_AND_THE_RANK_IS_THE_FILE_SIZE.md),
stations three, four and five.

---

## 1. The rebase — a ratio crossed where a magnitude could not

ATHENA-000 emitted raw depth-first indices, which are **absolute coordinates**, and a `BF16` ulp at
magnitude 16,000 is 64. Rebasing every coordinate against the tree's own extent makes it a ratio:

| | ATHENA-000, absolute | ATHENA-002, rebased |
|---|---|---|
| entries crossing **exactly** | 6,242 of 56,250 | **46,875 of 56,250** |
| widest residual | **64** | **781/800960 ≈ 0.00098** |

**A factor of about 65,000, and it is the no-absolute-frame law paying out as arithmetic** rather
than as doctrine. The falsifier stated in the ATHENA-000 record — *if rebasing does not drive the
residual toward zero, the absolute frame is not what the 64 was charging for* — did not fire.

## 2. ATHENA-002 declares its own architecture and produces from itself

```text
  CONTAINER  728,442 octets = 711 KiB
    athena.transport.{indptr, germ, target}     U32 / U16 / U32
    athena.class.{standing, suffix}             U32 / U32
    athena.vocabulary.{octets, offsets}         U16 / U32
    athena.architecture                         U32   6 layers · tree height 8 ·
                                                      25,030 classes · 43,049 transitions ·
                                                      3,125 vocabulary
    athena.embed.minkowski                      BF16  3,125 x 18
```

Mounted from the file alone — no ecology, no corpus, no organ — and asked:

```text
  "the receiver"                class 14905, standing 7
    depth 0:    6 continuations   what the FULL context licenses
                                  -  .  declaring  in  quotient  that
    depth 1:   17 continuations   by arcing one shorter
    depth 2: 3102 continuations   the root

  "a compression is a codec"    class 22740, standing 1
    depth 0:    1 continuation    "pivot"
```

**The full context licenses exactly one continuation and it is the right word.** The material reads
*"A compression is a codec pivot carrying a declared decoder"*, and a 711 KiB integer container
recovered it with nothing else present.

An unseen token drops the walk to the root — class 0, standing 19,970, the whole material — which is
the honest statement *nothing of this context survived*, not an `UNK` embedding.

**And the presentation was a defect until it was grouped by arc depth.** Sorted by germ the fiber
reads as 3,125 continuations dominated by the root's breadth; the specific ones are buried under the
generic ones. **The depth is the structure the material has**, and reporting the fiber without it
reports the root's breadth as though it were the answer.

## 3. Every Gemma language-tower circuit is full rank — all 168

`q_proj`, `k_proj`, `v_proj` and `per_layer_input_gate` at all 42 layers, through the dyadic mouth to
exact integers, rank over two declared primes:

```text
  168 of 168   256 x 2560   rank 256   deficit 0   both frames agree
```

**No deficit anywhere, at any depth.** This has not been reported before because rank is not well
posed in floating point — an SVD returns a spectrum and a human picks a cutoff — and over integers it
is a number.

The consequence is the one the earlier seven already indicated, now at full coverage: **there is no
free dimension inside a trained weight matrix.** The compression the field achieves is declared in
the architecture — `W_O W_V` is rank ≤ 512 in a 2560 stream by construction, `W_Qᵀ W_K` is ≤ 256,
grouped-query puts 8 heads on 2, and `embed_tokens_per_layer` injects 256 dimensions per layer — and
quantisation is what is left over after that structural compression has been taken.

## 4. Falsifiers

- The rebased residual must stay bounded by the relative ulp. A residual above `2^-8` of the
  coordinate would mean the rebase is not what carried it.
- The container's production must agree with the atlas's own emanation at every depth. A
  disagreement means the file does not carry the transport.
- Any Gemma circuit with a genuine deficit refutes section 3's headline, and the sweep prints each
  one by name.
- A wider rank sweep — the MLP blocks at `10240 x 2560` — must also come back full, or the reading
  is specific to attention.
