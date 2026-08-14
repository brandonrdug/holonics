# The map declares its own apertures, and an embedding is a declared receiver

**Date:** 2026-08-13
**Truth status:** `established-bounded [measured]` for every figure taken off
`/home/b/models/gemma-4-E4B-it/model.safetensors`; `proved-standard` for `H.0471`, `H.0472` and
`H.0469`, each cited to its registry entry; `interpretation` for the design that composes them.
**Evidence:** direct reads of the safetensors header and payload, this machine, 2026-08-13; four
verification passes over the cited owners; one driver re-run on an RTX 4080 SUPER with an active
display.
**Occasion:** Brandon, this session: *"I'd like you to more carefully analyze and design our
experiment here based on the actual model we're working with, Gemma. Be more considerate of how
arbitrary embedding spaces work in general, we have extensive research on this in our network and in
the old laboratory repository already."*

---

## 1 · What the map declares, read from the bytes with the config never consulted

2,130 tensors, **every one BF16** — so the intake's refuse-by-name on any other dtype is correct on
this file by measurement rather than by assumption.

**The shape alone recovers the model's own partition into two transport laws.** Grouping the
language tower's attention tensors by shape returns exactly two families:

```text
   q[2048,2560] v[512,2560] o[2560,2048]   35 layers
   q[4096,2560] v[1024,2560] o[2560,4096]    7 layers: {5, 11, 17, 23, 29, 35, 41}
```

and `config.json`'s `layer_types` lists `full_attention` at exactly `{5, 11, 17, 23, 29, 35, 41}`.
**Predicted against happened, agreeing at every boundary**, with the prediction taken from the byte
layout and the declaration read only afterwards to check it. That is the reading shape the mouth work
demanded — `ArrivalResponse`'s per-boundary predicted-versus-happened rather than a verdict — and it
came free from the header.

Four further facts, each measured, each bearing on the design:

- **The mouth and the endpoint face are one matrix.** `tie_word_embeddings = True`, so
  `embed_tokens [262144, 2560]` is both intake and readout. `H.0469`'s coarser endpoint face and the
  entry point share a carrier: a closed loop already present in the source material.
- **A token has forty-three coordinate presentations, not one.**
  `embed_tokens_per_layer [262144, 10752]`, and `10752 = 42 × 256` — one global vector plus a
  distinct 256-vector for every layer. *"An embedding is one coordinate presentation"* understates
  this map; it declares forty-three per token.
- **928 scalar-shaped tensors carry declared input/output bounds, per projection** — 480 audio, 448
  vision, and **not one is zero**: `input_max 12.8125` against `input_min −12.875`, real and
  near-symmetric. **Apertures stored as material**, one interval per port, in the weight file. The
  body has no such object and this is the first material encountered that carries its refusals with
  its weights.
- **`layer_scalar [1]` × 42** — one real BF16 scalar per layer, `0.061 … 0.887`, low at both ends,
  dipping at 22–23, high through 31–40. A per-layer conductance profile, in the weights.

And three towers land on one 2560 stream through `embed_vision [2560, 768]` and
`embed_audio [2560, 1536]` — multimodality that provably couples, against RELAMPAGO, where all
21,147 spectral pairs returned apart.

## 2 · Three corrections to a `measured` deposit made the same day

Recorded in full at
`2026-08-13_THE_SEARCH_WAS_IN_THE_WRONG_CHART_AND_THE_CARD_OWNS_THE_QUOTIENT.md`; the short form,
because each is a species that recurs.

1. **`48 × 8 = 384` and the return was `336`.** The driver declared `(0..48)`, six layers named
   nothing, and the print reported the declared count. An authored level, and a receipt carrying a
   figure nobody multiplied.
2. **"Head" was a label the material does not carry.** `num_key_value_heads = 2`: an eight-way row
   split of `v_proj` cuts *inside* a KV head. The pair reported as *"two heads of one layer"* was two
   row blocks in different KV heads. Third time in one evening a unit was fetched off the
   architecture the deed claims to discard.
3. **The counts crossed a frame boundary as bare magnitudes.** A block spans 64 rows at 35 layers and
   128 at seven, so the negative-hand count was taken over populations of 163,840 and 327,680.
   **Magnitudes do not cross; a `Ratio` does.** Both populations divide 327,680, so the rebase is
   exact with zero remainder.

**The rebase moved the return.** One-shot classes `329 → 328`, collapsed pairs `7 → 8`: the
un-rebased count had been *spuriously separating* a pair carrying the same ratio in different frames,
and the pair that appeared is `L34b4 (64 rows) ~ L35b0 (128 rows)` — **across the two frames**, which
the earlier reading could not have seen at all. The horizon law paid, on this body's own instrument.

## 3 · What an embedding is, and it is `proved-standard`

`H.0471`, *Intrinsic curvature and the dispensability of an ambient*, `proved-standard`, Gauss's
Theorema Egregium with Nash — verified verbatim at
`papers/source/holonics/manifold-knot-geometry.typ:618-643`. Its `transformations`:

> A receiver confined to the surface measures the curvature with no ambient; and since an isometric
> ambient always exists but is never unique, **an embedding is a declared receiver rather than a
> fact. Only the intrinsic quantities survive changing it.**

and the half that constrains the experiment, its `boundary`:

> Intrinsic determination is a statement about curvature, not about every geometric quantity.
> **Extrinsic invariants such as the second fundamental form genuinely depend on the embedding and
> are not recovered.**

**This supersedes the framing the design was using.** *"An embedding is one coordinate
presentation"* is the compressed doctrine; `H.0471` is the registered classical theorem it compresses,
and it is stronger — it says the ambient always *exists*, is never *unique*, and that exactly the
intrinsic quantities survive changing it. So the reporting discipline is forced: **every returned
reading is split into intrinsic (survives changing the declared receiver) and extrinsic (does not,
and is therefore a receiver artifact to be reported as one).**

`H.0472`, *Structure-group reduction and the holonomy classification*, `proved-standard`, carries
Berger's list — and its own boundary bars the use the design wanted: *"Berger's list is for
irreducible non-symmetric Riemannian holonomy. Reducible, locally symmetric, pseudo-Riemannian, and
torsionful connections are outside it."* A transformer's transports are not a Riemannian holonomy
group. **The finite-types-with-infinite-moduli shape transfers; the finiteness does not transfer with
it**, and it must be named as an analogy with that boundary rather than inherited as a theorem.

## 4 · The theorem that decides what the return can be

`crates/holonic-engine/src/token_invariance.rs` proves, of its own construction rather than of any
corpus, that two occurrences separate exactly when their windows differ — so a surface's conduct-block
count **is** its distinct-window count, and

> `windows > 1 && blocks == 1` is unsatisfiable, for every surface, at every horizon, on every
> material. A deeper horizon only separates more. **The collapse cannot come from refining; it can
> only come from coarsening the receiver family.**

**So "which transports do the same thing" is malformed at the full family.** The well-formed question
is which **nonempty proper sub-family** holds a set of transports in one block while the full family
separates them. The organ returns it without a search: the collapsing families are downward closed
with a single maximal element, read off the material as `constant_axes`, and the verdict exhibits by
name both the axes the material holds and the axes it varies, with `separations_withstood` forced
nonzero.

That is **conduct-invariance**, and it is the lifted-mechanism criterion stated in an organ that
already computes it. A lifted mechanism is a route family surviving lawful recharting; this is that
sentence made checkable.

**And the current panel is measured to be too fine for it.** Eight collapsed pairs of 336 means the
three-face family separates 328 on its first pass, leaving `found_to_exhaustion` almost nothing to
work on. The archetype lives in what a family holds *together*. **Start from one face and let the
material add the rest.**

## 5 · The admission rule for every successor

`2026-08-10_THE_MANIFOLD_IS_THE_INVARIANT_OF_THE_CURRENTS_NOT_THEIR_CONTAINER_AND_THE_RUNG_IS_THE_HINGE_DEFICIT.md`
§1.1, verified at `:96-110`:

| type system | manifold |
|---|---|
| a type's local representation | a **chart** |
| an implicit coercion | a **transition map** |
| coercion coherence (a `From` diamond must commute) | the **cocycle condition** |
| a coercion whose result depends on the path taken | **holonomy** |
| a lossy cast (`i32 → f64 → i32`) | a transition map that is **not invertible** |

> **an implicit cast is admissible exactly when it is a chart transition, and a chart transition is
> invertible** … **A machine that silently picks one of two routes has assumed the cocycle without
> checking it.**

Applied to this map, each candidate successor is a coercion between two of its typed carriers, and
they do not all have the same species:

```text
   stream -> stream        2560 -> 2560     a chart transition        lawful, invertible
   PLE injection           2560 -> 256 -> 2560   NOT invertible       a QUOTIENT
   vision -> stream         768 -> 2560     injective one way only    a quotient in return
   audio  -> stream        1536 -> 2560     injective one way only    a quotient in return
```

**So the design must declare, per successor, whether it is a chart transition or a quotient**, and
route every non-invertible one through a `ReconstructionFiber` — its loss returned as a collapsed
pair with a separating word, never as an untyped magnitude.

## 6 · The falsifier, in its operational form

`2026-07-21_THE_DATA_REMAINS_STANDING_THE_INFORMANT_ENTERS_ONLY_WHERE_RELEVANCE_FORMS.md:84-92`,
verified verbatim:

> Relevance is not a property stored on `D`, a similarity scalar, a topic label, **an embedding
> distance**, or the private certainty of a reader. At a fixed predecessor event `E`, let `D` expose
> one candidate face and let `D'` be a declared matched sibling: withheld, replaced, moved, or
> semantically foiled while the rest of the predecessor is held exact. Then
>
> ```text
> D informs E relative to D'
>   iff
> Succ(E with D) != Succ(E with D').
> ```

This is the ablation clause of the roadmap's Gemma plan stated as a relation, and it supplies the
discipline that clause lacked: a **matched sibling**, not an unpaired before-and-after. It also
names, in its first sentence, the thing this experiment must not become — an embedding distance.

## 7 · What the design is, after all of that

**Unchanged in target.** The success criterion is not agreement with Gemma; it is a standing
transport built from lifted parts that no admitted material contains.

**Changed in five places, each by something measured or `proved-standard`:**

1. **Start the receiver family at one face**, not three, and let `found_to_exhaustion` add the rest —
   because the three-face panel is measured to separate 328 of 336 and pre-empts the founding.
2. **Split every returned reading into intrinsic and extrinsic** (`H.0471`), and report the extrinsic
   ones as receiver artifacts rather than as properties of the map.
3. **Type every successor as chart transition or quotient** (§5), and give each quotient its
   `ReconstructionFiber`.
4. **Bound every search by the material's own bit-width**, never by a formal degree — Gershgorin and
   Hadamard on the operator's entries, with `refuting_prime` called before any census. The standing
   lesson of the 785×.
5. **Use matched siblings** in every ablation (§6).

**And two objects the map supplies that the design had no plan for.** The 928 declared bound scalars
are apertures carried as material — the first such material this project has read — and the
forty-three-fold coordinate presentation per token makes *"which presentation"* a receiver choice the
map itself declares rather than one the driver must invent.

## 8 · What a run may not claim

- **Berger's finiteness is not inherited** (`H.0472`'s own boundary). Carry the shape, name the bar.
- **No scale action exists**, so no cross-scale self-similarity claim, and scaling is repetition of an
  invariant unit rather than dilation of a magnitude.
- **No timing figure here is a cost law.** One machine, one frame, the card scanning out a desktop.
- **Shape is nearly the format.** The 35/7 partition is read off the byte layout, which is material —
  but a receiver face read off row width would restate the driver's aperture, and the returned-
  partition rule convicts it. It is carried as a **declared frame**, never as a face.
- **`H.0470` is `conditional` and is an instance, not a method.**

## 9 · One provenance correction

`2026-08-13_THE_COUPLING_IS_A_FORK_COUNT_TIMES_A_RATIO…md` attributed the horizon law to
`canon/THE_OWNER_ATLAS.md` §1. That section is *"The intake mouth"*, a table of owners, and the atlas
names the horizon once, at a different subject. The live owner is
`canon/THE_INFORMATION_ENGINE.md` §5.6, with `CLAUDE.md`'s *"The horizon law governs every crossing"*
and the frozen laboratory's `THE_HOLONIC_DERIVATIONS.md` §0 as source. **Corrected in place the same
day.** A misattributed citation in a deposit is the cheap form of the defect the operating contract
convicts at its expensive form, and it is recorded rather than quietly edited.
