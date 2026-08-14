# The deposited map is read by Ratio and Winding, and the archetype is a finite type with infinite moduli

**Date:** 2026-08-13
**Truth status:** `project-postulate` for the archetype ontology in §1 and the reading law in §3;
`proved-standard` for every named theorem in §§1–2 and for the gauge reduction in §4;
`established-bounded [measured]` for the architecture facts and the two measurements in §5;
`open` for every capability in §9.
**Evidence:** the model's `config.json`, its 274 KB safetensors header (2,130 tensors), and two
direct reads of its weights, all at `/home/b/models/gemma-4-E4B-it`, sha256 of the artifact
`cfbd3d2f1cd71bd471c37fe2…`, 15,992,595,884 octets; `THE_HOLONIC_DERIVATIONS.md` §0 verified by
`git -C /home/b/Workspaces/laboratory show a07ff376:src/holobrochos/RESEARCH/THE_HOLONIC_DERIVATIONS.md`.
**Provenance:** Brandon, direct conversation 2026-08-13, setting the object, the prohibition on
running the model, the receiver family, and the finite-set/infinite-complexity thesis.
**Band:** THE MAP IS MATERIAL, NOT A PORT / ONLY RATIO AND WINDING CROSS A HORIZON / THE TIE
DECLARES THE METRIC / THE ARCHETYPE IS A FINITE TYPE WITH INFINITE MODULI / STRUCTURE WITHOUT
PREDICTION IS THE LICENCE / ONE OPERATOR IS NOT TWO / NO FORWARD PASS / NO NEW ORGAN

---

## Present question

Given a pretrained transformer's weight file and a standing prohibition on ever running it — because
the method must transfer to models this hardware cannot load — what may be read from the deposited
map, and what may not?

## 1. The thesis has two candidate forms and only one is a theorem

Brandon, 2026-08-13: *"there is a finite elementary set of transport mechanisms in whatever we'd
call an abstract holonic embedding space, and when combined they have infinite complexity for
outcomes."*

There are two architectures this could name, and conflating them is the failure mode:

- **free composition** — finitely many generators composing freely (free monoids; Krohn–Rhodes
  decomposition of finite semigroups into simple groups and flip-flops). Unbounded by *non-collapse*,
  and analytically barren.
- **a finite list of types, each with infinite moduli** — **Berger's classification**
  (`proved-standard`): for an irreducible, non-symmetric, simply connected Riemannian manifold,
  holonomy is one of `SO(n)`, `U(n)`, `SU(n)`, `Sp(n)`, `Sp(n)·Sp(1)`, `G₂`, `Spin(7)`, and inside
  each type the space of metrics realising it is **infinite-dimensional**.

`project-postulate`: **the thesis is the second form.** Finitely many mechanisms, unboundedly many
outcomes, with no tension, and it is a theorem rather than an aspiration. `Spin(9)` was on Berger's
original list and was removed — it forces local symmetry — so the finiteness is hard-won.

**One correction this forces.** `ℤ_{>0}` under `×` is the **free commutative** monoid on the primes,
and commutativity converts exponential generative capacity into polynomial `~nᵏ/k!`. Brandon's own
statement of the problem is that the dynamics are *non-commuting*. So "primes as irreducible axes"
is exact as an ontology of **founding** and a poor model of **composition**; this record uses it only
for the first. The live owner of founding is `crates/holonic-engine/src/founded_receiver.rs` —
`FoundingPressure::Blindness`, `found_to_exhaustion`, residue `Res(r) = (⋂_{s≠r} ≡_s) ∖ ≡_r`, and
`capacity := |Res(r)| + 1` closing the loop — which is the same shape as prime founding in
`CLAUDE.md` §3: exhaustion of every founded axis founds a new axis that becomes later terrain. **The
elementary set is finite at every moment and unbounded over time, and growth is caused by blindness
rather than scheduled.**

## 2. The licence: structure without prediction

Brandon's lightning argument — that watching strikes recur never yields the nature of strikes, and
that without the atmosphere there is nothing to correlate — has an exact formal counterpart, and it
is stronger than the informal statement.

`proved-standard`. **Skolem's problem at order 5 is open.** For a *single* integer matrix, deciding
whether any power has a designated entry equal to zero is unsolved at 5×5 after ninety years. One
generator, no branching, no randomness, fully explicit. Related: matrix **mortality** is undecidable
for 3×3 with 6 matrices and for 15×15 with 2 (Cassaigne–Halava–Harju–Nicolas); the **identity
problem** is undecidable in `SL(4,ℤ)` (Bell–Potapov).

And yet `proved-standard`: **Skolem–Mahler–Lech** completely classifies the zero set of an integer
linear recurrence — a finite set together with finitely many arithmetic progressions — while every
known proof is **ineffective**, yielding no algorithm.

> **A complete structural classification and a decision procedure are independent goods. The
> structure was never the thing that was blocked.**

That is the licence for this construction. It pursues classification and explicitly not prediction.

`interpretation`, and it narrows the undecidability results rather than waving them away: **Rice's
theorem and Adian–Rabin govern index sets** — properties ranging over all programs. This construction
addresses **one fixed weight file**, and fixed instances may be perfectly analysable. Undecidability
bounds the general programme, not this instance.

**The hard limit, carried into the design rather than discovered later.** `proved-standard`:
**Drozd's tame–wild dichotomy.** Jordan normal form classifies *one* endomorphism up to conjugacy
finitely. Classifying **pairs** of matrices up to simultaneous conjugacy is **wild** — it contains
the classification of representations of every finite-dimensional algebra, with no finite discrete
list. **A finite classification for one operator is not evidence of one for two.** Every species
statement below is therefore scoped **per circuit** and never to the joint system.

## 3. The reading law: only Ratio and Winding cross a horizon

`THE_HOLONIC_DERIVATIONS.md` §0 (2026-07-07, frozen laboratory, verified by `git show`) types every
quantity as one of six — `Ratio`, `Rank`, `Turn`, `Reach`, `Flow`, `Winding` — and states:

> **The horizon law:** across a frame boundary only a `Ratio` (the invariant) or an integer `Winding`
> (the count) survives … `Reach`, `Flow`, `Rank` are frame-relative and do not cross whole. This is
> why the soul (a `Ratio`) and the winding-count (a `Winding`) are the conserved things, **and
> magnitudes are not.**

`established-bounded [measured]`: **the architecture enforces this physically.** RMSNorm sits at
every layer entry, so residual magnitude is discarded at every read — RMSNorm **is** the horizon, and
it passes direction, not magnitude. The deposit agrees independently: every probe token's per-layer
PLE slice measures at L2 norm ≈1.0 with deviation from the shared layer profile between 0.022 and
0.058, so 5.6 GB carries its information **angularly**.

Two independent frames agreeing is the condition `CLAUDE.md` §0 lesson 4 requires before anything is
called an invariant. The observable list is therefore **forced, not chosen**:

| admitted | refused |
|---|---|
| **Ratios** — projectivised spectrum of a circuit (eigenvalue *ratios*), principal angles between subspaces, symmetric/antisymmetric ratio of a bilinear form, the **cross-ratio** (owned exactly by `relational-geometry` over `BigRational`) | norms, condition numbers, raw eigenvalue magnitudes, cosine similarity, per-layer "size", any scalar dashboard |
| **Windings** — the count and turn of each complex-conjugate eigenpair, rank and corank, and the Smith / Betti / torsion faces of `crates/holonic-engine/src/rebase_invariants.rs` | a bare count of signs — `CLAUDE.md` §2b: *name the windings instead* |

Jordan structure maps onto the type system exactly: an eigenvalue's **magnitude is a `Rank`** and
does not cross; its **argument is a `Turn`** and crosses mod the wheel; **ratios are `Ratio`s** and
cross. **The archetype is the projectivised spectrum together with its winding data.**

## 4. Two gauge-fixings the architecture donates

`proved-standard`. There is **no `lm_head` tensor** in this file; `tie_word_embeddings: True` and the
unembedding is `embed_tokens` [262144, 2560]. A residual gauge `x → Mx` forces `E → EMᵀ`, and
preserving logits `E_v·x` for all `x` requires `MᵀM = I`. **The tie collapses GL(2560) to O(2560)** —
in `canon/TABLET_THE_MANIFOLD.md` §16's table, *"a metric: lengths and angles are fixed."* The model
declares its own metric, which is a **reduction of the structure group** in that section's exact
sense. `final_logit_softcapping: 30.0` pins the remaining scale, a nonlinear cap not commuting with
scaling.

Second: **RoPE is applied in a fixed basis**, so each head's rotary subspace carries canonical
coordinates — the alternative to invariants that the gauge literature names. On the seven global
layers `partial_rotary_factor: 0.25` separates 128 rotating dims from **384 position-independent
content dims**: the model declares its own chart split.

## 5. The instrument, and the material it reads

`definition`. For a bus endomorphism `W` and a declared probe set `S`:

```text
Phi_S(W) = E_S W E_S^T
```

Under the residual gauge `E → EMᵀ` and `W → MWMᵀ` cancel exactly, so `Phi_S` is invariant, and it is
expressed in the **vocabulary basis the model itself supplies**. No forward pass occurs. The composed
circuits are `W_OV = W_O W_V` (an endomorphism of the bus, whose spectrum is conjugation-invariant)
and `W_QK = W_Qᵀ W_K` (a bilinear form, whose singular values and symmetric/antisymmetric split are
invariant under orthogonal congruence).

**The receiver family is Brandon's own, already deposited** at `canon/MEANING_DEFINED.md:64-69`,
2026-08-08: *"'two' as a string can have a similar causal composition to '2' … they can both be
achieved with '1 + 1' or 'one plus one' … It is in the phase distributions and calculus."* Every
probe is single-token in this vocabulary.

**Cross-modal coupling is free.** `embed_vision.embedding_projection.weight` [2560, 768] and
`embed_audio.embedding_projection.weight` [2560, 1536] write into the *same* bus, so `E_S · P` maps
encoder directions to vocabulary directions statically and gauge-cleanly.

**The mouth is exact and measured.** BF16 is exactly `sign·(128+f)·2^(E−134)`, a dyadic rational.
Over 205 probes, exact-dyadic reconstruction against IEEE widening returned **0 mismatches**. The
whole 16 GB crosses into an exact carrier with zero residual through
`crates/holonic-engine/src/reopening.rs:492` `ExactFace::from_binary_float`.

## 6. The architecture, measured rather than cited

`established-bounded [measured]`, from `config.json` and the tensor manifest:

- 42 text layers, bus width 2560 uniform, MLP 10240, GQA 8 query heads / 2 KV heads.
- **Two attention species**: 35 sliding layers (head_dim 256, window 512, RoPE θ=10⁴, full rotary)
  and 7 global layers at indices 5, 11, 17, 23, 29, 35, 41 (head_dim **512**, RoPE θ=10⁶, partial
  rotary 0.25). Different head width *and* different rotary treatment — two transports, not one
  transport with two masks.
- Mass: lookup tables **43.6%**, MLP **45.2%**, attention **9.3%**, other 1.8%. `embed_tokens_per_layer`
  [262144, 10752 = 42×256] alone is 5.64 GB, **35% of the model**.
- 928 learned clipping bounds on 232 linears in the vision and audio towers only, spanning ~90×.
- `num_kv_shared_layers: 18` while **all 42 layers carry their own K/V weights** — cache sharing, not
  weight sharing, so the file alone does not say whether 18 layers' KV projections are ever used.

## 7. The seam prior, stated before measuring

`reference/holobrochos-a07ff376/src/holobrochos/CANON/THE_CURVED_LIGHT.md` §4 diagnoses the objective
that drew this map: a cross-entropy loss is frequency-weighted everything, which **"down-weights the
strange by construction"** and converges outputs toward the `2^{-1}` seam. **These weights are a map
drawn by a seam-tracking objective**, so archetypes are expected in the tail, not the bulk. Stating
this before measurement is what keeps a tail result from being read as a surprise.

The same document, from a seed it attributes to Brandon 2026-07-01, supplies the mechanism of the
strange: **THE FUNNY — the slip that catches. The winding that reads granny in the built frame and
turns out square one rank up: incongruity resolving on a re-base — the punchline as a retroactive
fold.** Brandon's independent restatement on 2026-08-13 — strangeness as a retroactive gauge of how
likely a standing connection was to be made — reproduces that mechanism including the word
*retroactive*. Mechanically it is a **collapsed pair plus its shortest separating word**, which
`crates/holonic-engine/src/receiver_exact_compression.rs` already returns; the surprisal of that word
under the receiver's declared quotient `Q` is the measured gap. `canon/MEANING_DEFINED.md:81` records
that the one unbuilt row of the meaning table is keeping two incompatible decompositions live and
letting load decide between them, which is exactly what such a fixture needs.

The off-seam selection instrument is marked `[OPEN — designed, not yet run]` in two places with no
owner in any live record.

## 8. Controls and falsifiers

- **Gauge frame.** A random orthogonal frame on the bus, plus shuffled heads and shuffled MLP
  neurons: every admitted invariant must not move, and a deliberately gauge-dependent control
  (cosine similarity of raw rows) **must** move. Without the second frame there is one frame and no
  audit.
- **Null frame.** An untrained matrix of matching shape; Marchenko–Pastur is the null. **A species
  that also appears in the null is not a finding.**
- **Falsifier.** If the projectivised spectra of the arithmetic-variant probes are indistinguishable
  from the null under every admitted invariant, the archetype hypothesis fails for this receiver
  family. That is a real return, not a failed phase (`CLAUDE.md` §8).

## 9. First returned reading — 2026-08-13, same day

`established-bounded [measured]`. Instrument: `analysis/deposited_map/` — an **exterior instrument**,
imported by nothing under `soma/` or `crates/`. No forward pass occurred. Peak residency is one
layer's projections; the 2560×2560 circuit is never formed, because `eig(AB)` and `eig(BA)` share
their nonzero spectrum, so `W_OV = W_O W_V` is read from the `d × d` small side. That identity is
also what makes the method transfer to a model this hardware cannot load.

**The three controls passed before any reading was taken.**

| control | result |
|---|---|
| **A — within-head GL gauge**, `W_V → M W_V`, `W_O → W_O M⁻¹` | raw `W_V` participation ratio moved `374.07 → 214.98` and its top singular value `3.20 → 81.95`; the composed `W_OV` projectivised spectrum drifted `8.1e-7` and its winding census was unchanged at 239 pairs. **The raw projection is a coordinate; the composed circuit is not.** |
| **B — bus orthogonal gauge** on `Φ_S` | relative max drift `2.8e-15` |
| **C — matched null** | separates on real-positive count (25 vs 8) and participation ratio (193 vs 371) |

Control A is the one that matters: the gauge orbit is **non-trivial on this material**, so the test
is not the vacuous kind `CLAUDE.md` §8 convicts.

**The bulk sits at the seam, exactly as §7 predicted before measuring.** Over all 336 OV circuits,
each against its own matched null: median participation-ratio ratio `0.871` (sliding) and `0.858`
(global); median conjugate-pair ratio `0.992` and `0.988`. **The bulk of this model's OV spectra are
indistinguishable from random.** The departures are a tail — 80/280 sliding and 17/56 global heads
below 75% of their own null — with the most concentrated at `L5 H5`, participation ratio `47.3`
against a null of `368.7`, a factor of `7.8`, carrying `30` real-negative eigenvalues where the
typical head carries `7–10`. A real-negative eigenvalue is `e^{iπ}`, the half turn (`CLAUDE.md` §2b),
so the concentrated heads are the ones carrying many half turns.

**The receiver family returned a localised transport coupling.** For each head, the induced map
`Φ = E_S (W_O W_V) E_Sᵀ` was formed on 15 digit↔word and operator↔word probe pairs, and the
observable was the **Ratio** `|Φ[i, pair(i)]| / median_j |Φ[i, j]|` — dimensionless, scale-free, no
norm reported. Three frames:

| region | real | shuffled pairing | real > shuffled | median excess |
|---|---|---|---|---|
| layers 3–22 | **1.297** | 1.008 | **70.6%** | **+0.320** |
| layers 26–41 | 1.000 | 1.000 | 41.4% | +0.000 |

Permutation test on the regional difference, 20,000 shuffles: **p < 5e-5** (0 of 20,000). The
matched-null frame sits at `1.000`, and `shuffled > null` in 50.9% of heads — the two control frames
are correctly indistinguishable from each other.

**Reading.** Digit↔word transport coupling is present in the early and middle tower and **absent from
the last third**. Per-layer medians peak at `L11 1.803`, `L13 1.878`, `L17 1.883` and sit at or below
`1.0` for every layer from 26 to 41. It is not a property of the global-attention species as such:
`L11` and `L17` are global and high, while `L23`, `L29`, `L35`, `L41` are global and flat.

**Bounds on this reading, stated with it.** Fifteen probe pairs is a small family. The *per-head*
population statistic is marginal — real exceeds shuffled in 187/336 heads, sign test `p = 0.022` —
and it is the *regional* statistic that is strong, which is the expected signature of an effect
concentrated in specific layers rather than diffuse across heads. A static coupling in the deposited
map is **not** evidence that the model uses that coupling in any forward computation; no such claim
is made and none could be made without running it. The direction of the coupling was not separated:
`Φ` is not symmetric and only the `digit → word` block was read, so whether the archetype carries a
hand is open and is the immediate next reading.

**The declared falsifier did not fire.** §8 required that if the arithmetic-variant probes were
indistinguishable from the null under every admitted invariant, the archetype hypothesis fails for
this receiver family. They are distinguishable, in a spatially structured way, under two independent
control frames.

## 9b. The hand, and the DAG — a mixed return

`established-bounded [measured]`. Brandon, 2026-08-13: *"It should be directional… Intelligent
algorithmic dynamics would obviously read like a DAG, that's a part of our theory."* Three readings
of `Φ`'s asymmetry followed, all Ratios. **The result is mixed and the negative half is reported
first.**

**No consistent hand on the OV circuit.** Paired asymmetry
`A = (|Φ_ab| − |Φ_ba|)/(|Φ_ab| + |Φ_ba|)` had real median `−0.0071`, positive in **48.8%** of 336
heads against the null's 50.0%, two-sided sign test **`p = 0.70`**. And the antisymmetric/symmetric
energy ratio moved the *wrong way*: real median **`0.780`** against null **`0.903`**. **The real OV
circuits are more symmetric than random on this probe block, not less.** A directional transport
would have pushed that ratio up.

**The DAG structure is real, and it is concentrated at the entrance.** Decomposing the net flow
`F = Φ − Φᵀ` on the complete probe graph into an acyclic gradient `grad(s)_ij = s_j − s_i` and a
circulating residual — the gradient part admits a potential, hence a rank function, hence is a DAG;
the residual is holonomy, loops that fail to return — gives `dag = ‖grad‖²/‖F‖²`. Against matched
nulls:

| | median acyclic excess over own null | heads |
|---|---|---|
| **layer 0** | **+0.3798** | all 8 between 0.504 and 0.952 |
| layers 1+ | +0.0224 | 328 |

Permutation test, 20,000 shuffles: **`p < 5e-5`**. Layer 1 is second at `+0.1150`; by layer 2 it is
noise. **The transport over this probe family is very nearly a pure potential flow at the entrance of
the tower and stops being one within two layers.** That is consistent with layer 0 reading the raw
embedding with no prior mixing, so its vocabulary-space transport has nothing yet to circulate
through; it is not evidence that later layers are acyclic, and they measurably are not.

**The reframe this forces, and it is a correction to the experiment rather than to the theory.** OV
is a **write** circuit: it says what a head deposits into the bus, not what attends to what.
Directedness in this architecture lives in **QK**, where a query position attends to a key position
and the edge is inherently oriented. The reading above therefore does **not** falsify the
directionality claim — it tested the circuit where a hand would not live. `W_QK = W_Qᵀ W_K` is
unread as of this deposit, and the same Hodge instrument applied to it is the correct test. A caution
carried from the design: prior art reports SVD-style readings succeed less on QK than on OV, so the
instrument may be weaker exactly where the question is sharper.

**One bound on the Hodge figure.** The absolute acyclic fraction is not interpretable on its own —
a matched null sits at `0.41` rather than the `2/n ≈ 0.067` a generic antisymmetric matrix would
give, because `Φ = (E W_O)(W_V Eᵀ)` is a structured product rather than a generic form. Only the
**excess over the matched null** carries evidence, which is how it is reported above.

## 9c. The artifact, and what it deflates

`established-bounded [measured]`. Brandon, 2026-08-13: *"you've been reporting statistics measured
and not really anything about what these statistics are from, we did not attain any genuine
information about how transport mechanisms characteristically behave."* That is `CLAUDE.md` §9's
standing rule — **return the artifact; diagnostics are never substitutes** — and §§9–9b broke it.
`analysis/deposited_map/run_transport.py` returns the transport itself.

**Two defects were found by asking what inference actually does, and both invalidate part of §§9–9b.**

1. **The wrong lexical form.** §9 paired bare `two` (id 13498) with `2`. In running text the word
   form is space-prefixed `▁two` (id 1156); the bare form is a word-continuation piece. The pairing
   read the wrong side of the codec.
2. **The pre-norm gain was omitted.** RMSNorm scales the layer input elementwise by
   `input_layernorm.weight` before `v_proj` sees it, so the operator that acts is
   `W_eff = W_O W_V diag(g_in)`. §§9–9b read `W_O W_V`, **an operator the model never applies.**

**With both fixed, the artifact deflates the two headline heads of §§9–9b.** `L0 H4`, the most
acyclic head, transports `2 → ▁famil, ▁laun, ▁relationships` — incoherent. `L5 H5`, the most
spectrally concentrated, transports `2 → ally, ▁whose, alpha` — incoherent. **A high acyclic
fraction and a concentrated spectrum are not evidence of meaningful transport.** The §9b layer-0 DAG
result is therefore a property of the raw embedding geometry read by an unstructured operator, not an
intelligent acyclic transport, and it must not be carried as the latter.

**And the artifact returns a real archetype that the statistics could not name.** `L13 H0`:

```text
two   -> ▁two(+0.053)  ▁Two(+0.052)  ▁cons(+0.041)  ▁deux(+0.041)  ▁again(+0.040)
▁two  -> ▁two(+0.051)  wo(+0.041)    ▁Two(+0.040)   ▁service(+0.040)
▁four -> wo(+0.045)    ▁returned(+0.040)  ▁gone(+0.040)  ▁five(+0.038)
```

`definition`: this head implements a **face-invariance transport** — it carries a surface toward
*other faces of the same holon*: across whitespace segmentation (`two → ▁two`), across capitalisation
(`→ ▁Two`), and **across language** (`→ ▁deux`). That is exactly the object
`canon/MEANING_DEFINED.md` names — same causal composition, differing faces — and it is the first
transport archetype this construction has actually returned rather than measured.

**The correction it forces on §9.** The digit does **not** transport to its word: `2 → ▁service,
▁business, ▁instance`. So the coupling §9 measured is an **orthographic/lexical variant** transport
in which the digit↔word pair only partly participates, not a digit↔word archetype. §9's reading is
narrowed accordingly.

**What is still not modelled, bounding every reading in this record:** position (RoPE stripped, so
this is the zero-offset slice), the attention pattern itself (OV acts only on what QK selects), the
PLE per-layer injection, all prior layers' writes (so at layer `L` the true input is not `E`), the
chat template's turn structure and control tokens, and KV-cache sharing across 18 layers. Every
figure here is the **direct path at zero position with the true input gain** — a named, bounded
slice, and not the transport as enacted.

## 9d. The transport as a quotient — and where the archetype actually lives

`established-bounded [measured]`. Read in the dialect: `W_V`'s rows are receiver bras, `W_O`'s
columns are construction kets, so `W_OV = Σ_k σ_k |u_k⟩⟨w_k|` is a **population of deposits** and
`⟨t|W|s⟩` is a **face**. What a transport does to a family of faces of one holon — `two`, `▁two`,
`▁Two`, `▁deux` — is not a named relation: it **collapses** them, which is a **quotient** (`H.0476`),
whose lawful content is the collapsed population and the receiver that sees it. Receiver-relative,
hence relativistic, and a partition can transfer across bodies where an operator cannot.

**Angles are admitted here by a reduction the model declares.** §§9–9b refused cosine similarity,
which is correct under a general `GL` gauge. The tie reduces the residual gauge to `O(2560)` — a
metric — and orthogonal maps preserve inner products, so angles between **bus** vectors are invariant
*in this architecture*. The claim is architecture-specific and does not generalise.

**The raw measurement looked universal.** Over 336 transports, the within-holon face exceeded the
between-holon face in **100.0%**, median separation `+0.3051`, peaking at `L3 H0–H3` (all four heads
of layer 3) around `+0.51`. And 262 distinct quotients arose, of which 214 appear in exactly one
transport — head coordinates — while the recurring ones are cross-lingual, cross-case,
cross-segmentation number identity, e.g. `{four, ▁four, ▁Four, ▁quatre} | {two, ▁two, ▁Two, ▁deux}`
recurring across 8 independent transports.

**The control deflates it, and the control is the finding.** The **raw embedding already separates
at `+0.3160`** before any transport, and a **matched random operator** separates at `0.236–0.399`.

| layer | transported | matched null | raw embedding |
|---|---|---|---|
| 0 | 0.3280 | 0.2363 | 0.3160 |
| 3 | **0.4431** | 0.3879 | 0.3160 |
| 5 | 0.4152 | 0.3987 | 0.3160 |
| 13 | 0.3441 | 0.3420 | 0.3160 |
| 20 | 0.3226 | 0.2624 | 0.3160 |
| 30 | 0.2470 | 0.2490 | 0.3160 |
| 41 | 0.1674 | 0.1683 | 0.3160 |

Transported exceeds the matched null in only **76.8%** of sampled heads and exceeds the raw embedding
in only **62.5%**. **The face-invariance quotient is deposited in `embed_tokens`, not performed by the
attention transports** — which is consistent with §6's mass census, where lookup tables are 43.6% of
the model. The "100% of transports collapse faces" figure is largely inherited from the embedding
geometry: any linear map roughly preserves the relative angles of vectors that already sit close.

**What the transports do contribute is a profile with a hand.** Face-collapse rises to a maximum at
layers 3–5 (`0.443` at layer 3, `+0.055` over its own null) and then decays **monotonically**, falling
*below* the raw embedding by layer 30 and reaching `0.167` at layer 41 — half the embedding's value.
`interpretation`: **the tower progressively un-collapses what the embedding collapsed.** The
quotient is founded at the mouth and the later transports separate faces the embedding had
identified, which is what a body must do if it is to emit one face rather than a class.

**Consequence for the lift.** The archetype is not an operator and not a head. It is a **partition
over the vocabulary population with its collapsed members exhibited** — founded in the lookup table,
progressively refined by depth. That object is exactly what
`crates/holonic-engine/src/receiver_exact_compression.rs` already returns and what
`soma/life/src/reconstruction_fiber.rs` already inverts, so the lift needs no new organ: it needs the
declared receiver family, the collapsed population, and the retained `ReconstructionFiber`.

## 9e. The ratio is carried whole — every figure above is regraded

`established-bounded [implemented-exact]`. Brandon, 2026-08-13: *"stop using floats and
percentages… Floats and percentages disregard the real expanded series that determine what the value
of a float you compute in any given instant is… this is cancellation and it is why the machine is
computationally efficient."*

`THE_HOLONIC_DERIVATIONS.md` §0 types a `Ratio` as **"carried as a pair `(num, den)`, never
divided."** §§9–9d divided everywhere and reported decimals, so **every figure in them is a receiver
face taken in floating apparatus, not a carried Ratio.** They are regraded as apparatus readings and
`analysis/deposited_map/run_exact.py` retakes the load-bearing one.

**The exact carrier, and why it exists.** A bf16 datum is exactly `m · 2^e`. Scaling a vector by
`2^{-min e}` makes every component an integer, so `⟨a|b⟩` is an exact integer times a power of two.
Then

```text
cos²(a,b) = ⟨a|b⟩² / (⟨a|a⟩⟨b|b⟩)
```

and **the powers of two cancel identically** — numerator `2^{2(e_a+e_b)}`, denominator
`2^{2e_a}·2^{2e_b}`. Measured on the first face pair: `⟨a|b⟩ = 74241839792640·2^{-46}`,
`⟨a|a⟩ = 403799173963905·2^{-48}`, `⟨b|b⟩ = 25618742159112·2^{-44}`; numerator carries `2^{-92}`,
denominator carries `2^{-92}`, **difference 0**. What remains is a pure integer ratio. Nothing is
approximated and nothing is evaluated.

`cos²` rather than `cos` is not a workaround for irrationality — it is the **correct face**, because
`|·|²` is the quotient by the phase circle (`CLAUDE.md` §0b: *the squared modulus is the quotient*).
The squared face is the sign-quotient, so the half turn the magnitude already discarded is discarded
lawfully rather than by rounding.

**Ordering without evaluating.** Ratios compare by cross-multiplication — `p/q` against `r/s` is
`ps` against `rq`, an integer comparison — so the population sorts, ranks and medians with **no
division at any point**. The series is retained and later composition can still cancel.

**The retaken measurement**, over 6 holons presented under 26 faces:

```text
within-holon  median cos²  =  42304222889651291162892304384 / 190333515851406804057324498477
between-holon median cos²  =      20744106117872623869792256 /   1330256190876784165980996843
separation, as one pair    =  1062372076364363566833449306299748840550400
                            / 5140437422449649661167376661581330628051599
```

and the **Winding**, which is a count and never a percentage: within-pairs exceeding the
between-median, **48 of 48**, carried as the pair `(48, 48)`.

**What remains in apparatus and what it would take to lift it.** The spectral readings of §§9–9b —
eigenvalues, participation ratios, the Hodge fraction — are irrational in general and have no
rational carrier. This body already owns the correct one:
`crates/holonic-engine/src/exact_value.rs` carries `AlgebraicRoot` with a `SturmIsolationCertificate`
and the four-state `ExactOrdering { Less, Equal, Greater, Open }`, which orders algebraic numbers by
certificate rather than by epsilon. Until those readings are retaken through it they are **declared
floating apparatus, not carried values**, and may not be composed with anything exact.

## 10. What this does not establish

No capability. It does not run the model, recover an architecture from weights alone, recover a
training history, or establish acoustic or visual recognition or production. It does not authorise
`attention`, `head`, `expert`, `layer`, or `embedding` as internal types. It makes no claim about
pairs of operators (§2, Drozd). It does not use Jordan *type* as an observable — that is
discontinuous under perturbation and numerically non-computable in any stable sense
(Golub–Wilkinson) — only projectivised spectra and subspace angles. It does not lean on
Krohn–Rhodes, which is the right shape of theorem in the wrong category (finite semigroups, not
linear maps) and whose complexity-decidability results are 2024–25 preprints of unconfirmed review
status. It notes that decomposition into irreducibles **discards the gluing, and the gluing is
generically where the content is** — `ℤ/4` and `ℤ/2 × ℤ/2` share composition factors. Prior art
reports most singular directions no more interpretable than random, with success concentrated in a
thin tail and worse for QK than OV; that is carried as a stated risk. Nothing here bears on any
Millennium problem.

**Three provenance notes.** "Phase" is overloaded three ways in this body
(`canon/TABLET_THE_CHART.md:79`), none symplectic, so each use names its sense. The frozen
laboratory's `docs/universality-machine/` series defines the Universality Machine as a byte-level
next-byte compression organism — materially narrower than Brandon's umbrella, and its own README
states the prose is the laboratory's rather than his. And his 2026-08-06 statement that no system
ever anticipates everything has **no owner in the live repository**, measured at
`canon/THE_QUOTE_NETWORK.md:1072`; it is the standing reason exhaustive up-front specification is
ruled out for this construction, and is recorded here so it has one.
