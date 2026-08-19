# The section must stay on the card: the contract before the resident layer

**Date:** 2026-08-18
**Kind:** pre-construction contract, failure map, dependency-cone and transfer census, and
source-authenticated candidate resolution for the paused Phoenix worktrack. Deposited **before**
any source edit, as the correction directive's first execution step requires. The returns of the
construction it contracts are deposited separately, after they exist.
**Truth status:** **established-bounded** for every measurement below (each carries its command);
**counterexample** for the paused pathway's promoted claims it refutes by reading source;
**proposal** for the contract itself, which schedules nothing until the roadmap's named gate returns.
**Authority:** [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) §"THE PHOENIX REBIRTH…",
[the Phoenix master](../../blueprint/THE_PHOENIX_REBIRTH_LIFTS_INHERITED_HEXIS_AND_RETURNS_A_NATIVE_EXECUTABLE_ECOLOGY.md),
[the Gemma instance](../../blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md),
and [the adversarial audit](2026-08-18_THE_SITE_RETURNED_BUT_THE_CARD_DID_NOT_OWN_THE_PATH_AND_PHOENIX_REMAINS_A_PARTIAL_LIFT.md).
**Position boundary:** [`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) is not moved by this
deposit.

---

## 0. The one correction this contract exists to hold

Brandon's directive, verbatim in its governing sentence: *"the GPU should not be 'used more'; the
continuing semantic section must remain owned by the GPU surface. That distinction is what prevents
another round of adding CUDA leaves to a CPU machine."*

The paused pathway is **closure by reification**:

```text
foreign description
  -> authored operation enum          PortedOperationKind, twelve transformer-shaped variants
  -> host interpreter                 ported_operation::realize / enact
  -> copied tensors + serialized program
  -> replay
  -> self-equality
  -> false native-model claim
```

Every station below refuses that shape by type, not by prose. The unit of the correction is one
**resident section handle** that enters a semantic operation on the card and leaves it on the card;
the CPU never sees a `Vec<Rat>` between two semantic operations.

## 1. Preflight, measured on the clean tree at `45e7c09`

`git status --short` → empty. `git log --oneline -5`: `45e7c09 Regrade the partial Phoenix lift…`,
`584b5d5`, `e43db49`, `5f12734`, `7ad6ab1`. **Nothing user-owned is uncommitted; nothing is reset.**

`bash tools/gates.sh`, 2026-08-18, exit 1, **8 passed, 4 failed** — every red is pre-existing and
none is weakened here:

```text
PASS  tests              2477 passed, 0 failed, 19 ignored over 43 result lines
PASS  authored-levels    0 failures; 390 authored numeric levels in DRIVERS
PASS  named-paths        0 failures; 2712 tokens
PASS  line-citations     0 failures; 431 citations
PASS  claim-index        current
FAIL  driver-catalog     DRIFTED — 0 uncatalogued, 0 missing, 246 rows re-measured
FAIL  output-manifest    recorded 47, present 52: 0 departed, 1 moved, 5 unrecorded
FAIL  closure-manifest   40 closures moved; producing crates holonic-engine, relational-geometry, life
PASS  boundary-artifacts 3 bound
PASS  typst              10/10
FAIL  architecture-lint  93 new ownership/materialization occurrences
PASS  document-law       0 failures; 71 absence claims carry command and date
```

`driver-catalog` is red on a **clean** tree, so the last commit did not regenerate the catalog after
its own driver edits; `output-manifest` and `closure-manifest` are the two ledger gates the roadmap
says cannot be green on a dirty tree — and here they are red on a clean one for the same reason, the
ledgers were not rewritten at the last commit; `architecture-lint`'s 93 is the figure the audit
already recorded. Their repair is a ledger decision taken at commit, not a preflight action.

## 2. The dependency cone and the transfer map of the paused pathway

Read directly from `crates/holonic-engine/src/ported_operation.rs` and
`crates/holonic-engine/examples/phoenix/site.rs` at `45e7c09`.

**The cone.** `phoenix/site.rs::conduct` → `ported_operation::realize` → `realize_handed` →
`enact` (host) → `PortedCarrier` (host closures in `ResidentSourceCarrier`). Of the twelve
`PortedOperationKind` variants, **exactly one — `Contract` — reaches the card**, through
`ResidentSourceCarrier::contract` → `embedding_fiber::MountedReadout::score_many`. `Lookup`,
`RebaseByGain`, `ReEntry`, `Hadamard`, `GatedPassage`, `GrainBoundary`, `Ablate`, `Project`,
`Chronology`, `ContactAndCarry`, `Concatenate` are enacted by the CPU inside `enact`
(`ported_operation.rs:1353-1637`).

**The crossings, per `Contract` occurrence** (`site.rs:105-150`): the standing `Vec<Rat>` is
rounded to BF16 words on the CPU, aligned on the CPU (`align_bfloat16`), uploaded (H→D, `2·width`
octets), scored, and the scores downloaded (D→H, `16·rows` octets) and rebuilt into a `Vec<Rat>`.
So every contraction is **one semantic section H→D and one semantic section D→H**, and every other
operation is CPU semantics between them.

**Census of the whole-layer diagram** (`Reach::WholeLayer`, `site.rs:270-621`), per position:
`Contract` occurrences `q, k, v, o, gate, up, down` = **7**; with `Reach::ThroughEmission` an
eighth. For the three compiled positions `CAUSED = [818, 18740, 563]`:

```text
semantic section crossings, whole layer, 3 positions
   H->D   21 (24 with emission)      the standing re-uploaded before every contraction
   D->H   21 (24 with emission)      the contraction's return copied back into a host Vec<Rat>
   host-enacted semantic occurrences per position:  rebase 7 · project 10 · chronology 9 ·
     contact 8 · concatenate 1 · hadamard 1 · gated 1 · re-entry 2 · grain 5 · lookup 1
weight uploads: once per population with residency (site.rs:87-95), 8 populations
```

The audit's finding is exact: *"only contraction leaves reach CUDA."* And the second finding is
also exact: `carried: BTreeMap<OccurrencePort, Vec<Rat>>` (`ported_operation.rs:1068`) is a host
map of every intermediate section, so **the whole semantic body lives in host memory** and the
device holds only weights and one query at a time.

**Chronology is serialized by the host.** `realize_handed` loops `for front in &fronts { for
occurrence in &front.occurrences { … enact … } }` — a host-authored total order over the fronts
`layers()` declared co-present. `the_front_is_co_present_or_the_gauge_moves_it` already returned that
this enforces dataflow and enacts nothing simultaneously.

## 3. Source-authenticated resolution of the open candidates

**Instrument.** The authoritative Gemma 4 implementation is present locally and is admissible
exterior realization testimony under the Gemma instance §6:

```text
locator   /home/b/scratch/huggingface/.venv/lib/python3.13/site-packages/transformers/models/gemma4/modeling_gemma4.py
version   transformers 5.8.1  (its __init__.py, __version__ = "5.8.1")
sha256    64ecac478c7d11b9a6993ea194bdf98ce867d0e6d361295d976140e0ded53933
config    /home/b/models/gemma-4-E4B-it/config.json  (text_config), and the safetensors header
```

Read directly, and every line below is a `SourceTestimony::Implementation` with that locator:

| open candidate | resolution | where |
|---|---|---|
| does the stored rebase gain carry a unit (`1+g`)? | **No.** `Gemma4RMSNorm.forward`: `normed_output * self.weight.float()`. The gain multiplies directly. | `modeling_gemma4.py:192-210` |
| which two coordinates does the chronology pair? | **The two halves.** `rotate_half(x) = cat(-x2, x1)` and `x*cos + rotate_half(x)*sin` with `emb = cat(freqs, freqs)`. | `:762-789`, `:1140-1157` |
| does the contact carry a scale? | **No.** `Gemma4TextAttention.__init__` sets `self.scaling = 1.0` and passes it to `eager_attention_forward` as `scaling`. **The paused site's `BASE` candidate scaled by `1/√256`; the source does not.** | `:1176`, `:803-834` |
| the PLE branch | Decided, in this order: `residual = h; h = per_layer_input_gate(h); h = GELU(h); h = h * per_layer_input; h = per_layer_projection(h); h = post_per_layer_input_norm(h); h = residual + h; h *= layer_scalar`. | `:1424-1433` |
| the PLE input itself | `per_layer_input = (RMSNorm_256(per_layer_model_projection(x0) · 2560^{-1/2})[layer] + embed_tokens_per_layer[id][layer] · 16) · 2^{-1/2}`. | `:1741-1789` |
| `layer_scalar` | A stored `[1]` multiplying the layer's complete return, last. Present for every layer in the header (`model.language_model.layers.N.layer_scalar`, BF16 `[1]`). | `:1435` |
| the value transport | **The values are RMS-normalized without gain** (`v_norm`, `with_scale=False`, `eps`) before the contact; the paused site carried no `v_norm`. `q_norm` and `k_norm` are per-head RMS with gain, and are applied **before** the chronology. | `:1197-1199`, `:1220-1234` |
| the K/V families | 8 query heads over 2 K/V heads, `repeat_kv`: K/V head `g` serves query heads `4g..4g+3`. Both families are projected on every non-shared layer. | `:791-800`, `:1213` |
| the sliding chronology | `rope_type = default`, `θ = 10^4`, `head_dim = 256`, `inv_freq_i = θ^{-2i/256}` for `i in 0..128`; positions `0..T-1`; the sliding-window causal mask admits `j ≤ t` with `t − j < 512`. Layer `0` is `sliding_attention`. | `:1105-1128`, config |
| the entering scale | `embed_tokens[id] · embed_scale.to(bf16)`, and the source's own comment says why: `sqrt(3072)=55.4256 to become 55.5`. Here `bf16(√2560) = 50.5`, an exact dyadic, **a quotient the source performs at law level**. | `:1441-1454`, `:1578-1580` |
| KV sharing | `first_kv_shared_layer_idx = 42 − 18 = 24`; layers `≥ 24` reuse `shared_kv_states[layer_type]` from the last non-shared layer of the same type, and their stored `k_proj`, `v_proj`, `k_norm`, `v_norm` are **ignored on load** (`_keys_to_ignore_on_load_unexpected`). Layer `0` is not shared. This binds the reuse law to occurrences; it licenses no ablation. | `:1181-1186`, `:1594-1601` |

**Two constants remain irrational and are carried as certified enclosures, never as floats:**
`per_layer_model_projection_scale = 2560^{-1/2}` and `per_layer_input_scale = 2^{-1/2}`. The source
realizes both as `binary64` scalars against BF16 tensors; the *law* is the algebraic number, and the
source's runtime float is a comparison face only.

**What remains open after this reading — nothing that the first layer needs.** Every population the
one-layer deed touches has a decided binding. The `CandidateDiagrams` fibre this contract retains is
therefore **empty for layer 0**, and the resident driver refuses to compile any binding whose
testimony is `Undecided` (falsifier 11).

## 4. The pre-construction contract

**Existing owners being composed, and nothing beside them:**

| responsibility | owner | how it is composed |
|---|---|---|
| typed ports, occurrences, fronts, species, closure | `ported_operation::{PortedOperationComplex, Front, OperationSpecies, SourceTestimony, DiagramClosure}` — the **generic** half, retained | the diagram is bound whole; `fronts()` decides co-presence |
| interchange | `interchange::{Interchange, Coherence, DistinguishingWord}` | **owner-local generalization**: a front's admitted legal orders are enacted into staging and their complete returns compared coordinate by coordinate; the verdict type and refusal type are the existing ones |
| apparatus cover | `hardware_cover::{HardwareCover, CoverDecomposition, FrontCell, Barrier→CoverBarrier}` | the front's occurrences are cells by extent; a cell landing on the CPU chart is a typed obstruction, never a fallback |
| work | `exact_work::{ExactWork, WorkBudget, Admission}` | the whole front's work — contraction, reduction, radical, series, resident write, bit burden, span — predicted **before** the first launch |
| BF16 mouth on the card, mounted weights, row masses | `embedding_fiber::{ResidentReadout, MountedReadout}` | weights mount once and stay resident; the mouth is on the card |
| exact codewords | `exact_value::ieee754`, `exact_value::{AlgebraicRoot, CertifiedSeries}` | site material (band elements, algebraic scales) founded once |
| the container | `foreign_map` | rows and populations named, never taxonomized |

**Typed ports.** A `ResidentSection { rows, width, grain }` is an opaque device handle: two `i64`
arrays `lo, hi` at one declared dyadic grain `2^{-F}`, so every coordinate is a certified interval.
Operations take handles and return handles plus a `LocalReceipt { launches, work, octave census,
width census, refusals }`. **No operation returns a host `Vec<Rat>`.**

**Event occurrence and predecessor identity.** One resident layer occurrence is
`(source occurrence: safetensors sha-lineage + tensor names, implementation locator + sha256,
entering token identities, declared grain and series apertures, cover mode identity)`. The
predecessor of every port is the occurrence and input port that wrote it, read off the diagram's
bonds; a host pointer, a driver ordinal, or a source path is never an identity.

**Local constitutive laws**, each realized as a resident kernel with directed rounding:
lookup with exact dyadic scale; contraction with `i128` accumulation over the mounted BF16 map;
RMS as a resident block reduction with exact `eps` (the `binary64` word `1e-6`) and a certified
reciprocal square root by integer Newton with floor/ceil; chronology as the site's band group
elements raised to the integer position on the card; contact as the interval scores, a declared
null that enters no ratio, certified exponential enclosures by series with an alternating tail,
and an interval division **correct for negative numerators**; GELU as the source's `binary64`
constants through the same exponential; Hadamard, re-entry, and algebraic scale as interval
products and sums. **Every enclosure widens outward, so every remainder propagates through every
successor to the terminal face**, and a magnitude leaving the carrier is a typed refusal.

**Receiver question.** *For declared entering tokens, what is the complete successor standing after
one source-authenticated layer, as a certified enclosure per coordinate, with the card owning every
semantic operation between the entering codewords and the terminal face?*

**Complete returned consequence.** The terminal face copied out once: `T × 2560` intervals; the
per-front receipts (certificate, cover, predicted and measured work, launches, resident octets,
octave and width census); the crossing census with **zero intermediate D→H section transfers**;
the barriers realized on the card, by name; and the parity testimony against the quarantined serial
reference, reported beside and never governing.

**Reconstruction / remainder fibre.** The interval width per coordinate at the terminal face **is**
the propagated remainder; the series and radical apertures are declared coordinates carried in the
receipt; the falsifier that a finer aperture nests the terminal enclosure is the check that the
fibre is propagated rather than sidelined.

**Open alternatives.** None for the layer-0 bindings (§3). The grain `F` and the series aperture are
apparatus apertures with their orbit exhibited; a carrier-range refusal returns the coordinate.

**Grade.** `open` for every Phoenix master station until its named artifact returns;
`implemented-exact` is claimed only for owner tests that pass; the one-layer resident deed is graded
`established-bounded` only if the twenty-four falsifiers the directive lists return.

## 5. Four obstruction species, and why they may not merge

```text
CoverBarrier            hardware_cover: malformed, overlapping, incomplete or inconsistent partition
GlobalCouplingBarrier   a within-section reduction — RMS quadratic capacity, the contact partition
                        function, the hull — named, and realized as a resident reduction or refused
InterchangeRefusal      interchange: an admitted legal order changes the complete return
ResourceObstruction     exact_work: predicted work, residency or carrier range exceeds the surface
```

Each is answered differently — repair the partition; realize the reduction on the card; keep the
order; change partition/factorization/residency/aperture — so one enum that answered all four with
sequential CPU execution would have deleted the information that decides the repair.

## 6. What this contract does not do

It does not resume `the_emission_is_a_section_and_the_answer_is_a_block`. It does not extend
`ported_operation.rs` around its host interpreter; that interpreter is quarantined as serial
reference machinery. It does not claim Phoenix completion, native inference, exact reconstruction,
condensation or cultivation. It moves `CONSTRUCTION_STATE.md` only if the roadmap's named gate —
one complete source-authenticated layer with both K/V families, PLE, epsilon-aware normalization,
propagated remainder, GPU-resident semantics, interchange, complete work admission and
runtime-supplied material — genuinely returns.
