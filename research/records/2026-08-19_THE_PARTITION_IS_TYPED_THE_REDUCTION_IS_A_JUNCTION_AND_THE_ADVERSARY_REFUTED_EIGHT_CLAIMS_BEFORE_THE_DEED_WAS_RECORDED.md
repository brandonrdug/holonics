# The partition is typed, the reduction is a junction, and the adversary refuted eight claims before the deed was recorded

**Date:** 2026-08-19
**Kind:** construction return for **Deed H1** of the single-card plan — the typed section partition
and shared-output reduction receipts, founded by composition — with the composition attempt that
returned the absent relations, the seven pass controls, the adversary pass that refuted eight
claims of the first build and the repairs, the pressure face, what it does not claim, and what it
hands H2.
**Truth status:** `established-bounded` for every measurement; `implemented-exact` for the two
owners; **Deed H1 PASSES on this tree**; no later deed is promoted.
**Authority:** the single-card plan §2, §3.2–3.4, §4.3, §8 "Deed H1", §11; the audit record §6
(H.5–H.8); `CLAUDE.md` §0o and §8 (tautology detection; a partition may not be the preimage of an
authored field; authored levels); [the H0 record](2026-08-19_THE_SCALAR_PATH_RETURNS_ITS_PROFILE_THE_CARD_IS_BUSY_ONE_TENTH_OF_THE_SPAN_AND_EVERY_SECTION_KERNEL_IS_BELOW_ONE_WAVE.md).
**Position boundary:** [`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) does not move.
**Owners:** `crates/holonic-engine/src/section_partition.rs` (1,900+ lines) and
`crates/holonic-engine/src/reduction_junction.rs` (1,200+ lines); one read-only accessor
`CompiledPlan::occurrence_work` (`front_passage.rs`, an iterator, zero ratchet delta).
**Driver:** `crates/holonic-engine/examples/the_partition_is_typed_and_the_reduction_is_a_junction.rs`;
artifact `output/the_partition_is_typed_and_the_reduction_is_a_junction/receipt.form`.
**Adversary:** `crates/holonic-engine/tests/h1_adversary.rs` — 35 public-API attack tests, kept.

---

## 0. Verdict

**The two returns the blueprint named as missing exist, composed from the standing owners, and they
survived an adversarial pass that refuted eight claims of the first build.**

- **`TilingReceipt`** (`section_partition.rs`): a declared partition of one section into coordinate
  regions with completeness and disjointness **computed** (a row-band sweep with a merged
  column-interval complement — a hole disguised by an equal extent sum, an order-hidden overlap,
  L-shaped unions and touching bands all return correctly), read/write footprints handed to
  `certify_footprints` unchanged (the verdict is the interchange owner's; this owner adds the
  *region* behind the returned address), shared-read/halo populations, lanes and barriers from the
  hardware cover, junction outputs checked within the section **and covered by their own partials**.
- **`ReductionReceipt`** (`reduction_junction.rs`): for `y = Σ_a T_a y_a` — the partial regions and
  their exact carried values (checked exactly representable at the declared carrier grain), the
  chart transitions, the **fixed reduction word** and its reversed control, the width at **every
  node** with a declared overflow aperture that refuses by naming the node, **one directed outward
  rounding at the declared boundary and nowhere else** (the count computed, the residual retained,
  its sign opposing the hand), the dependency span as the word's own depth, and the adjoint return
  `ȳ_a = T_a* ȳ` into every partial chart under declared metrics, with the defect returned as an
  **operator residual** `G_X·T_a* − T_a^T·G_Y` rather than a probe reading.
- **`PressureReceipt`**: per cell and per species, `R = ⌈N/C⌉` taken from a founded and radiated
  `ExactReceiverCurrentLaw` inside the declared enactment aperture, `BeyondAperture` (unknown,
  never zero) outside it, a **named zero** (`NoDemand`) for empty material, and **no combined
  coordinate anywhere in the type** — verified by reading the receipt's own field names.

## 1. The composition attempt, and the two relations it returned as absent

Attempted first, and stated in the module docs with the owner that could not carry it:
`hardware_cover::FrontCell` is `{index, extent}` — **no coordinate exists in it**, so no term asks
whether the coordinates partition; `interchange::MemberFootprint` proves pairwise disjointness and
**a partition with a hole is disjoint** — completeness is the one property a footprint certificate
cannot fail; `exact_linear::metric_adjoint` owns **one** map, not a family writing one output;
`exact_work::ExactWork` has one `peak_bits` and never refuses — no per-node width, no aperture;
`receiver_current` has one capacity per site — no resource-species axis. Founded therefore:
`SectionRegion` + the certified partition (absent consequence: `RegionUncovered`, a hole returned
by name), and `ReductionWord`/`NodeWidth` + the junction (absent law: one rounding at the boundary;
absent consequence: the adjoint into every partial). No `TensorPartition`, `ReductionComplex`,
`Scheduler`, `Planner` or `TensorEngine` cabinet.

## 2. The seven controls (each fails under its perturbation, on real Gemma shapes)

q/o/gate/down at T ∈ {1,5,16}, 24 cells each, tails nonmultiple; the reduction on real bf16 words
(layer-0 `q_proj` row against embedding row 0, K = 2,560 into 24 bands): **1** disjoint outputs
certify / a read into a written region orders the front at the named region; **2** 276 shared
immutable reads certify / moving the shared read into the written population refuses; **3** a
shared output refuses without the junction and certifies with it; **4** incomplete, overlapping and
foreign tiles refuse by name; **5** the fixed word and its reversed control agree on the value with
**46 of 47 nodes at different widths**, a one-bit-narrow aperture refuses naming the node, and the
every-node rounding policy is refused with the true count (24); **6** the adjoint reaches 24 of 24
partial charts with every operator residual zero, and every bare transpose exhibits a nonzero
residual under the declared non-identity metric; **7** the pressure receipt names no combined
coordinate (a fact about the type, read off the field names) and exchanging the species' units
moves the split while a combining receipt's sum would not move. Value agreement in control 5 is
**forced by exactness** and the receipt says so — the evidence is the widths and the refusals.

## 3. The adversary pass — eight refutations, each repaired, the tests kept

35 public-API attacks; 27 held on the first build; **8 refuted it**:

| refuted claim | attack | repair |
|---|---|---|
| a degenerate cell refuses | `r0==r1` via struct literal (fields are pub) certified | `certify` re-takes the `EmptyRegion` guard on every region |
| an empty section is no partition | 0-row shape with zero cells certified complete | `EmptySection` defect |
| a junction output is checked against the section | a foreign junction output covered a real hole | `within` checked for every junction output |
| the partials cover their junction's output | a whole-section junction with two 1-entry partials certified complete | coverage computed by the same sweep (`uncovered_within`), holes returned per junction |
| a foreign reduction leaf refuses | `Leaf(99)` over 2 partials silently read as exact zero | `UnknownLeaf` defect; a reading with defects is not a value |
| inner K-regions are checked | a partial contracting past the inner axis certified, and its foreign extent suppressed the hole check | `within` the axis; the sweep runs on regions clipped to the axis |
| the carrier grain binds the material | `1/3` carried at declared carrier `2^-4` certified (the builder's own fixture did it) | every carried value checked exactly representable at the grain |
| the adjoint defect is an operator fact | the bare-transpose control went vacuous at the one authored probe `(1,2,…,n)` (`T=I, G_Y=diag(1,3)` → defect 0) | the probe **removed**; the defect is the widest entry of the exhibited operator residual |

And the adversary's readings, acted on: the `roundings` field was a literal `1` → now a computed
count with its unit named; a zero demand was labelled `BeyondAperture` → now a named zero; the
driver's `.unwrap_or((2048, 2560))` fallback shape → a refusal (a failed header read may not run
controls on authored shapes under a "real shapes" heading); the unexplained source row 18,740 → row
0, the first the header offers, named; the three `characteristic_delay` values labelled declared;
the doc's *"C from the device declaration"* corrected (C is caller-declared per species; the driver
couples it to the cover, not the owner). Six adversary tests that had recorded defects as green
readings flipped under the repairs and were updated with dated in-place comments; no assertion was
deleted.

**Two readings kept as facts rather than repaired.** Control 5's original verdict clause
(*the two words disagree under per-node rounding*) is a property of the material — on symmetric
partials they agree — and was moved from the verdict to a reading, which is the tautology rule
applied to this deed's own control. And the write/read hazard is decided by the declared population
name (`writer_of` compares names): identical coordinates refuse under the section's name and
certify as an immutable shared standing under another — the returned class is partly the preimage
of a caller-set field, which is `CLAUDE.md` §8's rule surfacing in a composed owner; carried as a
stated boundary (a read footprint is a declaration this owner compares against the section's own
address space, nothing else).

**One flagged declaration:** `DeclaredSpecies::sink_capacity` replaced the authored `1`, but the
sinks are terminal so the declaration moves no returned coordinate today — documented on the field;
the alternative (derive 1 from the fan-out construction) is named there and either is lawful.

## 4. Tests and the ledger

`cargo test -p holonic-engine --lib -- section_partition reduction_junction` → **26 passed**;
`cargo test -p holonic-engine --test h1_adversary` → **35 passed**; `cargo check` clean; the driver
rebuilt and rerun once (exit 0). No float in any new file (grep over all four: zero hits). Two
ledger rows added by hand with the dispositions in the builder's report (returned populations and
material-relation indexes dominate; the clones are defects owning what they exhibit);
`front_passage.rs` byte-identical to its baseline (the accessor is an iterator).

## 5. What this deed does not claim

No device was mounted: the cover is `cpu_only()`, every apparatus capacity is a declaration, every
device-chart face is unknown rather than zero. `occurrence_work` is added but unexercised (needs
the card). The two large species stand `BeyondAperture` at the declared aperture with the stated
ceiling beside them. A partition is a decomposition and never a schedule; **tiling is not
compression**. No kernel changed; H2 enacts these receipts on the card. There is not yet an API
binding a certified `ReductionReceipt` to a `SectionPartition` — the junction face in a tiling
receipt is a declaration checked for coverage and containment, and the binding is H2's to realize
in the kernel geometry (the adversary named this absence; it is carried, not hidden).

## 6. The station table

| deed | grade | decisive evidence |
|---|---|---|
| A–D | PASS (frozen) | their records |
| H0 | PASS | the profile record |
| **H1** | **PASS** | this record; 26 + 35 tests; the receipt on real shapes; 8 refutations repaired with the attacks kept |
| H2 | open — next | the tiled contraction; its design study is prepared (scratchpad, 788 lines: subset-monotone tree admission with 44 octaves of headroom, the launch-geometry candidate family validated against H0's measured rows, split-K required for the 256-wide k/v maps, the tensor-accelerator route refused on evidence, the no-float control as a per-entry baseline because four exact kernels carry a compiler-lowered `rcp.approx.f32` seed) |
| H3–H5, P0–P5, M0–M3 | open | in order |

**The one complete gate**, `bash tools/gates.sh`, ending 2026-08-19 21:50:37 UTC, exit 0 — **12 of 12**:

```text
PASS  tests              2578 passed, 0 failed, 19 ignored over 30 result lines; example targets type-checked
PASS  authored-levels    0 failures; 420 authored numeric levels in DRIVERS
PASS  named-paths        0 failures; 2806 tokens
PASS  line-citations     0 failures; 431 citations
PASS  claim-index        current
PASS  driver-catalog     257 drivers catalogued, 0 uncatalogued
PASS  output-manifest    recorded 58 drivers, present 58: 0 departed, 0 moved, 0 unrecorded
PASS  closure-manifest   current: 59 return directories, 21 orphans
PASS  boundary-artifacts 3 bound
PASS  typst              10/10
PASS  architecture-lint  clean: 241 files, 22007 inherited occurrences, 0 retired
PASS  document-law       0 failures; 71 absence claims carry command and date
12 passed, 0 failed
```

Deed H1 passed; proceeding to Deed H2.
