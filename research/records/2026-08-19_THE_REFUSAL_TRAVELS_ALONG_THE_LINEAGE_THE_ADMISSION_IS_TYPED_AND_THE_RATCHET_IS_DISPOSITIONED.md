# The refusal travels along the lineage, the admission is typed, and the ratchet is dispositioned

**Date:** 2026-08-19
**Kind:** construction return against the resident-gate directive (Station A of the complete
Phoenix/Gemma sequence): the lineage-local refusal transport that replaced the shared global word,
the typed product-ordered admission that replaced `semantic: None`, the owner-local laws that
replaced the `ResidentBinding` cabinet, the ownership-ratchet disposition, the one real deed and its
inspected artifact, every falsifier with its predicate, and the release reading.
**Truth status:** `established-bounded` for every measurement below (each carries its command or
its artifact line); `implemented-exact` for the owners whose focused tests pass on the card;
**Station A of the directive PASSES on this tree**; every later Phoenix master station remains
`open` and is named so.
**Authority:** the directive of 2026-08-19 (Stations A–L);
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) §"THE PHOENIX REBIRTH…";
[the Phoenix master](../../archive/plans/THE_PHOENIX_REBIRTH_LIFTS_INHERITED_HEXIS_AND_RETURNS_A_NATIVE_EXECUTABLE_ECOLOGY.md);
[the Gemma instance](../../archive/plans/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md);
[the one-graph return this repairs](2026-08-19_THE_LAYER_IS_ONE_GRAPH_LAUNCHED_ONCE_AND_THE_IMMEDIATE_GATE_RETURNS_ITS_FALSIFIERS_WITH_THE_RATCHET_OPEN.md);
[the validation cadence](2026-08-18_THE_GATE_IS_A_RELEASE_RECEIVER_NOT_AN_INNER_LOOP_AND_REPEATED_VALIDATION_BECAME_THE_BOTTLENECK.md).
**Position boundary:** [`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) does not move. A
substation is not a station and a station is not the construction.
**Artifact:** `output/the_layer_stays_on_the_card/layer-0-resident-2-tokens-grain-48-terms-14.form`
(the driver's receipt; git-ignored, named here) and
`output/the_layer_stays_on_the_card/source-runtime-faces-2-tokens.tsv`.

---

## 0. Verdict

The one-graph result stands unchanged — one captured CUDA graph, one launch, one synchronization,
no between-node dispatcher, device-resident section intervals, one terminal return — and the three
blockers the directive named are closed:

- **A1.** There is no global refusal word. Every kernel inspects the refusal words of its
  **declared predecessors and only those**, through a lineage array that is the diagram's own bond
  structure uploaded before the capture opens; the graph's edges place every predecessor's census
  before the successor's kernel, so every word read is final and every thread reads one value. The
  join over several predecessors is the union of flags, the least refusing predecessor index and
  the count — commutative and associative — written into the occurrence's own twelve-word slot. The
  footprint certificate carries every predecessor slot read and the own slot written. The complete
  obstruction lineage is the return, it is one reading under the co-present, serialized and
  reversed-serialized schedules, and a terminal whose lineage refused cannot be read as standing.
- **A2.** `semantic: None` is gone. The deed's admission is a typed product order over every
  semantic coordinate of its `ExactWork` and every apparatus coordinate of its prediction, each
  bounded (by the receiver's declaration or by the mounted card) or **exhibited as unbounded with
  its reason and the apparatus limit that still constrains it**; source-map mounting is its own
  preceding material admission, predicted from the container's header and admitted before any map is
  allocated, which the deed cites; the allocation grain is measured and every allocation is rounded
  to it; no clock enters.
- **A3.** The eleven-variant `ResidentBinding` enum matched at six sites is replaced by owner-local
  laws (`crates/holonic-engine/src/resident_law.rs`): one type per kernel carrying its own species,
  arity, material, a-priori bound, shape, footprint and recording; a future architecture adds a type
  and a kernel and touches nothing else. Every one of the 121 ratchet occurrences was read and
  dispositioned (§6); the ledger rows were changed explicitly; `architecture-lint` is clean.

Measured on the real RTX 4080 SUPER: **twenty-four falsifiers with predicates that can fail return
`PASS`**, seven later stations `OPEN` by name, zero `FAIL`. The terminal face is bit-identical to
the one-graph return's (§4), so the arithmetic moved no coordinate.

## 1. A1 — lineage-local refusal transport

### What was unlawful, exactly

`exact_resident_section.cu` had every semantic kernel read one `global_word` at entry and every
census write it by `atomicOr`. Four consequences, each now a falsifier: `FootprintDisjoint` was
false as represented (the word was a shared mutable address outside every footprint); an unrelated
co-present sibling could see a refusal raised by a branch it never read; whether it saw it depended
on the device's scheduling; and a kernel already running could observe the word change between two
of its threads, so some threads wrote plausible words after others had stopped.

### What stands

Kernel (`kernels/exact_resident_section.cu`, 965 lines, `SLOT_WORDS = 12`):

```text
  [0] refused flags   [1] reach   [2] written   [3] inverted   [4] max octave   [5] bound violated
  [6..8] max width    [8] upstream flags (union over refusing predecessors)
  [9] upstream first (1 + least refusing predecessor index; 0 = none)   [10] upstream count
  [11] lineage inspected (how many predecessor slots this kernel read)
```

`upstream_refused(census, lineage, lineage_count, slot)` is every kernel's first act; the census
kernel writes bound/inverted refusals into **its own** slot and nothing else; **a refused
occurrence's census measures nothing** (marker only) so a partially written section never acquires a
second, spurious refusal from what allocation left in it — found by falsifier 28 returning two
origins on its first run.

Owner (`resident_section.rs`): `begin_passage(&lineage)` / `begin_passage_scheduled(&lineage,
Schedule)` allocate the census array and the **lineage array** (sorted, deduplicated predecessor
indices per occurrence) and upload it before the capture opens; `open(index, producers)` refuses if
the producers opened disagree with the declared lineage; `Lane { slot, census, lineage,
lineage_count }` carries what the kernel reads; `PassageReading::obstruction` is an
`ObstructionLineage` of `OccurrenceRefusal { index, flags, origin, upstream_flags, upstream_first,
upstream_count }`. `Schedule::{CoPresent, Serialized}` is the control axis; the serialized
schedule waits on whichever occurrence was opened before, so opening a front's members in reverse is
another legal completion order of the same diagram.

Passage (`front_passage.rs`): every member's footprint now reads its predecessors' slot ranges and
its own lineage list and writes its own slot (`FrontReceipt::footprints`, `slot_footprints`,
retained so the certificate's premise is inspectable); `launch` returns the deed whole with the
complete lineage and every typed refusal; `read_terminal(&returned)` and `read_section(&returned,
occurrence)` refuse by name — with the lineage — when the occurrence did not stand;
`standing(&returned)` is the verdict beside the lineage.

### The falsifiers, as run

| # | falsifier | result |
|---|---|---|
| 28 | a non-finite bf16 codeword at coordinate **7** of the per-layer entering rows (one branch): the per-layer token entry refuses `MALFORMED` of its own; every successor in its forward cone refuses `UPSTREAM` naming a refusing predecessor; the refusing population **equals** the forward cone (8 occurrences), nothing outside it | PASS, under all three schedules |
| 29 | the five unrelated sibling sections (input rebase, receiver projection, contact, first re-entry, second re-entry) read from each poisoned deed are **bit-identical** to the clean deed; restoring the codeword returns the base terminal bit-identically | PASS |
| 30 | co-present, serialized and reversed-serialized schedules return the **identical complete obstruction lineage** `[(1, origin), (12, ←1), (15, ←12), (30, ←15), (31, ←30), (32, ←31), (33, ←32), (34, ←33)]` and identical typed refusals | PASS |
| 31 | the poisoned terminal is refused by name with the complete lineage under every schedule; `standing` refuses likewise; every member footprint carries its predecessors' census slots as reads and its own as a write; every front `FootprintDisjoint` | PASS |

And the owner tests on the card: `a_runtime_refusal_at_a_nonzero_coordinate_travels_only_along_its_lineage_and_the_sibling_is_bit_identical`,
`the_complete_obstruction_lineage_is_one_reading_under_every_legal_schedule`,
`a_lineage_that_disagrees_with_the_producers_opened_is_a_declaration_error_not_a_silent_read`,
`a_runtime_refusal_in_one_branch_returns_the_complete_lineage_and_the_terminal_cannot_be_read_as_standing`.

## 2. A2 — typed semantic and apparatus admission

`DeedAdmission { semantic: Vec<CoordinateAdmission>, apparatus: Vec<CoordinateAdmission>,
cited_material, free_octets_at_admission }` with `CoordinateAdmission { name, required, ceiling:
Ceiling::{Bounded{ceiling, declared_by} | Unbounded{because, constrained_by}}, admitted }`. The
deed is admitted exactly when every bounded coordinate is inside its ceiling — the product order,
nothing summed, no clock. The receiver (`DeedReceiver`) declares per-coordinate semantic ceilings
by name, an optional scalar `WorkBudget` (priced as one more bounded coordinate), and apparatus
**apertures** that can narrow — never widen — what the card admits.

**The actual deed's admission, as the artifact carries it:** 9 semantic coordinates, all exhibited
unbounded (the receiver declared no ceiling) each with its constraint named; 24 apparatus
coordinates, 5 bounded — `carrier-peak-octaves 63 ≤ 63` (admitted **by construction**: the a-priori
bound is capped at the word before comparison, and a word-exceeding value is refused on the card as
`CarrierLeft` and before launch as `CarrierRange`; this coordinate exhibits, it cannot refuse),
`charged-resident-octets 155,189,248 ≤ 15,695,151,104` free, `scratch-octets 18,432 ≤ 49,152`,
`grid-extent 20,480 ≤ 1,099,511,627,264`, `source-standing-octets 749,844,488 ≤ 749,864,968` (the
cited material admission) — and 19 unbounded with their constraints (streams 36, events 36, graph
nodes 71, edges 78, launches 70, reductions 12, allocations 74, ingress 11,428, receipt egress
1,680, section egress 81,920, retained-remainder grain 48, allocation grain 2,097,152 …).

**The material deed** (`MaterialPlan` from the header → `predict_material` → `admit_material` →
mount → `reconcile`): 19 maps, 749,864,968 resident octets predicted, 187,469,320 stored octets to
cross, 24 allocations, **charged 782,237,696 octets at the measured allocation grain 2,097,152**,
transient peak 52,756,496; admitted against 16,450,125,824 free; **19 of 19 maps measured exactly as
predicted.** The allocation grain is measured by two probes that must compose
(`mount::BorrowedContext::allocation_grain_bytes`, shared with `Context`), never declared.

| # | falsifier | result |
|---|---|---|
| 5 | the scalar price one below requirement → `Semantic{scalar-price-under-declared-metric}`; `entries-written` one below → `Semantic{entries-written}`; the apparatus aperture `charged-resident-octets` one below → `Apparatus{charged-resident-octets}`; each before any allocation: captured launches, deed launches, allocations, resident octets unchanged | PASS |
| 24 | the actual deed's admission is typed throughout; every unbounded coordinate names its reason and constraint; the material admission is cited; nothing is `None` | PASS |
| 25 | predicted vs measured: captured launches 70/70, allocations 74/74, ingress 11,428/11,428, receipt egress 1,680/1,680, graph 71/78 vs 71/78, deed launches 1/1, synchronizations 1/1; material 19/19 | PASS |
| 26 | the charge law: at grain 1 = 2,806,580 = the words' sum; at the measured 2,097,152 = 155,189,248 = the admitted charge; at 2× = 310,378,496; at 4× = 620,756,992; monotone, multiples | PASS |
| 27 | no clock token (`Instant`, `elapsed(`, `SystemTime`, `utilization`, `nvidia-smi`, `Duration`) in the owners' production bodies | PASS |

A material plan that cannot fit (`2^40 × 2^20` entries) refuses at `material-charged-octets` with
zero allocations (`the_material_deed_is_predicted_admitted_and_cited_and_the_grain_moves_the_charge_lawfully`).

## 3. A3 — the laws are owner-local, and the ratchet is dispositioned

`ResidentBinding` (11 variants; matched in `species`, `arity`, `name`, `bound_octaves`, `shape_of`,
the material check, the footprint reads and the recording — six dispatch sites over one table) is
replaced by `trait ResidentLaw` with eleven types — `Enter`, `Contract`, `RmsRebase`, `Chronology`,
`Contact`, `GeluTanh`, `Hadamard`, `ReEntry`, `Scale`, `WithdrawColumns`, `CollapseControl` — each
carrying `name · species · arity · material · bound_octaves · shape · stages · reads · record`.
`ResidentRealization` binds `EventId → Box<dyn ResidentLaw>` and is consumed once at compile. The
determination the directive asked for: **yes, the cabinet is replaceable by typed owner-local
passage nodes, and it has been**; what remains central is the realization table — an index keyed by
the occurrence, which is the relation — and the compile loop that asks each law for its shape.

The disposition table is §6. The ledger `meta/HOLONIC_DSA_BASELINE.tsv` was changed **explicitly**
for the thirty files (the mechanism its header names), each row set to the measured census, with
every row's disposition recorded there; `cargo run -q -p holonic-architecture-lint` →
`holonic architecture clean: 239 files, 21643 inherited occurrences, 0 retired`.

## 4. The deed, measured on the artifact

**Command, closure and clock.** `./target/release/examples/the_layer_stays_on_the_card --tokens
818,18740 --grain 48 --terms 14` (the serial reference run), built by `cargo build --release -p
holonic-engine --example the_layer_stays_on_the_card` (1 m 13–24 s, three times), run 2026-08-19
16:05:17 → 16:11:33 UTC (6 m 16 s, of which the serial reference is 361.2 s), exit 0; and once more `--no-serial` on the final closure
(after the laws moved to `resident_law.rs` and the driver's production-cone scan added it), run
16:13:12 → 16:13:27 UTC, exit 0, 23 falsifiers PASS, 8 OPEN (11 because `--no-serial`), 0 FAIL. The terminal faces of the two runs are bit-identical (`diff` over the 5,120 `terminal face` lines of the two receipts: no difference), so the serial
reference's parity reading carries to the final closure; the two scopes are stated separately
(§7) and not spliced.

**The source occurrence** is the one-graph return's, unchanged: `modeling_gemma4.py` sha256
`64ecac47…` (transformers 5.8.1), `config.json` `33b10c02…`, `model.safetensors` 15,992,595,884
octets, header 281,040 octets `0e2afcbe…`, content `cfbd3d2f…`, 22 regions, 5 assets declared
unused; 35 operations · 84 symbols resolved · 36 fields · 21 shapes.

**The diagram and its price, before any allocation:** 5 ports · 35 operations · 35 occurrences ·
23 fronts · closed · widest front 4; semantic additions 188,506,016 · multiplications 189,457,824 ·
divisions 725,736 · entries written 349,184 · cumulative bits 31,793,152 · peak bits 242 ·
resident entries 81,920 · dependency span 23 · width-weighted 91,642,877,392 — identical to the
one-graph return; apparatus as §2.

**Bound and launched:** bound in 0.019 s · graph 71 nodes / 78 edges as the driver holds it ·
intended (71, 78) · kernel nodes 70 · memset nodes 1; the deed: deed launches 0→1 · captured
launches 70→70 · synchronizations 0→1 · receipt egress 0→1,680 octets (12 words × 35 slots × 4) ·
section egress 0→0 during the deed, 0→81,920 at the terminal read · ingress unchanged across the
deed · **obstruction lineage empty**.

**The terminal face:** 2 × 2,560 enclosures at `2^-48`, widest 70,229,731,541 grains ≈ 2.495e-4,
first coordinates `[-26265767959231/2^48, -26265757242083/2^48]`, … — identical to the one-graph
return's artifact.

## 5. Every falsifier, its predicate, and its result

Falsifiers 1–16 are the one-graph return's with three changes: 3 reads the obstruction lineage
instead of a global word; 5 is the three-way admission refusal above; 9 now includes the
reversed-serialized schedule and the lineage equality. 24–31 are new. All PASS; 17–23 OPEN by name.

| # | falsifier | result |
|---|---|---|
| 1 | production cone structural (eight tokens over six files incl. `resident_law.rs`) ∧ behavioural (no launch between graph and terminal) | PASS |
| 2 | negative interval quotient on the card | PASS |
| 3 | the card owns the chronology: one launch/sync/read ∧ every front `FootprintDisjoint` ∧ every cell on `Device(0)` ∧ graph = intended ∧ lineage empty | PASS |
| 4 | telemetry never grades (27 verdict predicates inspected) | PASS |
| 5 | semantic/scalar/apparatus coordinate below requirement refuses before allocation, naming it | PASS |
| 6 | source mutation refuses (symbol, slice, field, shape, intervention) | PASS |
| 7 | mode mismatch refuses without a deed | PASS |
| 8 | signed-shift controls, 11/11 | PASS |
| 9 | co-present vs serialized vs serialized-reversed: terminal, per-port octave/width and lineage identical; predicted edges = bound edges | PASS |
| 10 | source/runtime chi: bf16 face outside at the terminal 5,111 of 5,120, first separating port `input-rebase` | PASS |
| 11 | serial reference at `2^-96` (361.2 s): parity over 5,120 (0 disagree; widest resident 70,229,731,541 grains of `2^-48`, widest serial 5,013,495,537,701,795,784 grains of `2^-96`), poisoned reference 5,120 disagree, re-read bit-identical | PASS (serial run); carried to the final closure by terminal bit-identity |
| 12 | hidden card → typed refusal, exit 3 | PASS |
| 13 | both K/V families load-bearing | PASS |
| 14 | finer aperture nests 5,120/5,120 | PASS |
| 15 | remainder load-bearing: 5,120 moved | PASS |
| 16 | weights mount once; second tokens cross once | PASS |
| 24–27 | typed admission · reconciliation · grain law · no clock | PASS |
| 28–31 | lineage-local refusal transport | PASS |
| 17–23 | seal, native rest, runtime, adjoint, held-out, matched arms, targeted ablation | OPEN — later stations |

## 6. The architecture disposition

Every one of the 121 reported occurrences (29 files; `resident_law.rs` is a thirtieth, new) was
read into one of the directive's six classes: **(a)** index is the material relation; **(b)**
collection is a returned population; **(c)** collection is a hidden authored order; **(d)** clone
duplicates continuing ownership; **(e)** central enum/match is a hidden interpreter; **(f)** owner
too broad. The four Phoenix owners were read by the author of this record; the remaining
twenty-five by two audit agents whose returns were spot-checked at the flagged sites before being
carried (`interchange.rs:575`, `:864`, `lean_development.rs:693`, `exact_json.rs:51` re-read).

| file | production / test occurrences | (a)/(b) | (c) hidden order | (d) clone of a continuing body | (e) interpreter | (f) split | disposition |
|---|---|---|---|---|---|---|---|
| `front_passage.rs` | all production | every `BTreeMap` keyed by `EventId`, `OccurrencePort`, population name or front depth; every `Vec` a front/plan/receipt population | none — `DeedAdmission::refusing` and `standing()` name the **first** refusing item beside the **complete** set, which is also returned | none — sections, passages, surfaces are never cloned (they are not `Clone`); clones are names, `BigUint`s and receipts | none — the binding cabinet departed; `match` remains only over the two-variant `Ceiling` for reporting | laws split out to `resident_law.rs` this session | retained; ledger row set |
| `resident_law.rs` | all production | the realization index and `staged` keyed by name; `reads` return populations | none | none | none — eleven types, one trait, no table | — | retained; new row |
| `resident_section.rs` | 41 / 14 (`Vec`) | lanes/events/declared/offsets indexed by passage index; slots and refusals returned | none — `open` reads the declared lineage, `finish` joins every lane | none — `TransferCensus` readings only | none | — | retained; ledger row set |
| `source_occurrence.rs` | 38 / 4 | `regions` keyed by population; shapes, symbols, fields returned | none | none — names and shapes into refusals | none | — | retained; ledger row set |
| `ported_reference.rs` | quarantined serial reference | — | — | — | **by declaration**: the host `enact` loop and operation enum are its content, lifted out of production on 2026-08-18 and barred from the production cone by falsifier 1 | — | retained as the declared control; ledger row set |
| `ported_operation.rs` | 64 / 9 | law-keyed, port-keyed, returned lineage/fibre | none (`steps.first/last` read a causal word's endpoints) | none (matrix clones seed folds) | none — species name only | three owners (word algebra, lift-defect chain rule, diagram bridge) | retained; split named open |
| `athena.rs` | 26 / 1 | class-ordinal indexed; returned words/residuals | none | none | none | — | retained |
| `exact_contact.rs` | 4 / 2 | returned faces | none | none | none | — | retained |
| `exact_json.rs` | 12 / 1 | delimiter stack by depth; returned spans | `:51` `field()` resolves a duplicate key to the first pair with no declared rule (unreachable on safetensors headers) | none | none | — | retained; **named open: declare first-wins or refuse duplicates** |
| `exact_linear.rs` | 61 / 6 | pivot/kernel/image populations; RREF unique over ℚ | none | none | none | — | retained (6 of 45 raw `Vec` are doc-comment) |
| `exact_value.rs` | 83 / 8 | coefficients by power, Sturm sequence by position | none | none | `:838` `ExactValue::compare` is a 15-arm match over species pairs — a **total comparison law over types**, not a dispatcher over a program; read as (a) | `ieee754` (550 lines) is a second owner | retained; split named open |
| `exponentiated_ratio.rs` | 17 / 21 | keyed by member and `(i,j)` | none | none | none | — | retained (fixture population) |
| `interchange.rs` | 134 / 31 | founding orders, footprints, certificates | `:575` deferred junction = `founded.first()`; `:701` first refusing order exhibited; `:723` first disagreeing pair; `:864` first separating pair | `:1765` faces/refusals cloned into the certificate while the locals stay live | none | three owners (founding-order certificate, order price, front certificate) | retained; **named open: exhibit populations at 575/701/723/864, move at 1765, split** |
| `landauer.rs` | 11 / 0 | block ordinal | none | none | none | — | retained |
| `lean_development.rs` | 183 / 11 | name-keyed recruitment | `:693` join adopts `readings.first().grain`; `:329` longest chain tie broken by step order | none | none | lexer vs resolution algebra | retained; **named open** |
| `statement_grammar.rs` | 160 / 22 | — | `:1184` bracket family first-wins after sort; `:1638` first separator run | none | none | — | **superseded contaminant (banner 2026-08-17): discharged by deletion, not reduction**; row set until removal |
| `structure_group.rs` | 42 / 17 | permutation indexed by point | none (`.min()` canonical names declared) | none | none | — | retained |
| `surprisal.rs` | 43 / 25 | prime-keyed, event-keyed | none | none | none | `SectionModulus` a weak split candidate | retained |
| `candidate.rs` (agentic) | 146 / 0 | — | `:337/:340/:620` the uttered answer = `maximal.first()` in generation order — **the lexicographic-selection defect the roadmap already convicts** | 13 sites clone thoughts/candidates/currents while live | none | three owners | retained; named open (already convicted in the roadmap) |
| `bin/eros.rs` | 63 / 0 | — | `:214` first file as the printed sample; `:387/:398` `max_by_key` tie-break by index | none | `:615` per-extension intake `match`; `:107` station `match` | apparatus binary | retained; named open |
| `causal_language.rs` | 208 / 23 | route/feature keyed | none | `:654`, `:765`, `:1057/:1096/:1098` whole bodies cloned per branch | `:1457` branching-law `match` | three owners (wire codec, ecology, lexical mouth) | retained; named open |
| `eros_rest.rs` | 42 / 15 | name-addressed reads | `:116/:117` `medium`/`organs` encoded in caller order (sealed bytes depend on it) | `:663` (test) | none | — | retained; named open (canonicalise before sealing) |
| `exposure_codec.rs` | 179 / 24 | alphabet/spelling/unit keyed | none (`assemble` order declared) | `:1183/:1184/:1220/:1292` streams/alphabet/codec copied per rung | none | ladder vs recovery | retained; named open |
| `founded_mouth.rs` | 19 / 8 | position in the material | none | none | none | — | retained |
| `holonic_training.rs` | 138 / 16 | fiber/atlas keyed | none (`.max()` declared with remainder returned) | `:309/:787/:846/:1022` the `TransductionFiber` rebuilt by cloning its halves in four places; `:426/:641` a second atlas | `:1171` `instantiate` `match step {Copy, Found}`; `:557/:618` wire opcodes | three owners | retained; named open |
| `kernel_returns.rs` | 11 / 0 | motion-keyed, admission-keyed | none | none | none | — | retained |
| `lean_mathematics/tests.rs` | 0 / 14 | fixtures | none | none | none | — | retained |
| `material_incidence.rs` | 177 / 20 | atlas/constituent keyed | `:1731` shortest-word tie broken lexicographically | `:940` whole complex cloned; `:275/:282/:290` merge clones | `:1311` arithmetic evaluator over an operation enum | five owners | retained; named open |
| `presentation_quotient.rs` | 123 / 5 | block-keyed | `:879` block representative = least candidate identity (already convicted in the roadmap) | `:613` corpus cloned | `:426` seven-arm receiver `match`; `:484` | window/span vs quotient | retained; named open |
| `suffix_ecology.rs` | 65 / 23 | state/symbol/ordinal keyed | none (`:1429` is the automaton's clone-state) | `:1680` branch cloned into the emanation | none | — | retained; named open |

**What the table says about the three Station A owners:** zero (c), zero (d), zero (e); one (f)
taken (the laws). **What it says about the rest:** the growth that made the ratchet red was
committed between `d601e9e` and `HEAD` without re-seeding, across twenty-five files; it carries
**twelve named hidden-order sites, thirty-odd continuing-body clones and five runtime matches**, each
now addressed by file and line, two of them (`candidate.rs:337`, `presentation_quotient.rs:879`)
already convicted by the roadmap. These are retained at their measured counts with the repairs
named open; none is in the resident gate's cone, and none is reduced here because Station A's owners
are not their owners. A future session that lowers a count need not touch the ledger; one that
raises a count must say why, as this one has.

## 7. The validation epoch, with durations

Owner iteration: `nvcc --ptx` on the changed kernel alone (~1 s, three times); `cargo check -p
mount` (0.6 s); `cargo check -p holonic-engine --lib` / `--lib --tests` / `--examples` (15–30 s);
`cargo test -p holonic-engine --lib -- resident_section front_passage footprint_tests
source_occurrence` (25–30 tests, 1–5 s on the card, four times). Release builds of the one driver
(1 m 13–24 s, three times). Real deed: `--no-serial` twice (9 s each; the first found the census
measuring a refused occurrence, §1), then the complete run with the serial reference (6 m 16 s wall),
then `--no-serial` once on the final closure. Ledgers regenerated once; one complete `bash
tools/gates.sh` (§8). No `cargo test --workspace`, no `--all-targets`, no bare gate during
construction.

## 8. The release reading

**The one complete gate**, `bash tools/gates.sh`, 2026-08-19 16:15:03 → 16:19:30 UTC, exit 0,
4 m 27 s, after the ledgers were regenerated once (`claim_index.py`, `driver_catalog.py`,
`output_manifest.py`, `closure_manifest.py`, each run once; the ownership ledger changed explicitly
as §6 records; `authored_levels.py --check` 0 failures with `SLOT_WORDS` lawfully outside its
regex by the tool's own `WORDS$` exclusion for layout widths):

```text
PASS  tests              2511 passed, 0 failed, 19 ignored over 29 result lines; example targets type-checked
PASS  authored-levels    0 failures; 401 authored numeric levels in DRIVERS
PASS  named-paths        0 failures; 2747 tokens
PASS  line-citations     0 failures; 431 citations
PASS  claim-index        current
PASS  driver-catalog     249 drivers catalogued, 0 uncatalogued
PASS  output-manifest    recorded 53 drivers, present 53: 0 departed, 0 moved, 0 unrecorded
PASS  closure-manifest   current: 54 return directories, 18 orphans
PASS  boundary-artifacts 3 bound
PASS  typst              10/10
PASS  architecture-lint  holonic architecture clean: 239 files, 21643 inherited occurrences, 0 retired
PASS  document-law       0 failures; 71 absence claims carry command and date
12 passed, 0 failed
```

Taken whole, once, on the final closure; nothing is spliced. The cheap named gates
(`claim-index named-paths line-citations document-law driver-catalog authored-levels`) were also read
once before it, 6 of 6, as the edit-loop aperture.

## 9. What stands open, exactly — and the station table

| station | required artifact | current grade | decisive evidence | remaining obstruction |
|---|---|---|---|---|
| **A** resident graph/layer gate | lineage-local refusal transport; typed semantic+apparatus admission; footprints/interchange under refusal; exact arithmetic tests; architecture dispositioned and green; the real one-layer graph deed; release reading | **PASS** | this record §1–§8; 24 falsifiers; ratchet clean; gate reading §8 | none |
| B complete source admission + potential transport | complete manifest over 2,130 tensors, authentication binding, potential atlas over the full tower | open | — | not begun |
| C complete contextual text pathway | layers 0–41, KV sharing, both species, final norm, tied output, plural future section, decoded surface | open | layer 0 only | not begun |
| D source dissection | intervention-backed taxa | open | K/V families + collapse interventions on layer 0 only | not begun |
| E native baseline | executable Eros/Athena arm | open | — | not begun |
| F cross-chart lift | chi, chain law, BF16 fibres, native morphology, recombination | open | PortDefect census is a receiver mismatch face, not chi | not begun |
| G condensation | receiver-exact factorisation | open | — | not begun |
| H cultivation | adjoint-derived delta | open | — | not begun |
| I rest/export/frozen inference | `eros phoenix infer/cultivate` | open | — | not begun |
| J reborn dissection + Phoenix grade | four-body comparison | open | — | not begun |
| K mathematics codec | first vertical circulation | open | — | not begun |
| L GDL/gauge/manifold fold | controls folded into K's artifacts | open | — | not begun |

Station A passed; proceeding to Station B.
