# The roadmap

**This is the single active roadmap.** It supersedes `THE_ORDER_OF_WORK.md`, `THE_SPINE.md`,
`THE_FOUNDATION_REMAINDER.md`, `THE_GROWN_CIRCUIT.md`, `EROS_EMBODIMENT_ROADMAP.md`,
`EROS_MATHEMATICS_PRODUCTION_FLOOR.md`, and `COMPLETE_CPP_ENGINE_ROADMAP.md` as the statement of
what is open. Those files become **provenance**: the record of completed construction and the
source-file map per owner. Read them for history, never for direction.

They are superseded for one reason, stated plainly in the next section: **every one of them
describes a body that is no longer the body.**

## Naming

**No movement here is named by an ordinal.** Each is named by the mechanism it changes, and is
referred to everywhere by that name. Position in this document carries order of work and nothing
else — no capability, no version, no schedule. Brandon has corrected ordinal naming three times:

> *"I do not want to attribute capabilities and version numbers to the phases or the numbers you
> associate with the build, because then you eventually start to refer to the numbers like facts
> instead of using proper semantics."*
> — Brandon, direct ruling

Do not reintroduce numbering by writing "the first movement" as though that were a name.

## The objective

Brandon, verbatim:

> *"a machine that can rigorously perform and analyze computations using internal machinery that
> accommodates transport mechanisms between arbitrary charts, the learning is the intermediary
> mechanism/law/equation"*

And on the encompassing frame, verbatim:

> *"an umbrella term for a machine that can relate arbitrary informants in simulated ecologies,
> where holonics is a framework that encapsulates interdisciplinary features of mathematics,
> physics, and computer science because they are all related and generalize to everything"*

Everything below is ranked by **what unblocks that**, not by what is easy and not by what is
adjacent. Two movements near the end are the hardest work in the document and they are not last
because they are optional; they are last because the movements above them are the instruments
that make them statable as falsifiable laws.

---

## The active line, ratified 2026-08-07 and deposited so it is not re-derived

> *"I have been more explicit about my desire to use a conditioned variant of the machine for
> mathematics derivation and theorems involving linguistics! That directly involves the curvature
> loop, the atlas reader, the skein relations, integration through reflection & sphere packing, and
> codec recovery!"*

**This is one piece of work, not six.** It was repeatedly mistaken for six adjacent items and put to
Brandon as a choice between them; it is not a choice and the composition is stated here once.

**A conditioned variant of the machine, on mathematical and linguistic material, producing
derivations and analysing them as grown circuits.** A derivation *is* a circuit. Analysing it is
reading its invariants. The named pieces are the operations that reading needs:

| piece | what it is in the line | state |
|---|---|---|
| **codec recovery** | the decomposition must be **recovered**, never authored. A tokenizer is a codec; braille, morse and colour are the same operation on other surfaces. Hand-auditing one is not work. | `crates/holonic-engine/src/bit_causal.rs` recovers opaque bit transducers; the symbol-transducer analogue is being built |
| **integration through reflection** | the derivation is traversed as an exact **running sum**, and two paths enclosing one region are compared as a pair whose disagreement is **deposited as holonomy** rather than refined away | `Derive_FTC.lean` proves `∂`/`∫` inverse in the frozen laboratory; the Rust owner is being built |
| **curvature loop** | where those paths disagree is curvature, and it lives on the hinges. `coordination_defect` computes the disclination charge and `geometry_responses` never consumes it — the loop is drawn and open | being built |
| **sphere packing** | Brandon's lightning-leader quadrature: the integration paths are **leaders extending along founded paths**, not spheres radiating. The packing of their reach is the area, and the pathway population is the phase distribution | being built |
| **skein relations** | when two derivations are the **same theorem**: related by local substitutions that preserve the invariant. Supplied 2026-07-24 as *"pivotal for the Riemann Hypothesis and how we define compression for machine learning"* | `crates/holonic-engine/src/skein.rs` |
| **atlas reader** | what lets any of it be read back rather than emitted into a directory nothing opens | open |

**Lean is an export codec**, not a judge and not the proof line — see the redirection at Part two.
The machine produces the derivation and analyses it internally; Lean formalizes what was already
produced so it can be verified and cited.

**What is explicitly NOT this line, and has been refused twice:** the tiger phase atlas, landscape
photography, music decomposition. Those are *material*, and choosing material as the subject is the
hyperfixation `CLAUDE.md` §4 convicts. The mechanism is domain-free — *"the communication medium is
arbitrary and it is the causal calculus that informs common ecological invariants intersecting
between domains."* Do not propose them again.

**Standing conduct on this line.** Brandon, 2026-08-07: *"You need to proceed continuously… this
checkpointing shit you're doing is the reason we can't progress."* Build through the line rather
than stopping after each organ to report and ask which is next. Where his intention or this roadmap
is unclear, **deposit the clarification here** rather than putting the question to him.

---

## The fact that reframes every prior blueprint file

**HEAD is `06518c3`, 2026-08-07: "Transition to Rust: archive the C++ body, import the laboratory
machinery."** Brandon's decision after a comparative audit.

- The C++ engine moved to `/home/b/Workspaces/holonics/archive/cpp-engine/`.
- `crates/{holonic-structure, holonic-language, relational-geometry, holonic-engine,
  holonic-architecture-lint}` and `soma/{body, abi, membrane, surface, life, mount, tools}` were
  imported from laboratory `a07ff376` — 326 files, 282,274 lines.
- The import is **byte-identical**. SHA-256 equality against `a07ff376` was verified for
  `holonic_complex.rs`, `simplicial.rs`, `local_star.rs`, `receiver_phase_atlas.rs`, `conic.rs`,
  `algebraic.rs`, `basin.rs`.
- `cargo check --workspace --all-targets` passes in 23 seconds. 282 Rust files.
- `grep -rnE "\bf32\b|\bf64\b" crates/holonic-engine/src crates/relational-geometry/src` returns
  **zero**. The no-float discipline survived the transition in the two crates that carry the
  mathematics.

**The laboratory machinery is no longer only in the frozen laboratory.** It is live code at
absolute paths under `/home/b/Workspaces/holonics/`. Reading it is no longer archaeology.

The laboratory itself remains **frozen and dirty** and is still read only through git
(`git -C /home/b/Workspaces/laboratory show a07ff376:<path>`). Never read its working tree, never
write to it. That rule is unchanged.

**No authority file had been updated for the transition when this roadmap was written.**
`THE_ORDER_OF_WORK.md`, `THE_SPINE.md`, `THE_FOUNDATION_REMAINDER.md`, `CONSTRUCTION_STATE.md`, and
`CLAUDE.md` §0/§11/§13 all named C++ headers that resolve only under the archive. Verified by
`find`:

| Header named as live by an authority file | Actually resolves at |
|---|---|
| `body/live_machine.hpp` | `archive/cpp-engine/src/include/holonics/body/live_machine.hpp` |
| `body/spine_execute.hpp` | `archive/cpp-engine/src/include/holonics/body/spine_execute.hpp` |
| `structure/transition_invariants.hpp` | `archive/cpp-engine/src/include/holonics/structure/transition_invariants.hpp` |
| `event/checker_return_schema.hpp` | `archive/cpp-engine/src/include/holonics/event/checker_return_schema.hpp` |
| `structure/chi_pair.hpp` | `archive/cpp-engine/src/include/holonics/structure/chi_pair.hpp` |
| `exact/enclosure.hpp` | `archive/cpp-engine/src/include/holonics/exact/enclosure.hpp` |

Each of those is the subject of a movement in `THE_ORDER_OF_WORK.md`. **Those six movements are
not open work in this body.** They describe defects in an archived engine. Some of them name real
mechanisms that must be *re-established* in Rust — the Chi pair especially — and where that is
true, the movement below says so and does not inherit the C++ framing.

**Corrected 2026-08-07 by the movement "The record names the body it has".** The table above is
kept because it is the finding, not because it is still the state. `CLAUDE.md` §0, §11 and §13 are
rewritten against the Rust body; `CONSTRUCTION_STATE.md` is the live position record and the C++
one moved to `archive/cpp-engine/CONSTRUCTION_STATE.md`; eleven blueprint files carry the archive
banner. **The enclosure carrier turned out not to need re-establishing** — it has a live Rust owner
at `crates/holonic-engine/src/exact_value.rs` that is stronger than the archived header, and what
it needs is a driver. `tools/resolve_named_paths.py` is the permanent check.

---

## Verified negative findings

Per the ground rules, absences are reported as first-class results. Each of these was measured in
`/home/b/Workspaces/holonics` at HEAD `06518c3`. "Zero" means zero.

| Claim | Command | Result |
|---|---|---|
| Integer homology exists | `grep -rniE "smith_normal\|hermite_normal\|invariant_factor\|betti\|torsion" crates soma --include="*.rs"` | **1 hit, a doc comment** at `crates/holonic-engine/src/basin.rs:363` |
| A Rust `ChiPair` exists | `grep -rn "ChiPair\|chi_pair" crates soma --include="*.rs"` | **zero** |
| The recruitment remedies are implemented | `grep -rniE "mincover\|min_cover\|provisional" soma/life/src` | **zero** |
| The deposit registry crossed to Rust | `grep -rln "closure_sha256" .` | **only** `archive/cpp-engine/cmake/HolonicDeposit.cmake` and `archive/cpp-engine/standing/MANIFEST.txt` |
| `lean_mathematics.rs` composes reflection | `grep -c "holonic_language\|Reflect" soma/life/src/lean_mathematics.rs` | **zero** |
| A Lean project is in the tree | `git ls-files soma/formal` | **7 files, all generated `.lake/agentic-research-kernel/formal_carry-0000{0..6}.lean`**; no `lakefile.toml`, no `lean-toolchain`, no manifest |
| The atlas TSVs are read | `grep -rn "File::open" crates soma --include="*.rs" \| grep -i tsv` | **1 hit**, `mms_reconnection_traversal.rs:1443`, reading `source-sha256.tsv` — a provenance manifest, **not** the atlas |
| A traversal schedule can be varied | `grep -n "pop_front" simplicial.rs local_star.rs graph_receiver.rs` | **5 hits, all hardcoded BFS**: `simplicial.rs:540`, `simplicial.rs:1203`, `graph_receiver.rs:1858`, `local_star.rs:370`, `local_star.rs:492` |
| `exact_rational_rank` is reusable | `grep -rn "fn exact_rational_rank" crates` | **1 definition**, `algebraic.rs:1081`, **private**, ℚ-rank only |

Two losses are permanent and are recorded so they are not searched for again:

- `git log --all -- "*tiger*"` returns nothing in **either** repository. The tiger prediction PNGs
  are gone.
- `git log --all -- "*semantics_invariant*"` returns nothing in the laboratory at any commit. The
  machine's kernel-accepted theorem `semantics_invariant_under_exact_chart` survives only as a
  name, the proof term `by exact semantics_rebase_iff A e θ input output`, the axiom surface
  `[Quot.sound]`, and SHA-256
  `10eeb3fd789972d071498e590e836a5ac036dc4b4261bef29102366c28e00be1`.

`.gitignore` still carries `/target/`, `/output/`, `/runs/`, `/data/`, and `.lake/` — the exact
mechanism that lost them.

---

## What the laboratory already did

Stated first and in full, per `CLAUDE.md` §7. **None of this is a construction target.** All of it
is now live code in this repository, not a frozen achievement elsewhere.

**The circuit is already a simplicial complex with enforced locality.**
`crates/holonic-engine/src/simplicial.rs` (1,797 lines): `found_vertex` (:197), `found_face`
(:211), `found_hinge` (:255). A wire is `HingeTransport { source, target, turn: ProjectiveTurn }`
(:682); its law is `ProjectiveTurn` (:618-679), exact `(a·s+b)/(c·s+d)` over `BigRational` with
`followed_by`, `inverse`, `is_projective_identity`. `HingeTransportNetwork::add` (:708) **refuses**
any transport whose hinges do not share a face — `SimplicialError::NonlocalTransport`. Locality is
a constructor invariant, not a convention. `flip_hinge` (:295) is the identity-preserving 2↔2
rewrite.

**`∂∂ = 0` is enforced at construction, not tested.**
`crates/holonic-engine/src/algebraic.rs` (2,490 lines): `GradedCausalComplex::found_cell` (:269)
refuses the cell when `boundary_of_chain(&boundary)` is nonzero —
`CausalAlgebraicError::BoundarySquaredNonzero` (`:295`, `:400`). Coefficients are
`ComparativeMultiplicity` (:40), signed ℤ as a `(BigUint, BigUint)` pair with `difference() ->
BigInt` (:86). **The exact integer coefficient ring that Smith normal form needs already exists.**
`SimplicialIncidenceReceipt::realize(&SimplicialComplex)` (:575) is the bridge from the grown
circuit to the chain complex.

**Layout is already exact and gauge-correct.** `crates/holonic-engine/src/local_star.rs` (3,805
lines): `LocalSpatialStanding` (:258) holds no absolute positions. Edges carry `LocalEdgeState {
previous_vector, vector }` where `vector = x_upper − x_lower` (:236-240) — Brandon's *"an absolute
volume is the gauge violation"* is already the type. Positions are reconstructed on demand by
`realize_vectors` (:335). `reform_obstructions` (:399) emits two residual populations that are
already the right shape for the schedule work below: `face_residuals` (schedule-independent — it is
`∂` on the 1-cochain) and `chord_residuals: Vec<LocalChordResidual>` (:244), which is
`carried_vector − realized_vector` per non-tree edge and is **schedule-dependent by construction**.

**Regge curvature is implemented.** `coordination_defect` (local_star.rs:1143) returns
`LocalCoordinationDefect::InteriorCycle { coordination, charge: 6 − |link| }` — the disclination
charge. `LocalTopologyChange::exact_charge_residual: Option<i64>` (:1177) is present only when every
changed link is an interior cycle.

**The spanning-tree / chord decomposition is implemented in the projective-transport case.**
`HingeWorldLaw::propagate` (simplicial.rs:1174) does BFS from the pivot hinge, builds `tree_words`,
and emits a `HingeCycleReturn` (:912) per chord carrying `tree_to_source`, `chord`, `tree_to_target`,
`transition_word`, `class`, and `target_residual`. `HingeCycleClass` (:898) is
`ProjectiveGauge` / `FixedPointHolonomy` / `DisplacedHolonomy`, decided **without materializing the
product matrix** by testing `0, 1, ∞` (`transition_word_is_identity`, :1004). Ungluable
disagreements become `HingeOpenSeam::ConflictingCandidates` (:846), carrying both arrival words.
**This is `CLAUDE.md` §11's "spanning-tree interval labelling, where every non-tree edge forces
additional intervals and that forced population is the certified remainder" — already built, for
projective transport.**

**The expansion schedule is already a typed receiver deed with a measured cost law.**
`crates/holonic-engine/src/graph_receiver.rs` (2,547 lines): `ReceiverGraphDeed` (:922) =
`Found | Dilate | Traverse | Refine | Coarsen | Retain`. `receive_section` (:85) is a
layer-synchronous BFS over the coboundary, then `closed_hull`, then a hard `is_closed_support`
check (:137), returning `ReceiverGraphQueryWork { roots, traversed_fronts, coboundary_lookups,
coboundary_terms, closure_cells, returned_cells }`. `ReceiverGraphAnalysis` (:1003) returns
`dimension`, `f_vector`, `euler_characteristic: BigInt`, `connected_components`, and
`graph_cycle_rank: Option<BigUint>` (:1012), `None` unless every grade-1 cell has exactly one `+1`
and one `−1` unit boundary member.

**Recursive cell definition is the grain quotient.**
`crates/holonic-engine/src/holonic_complex.rs` (1,298 lines): `promote_closed_hull` (:203) takes a
cell's complete closed hull at grain `g` and founds one point at grain `g+1`, retaining the hull
under `HolonicQuotient` (:137), refusing non-coarsening (`NoncoarseningQuotient`, :211).
`HolonicOverlapCell` (:149) records genuine n-way sharing with no fabricated pairwise clique. A
sub-circuit is one point at the parent grain and the parent never loses the child.

**Planar-diagram analysis with a declared aperture.**
`crates/relational-geometry/src/receiver_topology.rs` (1,268 lines): `analyze_receiver_topology`
(:333) returns `{nodes, edges, faces, source_graph, face_dual_graph, source_ihara,
face_dual_ihara}`. Cellularity is checked as Euler (`expected_faces = edges + 2 − nodes`, :550-559).
`IharaSignature` (:219) is the exact-integer Ihara zeta of the graph **and** its face dual.
**Declared aperture:** `DeterminantCutExceeded` — *"the determinant cut admits at most 20
vertices"* (`:306`). `CLAUDE.md` §8 applies: using it past twenty vertices is a defect even if it
appears to return.

**Loss is already a geometric body, not a scalar.**
`crates/holonic-engine/src/basin.rs`: `enact_outcome_basin` (:138) advances every preparation from
its own immutable predecessor and cuts by a declared `observe`/`accepts` pair, returning
`ExactGeometricLoss { region, boundary, minimum_corrections, measure }` (:384). `minimum_correction`
(:256) is exact-rational Dijkstra with a deterministic `(distance, id)` tie-break. `probability` is
a **derived** field, never a primitive.

**And the learning ecology.** `CLAUDE.md` §5's established floor — conditioning and generation
without a distribution, training with a behavioral ablation, multimodality with no fusion module,
receiver-relativity on measured physics, formal mathematics from a detached body, continual
restriction, reflective revision — all of it is `established-bounded` and all of its code is now
in this tree.

---

## The order of work

Movements in order. Each names the mechanism it changes, states the gap, what replaces it, the
grade it must return, an explicit falsifier, and an honest split between what the laboratory
already did and what remains.

### Part one — the body can state what it is

Nothing below Part one can be graded until Part one returns, because until then the repository
cannot say which of its own claims survived the transition.

> **RETURNED 2026-08-07.** All five movements ran and every one returned. Each carries a
> **`Returned`** block below stating what it produced, what was measured, and — this is the part
> that matters — **what an independent adversarial reader cut down.** Four of the five receipts
> were graded `overstated` and one `holds`; no repair was refuted. The **repairs** survived every
> attack. The **receipts** did not, and the corrections are recorded in place rather than in a
> separate errata, because a receipt read later without its correction is the exact failure
> `CLAUDE.md` §8 convicts: *grade the implementation, not the receipt.*
>
> The prose above each `Returned` block is the state the movement was **written against** and is
> kept as provenance. Where it speaks in the present tense about a gap that has since closed, the
> `Returned` block governs.
>
> **Measured 2026-08-07 16:0x**, after the adversarial pass and the repairs it caused:
> `cargo test --workspace` → **758 passed, 0 failed, 14 ignored**, counted off the 37 `test result:`
> lines rather than through a pipe. `python3 tools/resolve_named_paths.py` → **0 failures, exit 0**,
> over 991 path tokens.

---

#### The record names the body it has

**The gap.** No authority file has been updated for `06518c3`. Six C++ headers named as live
subjects of open movements resolve only under `archive/cpp-engine/` (table above).
**Nothing in the repository says which movements survived the transition.** A fresh session reading
`CLAUDE.md` §0 is directed to `THE_ORDER_OF_WORK.md`, which describes an archived engine.

This is not bookkeeping. `CLAUDE.md` §13's standing obligation — *"the scorer, the
counter-morphology, and the constant-subtraction ablation are removed, not deprecated"* — was
about C++ owners that are now archived wholesale. Whether the obligation is **discharged** (the
contaminated owners are out of the live body) or **inherited** (the imported Rust owners carry
their own version of it) is unanswered, and that answer changes what every later grade means.

**What replaces it.** `CLAUDE.md` §0, §11, and §13 are rewritten against the Rust body.
`THE_ORDER_OF_WORK.md`, `THE_SPINE.md`, `THE_FOUNDATION_REMAINDER.md`, and
`THE_GROWN_CIRCUIT.md` are marked provenance and point here. `CONSTRUCTION_STATE.md` gets a
"Verified position" section stating, per admitted mechanism, whether it survived the transition,
was archived, or must be re-established. The §13 contamination audit is **re-run against the
imported Rust** — a scalar-scorer, counter-morphology, and hardcoded-delta sweep over
`crates/` and `soma/` — and its result recorded either way.

**Grade.** Every mechanism `CONSTRUCTION_STATE.md` admits resolves to a path that exists in the
live tree, or is explicitly marked archived. The §13 sweep returns a count and named sites, or a
verified zero.

**Falsifier.** Take every file path named in `CLAUDE.md`, `CONSTRUCTION_STATE.md`, and this file,
and resolve it. **Any path that resolves only under `archive/` while its surrounding prose is in
the present tense fails this movement.** Run it as a script; it is a five-line check and it should
be permanent.

**Laboratory vs remains.** Not a laboratory question at all. This gap was created by the
transition and is owed entirely here.

**Returned 2026-08-07 — receipt graded `overstated`, repair holds.**

The falsifier exists as a permanent script, `tools/resolve_named_paths.py`, with its declared
absences in `tools/resolve_named_paths.allow`. It resolves 991 path tokens across the root,
`canon/` and `blueprint/`, classifies each LIVE / PROVENANCE / ARCHIVE / MISSING, and exits
non-zero when a live document names a path that does not resolve live. **0 failures.**
`CONSTRUCTION_STATE.md` is a live position record again — a prior session had archive-bannered the
only one, leaving the repository with none against document law §1.4 — and eleven documents now
carry banners that schedule nothing.

Three corrections to `CLAUDE.md` came out of it and are carried there in full: the certified exact
enclosure carrier **is not owed as a port**, because `crates/holonic-engine/src/exact_value.rs` is
a stronger owner than the archived header (exact rationals over dyadics, a four-state ordering with
`Open`, Sturm isolation, three species of series-tail certificate) — but its remainder half has
**zero driver references**, so it is written and never exercised. Four of the six convicted §13
owners are not in the archive at all; they were *deleted*, at `2b562c8` and `40e1211`, which is the
fail-closed rule actually working. And `hodge` in this body names the cellular-sheaf Hodge
Laplacian in `sheaf_diffusion.rs`, a different object from the supported-realization mechanism §2
and §11 are about — a reader grepping the word would conclude §11's carrier exists.

**What the receipt claimed and could not support.** The gate reported `0 failures` on a checker
with three ways to be talked out of a check, all three since closed:

- A directory named **without** its trailing slash was skipped entirely. Planting
  `archive/cpp-engine/src/include/holonics/event` in `CLAUDE.md` produced `FAILURES: 0`. The discriminator is now the
  first segment — it must name a real top-level directory, live or archived — which admits
  `research/records` while leaving `Z/p`, `dx/x`, `C/d` and `RIDE/FOUND` alone. Closing it
  immediately surfaced a real dead token that had been hiding.
- The archive banner was a whole-document off switch reachable by ordinary prose. A quoted example
  banner planted at line 9 of the active roadmap took it from exit 1 to exit 0. The test is now
  structural rather than a line window: a document's own banner is front matter, and an ordinary
  prose paragraph appearing first means any banner below it is a quotation. Making that strict
  exposed `THE_SPINE_THE_CUT_AND_THE_TERRAIN.md` opening with a leaked assistant sentence above its
  own title, which was deleted rather than the rule being loosened.
- The allow file could assert an absence that was **false** and the tool would honour it: the
  exemption applied at any verdict, including LIVE, and a stale entry printed without affecting the
  exit code. Both now refuse. Enforcing it caught `blueprint/THE_ROADMAP.md :: lakefile.toml`,
  declared absent while the Lean import had already made it resolve live.

A falsifier's own coverage is part of its grade, and a gate reporting zero is evidence only once
its blind spots are known.

---

#### The proof-line owners get drivers

**The gap.** Ten imported owners have **zero** drivers — zero references in any `examples/`,
`tests/`, or `bin/` path. Measured at HEAD:

| Owner | Definition | Total refs | Driver refs |
|---|---|---|---|
| `ExactReceiverCurrentLaw` | `crates/holonic-engine/src/receiver_current.rs` | 12 | **0** |
| `ExactRelationalLanguageEcology` | `soma/life/src/relational_language/ecology.rs` | 46 | **0** |
| `LaboratorySourceAtlas` | `soma/life/src/laboratory_language/repository.rs` | 12 | **0** |
| `LaboratoryResearchEcology` | `soma/life/src/laboratory_language.rs` | — | **0** |
| `AgenticResearchSession` | `soma/life/src/agentic_research.rs` (1,426 lines) | 15 | **0** |
| `AgenticLanguageEcology` | `soma/life/src/agentic_language.rs` (863 lines) | — | **0** |
| `LeanMathematicsEcology` | `soma/life/src/lean_mathematics.rs` (878 lines) | 33 | **0** |
| `LeanKernelWorld` | `soma/life/src/lean_mathematics.rs` | 4 | **0** |
| `CudaResidentTextMaterialAtlas` | `soma/life/src/text_material/resident.rs` | 13 | **0** |
| `ReflectiveRuntime` | `crates/holonic-language/src/lib.rs` | 82 | 5 |

Contrast: `LiveCurrentMachine` (`soma/membrane/src/live_current.rs`) has **400** references and
**223** in drivers. **The proof-line owners are precisely the undriven ones.** The correlation is
not accidental — the proof line is the deed the laboratory left interrupted, so its owners were
written and never exercised end to end.

**What replaces it.** A driver per owner, or one composed driver that conducts through all ten.
One composed driver is preferred: it is the shape the two-theorem deed needs anyway, and ten
isolated examples would each prove its owner compiles without proving any of them compose.

**Grade.** Each owner is entered from a driver, conducts, and returns its artifact — not its
counts. Per `CLAUDE.md` §9, *"a generated proof, text, image, classification, or obstruction must
itself be returned and inspected."*

**Falsifier.** Delete each owner in turn and confirm the driver fails to build or fails to return.
An owner whose removal changes nothing was never driven. Additionally: a driver whose declared
material cannot exercise the owner's law returns zero and proves nothing about itself
(`CLAUDE.md` §8) — each driver declares a control that makes its law return non-zero.

**Laboratory vs remains.** The laboratory **wrote** all ten and unit-tested some. It **never drove
them**; `ExactReceiverCurrentLaw`, `LaboratorySourceAtlas`, `LeanKernelWorld`, and
`CudaResidentTextMaterialAtlas` have zero test lines even there. Nothing about this movement is
theory work. It is the cheapest movement in the document and it gates the whole proof line.

**Returned 2026-08-07 — receipt graded `holds`. The only one of the five that did.**

Scoped to `LeanMathematicsEcology`, the proof-production owner: 33 references, zero drivers. One
composed driver, `soma/life/examples/eros_lean_proof_production.rs`, now conducts through it and
returns its artifact. It reads the repository's real Lean corpus — 13 documents, 27,980 bytes —
and returns 39 declaration organs, 229 binder charts, **0 retained source surfaces**, 31 proof
paths, 9 admitted against 22 obstructed (6 mathematical, 16 environment), and 8 admitted paths that
recruited an organ. Twelve declared controls, all holding. The `.lean` files themselves are
returned to `output/lean-proof-production/` and inspected, not summarized into counts.

The controls are load-bearing on the owner's actual behavior, and this was established the strong
way. A compile-break falsifier only proves the driver names a symbol, so the verifier made a
single-point **semantic** mutation instead — `push_candidate` in
`soma/life/src/lean_mathematics/syntax.rs:402` forced to store an empty `declaration_lineage`. The
driver returned `[FAILS] the kernel admitted at least one path that recruited a conditioned
declaration organ`, holds fell 12 → 11, exit 1. Reverted bit-identical.

**Two limits, neither of which changes the grade.** One of the twelve assertions cannot fail: *"no
generated path names the removed declaration"* is unfalsifiable, because the generator draws names
only from its own organ set, so once the organ is gone naming it is impossible. It is harmless and
it is not evidence. And the corpus this driver conditions on is the Lean import from the movement
above — the driver does not stand alone, and committing it without the corpus and the Lake project
would leave it reading zero documents and dying at its own `.expect`. They are committed together.

---

#### The Lean project returns to the tree

**The gap.** `soma/life/src/lean_mathematics.rs:811` shells
`Command::new("lake").arg("env").arg("lean")` against a caller-supplied `project_root`. There is
no project to supply.

`git ls-files soma/formal` returns **7 files, all of them generated fixtures** under
`.lake/agentic-research-kernel/formal_carry-0000{0..6}.lean`. There is no `lakefile.toml`, no
`lean-toolchain`, no manifest. Worse: `.gitignore` carries `.lake/`, so the only tracked artifacts
of formal mathematics in this repository are seven files matching an ignore pattern.

The real projects exist. Laboratory `a07ff376` carries
`src/soma/formal/elementary-holonics/{lakefile.toml, lean-toolchain}` and
`src/soma/formal/rh-source-transport/{lakefile.toml, lean-toolchain}`, plus
`src/labyrinth/mathematics/lean/`. The archive carries
`archive/cpp-engine/formal/{elementary-holonics, rh-source-transport}`.

**No formal mathematical production could run in this repository before 2026-08-07.** That was a
hard stop on the objective, and it was a missing-file problem, not a research problem.

**What replaces it.** Import `elementary-holonics` and `rh-source-transport` from `a07ff376` with
their toolchain pins. Narrow `.gitignore` so that generated `.lake/` build output is ignored while
project sources are not. Pin the toolchain explicitly — the kernel verdict is the evidence, and a
verdict from an unpinned toolchain is not reproducible evidence.

**Grade.** `lake env lean` returns a real kernel verdict on a real source from a driver, and the
toolchain version is recorded in the receipt beside the verdict.

**Falsifier.** Submit a proof term known to be wrong and confirm the kernel **refuses** it. A
formal pipeline that has never returned a refusal has not demonstrated that the kernel is in the
loop. This is the same test the archived C++ deed passed with its foil, and it must be re-passed
here.

**Laboratory vs remains.** The laboratory has the projects, the toolchain pins, and 1,164
source-free declaration organs. Remains: import, pin, unignore, and prove refusal.

**Returned 2026-08-07 — receipt graded `overstated`, repair holds.**

Three Lake projects stand in the tree: `soma/formal/{elementary-holonics, kernel-witness,
rh-source-transport}`, 23 files, each byte-identical by blob hash to its source. `.gitignore` was
narrowed so `.lake/build`, `.lake/packages` and the compiled artifacts are ignored while
`lakefile.toml`, `lean-toolchain`, `lake-manifest.json` and every sibling `.lean` are tracked. The
toolchain is pinned `leanprover/lean4:v4.27.0` and the driver records the version beside the
verdict.

The falsifier passed and has teeth. `soma/life/src/lean_mathematics.rs:811` really does shell
`lake env lean` and grade on the process status; a real Lean 4.27.0 kernel refused four
known-wrong terms — two of them for a *false statement*, not merely a malformed proof — and
admitted one correct one. An independent verifier inverted the expectations and got
`disagreements = 2` against a driver that exits non-zero on any disagreement, so the comparison
can fail; and with `PATH` emptied the owner returns `Err(Io(...))` rather than a silent
`Obstructed`, so an absent toolchain cannot read as a refusal.

**What the receipt claimed and could not support.** *"Built a fourth Lean project — this is
required, not decorative"* inverts the situation. `render()` ignores `source_scope`, the driver
re-declares `exactCarrier` in its own prefix, and no submitted source emits an `import` — so the
same owner pointed at the repository root, which contains no Lake project at all, returns
**byte-identical verdicts**. The three declarations in `KernelWitness.lean` are never elaborated by
any test or driver. What this movement established is that Lean 4.27.0 is installed and that
`LeanKernelWorld` correctly wraps it — a real and previously undriven result — **not** that the
returned projects are in the loop. Putting them in the loop is Part two's first movement.

Second correction: the files did not come from the laboratory. All 23 are byte-identical to files
already tracked under `archive/cpp-engine/formal/`, so the move is archive-to-live. The doctrine
sanctions that, but the provenance story in the receipt was wrong, and *"the only tracked artifacts
of formal mathematics in this repository"* was false when written.

---

#### The mount reference agrees with itself

**The gap.** `soma/mount/src/bin/mount-scope-gate.rs:1436` —
`founded_reference_path_is_deterministic_and_nonvacuous` fails, left `(255, 159, 35)` against right
`(256, 160, 38)`. Confirmed failing live. The transition commit declared it pre-existing laboratory
fixture drift *"now visible rather than frozen."* It is not diagnosed.

The assertion that fails is `radiation_species(&a.3) == expected_species` (:1436-1440) — *"the
founded radiation fixture retains its exact non-vacuous FOLD/STEP/CUT species."* The three-tuple is
a FOLD/STEP/CUT population count, off by one, one, and three.

**What replaces it.** A diagnosis, then either a corrected fixture or a corrected law — and the
choice stated. `CLAUDE.md` §8's first rule governs: **grade the implementation, not the receipt.**
If `founded_reference` is right and `EXPECTED_RADIATION_SPECIES` is stale, the constant is
regenerated and the regeneration is shown. If the constant is right, a real defect in the founded
reference path has been sitting frozen in the laboratory and that is the more valuable finding.

**Grade.** The test passes for a stated reason. The receipt names which side moved and why.

**Falsifier.** Perturb the founded reference path and confirm the species tuple moves. A fixture
that cannot be made to disagree is not measuring the reference path, and "fixed" by regenerating a
constant against a broken law would be exactly the receipt-over-implementation defect §8 convicts.

**Laboratory vs remains.** The laboratory carried this failure frozen. It is small and it is not on
the proof line — it is here because a red suite makes every later green result unreadable, and
because §8 says a drifted fixture is a claim about code that has not been checked against the code.

**Returned 2026-08-07 — receipt graded `overstated`, repair holds.**

Diagnosed, and the constant was the stale side. `EXPECTED_RADIATION_SPECIES` moved
`(256,160,38)` → `(255,159,35)` and `(408,250,67)` → `(407,249,62)`, **refounded against the law
rather than regenerated against the output**: two named laboratory commits are cited with the
mechanism each contributed, and the change adds a structural assertion
(`RESERVATION_LIMITED_LANES`) plus a measurement at reservations 8/9/10/12/16. The failure was
inherited, not introduced — `git show HEAD:soma/mount/src/bin/mount-scope-gate.rs` is
byte-identical to the laboratory reference, as are all 20 files in `soma/body/src`.

The falsifier is real and is not cherry-picked. Perturbing the founded reference path moves the
tuple, and an independent verifier perturbed each of the first 64 words of `packed` separately: 57
moved it, 7 did not, so the site the test perturbs is an ordinary sensitive one rather than a lucky
one.

**What the receipt claimed and could not support.** Its headline evidence was *"an independent
implementation — two independently compiled realizations of the law agreed."* That is a check that
cannot fail. `soma/mount/soma-kernel-cuda` declares `body = { path = "../../body" }` and imports
`body::carriage::carry_founded_stroke_trusted`; both that and `carry_founded_stroke` tail into the
**same** `carry_founded_with_layout`. The kernel crate's own header says so in bold: *"the law is
NOT re-expressed."* Host/device parity therefore tests nvptx64 codegen and span carving — a wrong
law returns the same wrong tuple on both sides and the gate still prints `radiation EXACT`. This is
the archived body's own convicted pattern, a deed asserting its dependence as its success
condition, applied to the piece the receipt billed highest. It was also unnecessary: the genuinely
decisive evidence — the content of the removed branch — was in the same receipt, billed as
background.

`CLAUDE.md` §8's *"where an independent implementation exists, state both costs"* means an
independent **implementation**. A second compilation of one source is not one.

**The gap.** The artifact registry was built — **in C++, and it is archived.**
`archive/cpp-engine/standing/MANIFEST.txt` carries `columns=path content_sha256 closure_sha256
founding`, `deposited_returns=123`, `deposited_octets=802855`, and
**`derived_returns_not_deposited=126`**. Commit `c3f75ca` added the verifier that separates
**CONTENT drift** (*the deposit is corrupt — refuse*) from **CLOSURE drift** (*the machine advanced
past what it rested — report*), and it caught the path-fold contamination in 0.03 seconds. The
depositor is `archive/cpp-engine/cmake/HolonicDeposit.cmake:119-122`.

`grep -rln "closure_sha256" .` hits **only the archive**. On the Rust side the mechanism does not
exist, and `.gitignore` still carries `/output/`, `/runs/`, `/data/` — the exact mechanism that
lost the tiger PNGs and `semantics_invariant_under_exact_chart` permanently.

**This movement is here, above the proof line, for one reason: every movement below it produces
artifacts, and without it they are produced into an ignored directory.** The two verified permanent
losses above are what that costs.

**What replaces it.** Port the manifest, depositor, and verifier to Rust with the content/closure
distinction intact. Deposit the **126 underived returns**. Bind every emitted figure to the
standing that produced it.

**Grade.** A deposit is content-addressed, its closure hash is recorded, and the verifier
distinguishes the two drift species on a deliberately corrupted deposit and on a deliberately
advanced standing. Both cases exercised — a verifier that has only ever seen clean input returns
zero and proves nothing about itself.

**Falsifier.** Corrupt one deposited octet and confirm **refusal**. Advance the machine one step
past its rest and confirm a **report**, not a refusal. If both produce the same response, the
distinction that caught the path-fold contamination has not been ported.

**Laboratory vs remains.** The laboratory **did not have this** — it is the one place the archived
C++ body led. Its absence is exactly why the laboratory lost its tiger outputs. Remains: the whole
port, plus the 126 deposits.

**Returned 2026-08-07 — receipt graded `overstated`; the fail-open it missed is now closed.**

`soma/tools/standing-deposit` carries the manifest, depositor and verifier in Rust with the
content/closure distinction intact, and `standing/` holds 43 deposited returns under three
foundings. Both halves of the falsifier were exercised independently, including by a verifier who
made its own perturbations: one flipped bit in a deposited octet gives
`content_drift=1 closure_drift=0 verdict=REFUSED exit=1`; 23 octets appended to a founding's
material gives `content_drift=0 closure_held=36 closure_drift=7 verdict=HELD exit=0`. The two
responses differ in verdict **and** exit status, which is the distinction that caught the path-fold
contamination. Four independent mutations of `registry.rs` each killed a disjoint set of tests, so
the two halves are separately load-bearing and neither passes by the other's mechanism. The reader
consumes the real archived 123-row C++ manifest natively — an independent implementation in the
sense §8 actually means, since CMake computed those hashes.

**What the receipt claimed and could not support.** *"`verify` REFUSES on content drift or an
absent deposit"* had a counterexample. Corrupting **one character of a recorded hash inside
`MANIFEST.txt`** made `is_hex64` false; the row fell through the parser's `if` with no `else`; and
because `verify_manifest` iterates only rows that survived parsing, the deposit left the gate and
the gate returned `verdict=HELD exit=0`. On that input class the port was **strictly weaker than
the machinery it replaced** — `archive/cpp-engine/cmake/HolonicRegistry.cmake:41`'s looser `([0-9a-f]+)` matched the row and
refused it on comparison. Failing open where superseded machinery failed closed is the §13 rule-3
defect exactly. A second gap sat beside it: the verifier walked the manifest and asked the tree
about each row, but never walked the tree and asked the manifest, so a file no row binds was
invisible.

Closed 2026-08-07 with three closures, each shown load-bearing by reverting it and watching exactly
its own test fail:

- A row **shaped** like a deposit — two adjacent 64-character fields — whose digests are not hex
  now refuses as `CorruptDigest` instead of vanishing. Width-only, so it cannot fire on prose.
- `deposited_returns` and `foundings` are compared against the rows actually read. This is the
  strictly necessary one: it catches a row lost by **any** mechanism, including deletion outright,
  which nothing else catches, and it alone would have closed the demonstrated attack. The archived
  reader parsed that header and never compared it to anything.
- A file under the manifest's own territory that no row binds is `unmanifested` and **refuses**.
  Territory is the set of first path components the rows occupy, so `MANIFEST.txt` and `PLAN.txt`
  are outside it by construction rather than by a name list that would rot. `deposit` now prunes a
  return dropped from the plan, so superseded returns fail closed instead of lingering — bounded to
  the new manifest's own roots, and skipped entirely when it has no rows, so an empty plan can
  never destroy a standing.

Both real manifests pass all three unchanged: live 43 rows against 43 files, archived 123 against
123, zero strays in either.

**Not closed.** The manifest can still drift from the standing in one direction — `deposit` binds
what the plan names, and a *plan* that goes stale relative to its driver is not detected here. The
126-deposit backfill is also not done; 43 stand.

---

### Part two — the proof line

> **REDIRECTED 2026-08-07 by Brandon, direct ruling. Lean is not the authority and never was.**
>
> Part two as written below centres an external checker. That is a defect in this document, and its
> provenance is legible: the single sentence the whole proof line descends from names Lean as where
> the request *came from* and corrects to internal machinery in the same breath — *"this came from
> wanting the machine to work with linguistics and Lean in the last laboratory […] I meant for it to
> lead into a machine that can rigorously perform and analyze computations using **internal
> machinery** that accommodates transport mechanisms between **arbitrary charts**."* The documents
> kept the origin and dropped the correction. Lean got centred because it is easy to grade —
> binary, legible, produces receipts — which is `CLAUDE.md` §9b's convicted hyperfocus exactly.
>
> The ruling, verbatim:
>
> > *"What does the machine need Lean for? We don't need Lean to give the machine approval to grow
> > circuitry, it can be its own Lean, I don't understand this obsession, I have already deterred it
> > in the past."*
>
> > *"All of the complex geometry references I've made, references to polynomials, to the problems
> > like RH and Hodge, they're all related not by the fields they come from, but by the fact that I
> > know that they all fundamentally come down to being computationally founded and validated. There
> > is nothing special about language in terms of 'proving' something, language is just a way of
> > giving information degrees of freedom to transport and evolve […] it fundamentally doesn't
> > matter if there is an existing paper that says anything about RH or Hodge, machines will still
> > have to compute the consequences and intelligent constructs will have to think through the
> > derivation independently thereafter still simply to continue networking the consequences."*
>
> **What replaces it.** Identity is what survives reorganizing the symbols — his 2026-08-06
> statement, which the quote network already files as *the invariance requirement for the proof
> machine*: *"the symbol does not dictate what the information contains, you could reorganize the
> symbols and the structure of the proof or algorithm would determine the identity of the underlying
> algorithmic patterns."* That is `chi' = G chi G^-1`, it is the MorphoHDL question *what survives
> every expansion schedule*, and over an integer incidence it has an exact internal answer. Lean, if
> it stays at all, is one receiver among receivers — a cheap second frame, never load-bearing, never
> what a morphology keys on.
>
> **Returned the same day.** `crates/holonic-engine/src/rebase_invariants.rs` and
> `crates/holonic-engine/examples/grown_circuit_invariants.rs`. See *The circuit becomes an integer
> chain complex with torsion* in Part three, which this ruling moves above the proof line.

> **DEMOTED 2026-08-07 by Brandon, direct ruling. Lean is an export codec, not a proof line.**
>
> > *"We can produce MorphoHDL-like artifacts with the machine and analyze them, that was what I
> > wanted the machine to do in terms of learning mathematics and producing derivations and
> > theorems; **Lean was just a side-effect** where we can ideally translate the production of the
> > machine into Lean artifacts that can be used for verification and formalization."*
>
> So the objective is: **the machine produces a derivation, the derivation is a grown circuit, and
> the machine analyses it internally** — `β₀` the distinct contents derived, `β₁` the independent
> distinct routes to one result (the phase distribution over proofs, as an exact integer, not a
> probability over tactics), torsion a step that cannot be un-derived. Lean then formalizes what was
> *already produced*, at the boundary, so it can be verified and cited.
>
> The two movements below keep their mechanisms and lose their rank. They are the **export path**.
> One consequence is immediate: *the reflective composition belongs on the decomposer, not on the
> kernel verdict* — what re-integration founds must change how the next decomposition cuts, which is
> the downward crossing the laboratory's own record names as absent (*"`wr` is inert; founding is
> byte-level bottom-up"*).

This is the objective directly. `CLAUDE.md` §0 names it: *"the machine learning to produce
mathematical proofs."*

---

#### The kernel return becomes a reflective morphology event

**The gap.** Laboratory
`src/soma/RESEARCH/2026-08-02_THE_PORT_CARRIES_THE_INTERIOR_THE_KERNEL_RETURN_CULTIVATES_THE_NEXT_THEOREM_PLAN.md:385`,
verbatim:

> *"make the kernel return a reflective morphology event. Compose `LeanMathematicsEcology`,
> `LeanKernelWorld`, `AgenticResearchSession`, symbolic reasoning, and `ReflectiveRuntime` so the
> formal return is not a detached report."*

Every piece exists. `ReflectiveRuntime`, `ReflectionFrame`, `ReflectiveContinuation`, and
`CodecStep::{Advance, Rest, Reflect}` are in `crates/holonic-language/`, `no_std`, deliberately not
`Clone`. The reflective-force law is exact: `step(α_a(B, m'), x) = execute(m', x)`.

**The composition was never made.** `soma/life/src/lean_mathematics.rs` contains **zero**
references to `holonic_language` or any `Reflect*` symbol. Only
`soma/life/src/agentic_language.rs:21-23` uses `ReflectiveRuntime`. The session that was to build
it was interrupted by a resource failure.

**This is the movement in which Brandon's "the learning is the intermediary mechanism" becomes true
of mathematics rather than of a corpus about mathematics.** Today a kernel verdict is a detached
report: the ecology emits a source, `lake` returns, and the return is read. Nothing about the
machine's own morphology changed as a consequence of the kernel having spoken. A machine that
learns to produce proofs is one whose next proof attempt is structurally different because of the
last verdict — acceptance and refusal alike.

**What replaces it.** The kernel return enters as a reflective morphology event through
`CodecStep::Reflect`, founding a `ReflectionFrame` that later production conducts through. A
refusal must change morphology as much as an acceptance does — a machine that only learns from
success has not learned from the kernel, it has filtered on it.

**Grade.** A kernel verdict causes a structural change in the reflective morphology, and a
subsequent production passage conducts through the changed structure. Per `CLAUDE.md` §13's
obligation 3: *a training claim requires a structural change in that organization plus
source-detached remount plus an ablation that removes the claimed later conduct by removing
structure.* All three, or the claim is not made.

**Falsifier.** Ablate the reflection frame founded by verdict *V* and confirm the later production
that depended on *V* **stops**. If it still returns, the verdict was decorative and the composition
is a wrapper. Second falsifier: run with kernel refusals only, no acceptances, and confirm
morphology still changes. If it does not, the mechanism is success-filtering wearing reflection's
name.

**Laboratory vs remains.** The laboratory built every component and **never composed them**;
verified zero references. Remains: the whole checkpoint. Depends on **the proof-line owners get
drivers** and **the Lean project returns to the tree**.

---

#### The two-theorem deed runs at declaration scale

**The gap.** Laboratory `SESSION_HANDOFF.md` at `a07ff376`, "Ratified objective," verbatim:

> *"The second theorem must use the first returned theorem fiber; removing that fiber must remove
> every accepted second proof."*
>
> *"The actual conversation, complete Lean sources, kernel verdicts, alternatives, morphology
> changes, causal-information receipts, exact card receipts, physical testimony, and rest/remount
> are the deed. Counts, diagnostics, topology diagrams, local fixtures, and prior accepted proofs
> are supporting evidence only."*
>
> *"This real two-theorem production deed has **not** been run. The cleanup below does not imply
> its completion."*

**Laboratory progress: none.** Never run. Its 2026-08-03 attempt is recorded as interrupted.

**Archived C++ progress: ran, at toy scale.** `CONSTRUCTION_STATE.md:239-270`; artifacts at
`archive/cpp-engine/receipts/CONDITIONED_PRODUCTION_DEED.txt`, `archive/cpp-engine/receipts/CONDITIONED_PRODUCTION_RECEIPT.md`,
`archive/cpp-engine/standing/artifacts/HolonicsConditioned{One,Two,Foil}.lean`. Three declarations / 209 states → first theorem accepted
(382 source octets, 45,576 produced) → the acceptance admitted back as emanated material
(occurrences 3→4, states 209→298) → second theorem accepted, naming the first, splicing its name
out of the retained surface octet by octet (605 octets, 46,904 produced) → a foil with the same
proof term and the first declaration absent **refused by the kernel** → structural exclusion
returns 4→3 and 298→209, the route's fiber is deleted, the second target becomes unreachable, and
**nothing is emitted**. No counter decremented, no flag set.

What is **not** claimed, verbatim from `CONSTRUCTION_STATE.md:265-267`:

> *"both theorems are trace identities and the grade is the dependency mechanism. Three
> declarations, not the laboratory's 1,164. The statement forms and proof shapes are authored in
> the exterior codec; what the body supplies is whether to emit, which target, and the name it
> splices. Joining that to the existing renderers, which compose whole proofs from the exact
> organs, is the next deed."*

**What replaces it.** Re-run in Rust through `LeanMathematicsEcology` + `AgenticResearchSession` at
the laboratory's declaration scale, with **the actual conversation as the deed** rather than three
authored strings. Then join it to proof composition from the exact organs — so the statement form
and proof shape come from the body's own mathematics, not from an exterior codec.

That join is the difference between a machine that *selects* proofs and a machine that *produces*
them, and it is the sentence `CONSTRUCTION_STATE.md` itself names as the next deed.

**Grade.** Two kernel-accepted theorems where the second depends on the first's returned fiber;
structural exclusion of that fiber removes every accepted second proof; a foil carrying the same
proof term with the first absent is kernel-refused independently. At declaration scale, with the
conversation as the deed. The proof terms themselves are returned and inspected.

**Falsifier.** Three, all required:
1. Remove the first theorem's fiber; if any second proof is still accepted, the dependency is
   decorative.
2. Submit the foil; if the kernel accepts it, the dependency was never in the proof term.
3. Author the second statement form in the exterior codec; if the return is unchanged, the join to
   the exact organs did not happen and this is the archived toy deed at larger scale.

**Laboratory vs remains.** Honestly: the laboratory has the scale (1,164 declarations) and never
ran the deed. The archive ran the deed and never had the scale. **Neither has run what is
specified.** Remains: both at once, plus the composition join.

---

### Part three — the circuit becomes analyzable

This is a first-class line, not an appendix. The reason is `CLAUDE.md` §4: mathematics, physics,
and code are not domains this project alternates between — they are different **material** carried
by the same operation. The circuit is where the operation is visible as geometry, and it is the
only place where a learning claim can be falsified **topologically**, in exact integers, with no
tolerance anywhere.

`THE_GROWN_CIRCUIT.md`, ratified by Brandon 2026-08-07, is current direction and **none of it has
begun.**

---

#### The circuit becomes an integer chain complex with torsion, and the atlas gets a reader

**The gap, two halves that run together.**

*Homology.* There is no integer homology. `grep -rniE
"smith_normal|hermite_normal|invariant_factor|betti|torsion"` over `crates` and `soma` returns
**one doc comment**, `basin.rs:363`. What exists does not substitute:
`graph_cycle_rank` (graph_receiver.rs:1012) is `b₁` of the **1-skeleton only** and is `None` for
any non-graph complex; `euler_characteristic` cannot separate `b₁` from `b₂`; `exact_rational_rank`
(algebraic.rs:1081) is **private** and returns ℚ-ranks, which carry no torsion.

**Torsion is the object `CLAUDE.md` §3 identifies as *the* integral-Hodge obstruction** — *"the
failure of the integral version is the framework speaking: the obstruction is torsion, and torsion
is winding that cannot be un-deposited."* It is unreachable without Smith normal form. The
framework's own named obstruction is currently not computable by the framework.

*The reader.* The seven TSVs per run are written by the examples and **read by nothing**.
`crates/holonic-engine/examples/whole_receiver_holonic_complex.rs:74-87` writes `summary.tsv`,
`causal_layers.tsv`, `grain_cells.tsv`, `quotients.tsv`, `overlap_nerve.tsv`. The only
`File::open` on a TSV anywhere is `mms_reconnection_traversal.rs:1443`, reading a provenance
manifest. `THE_GROWN_CIRCUIT.md`: *"Costs almost nothing and makes step 1 checkable against figures
that already exist."*

**What replaces it.** `crates/holonic-engine/src/homology.rs`: `∂_k` extracted as ℤ-matrices from
`GradedCausalComplex` (the `ComparativeMultiplicity::difference() -> BigInt` ring is already there),
Smith normal form over ℤ, returning `(b_0…b_n, torsion: Vec<Vec<BigInt>>)`. Make
`exact_rational_rank` public rather than maintaining a third copy — there are already two, the
second at `receiver_ecology.rs:578`, also private. Plus germ, connection, and cycle queries over the
emitted tables.

**Grade.** Betti numbers **and torsion coefficients** over the machine's own transports and Chis,
in exact integers, cross-checked against `euler_characteristic` (`Σ(−1)^k b_k = χ`) and against
`graph_cycle_rank` on the graph species where both are defined.

**Falsifier — and this is the strongest single falsifier in the document.**
`THE_GROWN_CIRCUIT.md` states it: *"Excluding a deposit must change the homology: raise `b₁` where
a filling was, or split `b₀`. **If exclusion changes nothing topological, the dependency was
decorative** and the receipt overstates the code."*

This is the conditioned-production ablation restated homologically. It applies to **the two-theorem
deed's own dependency**: excluding the first theorem's fiber should be visible as a homological
change in the circuit, not only as a stopped emission. If the two-theorem exclusion is topologically
invisible, one of the two movements is overstating.

Second falsifier: build a complex with known torsion — the standard `ℤ/2` example is enough — and
confirm it is returned. An SNF that has only ever run on torsion-free input returns zero and proves
nothing about itself.

**Laboratory vs remains.** The laboratory built the entire substrate: `∂∂=0` as a constructor
invariant, the exact signed-ℤ coefficient ring, the incidence bridge from the grown circuit, the
Euler and cycle-rank analyses. It **never computed homology**. Remains: SNF, torsion, the public
rank, the reader.

**Returned 2026-08-07, in part — the invariants exist; the reader does not.**

`crates/holonic-engine/src/rebase_invariants.rs`. Smith normal form over ℤ on the boundary matrices
of `GradedCausalComplex`, returning per grade the **actual invariant factors** — not a count of them
— with Betti numbers and torsion. Every entry is a `BigInt`; there is no float and no tolerance
anywhere in the reduction, and each row and column operation is literally a rebase of one of the two
chain groups, which is why what it computes is what rebasing leaves alone.

The organ carries the one hazard its own history names. A convicted contaminant in this project was
*a solver's pivot order promoted into a reduction*, so the pivot rule is an explicit parameter over
three strategies, and `the_invariants_do_not_depend_on_the_pivot_rule` requires all three to return
byte-identical factors. That check has teeth: removing the divisibility repair makes the rules
genuinely disagree and the test fails. `the_invariants_do_not_depend_on_the_founding_order` does the
same for the cell ordering, which is the other receiver coordinate in reach.

`crates/holonic-engine/examples/grown_circuit_invariants.rs` is the driver, and it is the MorphoHDL
question made executable. A recursive cell grows under **three expansion schedules** — breadth,
largest-first, depth — producing three distinct charts, and the invariants are required to be
identical across all three. Three structures are grown so that no law here returns zero and calls
that evidence: a tree (no loops, no torsion), a rim (5 loops, so the loop reading is shown capable
of being nonzero), and a rim carrying a face attached to it **twice**, which returns `Z/2`. **19
declared controls, 0 failed.**

The measured artifact, which is the point of the whole line:

```text
tree     betti [1, 0]                 no winding
rim      betti [1, 5]                 five free loops
wound    betti [1, 4, 0]  +  Z/2      one free loop traded for winding that cannot be un-deposited
```

Torsion is invisible to every rational rank in the tree, including `algebraic.rs`'s
`exact_rational_rank`, which is why this had to be integral. Two defects were caught by the driver's
own controls while it was being built: a uniform aperture made `largest-first` coincide exactly with
`breadth`, so a schedule that could not change the layout was being reported as a third data point;
and the claim that the wound face *kills* the loop was too strong — it trades exactly one free loop
for `Z/2` and leaves the other four standing.

**Remains:** the reader over the emitted atlas tables, and the public exact rank. The schedule is a
parameter in the driver but the engine's own ten `pop_front` sites are still hardcoded — that is the
next movement, and it is now the load-bearing one.

---

#### The schedule becomes an object and its difference is deposited as a Chi

**The gap.** Every traversal in the engine is a **hardcoded breadth-first search**:
`simplicial.rs:540`, `simplicial.rs:1203` (`HingeWorldLaw::propagate`), `local_star.rs:370`
(`realize_vectors`), `local_star.rs:492`, `graph_receiver.rs:1858`. There is no seam at which a
different schedule could be supplied.

This matters more than it appears. `local_star.rs` already separates its residuals into
`face_residuals` (**schedule-independent** — `∂` on the 1-cochain) and `chord_residuals`
(**schedule-dependent by construction**). The engine's own types assert that some returns depend on
traversal order and some do not. **That assertion has never been tested, because there is only one
schedule.** By `CLAUDE.md` §8, a law that returns zero proves nothing about itself; a law that
cannot be exercised at all proves less.

And there is no Rust `ChiPair` — verified zero. `structure/chi_pair.hpp`, the `{composed, direct}`
pair that **is** the boundary of a 2-cell, was C++ and is archived. `ReceiverGraphDelta::between`
(graph_receiver.rs:978) compares two **sections**, not two **schedules** — a different object.

**What replaces it.** A `GrowthSchedule` enum carrying at minimum `BreadthFirst` and `LargestFirst`,
threaded through `realize_vectors`, `propagate`, and `receive_section`. Then a Rust `ChiPair`:
`{composed, direct}` over two schedules' returns on the same circuit, with the residual
**deposited** — not refined away, not tolerated, not averaged.

This is the constraint mechanism `CLAUDE.md` §0 already names: *"A constraint equation is a `Chi` —
two transports asserted equal — and the unknown is whatever the present chart does not determine."*
Two schedules over one circuit are two transports asserted equal. Where they disagree, the schedule
is the chart and the disagreement is the unknown.

**Grade.** `face_residuals` are **identical** across schedules; `chord_residuals` differ; the
difference is deposited as a Chi with its invariant retained. Both halves required — the invariance
alone could be vacuous, and the variance alone would not distinguish a bug from a gauge.

**Falsifier.** Run both schedules and confirm `face_residuals` agree **exactly**, as rationals, not
to tolerance. If they differ, `∂` is being computed schedule-dependently and something is wrong
with the boundary, not with the schedule. Conversely, if `chord_residuals` are **also** identical,
the second schedule was not actually threaded through and the seam is decorative.

**Laboratory vs remains.** The laboratory built the residual separation that makes this testable
and never varied the schedule. Remains: the enum, the threading, the Chi carrier, both deposits.

**Returned 2026-08-07 as DILATION AND LINEAGE — Brandon's naming, and it is the better one.**

*"That next step is something we've referred to as 'dilation' or 'lineage' in the past."* Calling it
*the schedule* was MorphoHDL's vocabulary imported over the project's own. Both words already had
apparatus here: `ReceiverGraphDeed::Dilate { upper_horizon }` changes how far a receiver sees and
returns `Retained` when the horizon did not move, and lineage is *"existing structure to be pivotted
off of"*, carried by `BranchLineage<T>` and `dialogue_lineage.rs`. So the gap was never "the
schedule is hardcoded" — it is that **ten traversals bypass a receiver vocabulary the engine already
owns**, each an undeclared horizon with no record of what it pivoted off. The sharpest instance is
inside the file that defines the vocabulary: `graph_receiver.rs:1858` counts components with a raw
unbounded walk.

`crates/holonic-engine/src/dilation.rs` gives a walk a declared `Horizon`, a `WalkOrder`, and a
`DilationLineage` recording what it reached, in what order, at what incidence distance, **what it
had to pivot off to close** (`closure_added`, retained rather than folded in), and what lies one
step beyond (`open_frontier`). `rebase_invariants_on` then reads the invariants of a section, so
*"did dilating move the invariants?"* is an exact integer question.

**The law, with the condition `CLAUDE.md` §12 omitted:**

```text
horizon >= covering  ->  GAUGE.       chart moves with the walk order; invariants do not
horizon <  covering  ->  RESTRICTION. the receiver genuinely sees less; invariants move
```

Measured over a grown circuit, focus at the root, covering horizon 7:

```text
horizon  0   1 cell    betti [1]        horizon  5  21 cells  betti [1, 4]
horizon  1   5 cells   betti [1, 0]     horizon  6  21 cells  betti [1, 4]
horizon  3  13 cells   betti [1, 0]     horizon  7+ 22 cells  betti [1, 5]   GAUGE
```

§12's unconditional form was untestable — without the restriction half there is nothing that could
have moved, and "invariant under dilation" would be a claim about a walk that always covered
everything. The measurement §12 rests on was taken on the residue-stratum atlas, which resolves at
no commit in either repository, so the gauge/non-gauge pair is **re-established here on live
material** rather than cited.

**The second frame, and it was free.** `graph_receiver.rs:1868-1874` already computes `b0` and `b1`
by the Euler route, and nothing had ever compared them to the integer homology. `euler_reading`
makes that comparison a control, and declines rather than returning a number where the shortcut
does not apply. Two independent implementations of the same two integers is what §0 means by an
invariant needing two frames.

**Three defects the controls caught, one of them in the organ.** The horizon was labelling cells by
*discovery depth*, so under a depth-first walk the walk order changed which cells fell inside the
horizon — the horizon was not a receiver property and dilation was not a gauge. Distance is now
always breadth-first, which is what makes it distance, and the order decides only the chart. Second:
`is_covering` was being compared against the whole complex, which makes the horizon answer for
connectivity too; it means the receiver covered *its own component*. Third, and for the third time
in one day: **material that cannot distinguish the coordinate under test proves nothing about it** —
the gauge test first used a path, where breadth and depth produce identical walks, and a deliberate
corruption of the Euler formula's `components` term passed unnoticed because every section reached
from one focus is connected. A disconnected fixture now exists for exactly that term.

**26 declared controls, 0 failed.** Remains from this movement as originally written: the Chi
carrier and the two deposits; and porting the ten bare traversals onto `Horizon`, which is now a
mechanical change rather than a design question.

---

#### A second receiver exhibits the gluing obstruction

**The gap.** `THE_GROWN_CIRCUIT.md` states it as *"**Only one receiver has ever been
constructed**"*, and **that wording is too strong — a grep refutes it.** Measured 2026-08-07: a
dozen distinct `ReceiverId`s occur across the examples. The accurate claim is narrower and still
damning: **no two receivers have ever held overlapping sections of one source with a map between
them**, so no gluing could fail. `whole_receiver_holonic_complex.rs:44` constructs exactly one
receiver, and the overlaps exercised in `analytic_field_transport.rs` are germ overlaps in the field
atlas, not two receivers' sections.

**The framework's central claim is receiver-relativity, and it has been tested with one receiver.**
That is the shape of `CLAUDE.md` §8's tautology rule at the level of architecture: a receipt that
could not have come out otherwise carries no evidence. With one receiver there is no transition map,
so no gluing can fail, so nothing about receiver-relativity is at risk in any current figure.

The machinery is present and unexercised: `HingeOpenSeam::ConflictingCandidates`
(simplicial.rs:846) already carries **both** arrival words when candidates cannot glue. It has never
had two receivers to disagree.

**What replaces it.** A second receiver with its own ray family, overlapping the first. Transition
maps on the overlap. Where sections fail to glue, **an exhibited obstruction** — returned and
inspected as an artifact, per §9, not summarized as a count. Then the grain-1 renderer: draw the 82
coarser quotient points and the 71 overlap cells, one of which has 14 members. `THE_GROWN_CIRCUIT`:
that is the hypergeometric content — *points which are lines which are loops, which are also
distributions of triangular vertices* — and **it has never been seen.** Only grain 0 has ever been
looked at.

**Grade.** Two receivers, a transition map on the overlap, and either an exact gluing or an
exhibited obstruction with both arrival words. The grain-1 figure is deposited and bound to its
standing.

**Falsifier.** Construct two receivers whose sections are **known** not to glue and confirm the
obstruction is returned rather than silently resolved. Then construct two that **must** glue — the
same ray family twice — and confirm the obstruction is empty. A gluing law that returns an
obstruction on the identity overlap is broken; one that returns none on a known conflict is not
looking.

**Laboratory vs remains.** The laboratory built the seam type, the overlap nerve, the quotient
promotion, and every object the law acts on. It **constructed one receiver**. Remains: the second
receiver, the transition maps, the obstruction return, the grain-1 render.

**Returned 2026-08-07 in its exact-integer half — `crates/holonic-engine/src/gluing.rs`.**

Two sections over one incidence, their overlap and their union, each checked to be a genuine
subcomplex before it is read, and the gluing obstruction computed exactly. The standard name is
**Mayer–Vietoris**, and the connecting map is the obstruction — not by analogy, it is the map saying
what the union carries that neither piece does.

The sentence the module exists for, measured on rims of length 6, 12, 25 and 64:

```text
left arc   betti_1 = 0     each arc is a tree and carries no loop
right arc  betti_1 = 0
union      betti_1 = 1     their union is the rim and carries one
overlap    betti_0 = 2     and the loop comes from the overlap being DISCONNECTED
obstruction              grade 1, rank 1
```

**The invariant lives in neither receiver; it exists only in their disagreement.** That is
`CLAUDE.md` §0's *"an invariant is only visible across two frames"* made computable, and it is the
first construction in this repository where receiver-relativity could have failed.

**Synthetic, and deliberately not a toy.** Brandon's correction: a known answer that comes from the
structure being small enough to eyeball is a regression. The known answers here come from
independent routes at parameterized scale — the classification of surfaces, where a one-vertex
genus-`g` model must return `betti = [1, 2g, 1]` and `chi = 2 − 2g`, swept `g = 1..8`; a `p`-fold
attachment which must deposit exactly `Z/p`, swept `p = 2..9`; and every cover of a rim at three
lengths across every split, whose union reading must reproduce the **direct** reading of the same
support. Nothing here is checked by inspection.

**The controls that make the obstruction mean something.** A cover that must glue — the identity
overlap — must return **no** obstruction; a law that obstructs there is broken. And a section that
is not closed under boundary is refused rather than read, because its invariants would describe a
structure that does not exist.

**One defect the controls caught, and it was the central definition.** The obstruction was first
written as the naive difference `b_n(A∪B) − (b_n(A) + b_n(B))`. That double-counts the overlap: two
arcs each carry one component, so it reports `−1` at grade zero — not an obstruction but the
ordinary fact that two overlapping connected pieces union to one — and it reported an obstruction
for the identity cover, which is precisely the case that must return nothing. The correct quantity
is the rank of the connecting map, which the exact sequence determines once solved downward from the
top. Reverting to the naive form kills the genus sweep, so the correction is load-bearing.

**Remains:** two receivers as *ray families over an image* rather than as supports — the tiger phase
atlas is the next material, on this same organ — plus the transition maps and the grain-1 render.

---

#### The layout answers its own curvature

**The gap.** `local_star.rs:2082` — `displacement = geometry_responses[hinge] · (Δcoordinate/2)`,
applied `−` to `edge.lower` and `+` to `edge.upper`. Exact rational, momentum-symmetric, and
`geometry_responses` is **supplied, never updated by what the layout returned.** The metric does not
respond to the curvature it produced.

`coordination_defect` (:1143) already computes the discrete curvature — the disclination charge
`6 − |link|` at each vertex, which `FORMULA §CVIII` notes is *"a strong structural resonance with
Regge's codimension-two hinges."* The curvature is measured and discarded.

**What replaces it.** `geometry_responses` updated by the traced deviation of the current face and
chord residuals — discrete Ricci flow on the exact rational metric, with the update law stated as a
law and its fixed points characterized.

**Grade.** The response update is exact-rational with no tolerance, its fixed points are
characterized, and the flow's effect on `coordination_defect` is measured across iterations.

**Falsifier.** Start from a configuration with known nonzero disclination charge and confirm the
flow **moves** it. Start from a flat configuration and confirm the flow leaves it fixed. A flow that
moves a flat configuration is introducing curvature rather than responding to it; one that cannot
move a charged configuration is not coupled.

**Laboratory vs remains.** The laboratory built the exact force law, the momentum symmetry, the
curvature measurement, and the two residual populations the update would consume. It **never closed
the loop**. Remains: the update law and its characterization.

---

### Part four — the wall

`CLAUDE.md` §11: *"The learning wall and the mathematical wall are the same wall, and naming this is
the point of this contract."* These two movements are that wall from its two sides. They are last
because the movements above are the instruments that make them statable, not because they are
optional — and `THE_GROWN_CIRCUIT.md` names the second as **the highest-leverage single item.**

---

#### The receptive star is factored and contact separates from cultivation

**The gap.** `research/records/2026-07-31_THE_PREFIX_GROWS_THE_DEED_RETAINS_ITS_WITNESSES_THE_LEXICAL_STAR_REMAINS_TOO_BROAD.md:195-231`.
Verbatim: *"The stronger claim that recruitment is already scale-independent is false"* — the
mechanism is *"broad union-based lexical recruitment followed by commitment-before-witness."*

Measured: `S(R) = ⋃_{f∈R} I(f)`; **8,748 candidate visits over 2,701 unique sections of 11,795**
(22.9%) for a question whose final witness contains **no** dialogue; **40 return visits over 24
unique passages committed to persistent morphology though none belongs to the minimal witness
family.** Across `0/127/254/508/1009` dialogue occurrences the deed, minimal witness, five leaders,
two waves, and thirteen visits stayed **invariant**.

State the wall exactly as `CLAUDE.md` §5 requires: **consequence isolation holds; scale-independent
recruitment does not.** Do not restate it as a missing comprehension, consequence, semantics,
relevance, or research-mode subsystem — §6 convicts that, repeatedly and by direct correction.

**What replaces it.** Both remedies are named in that record and **neither is implemented**;
`grep -rniE "mincover|min_cover|provisional"` over `soma/life/src` returns **zero**.

1. *Factor the receptive star*: `I(R) = ⋃_{K ∈ MinCover(R)} ⋂_{f∈K} I(f)`, with `MinCover`
   — verbatim — *"founded by the receiver's clause and entity morphology, not by an externally
   assigned inverse-frequency score."* The parenthetical is the whole constraint: an
   inverse-frequency weight would be a scalar score in the conditioning path, which `CLAUDE.md` §13
   obligation 4 bans outright.
2. *Separate provisional contact from continuing cultivation*: a section becomes continuing standing
   **only if** it belongs to a minimal closed witness family, supports a still-open front surviving
   rest, or returns an obstruction that changes morphology.

**Grade.** Candidate visits scale sublinearly in corpus size while the minimal witness family, the
leaders, the waves, and the visit count remain **invariant** — the same invariance already
demonstrated across `0/127/254/508/1009`. Committed persistent morphology contains no passage
outside the witness family.

**Falsifier.** Quadruple the corpus and measure. If candidate visits grow proportionally, the star
was not factored. If the minimal witness family changes, the factoring **broke consequence
isolation**, which currently holds — and that is a regression, not a trade. Both must be reported;
a receipt showing only the first has not graded the second.

**Laboratory vs remains.** The laboratory **measured the wall precisely** and named both remedies.
It implemented neither. Remains: both, and the scaled re-measurement.

---

#### The filler admission law returns a certified remainder

**The gap, from two sides that are one gap.**

*From the vision side.* Laboratory
`src/soma/RESEARCH/2026-07-28_THE_POINT_CARRIES_THE_LOOP_THE_COMPLETED_COMPLEX_RETURNS_AS_ONE_RECEIVER_CELL.md:376-381`,
verbatim:

> *"Given an open lower-grain horn and a population of inherited closed complexes, the engine does
> not yet have the derived receiver-relative admission relation which distinguishes a lawful new
> filler from a merely graph-completable boundary. The correction forbids substituting pixel
> continuation or an authored mask for that law."*

The objects it must act on are all built — verbatim from the same record, *"analytical internal
sections, exact boundaries and coboundaries, connection holonomy, source lineage, closed hulls,
grain quotients, and genuine plural overlap"* — in `crates/holonic-engine/src/holonic_complex.rs`
and `receiver_phase_atlas.rs`. The law itself: nothing.

*From the mathematical side.* `CLAUDE.md` §11: **an exactly computed positive form on a supported
realizer population, with a certified remainder and a reopening rule keyed to the receiver family.**

`THE_GROWN_CIRCUIT.md:134-136` states the identification directly: *"That is the horn-filling law,
and it is **the same gap as §11's one missing organ**, reached from the vision side."* **One law
closes both.**

**What exists, honestly.** The certified exact enclosure carrier was `exact/enclosure.hpp` — four
typed states over `archive/cpp-engine/src/include/holonics/exact/dyadic.hpp` and `archive/cpp-engine/src/include/holonics/exact/separation.hpp`, the enclosure defined as a **set
and never a value** — and it is **archived**. The trivial tree instance was Phase 7 movement one's
suffix-link DFS interval labelling, also archived. On the Rust side, `enclosure` appears in
`crates/holonic-engine/src/{coupled_informant, atmospheric_inverse, exact_value}.rs`,
`crates/relational-geometry/src/exact_analysis.rs`, and `soma/body/src/medium.rs` — **not verified
as the same four-state set-never-a-value carrier.** That verification is the first task of this
movement, and if it fails, the carrier is re-established in Rust before anything else here.

**The tree case is already solved and its triviality is the content.**
`research/records/2026-08-06_THE_TREE_CONDENSES_FOR_FREE_THE_REMAINDER_IS_THE_DEPARTURE_FROM_A_FOREST.md`
(graded `interpretation`): a depth-first order over a tree replaces every state's descendant
population with a two-word interval, exactly, with an **empty** remainder — free, because subtree
equals interval and the interval is its own reopening rule. **So the difficulty lives entirely in
the departure from tree-ness**, and the standard object for it is spanning-tree interval labelling,
where every non-tree edge forces additional intervals and **that forced population is the certified
remainder**, zero exactly when the incidence is a forest.

And that object **already exists in this repository for projective transport** —
`HingeWorldLaw::propagate` and `HingeCycleReturn` (simplicial.rs:912), described above. The
generalization is from projective transport words to a positive form on a realizer population.

**What replaces it.** The admission relation, derived and receiver-relative, returning a certified
exact remainder and a reopening rule keyed to the receiver family. Not pixel continuation. Not an
authored mask. Not a floating tolerance — `CLAUDE.md` §11 is explicit that *floating tolerance may
not become standing.*

**Grade.** A lawful filler is admitted and a merely graph-completable boundary is **refused**, by
the derived relation, with the remainder returned exactly and the reopening rule stated. The
remainder is **zero exactly when the incidence is a forest** — that is the calibration that proves
the general law degenerates correctly to the case already solved.

**Falsifier.** Four, all required:
1. Present a boundary that is graph-completable but not lawfully fillable; if it is admitted, the
   relation is graph completion wearing another name — the exact substitution the correction
   forbids.
2. Present a forest incidence; if the remainder is nonzero, the law does not degenerate to the
   solved case.
3. Change only the receiver family; if the admission decision does not change, the relation is not
   receiver-relative and the framework's central claim is not in it.
4. Search for a floating value anywhere in the remainder path; one is a failure.

**Laboratory vs remains.** The laboratory built every object the law acts on and **named the law as
missing** rather than substituting for it — that restraint is itself a result and it is why this is
statable now. The archive built the enclosure carrier and the tree case. Remains: the general law,
the departure from tree-ness, and the Rust enclosure verification that precedes both.

---

## Discipline that governs every movement

- **Grade the implementation, not the receipt** (`CLAUDE.md` §8). A receipt is a claim about code.
  Read the owner before carrying any capability claim forward, including one already marked
  `established-bounded`. Thirty-five phases were admitted on a contaminated foundation because this
  was skipped.
- **A cost law is a law.** Grade complexity against the source owner, measure across a changed
  aperture, state the bound as a falsifier. `ReceiverGraphQueryWork` already does this and is the
  pattern to copy.
- **A law that returns zero proves nothing about itself.** Where declared material cannot exercise a
  law, add a declared control that does, and make the grade require a non-zero return.
- **An organ used past its declared aperture is a defect even when it appears to return.** No audit
  catches a capacity mismatch — it is not a banned token. `analyze_receiver_topology` admits **at
  most 20 vertices** (`receiver_topology.rs:306`). Read the aperture before borrowing the carrier.
- **A falsification is a first-class return.** A deed proving its own receiver family cannot see
  what it was built to see has returned real evidence and passes its grade.
- **Return the artifact** (`CLAUDE.md` §9). Counts, morphology totals, atlases, and diagnostics are
  supporting receipts and never substitutes.
- **Depth on a question, not breadth in the cabinet.** Before building, name the receiver question
  that several movements in sequence are answering. For this document it is one question and it is
  Brandon's: **can the machine learn to produce mathematical proofs, with the learning as the
  intermediary mechanism?**
- **Halt and say so.** If a run is not doing what was claimed, stop it and report the actual state
  before proposing a repair.
- Pushing to `origin` remains Brandon's call.
