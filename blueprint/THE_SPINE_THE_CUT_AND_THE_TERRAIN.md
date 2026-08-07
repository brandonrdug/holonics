# THE SPINE, THE CUT, AND THE TERRAIN

> **SUPERSEDED 2026-08-07 — ARCHIVED-BODY PROVENANCE.** This file describes the C++/CUDA engine,
> which was archived whole at `archive/cpp-engine/` when the body moved to Rust. Its mechanisms,
> measurements and open items are **historical record**, not the present position and not a
> schedule. The active spine is `CLAUDE.md` §0; the active roadmap is `blueprint/THE_ROADMAP.md`.
> What it does not settle: it is a direct measurement of the C++ tree and remains the most complete
> map of what that tree contained. Nothing here is deleted — a reader following a citation into this
> file should find what it said, and this banner telling them it no longer governs.


**Measured 2026-08-06 over the actual include graph. Every number below is computed, not cited.**

## 0. THE GOVERNING MEASUREMENT

I recomputed reach with two seed sets: the **live deeds** (`spine_deed`, `resident_mount_deed`, `text_mount_deed`, `conditioned_production_deed`, `constraint_rebase_deed`, `one_standing_deed`, `enclosure_deed`, plus `cuda/executor/{spine_executor,text_material_mount,resident_ecology_executor}.cu`) and the **frozen R1–R35 line**.

| | headers | live-deed closure | frozen-R closure |
|---|---|---|---|
| `exact/` | 23 | **21** | 23 |
| `structure/` | 31 | **16** | 28 |
| `body/` | 12 | **11** | 11 |
| `current/` | 14 | **3** | 14 |
| `receiver/` | 25 | **0** | 23 |
| `organ/` | 180 | **12** | 180 |
| `codec/` | 97 | **4** | 95 |
| `event/` | 154 | **3** | 152 |
| `apparatus/` | 116 | **7** | 116 |
| **total** | **652** | **77** | **589** |

Spine-mechanism reach, from `build-final/receipts/REACH_AUDIT.txt`:

```
swing.hpp             9/652     chi_pair.hpp        13/652
live_machine.hpp      8/652     transition_inv.hpp  10/652
continuing_body.hpp 169/652     information_receipt  1/652
small_rational.hpp  256/652
```

**Three facts govern everything that follows.**

**(a) The live engine is already 77 headers.** Brandon is right that it grew beyond what is pure — but the growth is not in the live engine. It is in the 575-header frozen R-line hanging off it. The pure engine is already small; it is buried, not bloated.

**(b) The exact mathematics is the most-conducted-through thing in the repository** (`small_rational` 256/652) and **the one move and the mandatory receipt conduct through almost nothing** (9 and 1). This is exactly Brandon's correction stated as a measurement: the terrain is dense and sound; there is no current. Annihilating mathematics would make this worse, not better.

**(c) `receiver/` is dead. Zero of 25 headers are in the live closure.** `projective_swing_law.hpp`, `condensation_law.hpp`, `sameness_law.hpp`, `projection_chart.hpp`, `connection_law.hpp` — the entire chart/projection/condensation layer the record's §6 requires — is reachable only from frozen deeds. This is the single largest unreached owner and nobody has named it before.

**(d) There are THREE standings, not two.** This is the corrected diagnosis:

| standing | what it is | reach |
|---|---|---|
| `body/continuing_body.hpp` | head + linear continuation + 4 `rest_region{admitted_tally, current}` | 169 |
| `body/live_machine.hpp` | Swing + persistent `standing_surface` + lineages | 8 |
| `body/returned_standing.hpp` | returned organs by identity, reachable, composable, ablatable by `caused_by` cascade | live, new |

`returned_standing.hpp:24-34` is correct and is the one that must win. `standing_surface` inside `live_machine` is a second, redundant standing. `continuing_body`'s four tallies are the deposit that nothing reads.

---

# PART 1 — THE SKELETON

Seven mechanisms. Nothing else is spine. Everything else is either terrain a current pivots off, or a cut.

### S1. `exact` — the bit-pure carrier, including the certified enclosure

Limb words, normalized rationals, finite fields, exact polynomials; overflow is a typed refusal or a lineaged promotion; no float may decide a branch, index, coefficient, or any committed bit.
— `canon/08_CORE_MATHEMATICAL_INSTRUMENTS.md:78-94`; `blueprint/CPP_GPU_FOUNDATION.md:62-80`

**Status: BUILT, and the record is out of date.** `CLAUDE.md` §11 says the certified exact enclosure carrier "does not yet exist as a built instrument." It exists: `include/holonics/exact/enclosure.hpp:9-33` defines the enclosure as a **set, never a value** — closed dyadic interval, four typed states `{admitted, aperture_refused, bracket_absent, order_refused}` — over `exact/dyadic.hpp` (205 lines) and `exact/separation.hpp` (109). The first brick is laid. Amend §11.

### S2. `structure` — the minimum carrier `K=(O,I,D,T)`, Chi, and OPEN

`chi_pair` as the **ordered transport pair**, projections available only after a chart exists; OPEN as a first-class disposition carrying the complete attempted routes; the eight transition invariants.
— `blueprint/EROS_EMBODIMENT_ROADMAP.md:102-138`

**Status: BUILT AND CORRECT** (`structure/chi_pair.hpp`, `structure/disposition.hpp`, `structure/local_transport.hpp`, `structure/transition_invariants.hpp:18-27`). **One defect, in the live spine, reported below as CUT 10.**

### S3. `returned_standing` — THE ONE STANDING

A mathematical return deposits its exact words under an identity; a later current **reaches** them; excluding the deposit removes the reach **by removing structure**, cascading along `caused_by`.
— `THE_FOUNDATION_REMAINDER.md:38-53`; `body/returned_standing.hpp:24-34`

This replaces `continuing_body`'s `rest_region.admitted_tally` and it replaces `live_machine`'s `standing_surface`. **There is one standing and it is this one.** `continuing_body` keeps head identity, the linear continuation, lineage — and loses the four tallies.

### S4. The one move — `swing_law` against S3

MEETING · FLYWHEEL (the current's own state, not a store) · TEST by cross-sign · RIDE carries cheap / FOUND deposits one integer winding quantum and pays curvature. `rebase_exposed` may only RIDE or stand OPEN.
— `EROS_EMBODIMENT_ROADMAP.md:181-202`; `body/swing.hpp:65-125`

`swing.hpp` is 139 lines and it is right. Its defect is not its content; it is that its only consumer is `live_machine`, which owns the wrong standing. **The Swing must cross against `returned_standing`, and `standing_surface` must go with `live_machine`'s duplicate role.**

RIDE's cheapness is already measured, correctly, in `body/standing_residency.hpp:16-23` (`rides`, `avoided_octets`, shape short-circuit at `:48-56`). That is the first place in the tree where RIDE is *a measured absence of work* rather than an enum branch. Wire it to S4.

### S5. The one event — open / resume / commit-once, one linear capability

`open` derives only a pending continuation and outbound occurrence; only a typed returned occurrence crossing the expected port resumes; commit once, while the head is `v`; refusal returns both bodies intact.
— `canon/01_CAUSAL_CALCULUS.md:19-53`; `blueprint/PURE_HOLONIC_ENGINE.md:34-59`

**Status: BUILT** (`event/lifecycle_law.hpp:27-52`, `event/deed.hpp:14-30`, `body/continuation.hpp`). The capability is genuinely moved, not copied.

### S6. The membrane — variable-extent material in, real exterior process out

`codec/text_material.hpp` (exact-surface identity, `pair_population` gate that must stay zero, `open_causal_fibers` implementing *corpus adjacency is not ancestry*) and `codec/text_rest.hpp:20-30` (the **only variable-extent rest in the tree**, `[header][surface][occurrences][caused]` with a computed `total()`). Out: `apparatus/host/lean_checker_process.cpp:115,124` really `fork`/`execl`s `/usr/bin/lake env lean`.
— `PURE_HOLONIC_ENGINE.md:66-85`, `:168`; `THE_FOUNDATION_REMAINDER.md:55-64`

**Status: BUILT AND CORRECT.** `text_rest.hpp` is the answer to remainder #2, already written. The 34 fixed-size `event/*_rest.hpp` records must be refounded against it, not the reverse.

### S7. The receipt — mandatory, on every deed

`I_{ρ,E}` with three continuation fibers, every inclusion-minimal witness family, typed morphology change, logical work, complete obstruction. **An ecology that returns a count instead of a receipt is not admitted.**
— `canon/02_INFORMATION_PHYSICS.md:13-27`; `EROS_EMBODIMENT_ROADMAP.md:262-278`, `:327-329`

**Status: BUILT AND CORRECT AND UNUSED.** `current/information_receipt.hpp:57-68` is the right structure; `receipt_law::try_admit_minimal` at `:76-102` genuinely computes the inclusion-minimal set; `necessary()` at `:106-120` returns necessary/possible/irrelevant with no scalar. Reach: **1/652 — itself.** One consumer exists (`apparatus/host/one_standing_report.hpp`). Make it mandatory: every deed constructs one or does not commit.

### What grows rather than being authored

Four mechanisms, all built, and together they are the emergence substrate the record demands ("no organ is authored", `THE_TRANSACTIONAL_SEAM.md:119-121`):

- `organ/suffix_arena.hpp` + `suffix_extend.hpp` — exact suffix automaton, canonical order, clone handling, **instrumented `lookup_steps`** (`suffix_extend.hpp:14-40`). The only path in the repository to corpus scale.
- `organ/incidence_arena.hpp` + `source_incidence.hpp` — `O(states + occurrences)` source attribution that never allocates `states × sources`.
- `organ/training_ecology.hpp` — `minimum_recurrence >= 2`, `template_budget` as a physical refusal, and `ablate()` at `:196-208` that genuinely **removes the array element and bumps the generation**. Structural, not a counter.
- `body/returned_standing.hpp` — deposits founded by returns, excluded by cascade.

Growth is these four. There is no organ atlas, no scheduler, no dispatch table, and none is to be written.

---

# PART 2 — THE ANNIHILATION LIST

Ordered leaves-first so it executes. Every entry names its test. **Git history is the recovery surface; everything listed is tracked and recoverable by `git show`.**

Nothing here is convicted for being hand-written or for being unreached.

---

### CUT 1 — The R12 island. Test (1): the name is the objective and the code is a struct copy.

`organ/generative_math_law.hpp:51-61` builds `receipt.fibers[slot]` by copying `rule.identity, rule.lineage, rule.formation, rule.dependency_count` verbatim under an incremented identity; `:62` then sets `obstruction = receiver_underdetermined` **unconditionally**; `:72` selects by `fiber.dependency_count <= goal.maximum_dependencies` — a scalar threshold, banned by name (`CLAUDE.md` §13 obligation 4); `:45` requires `!goal.reverse_orientation`, making the answer's orientation a precondition of asking.

The returned artifact is a string literal: `codec/formal_math_renderer.hpp:16-32`. `selected.rule`, `.lineage`, `.formation` never reach the renderer — flip which fiber wins and not one emitted byte changes. `codec/conversational_math_renderer.hpp:21-23` emits, as a literal, *"The theorem statement and proof object are new; no mounted theorem source was quoted as the answer."* That sentence is itself quoted.

Delete: `organ/generative_math_{law,schema,receipt}.hpp`, `event/{generative_math_return,resident_generative_math_current}.hpp`, `apparatus/generative_math_{receipt,executor,resident}.hpp`, `receiver/generative_math_question.hpp`, `codec/{formal_math_renderer,conversational_math_renderer}.hpp`, `cuda/executor/r12_generative_math_{executor,kernels}.cu`, `apparatus/host/r12_generative_mathematical_current_deed.cpp`, `tests/model/r12_*`, `tests/conformance/r12_generative_math_host_conformance.cpp`, `tests/compile_contracts/forbidden_generative_math_current_copy.cpp`, `cmake/R12GenerativeMathematicalCurrent.cmake`, `receipts/R12_*`.

**Blast radius:** R12 dies. `codec/formal_math_renderer.hpp` is also included by `tests/conformance/r13_lean_checker_host_conformance.cpp:3` — R13 is regraded in the same motion (see CUT 2). `apparatus/host/lean_checker_process.cpp` is untouched and keeps working.

### CUT 2 — The R14/R15/R16 island and the three-limb string loop. Test (1) and test (3).

`organ/theorem_production_law.hpp:32-40` is `generative_math` function-for-function, and worse: `:34` does raw `goal.identity.value() + slot + 1U` with **no overflow check**, having dropped the `exact_add` guard its source had.

The loop is closed by three files holding the same literal:
- emitter `codec/theorem_production_renderer.hpp:18` — `theorem generated_trace_rebase_transports_composition`, proof term `exact (trace_rebase_iff A e theta s u).2 (Trace.trans hst htu)` at `:29-33`, gate at `:9-11` reads `statement.value() != 0` and never reads the value again;
- prober `codec/formal_checker_face.hpp:48-52` — `#print Soma.Holonics.generated_trace_rebase_transports_composition`;
- acceptor `event/checker_normalization_law.hpp:64-89` — three hardcoded `constexpr char declaration[]` names; a fourth theorem falls to the `else` and is reported rejected.

Test (3): a dispatch table nothing can re-route, over three strings the same tree emits.

Six receipt fields certifying the entire anti-cheating contract (`organ/theorem_production_receipt.hpp:12,:19-23,:35` — `global_candidate_scans`, `mounted_answer_matches`, `lookup_entries`, `quoted_source_bytes`, `reference_calls`, `retained_development_source_bytes`) have **zero assignments anywhere in the tree** and are asserted `== 0`. `blueprint/R14_FROZEN_THEOREM_REQUEST.md:38` is certified by reading zero-initialized memory.

Delete: `organ/theorem_production_{law,schema,receipt}.hpp`; `codec/theorem_production_renderer.hpp`; **the function `render_formal_checker_face` in `codec/formal_checker_face.hpp:27-61` (keep the `formal_checker_face` struct at `:18-25` — the live `lean_checker_process` uses it as a byte buffer)**; `event/{checker_normalization_law, resident_theorem_production, theorem_production_return, theorem_production_rest, dependent_theorem_production_law, resident_dependent_theorem_production, terminal_theorem_rest, absent_fiber_control, return_conditioning_return, geometry_inquiry_rest}.hpp`; `receiver/theorem_production_question.hpp`; `apparatus/{theorem_production_executor,theorem_production_resident,terminal_theorem_resident,theorem_rest_store_adapter}.hpp`; `cuda/executor/r14_*`; `apparatus/host/{r14,r15,r16}_*.cpp`; `tests/model/r14_* r15_* r16_*`; `cmake/R14* R15* R16*`; `blueprint/R14_FROZEN_THEOREM_REQUEST.md`, `R15_FROZEN_DEED_B_SETUP.md`; `receipts/R14_* R15_* R16_*`.

**KEEP: `formal/elementary-holonics/ElementaryHolonics/Algorithm/Rebase.lean` entire.** `trace_rebase_iff` at `:23` is real, human-authored, and is the actual mathematics. The "generated" theorem is one corollary of it, and `Rebase.lean:53` already contained `exact (trace_rebase_iff A e θ s₀ sₙ).2 htrace` in ancestor commit `be93ed3`, before `348d838` landed the frozen request and its answer together.

**Blast radius:** R14, R15, R16 die as *generation* claims. R35's discovery family has zero dependence on any of it (`grep theorem_production` over `apparatus/host/r35_*`, `cuda/executor/r35_*`, `organ/trace_rebase_*` returns empty). The discovered coefficients survive.

### CUT 3 — R17's inquiry law and the geometry theory renderers. Test (1).

`organ/geometry_inquiry_law.hpp:43-44` sets `expected_answer_absent = true` and `mode_field_absent = true`; `:60-72` hardcodes all four conjecture verdicts and obstruction codes; `:73-74` assigns `closed_fiber_count = 2; obstructed_fiber_count = 2` as literals. `derive_fractional_difference` at `:11-21` writes `{1,1,1,1,-1,-1,-1,-1}` and then verifies the constants it wrote.

Every verdict-bearing field is a compile-time constant for every admissible input, because `form_geometry_probe` (`geometry_probe_law.hpp:36-63`) derives every point from `slot` alone and `foundation.probe_seed` reaches only the decorative `result.identity` at `:36`. `probe_geometry_inquiry<<<1,32>>>` (`cuda/executor/r17_geometry_inquiry_kernels.cu:70`) burns the card recomputing a folded constant — test (2) as well.

`codec/geometry_theory_renderer.hpp:8-108` emits ~2KB of complete Lean (`generated_mobius_sub`, `generated_swing_affine_commRing`, `generated_crossRatio_mobius`, `generated_coordinate_counterexample`) as literals through a pure byte copy (`geometry_theory_face.hpp:39-47`), and `:129-146` narrates a symbolic expansion that does not exist.

Delete: `organ/geometry_inquiry_{law,receipt,schema}.hpp`, `codec/geometry_theory_{renderer,face}.hpp`, `event/{resident_geometry_inquiry,resident_geometry_inquiry_return,geometry_inquiry_return}.hpp`, `apparatus/geometry_inquiry_*`, `cuda/executor/r17_*`, `apparatus/host/{r17_*,geometry_inquiry_store_adapter.cpp}`, `tests/model/r17_*`, `cmake/R17*`, `blueprint/R17_*`, `receipts/R17_*`.

**KEEP as terrain: `organ/geometry_probe_law.hpp:17-30` (`swing_pair`, the real cross-ratio) and `:64-113` (Möbius image + exact projective equality by cross-multiplication — the identity `transformed = original * det²` is true and is actually checked). KEEP `organ/geometry_inquiry_exact.hpp`.** Delete `form_geometry_probe`'s slot-derived generator (`:36-63`) and the `probe_count == geometry_inquiry_probe_capacity` gate (`:14`) — those are the freeze.

**Blast radius:** R17 dies. R18 consumes R17's rest file (`cmake/R18PhaseCrystalHypergeometry.cmake:76` → `apparatus/host/r18_phase_crystal_deed.cpp:13`) and must promote its already-existing synthetic `r18_host_geometry_rest()` (`tests/model/r18_cases.cpp:23-43`) — which is itself a hand-written constant, so nothing real changes.

### CUT 4 — The remaining constant emitters. Test (1) and test (2).

Measured with a literal-stripping classifier over all 65 `codec/*renderer*.hpp`: **44 emit computed data, 19 emit only literals, 2 are pure dispatchers.** After cuts 1–3, the surviving constant emitters are:

`codec/{phase_crystal_renderer, characteristic_renderer, regular_singular_renderer}.hpp` (theorem emitters: emits==literals exactly, 33/33, 51/51, 49/49) and the nine `*_explanation_renderer.hpp` files (`algebraic_variation, arithmetic_spectral, blind, causal_linear, cm, expression_geometry, hodge_realization, intrinsic_hypergeometry, toric`).

The output is provably independent of the input. `characteristic_renderer.hpp:116-147` is twelve `append` calls, twelve literals, zero data.

**Do NOT touch the 44 transforming renderers** (`blind_moment_renderer.hpp:74-91` emits `surface.determinant`, `polynomial[0..2]`, `discriminant`; `trace_rebase_renderer.hpp:82` emits `deck_eigenvalue`). Those are real chart transport and are the only working exemplar of *a template with holes that computed values fill* — the shape every future generation must take. **Do NOT touch the two dispatchers** (`arithmetic_spectral_renderer.hpp`, `hodge_realization_renderer.hpp` — zero emits, one delegation each into files that do transform).

### CUT 5 — `event/cultivated_route.hpp`. Test (1), whole file.

`:59` is `returned.product = left * right;` under a doc comment at `:44-49` reading *"the product is computed by the founded law"* and `:11-14` claiming the body was given passages of shape `(a,b) → a*b`. The founded law is the C++ `*` operator. `product_route()` (`:22-32`) is **nullary and `constexpr`** — it takes no operands and returns one global constant fiber, so the "two distinct developmental passages" in `tests/model/ecology_cases.cpp:319-323` are the same constant twice. No operand pair is ever supplied to the ecology by any path in the repository.

This carries an `established-bounded` grade in `CLAUDE.md` §5 ("the trained body returned 72… a source-detached remount returned 63 for novel 7*9"). **9\*8 is 72 and 7\*9 is 63 because C++ says so.** §5 must be amended in the same commit.

Whole file, 65 lines, zero exact mathematics. `organ/training_ecology.hpp` survives untouched.

### CUT 6 — The tally deposit. Test (2), and test (3) on the grades.

**66 `admitted_tally_ += accepted ? N : M` sites** across 23 resident owners, weights hand-picked and generated by no law (`3/8/64/24/37/32/23/20/16/14/10/9/80/…`). I grepped every conditional in `include/`, `apparatus/`, `cuda/`: **zero conduct branches on any tally.** The only branch is the overflow guard at `body/continuing_body.hpp:94`. The deed runs, the card burns, the deposit changes no later conduct — `while True: pass` with a counter.

`git show 2b562c8 -- include/holonics/event/resident_characteristic_return.hpp` shows the increment expressions **byte-identical across the diff**: `mathematical_morphology_ += accepted ? 8U : 1U` became `mathematical_admitted_tally_ += accepted ? 8U : 1U`. The Phase 0 excision renamed the field and preserved the object.

`event/checker_return_schema.hpp:71-78` — `struct checker_morphology_return`: four counters plus a commit receipt, and `returned_difference_applied` at `:77`. Read against `event/resident_characteristic_return.hpp:16-45`: lineage is validated at `:16-20`, then commit fires **unconditionally** with `delta = accepted ? 12U : 4U`. **A rejected checker return advances the head, consumes the continuation, and sets `returned_difference_applied = true` exactly as an accepted one does.** The field named *the returned difference was applied* is insensitive to the returned difference. That is test (1) in the live spine — `checker_return_schema.hpp` is one of the 3 live `event/` headers.

Test (3): the tallies are cumulative totals welded across R13→R35 as literal grades — `tests/model/r18_verify.cpp:103-104` (55→62, 39→42), `:108` (181→192); `r21_verify.cpp:176-178`; `r26_verify.cpp:149-150`; `r29_verify.cpp:131-132`; `r30_verify.cpp:202-203`; `apparatus/host/r32_heldout_holonomy_deed.cpp:21-22` (1103/370/171); `apparatus/host/r33_characteristic_application_deed.cpp:35-37` (1199/418/195). **27 files hardcode tally values as grades.** R33 asserts 1199 because every prior deed's magic constant summed to 1199. Inserting a deed, reordering, or changing one increment breaks downstream assertions in every later phase. That is a ratchet that structurally penalizes recombination.

**Cut precisely:** delete the four `uint64_t` fields from `checker_morphology_return` and rename the type off the convicted word; delete all 66 increment sites; delete `rest_region.admitted_tally` from `body/rest_record.hpp` and the `admitted_tally_delta` parameter from `continuing_body::commit`; delete the 27 hardcoded cumulative grade constants.

**KEEP `body::body_change_receipt commit` and the real head advance at `continuing_body.hpp:96-108`** — `capability.consume()`, `head_ = head_mint_.mint()`, fresh `linear_continuation`, `++lineage_`, four typed refusal states. That is spine substrate and deleting it would be the error. **KEEP `checker_raw_return` (`:39-56`) and `checker_typed_return` (`:58-69`)** — real process bytes normalized into typed classification.

Replace `returned_difference_applied` with a predicate that is a function of the return, and regrade the 27 files on the structural delta plus the artifact they already check (`r18_verify.cpp:84-91` asserting real `theorem generated_*` strings is the sound part of those grades and should become the whole of them).

Also cut in the same motion: `event/absent_fiber_control.hpp:48-52`, which grades an *ablation* by tally equality — the convicted "constant subtraction called exact ablation" in a new costume; and `:44-47`, which assigns `projected.integrity = f(projected)` then checks `projected.integrity == f(projected)`.

### CUT 7 — The empty contracts. Test (1).

`organ/constitutive_contract.hpp:7-11` — two type aliases, `final`, zero members, zero callables, zero implementors. It names the record's central mounting requirement (`PURE_HOLONIC_ENGINE.md:100-107`: typed pullback yielding **zero, one, or plural** organs, obstruction on zero-match and unresolved plurality) and types none of it. `constitutive_contract<outbound_port, outbound_port>` compiles. Both parameters are already constrained by `structure::typed_port` (`structure/port.hpp:17-22`) at every use site, so it adds exactly zero constraint.

Cut with it: `codec/environment_contract.hpp:19-23` (`face_contract`) — the byte-identical shape one owner over, whose sole consumer `codec/source_environment.hpp:49-50` instantiates it with the same port twice and asserts a property that belongs to the port.

**Blast radius, corrected — "none" was wrong:** three edits in `tests/compile_contracts/valid_host.cpp` (lines 12, 26, 40), which is the live target `r0_host_contract` (`CMakeLists.txt:43`). The R0 graded-source SHA (`receipts/R0_ARCHITECTURE_RECEIPT.md:50`) and manifest hashes change. **R0 must be re-issued, not left silently green.** Coverage lost: zero — the deleted `static_assert` asserts a type alias equals the type it aliases.

### CUT 8 — The nine schema-serial gates. Test (3): an aperture no return can widen.

`organ/hodge_realization_law.hpp:10-18` demands `schema == 280'028 && factor_count == 2 && rank == 6 && question_count == 3 && base_t == 2 && base_u == 2 && off_diagonal_u == 3 && coefficient_min == -1 && coefficient_max == 1 && denominator_aperture == 2` and every `factor.term_count == 5`. `intrinsic_phase_incidence_law.hpp:9-12` puts the receiver's own weights in the validator as literals. Siblings: `arithmetic_spectral_law.hpp:12-15`, `expression_geometry_law.hpp:10-13`, `variation_polynomial_law.hpp:12-13`, `cm_incidence_law.hpp:19-23`, `blind_reconstruction_law.hpp:15-19`, `toric_fan_law.hpp` (230'023), `causal_linear_law.hpp`.

The organ refuses to conduct on any input except the one card compiled into it. There is one input and the "law" is its acceptance test.

**Delete the literal-lock validator bodies, not the files.** The mathematics below each gate is terrain (CUT is surgical: replace each `valid_*_foundation` with structural well-formedness checks — nonzero, in-range, internally consistent — and let contact return zero/one/plural with an explicit obstruction, per `PURE_HOLONIC_ENGINE.md:100-107`).

### CUT 9 — The answer-key closes. Test (1) at the grade line.

`theory_formed` computed as a recount of a hand-typed table:
- `organ/phase_crystal_law.hpp:88-91` requires `prime_cases == 7 && composite_cases == 5 && shared_factor_cases == 2 && control_cases == 9` — those are literally the row counts of the 16-row table at `phase_crystal_cases.hpp:17-33`.
- `characteristic_law.hpp:39-41` (`repeated_mode_cases == 2 && simple_mode_cases == 14` — the same 16 rows).
- `composition_receiver_law.hpp:82-84`; `occurrence_incidence_law.hpp:71` (`selected_mask == 31`); `regular_singular_law.hpp:46`; `causal_linear_cm_law.hpp:54-56`; `causal_linear_toric_law.hpp:22`; `intrinsic_hypergeometry_law.hpp:78` (`source_mask == 0x0fff`); `hodge_cycle_locus_law.hpp:38`.
- `organ/hodge_cycle_law.hpp:33-34` sets `alternatives_retained` true exactly when `realizer_count == 16`, and 16 **is** `hodge_realizer_capacity` (`hodge_realization_schema.hpp:17`) — "alternatives retained" means "the array saturated."
- `organ/algebraic_variation_law.hpp:46` `auto& selected = out.selection.candidates[3];` and `:49` `out.selection.no_score = true;` — the denial and the mechanism it denies on adjacent lines.
- `organ/trace_fiber_close_law.hpp:46` `const auto selected = ... (target == 0 ? 3 : 7);` with an answer key at `:9-25`.
- `organ/self_holonomy_organ_law.hpp:88-90` requires the held-out product to equal `[2,1,1,1]` — the product of the edges the card supplied. It verifies that C++ multiplied the numbers it was given.
- `organ/heldout_characteristic_law.hpp:21` `predicted_fixed_rank = predicted_trace == 2 ? 1 : 0` — a two-branch lookup on a literal, called a prediction.
- `organ/arithmetic_spectral_law.hpp:107-112` checks `== 12`, `== 252`, `== 28`, `== 4'396` instead of the computed `2(q+1)`; `:115` `reduced(3 - 16, 13) == 0` is a hardcoded arithmetic fact where a derivation belongs. The **theorem** (#E + #E^twist = 2(q+1)) is real; only the fixture-frozen check is cut.
- `organ/trace_rebase_control_law.hpp:129-142` — `exact = exact && height <= 64` (`trace_rebase_schema.hpp:24`): a boundary sentence doing the work of a grade (`CLAUDE.md` §7).

**Delete the grade clauses. Keep every census, sweep, hull, Jacobian, and residual computation they sit on top of** — that work is genuine and is terrain.

### CUT 10 — The literal-`true` transition invariants, IN THE LIVE SPINE. Test (1). *This is mine and it has not been reported before.*

`body/live_machine.hpp:150-166` admits **seven of the eight** transition invariants with hardcoded `true`; only `bounded_emission` is conditional. `body/spine_execute.hpp:68-85` admits **six of eight** with hardcoded `true`.

This is the same shape as R14's five lawfulness flags and R17's four verdicts: the eight invariants the record makes the atomic-successor contract (`EROS_EMBODIMENT_ROADMAP.md:130-138`) are certified by assignment. `grade.complete()` (`structure/transition_invariants.hpp:44-47`) requires all eight bits, and six or seven of them cannot be false.

The live Swing crossing is graded by a constant. **Fix, do not delete:** each invariant needs a real predicate against the pre- and post-state, or it must not be claimed. `occurrence_preservation` and `bounded_emission` already have real predicates (`transition_law::occurrences_preserved`, `emission_bounded`) — the pattern exists; six more are owed.

---

### Blast radius, summed

**Dies:** R12, R14, R15, R16, R17 as generation/theorem claims. R13 is regraded (its conformance test fabricates the checker return by hand at `tests/conformance/r13_lean_checker_host_conformance.cpp:22-32,44-49` — `exit_status = 0`, `produced_artifact_bytes = 64`, hand-typed stdout). R0 is re-issued. R18's rest producer is replaced with the constant it already has. 27 verify files lose their tally assertions and keep their artifact assertions.

**Survives untouched:** R1–R11, R18–R35 mathematics; the entire R31–R35 discovery family; `formal/`; `apparatus/host/lean_checker_process.cpp`; all seven live deeds.

**Files fully removed: on the order of 90.** Headers surgically edited (gates, grade clauses, tallies): on the order of 120. That is ~14% of the tree removed and ~18% regraded — and it removes **no mathematics whatsoever**.

---

# PART 3 — THE TERRAIN, AND THE MISSING CURRENTS

This is the larger half and it is the real work. Everything below is sound, exact, float-free, and reachable by nothing that matters. **Deleting dead trees does not make a forest alive.**

### T1. The discovery core — the single most valuable thing in the repository

`organ/shift_organ_cultivation_law.hpp:36-64` exact rational Gaussian elimination; `:66-101` primitive kernel with gcd normalization and sign canonicalization; `:103-130` the typed obstruction ladder `{insufficient_rows, full_rank, nonunique_kernel, candidate_absent, zero_forward_face, none}`; `derive_family` at `:133-156` walks a nine-candidate `(order,degree)` ladder in **ascending complexity** and takes the **first** returning `none` — minimal-order selection with no score, no argmax, no crowning.

`organ/trace_rebase_discovery_law.hpp:84-128` is the same at rank 121 over `F_1000003`, extracting a nullity-1 kernel and verifying `residual == 0` on **every admitted row** (`:111-120`) before accepting — a certified exact remainder. `excluded_source` at `:84-92` is a real structural ablation.

**This is Chi with one slot undetermined returning the locus** (`2026-08-06_THE_CONSTRAINT_IS_THE_CHI…:36-48`) and it is the precise shape `CLAUDE.md` §11 asks for.

**MISSING CURRENT:** it is reached only by a frozen R31–R35 deed, and its wrappers grade it against literals (CUT 9). **The current that must exist: a live deed that takes material mounted through S6, forms a transport population from it, calls `derive_family` on that population, deposits the returned law into S3 (`returned_standing`) under an identity, and returns S7.** Then a second deed reaches the deposited law and composes with it. That deed does not exist and it is the highest-value single construction in the project.

### T2. The constraint rebase — the one deed the 2026-08-06 deposit specifies, and it is ALIVE

`organ/constraint_cycle_reading.hpp:17` `read_cycle_type`, `:112` `carries_transposition`, `:127` `witnesses_transitivity`, `:135` `roots_form_radical_coset`; `organ/constraint_obstruction_law.hpp:54` `verdict()` returning `chart_obstruction`, `:70` `divides`, `:106` `reduce_at`, `:117` `irreducible_quadratic`, `:132` `divide_out`, `:169` `product_agrees`. Real Dedekind factorization over a prime ladder; the unknown that cannot be determined in the present chart returns as an OPEN carrying `group_not_solvable` — the unsolvable group **named**, not a failure code — then rebases to a chart where the root is determined, with a positive control that splits as a radical coset. It abandons the aperture as soon as the witnesses decide.

**In the live closure** (`apparatus/host/constraint_rebase_deed.cpp`, `one_standing_deed.cpp`). This is spine and it is the model every other organ should be rebuilt against.

### T3. The suffix/incidence substrate — the only path to corpus scale

`organ/{suffix_arena, suffix_extend, suffix_symbol, incidence_arena, receiver_fiber, resonance_germ}.hpp`. Live, via `cuda/executor/text_material_mount.cu` and `resident_ecology_executor.cu`. `suffix_extend.hpp:29-35`'s ascending-insert fast path is a real algorithmic choice with a stated constant-work justification, and `arena.lookup_steps` is a real cost instrument.

Contrast: **all 39 `apparatus/cards/` files total 3,741 bytes.** The frozen line's entire external material is 29–191-byte cards. This substrate mounts megabytes.

**MISSING CURRENT:** it conditions text and nothing mathematical mounts through it. **The current that must exist: mathematical material — Lean declarations, exact transport populations, discovered coefficient words — mounted as `text_material` and conditioned by `text_conditioning`, so that `production_law::reach` (`event/conditioned_production.hpp:40-59`) answers questions about mathematics rather than about English.**

### T4. `receiver/` — 25 headers, ZERO live reach. The largest unreached owner.

`projective_swing_law.hpp` (the cross-ratio chart, correctly demoted from the object), `condensation_law.hpp` and `condensation_response_law.hpp` (canon §6.6 coinductive bisimulation), `sameness_law.hpp` (the eight sameness relations, never collapsed), `projection_chart.hpp` and `projection_law.hpp` (projection non-creation), `connection_law.hpp`, `information_geometry_law.hpp`, `geometry_exact.hpp`, `hypergeometric_law.hpp`, `extended_carrier_law.hpp`, `chart_contract.hpp`.

**MISSING CURRENT:** the whole receiver layer. The record's §6 has no conduct at all. **The current that must exist: every deed declares its receiver family, and the sufficiency test — an exhibited colliding pair, not a radical rank (`THE_FOUNDATION_REMAINDER.md:126-128`) — runs against that declaration before the deed commits.** Without it there is no reopening rule anywhere in the engine.

### T5. `current/` — 11 of 14 unreached

`information_receipt.hpp` (S7, reach 1), `interchange_certificate.hpp`, `weave_law.hpp`, `weave_certificate_law.hpp`, `resident_weave.hpp`, `current_law.hpp`, `frontier_pending.hpp`, `resident_causal_body.hpp`. The sparse-front machinery and the interchange certificate that alone licenses independent members onto grids/blocks/warps (`CPP_GPU_FOUNDATION.md:127-131`).

**MISSING CURRENT:** no deed carries a sparse front. This is why **213 of 257 kernel launches are `<<<1,1>>>`** — there is no front to place on the card. The interchange certificate exists and nothing asks it for permission. **The current that must exist: the discovery deed of T1 running its nine-candidate ladder as nine independent members under an interchange certificate, on `<<<9, 256>>>`, instead of serially.** That is remainder #4 and it is one deed away.

### T6. The exact carriers and rational kernels — 11 files, 99 callables, zero floats

`organ/{blind_integer_exact, phase_crystal_exact, cm_arithmetic_exact, characteristic_exact, expression_exact_law, toric_exact_law, regular_singular_exact, causal_linear_rational, blind_polynomial_exact, blind_code_exact, geometry_inquiry_exact}.hpp`. Real overflow refusal (`blind_integer_exact.hpp:9` `exact_limit`). This is the bit-pure carrier the record requires, sitting in the wrong owner. **Consolidate into `exact/` and delete the duplicated helpers** (`geometry_multiply` exists at `receiver/projective_swing_law.hpp:121-122` and again in `geometry_inquiry_exact.hpp`).

### T7. The mathematics families — built, exact, and nothing asks them anything

- **Linear algebra:** `causal_linear_matrix.hpp:57-96` (Smith-form rank with real pivoting, exact nullity), `:132-146` (`smith_rank_two`), `causal_linear_characteristic.hpp`, `elementary_matrix_law.hpp` (`trace_stream`, `multiply` — consumed by T1), `trace_rebase_matrix_law.hpp`, `trace_fiber_matrix_law.hpp`, `characteristic_matrix_law.hpp`.
- **Convex/lattice geometry:** `phase_crystal_hull_law.hpp:7-69` (genuine monotone-chain hull with lexicographic comparison and duplicate elimination), `phase_crystal_{geometry,shape_law,series_law,probe_law}.hpp`, the six `rederivation_*` files. `CLAUDE.md` §12 already credits this family with a real standing result: the contracted hull residue word is a complete degree-one cycle through `Z/p` with every step exactly `+1`, and convex contraction is an exact phase demodulator where pointwise assignment degrades to 45% at `p=17`.
- **Finite field / number theory:** `arithmetic_field_law.hpp:22-218` (irreducibility by trial division, tower discovery, full extension-element arithmetic, `:207` inverse by extended power — **live-reached**), `arithmetic_curve_law.hpp` (point arithmetic, Frobenius), `cm_{arithmetic_exact,window_law,characteristic_law,theory_law}.hpp`.
- **Algebraic geometry:** `toric_intersection_law.hpp:13,24,37,42,129` (fan self-intersection, Chow class, intersection pairing, form comparison over `exact::small_rational`), `hodge_{correspondence,product,factor,blowup}_law.hpp`, `toric_{realization,cycle}_law.hpp`, `intrinsic_{supported_cycle,transport,section,phase_distribution,control}_law.hpp`.
- **Differential/expression:** `expression_{ideal,connection,series,residue,cyclic,sparse}_law.hpp`, `variation_{connection,operator,invariant,reduction,loop}_law.hpp`, `regular_singular_{connection,probe}_law.hpp`.
- **Blind reconstruction:** `blind_code_law.hpp` (201 lines), `blind_moment_law.hpp` (240). The LD_PRELOAD source-access audits around it are the strongest evidential apparatus in the repository and must be kept.

**MISSING CURRENT — and this is the one that matters most.** `CLAUDE.md` §3 names Hodge as the realization law and §11 names the one missing organ: *an exactly computed positive form on a supported realizer population, with a certified remainder and a reopening rule keyed to the receiver family.* `toric_intersection_law.hpp` computes exact intersection pairings. `hodge_product_law.hpp` computes Hodge product forms. `exact/enclosure.hpp` is the certified remainder carrier. **All three pieces exist and no deed composes them.** The missing current is a deed that assembles the positive form on a realizer population, certifies its remainder through the enclosure carrier, deposits it into S3, and returns S7. That is the organ §11 says closes the learning wall, the far-field folding wall, and the Hodge-facing wall at once.

### T8. The Phase-6 upper ecologies — ported, sound, test-only

`organ/{morphological_surface, source_incidence, suffix_automaton}.hpp`; `event/{resonance_ecology, resonance_registry, relational_surface, research_ecology, formal_production, agentic_mouth}.hpp`; `codec/reflective_runtime.hpp`. I read them for the convicted shapes and did not find them: no scalar crown, no argmax, no probability weighting. `resonance_registry.hpp:26` uses `rode`/`founded`/`capacity_refused` correctly; `:38-46` states its own negative space structurally. `reflective_runtime.hpp:15-22` retains **four parents** per codec version, so a correction founds a child rather than overwriting — genuine plurality, and the mechanism `event/resident_reflective_codec.hpp` should have used instead of its monotone `bias` scalar.

`event/resonance_ecology.hpp:56` is one of only two sites that instantiate `body/live_machine.hpp`. **No deed instantiates it.**

**MISSING CURRENT:** these terminate in `tests/model/ecology_cases.cpp` and nowhere else. The current is Phase 7 broad mounting, and it must mount *through* S3/S7, not beside them.

### T9. The corpora and fixtures — explicitly not convicted

`organ/phase_crystal_cases.hpp:17-33` (16 rows: seven prime pairs, composite coprimes, shared factors, and the `exact_dilation 25/16` and `exact_turn` control rows that produced the standing correction in `CLAUDE.md` §12), and the `*_receipt.hpp` fixture tables. **A table of prime pairs is a corpus — the material the machine reads.** Hand-written material is precisely what Brandon's correction protects. The contamination was never the table; it was `phase_crystal_law.hpp:88-91` recounting its rows and calling that theory (CUT 9).

---

# PART 4 — WHAT MUST BE REFOUNDED, AND AGAINST WHICH SOURCE

| # | What | Refound against |
|---|---|---|
| 1 | **The three standings collapse to one.** Delete `rest_region.admitted_tally`; retire `live_machine`'s `standing_surface` as a second standing. | `body/returned_standing.hpp:24-34` — deposits by identity, reach, `caused_by` exclusion cascade. |
| 2 | **The 34 fixed-size `event/*_rest.hpp` records.** Each carries a summary plus tallies plus an integrity fold; a rest that omits what was derived cannot make remounting cheaper than re-deriving. | `codec/text_rest.hpp:20-30` — variable `text_rest_extent` with computed `total()`, image `[header][surface][occurrences][caused]`, remount founds from octets alone. `THE_FOUNDATION_REMAINDER.md:55-64`. |
| 3 | **`organ/training_ecology.hpp:159-161`.** `occurrences = observed(fiber) + 1U` is a bare scalar with no occurrence identity retained, so it cannot distinguish recurrence across two *distinct* occurrences from one occurrence counted twice. The **law** (`minimum_recurrence >= 2`) is ratified and stays. | `ELEMENTARY_MECHANICS.md:51-54` @ `a07ff376` — *multiplicity is represented by distinct occurrence identities, not by a numeric coefficient.* Retain the occurrence identity set, not a count. |
| 4 | **`event/resident_reflective_codec.hpp:120,132,143`.** `next_bias <= old_bias` is monotone scalar overwrite — the exact rule §13 convicts in `organ/conditioning_law.hpp:61-88`; `law_changed = bias != bias` defines "the law changed" as an integer differing. `bias` is a banned field name. | `codec/reflective_runtime.hpp:15-22` — parented codec versions, both retained. Already correct, in the same tree, unreached. |
| 5 | **The eight transition invariants** (CUT 10). Six-to-seven of eight admitted `true`. | `transition_law::occurrences_preserved` and `emission_bounded` — the two that already have real predicates. Six more are owed. |
| 6 | **`organ/trace_rebase_close_law.hpp`** recomputes `generator_controls` three times (`:130`, `:235`, and inside `:98-115`) and runs on `close_kernel<<<1,1>>>` (`cuda/executor/r35_trace_rebase_kernels.cu:143`) — **527.41 s, 23.4% of the whole suite, 79 of 80 SMs idle.** The mathematics (6,360 edges, 7×7 Jacobians, tangent transport, 1,272 states) is real and stays. | `current/interchange_certificate.hpp` — the certificate that licenses the front onto grids/blocks/warps. `THE_FOUNDATION_REMAINDER.md:101-115`. |
| 7 | **The nine schema-serial validators** (CUT 8). | `PURE_HOLONIC_ENGINE.md:100-107` — contact is a typed pullback returning zero, one, or plural, with an explicit obstruction at zero-match and at unresolved plurality. |
| 8 | **The capacities that ARE the answer.** `arithmetic_fixed_capacity = 156'260`, `arithmetic_point_pair_capacity = 144'062`, `trace_rebase_states_per_seed = 106`, `state_capacity = 1'272` (=106×4×3), `edge_capacity = 6'360` (=1272×5), `intrinsic_vertex_capacity = 17*19`, `phase_crystal_point_capacity = 19*19`. The aperture was set by knowing the result. | `EROS_EMBODIMENT_ROADMAP.md:158,166` — `SparseOrdinalAtlas`, **arenas grow**, `capacity()` is physical testimony and never an admission gate. Note `structure/marked_population.hpp:12-14` still admits **four sources** with `uint16_t` slots — the §13 ceiling stands and blocks everything. |
| 9 | **The missing audit.** No existing audit can tell a renderer from a quotation. Thirty lines: strip string literals, find every `append_face` call, require at least one argument containing an identifier that is not the buffer. I ran exactly this classifier to produce CUT 4; it separated 44 transforming files from 19 constant ones with the 2 dispatchers correctly distinguished. | `COMPLETE_CPP_ENGINE_ROADMAP.md:255-267` clause E11 — *tests which grade only counts, hashes, timing, or topology when an actual deed is required.* This is its missing enforcement. |
| 10 | **Amend the record in the same commit.** `CLAUDE.md` §5 loses the 9\*8=72 / 7\*9=63 claim (CUT 5). §11 gains: the certified enclosure carrier **exists** (`exact/enclosure.hpp`). §13 gains: the excision was a rename — 66 increment sites survived it byte-identical, proved by `git show 2b562c8`. | Direct source inspection, this document. |

---

# PART 5 — THE ORDER OF WORK

**Movement 0 — Commit and push first.** Three commits are already unpushed. Push before cutting, so annihilation is recoverable by URL and not only by reflog. Brandon's standing instruction.

**Movement 1 — The cut (CUTs 1–9).** One commit, leaves-first. ~90 files removed, ~120 edited, zero mathematics lost. Re-issue R0. Regrade R13. Promote R18's synthetic rest. The suite gets *faster*: R12/R14/R15/R16/R17 leave, and their PTX/cubin targets with them.

**Movement 2 — One standing, one head, one receipt (skeleton S3 + S5 + S7, refound 1 + 5).** Collapse the three standings onto `returned_standing`. `continuing_body::commit` takes a deposit, not a tally. `live_machine` crosses the Swing against `returned_standing` and loses its duplicate surface. The eight invariants get six real predicates. **Every deed constructs a `causal_information_receipt` or does not commit.** After this the reach audit should show `swing.hpp` and `information_receipt.hpp` in the hundreds, not at 9 and 1 — and the audit must record the number, never target it (`THE_SPINE.md:20-25`).

**Movement 3 — The current onto the discovery core (T1).** The single highest-value construction. A live deed that: mounts a transport population through S6; calls `shift_cultivation_detail::derive_family` on it; **deposits the returned law into S3 under an identity**; returns S7 with three fibers and the complete obstruction. Then a **second** deed that reaches the first's deposit through `follow_read` into `incidence_law::span` and composes with it — and a falsifier: the second deed with the first's deposit excluded must **stop**, by structure, not by flag. That is `THE_FOUNDATION_REMAINDER.md:38-53`'s crux, closed, with the discovery core as its content instead of a tally.

**Movement 4 — The front onto the card (T5, refound 6).** The nine-candidate ladder becomes nine independent members under an `interchange_certificate`, launched `<<<9,256>>>`. `trace_rebase_close_law`'s 6,360 edges become a real front. Remainder #4 closes and the 527-second serial tax goes with it. State both costs in the receipt (`THE_SPINE.md:95-96`).

**Movement 5 — The receiver layer wakes (T4).** Every deed declares its receiver family; sufficiency is tested by **an exhibited colliding pair**, not a radical rank. Without this there is no reopening rule and no honest condensation anywhere in the engine. 25 headers, currently zero reach.

**Movement 6 — The positive form on a supported realizer population (T7).** `toric_intersection_law` + `hodge_product_law` + `exact/enclosure.hpp`, composed into one deed that computes the form exactly, certifies its remainder, deposits it, and keys its reopening to the declared receiver family. This is `CLAUDE.md` §11's one missing organ. Every piece exists; nothing composes them. **This is where frontier machine-learning-for-mathematics actually begins** — because at that point the machine is fitting minimal exact laws to observed transport (Movement 3), running them as fronts (Movement 4), deciding what its receivers can and cannot separate (Movement 5), and condensing a far population into a compact realizer with a certified remainder (Movement 6). That composition is the learning, and it is intermediating the mathematics rather than a corpus about it.

**The test to hold the whole plan against, from `THE_FOUNDATION_REMAINDER.md:15-32`:** *is the learning intermediating the mathematics, or intermediating a corpus about mathematics?* Today the second, and the reason is structural and now measured: a mathematical deed commits `admitted_tally += n`, and **there is nothing for its return to change.** Movement 2 gives it something. Movement 3 makes it mathematics. Everything after is depth on one question, not breadth in the cabinet.