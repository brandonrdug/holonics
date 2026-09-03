# lineage_a_dependents_audit

Testimony of one Opus 5 audit sub-agent, 2026-09-03, read-only over the repository and the conversation logs; integrated by the primary session in `../2026-09-03_SKE_AUDIT_THE_COORDINATE_GRAIN_THE_HOST_READOUT_AND_THE_COMPRESSION_LAW_WERE_INJECTIONS_AND_THE_CANON_ALREADY_OWNS_THE_ANSWERS.md`. Every claim below is testimony until cited there.

I'll start by reading the governing files and the audit record, then map the dependency graph.
Fish shell needs quoted globs. Let me redo the grep.
Comprehensive hit list. Now let me read the core sources and the audit record.
Now the receipt reader, the blueprint's SKE4 clause, and the "productive closure" definitions.
The HNA5 receipt defines "productive imports" operationally. Let me read it, the blueprint SKE4 clause, and AGENTS.md's retraction record.
Let me pin exact line numbers in the blueprint and read AGENTS.md's retraction record.
Now let me examine each dependent. First the two productive-source ones and the module exports.
Let me delegate the records search (task 4) while I continue the code analysis.
The working tree has uncommitted SKE4 work touching lineage A. Let me diff it.
The records survey is complete. Let me verify two load-bearing claims from it directly.
The audit is complete. Here is the report.

---

# Lineage A departure audit — Soulkiller SKE4

**Lineage A** = `crates/holonic-engine/src/holonic_intelligence/scaffold_lift.rs` (519 lines) + `crates/holonic-engine/src/holonic_intelligence/scaffold_excitation_receipt.rs` (337 lines), declared at `crates/holonic-engine/src/holonic_intelligence.rs:59-62` and re-exported wholesale at `:92-93`. Both files were added in one commit, `d49c55c1` "Complete SCF multimodal scaffold circulation and release" (2026-09-01).

The SKE4 clauses in question are `blueprint/THE_SOULKILLER_EXCITES_THE_RESIDENT_REALIZATION_AND_RETURNS_THE_RECEIVER_FAMILY_QUOTIENT_AS_CONE_RESTRICTED_ECOLOGIES.md:260-261` ("the per-event generator construction departs without alias, its dependents (the `soma/life` lifecycle tests, the workbench demo, the AAC5 deed) departing or re-founding with it as Brandon rules") and `:270` ("the retired constructions are absent from the productive closure"), against `:146` ("Not reusable as the return: the per-event generator construction of `scaffold_lift.rs`…").

---

## 1. Complete dependent inventory

### 1.0 The construction itself

| Symbol | Definition |
|---|---|
| `ForeignBf16Excitation` | `scaffold_lift.rs:24-35` |
| `Bf16ExcitationColdWitness` | `scaffold_lift.rs:37-43` |
| `validate_bf16_section_reconstruction` | `scaffold_lift.rs:50-70` — `pub`, **called only from `:359`**; no external caller anywhere |
| `Bf16ExcitationDismantling` | `scaffold_lift.rs:84-87`; `impl SoulkillerDismantlingInput` at `:89-103` |
| `dismantle_bf16_excitations` | `scaffold_lift.rs:117-361` — private |
| `CompleteGemma4ExcitationReceipt` | `scaffold_excitation_receipt.rs:29-33`; `::interleaved()` at `:36-56` is **dead — zero callers repo-wide** |
| `read_complete_gemma4_excitation_receipt` | `scaffold_excitation_receipt.rs:108-200` |
| `COMPLETE_GEMMA4_EXCITATION_SCHEMA` | `scaffold_excitation_receipt.rs:21` |
| `Gemma4ExcitationFamily` | `scaffold_excitation_receipt.rs:24-27` |

The per-event shape is explicit: one `InputId` generator per event (`:170-174`), one `NativeThread` per excitation with exactly one occurrence (`:180-262`, occurrence at `:232-239`), one incidence term (`:241-246`), `chronology: vec![generator]` (`:254`), `reconstruction_fibre: BTreeSet::from([excitation.event])` (`:260`), and each `NativeGeneratorDescent` carrying exactly one step with `open_domain` = every state but the entering one (`:271-289`).

Own tests: `scaffold_lift.rs:383-518` (4 tests), `scaffold_excitation_receipt.rs:233-336` (2 tests).

### 1.1 Productive source (compile-breaking on departure) — 3 sites

| # | Site | What it is | Established by | Material |
|---|---|---|---|---|
| **P1** | `applications/athena-alpha/src/application.rs:1-8` (imports), `:52-75` (`from_complete_gemma4_receipt`), `:56` (`Bf16ExcitationColdWitness` in the return type) | Public API of the named product crate | **VWS0** (`research/records/2026-09-01_VWS0_ACTUAL_GEMMA_RECEIPT_ENTERED_ATHENA_WITHOUT_FOREIGN_EXECUTION.md:9-12`), grade `established-bounded` / `implemented-exact, source-inspected, process-audit, measured` | Receipt directory — real in principle, **fixture in every test** |
| **P2** | `applications/holonics-application/src/workspace.rs:335-352` (`lift_gemma_receipt`, calls P1 at `:352`) | The VWS application's `lift-gemma-receipt` command | **VWS0/VWS1–VWS5/VWS6**; blueprint `THE_VARIANT_WORKSPACE_APPLICATION_...md:60-66` prints the exact symbol chain and `:69-72` says "`lift-gemma-receipt` admits that path and no stronger one" | Receipt directory |
| **P3** | `applications/holonics-workbench/src/runtime.rs:8-15` (imports), `:307-337` (`athena_demo_open`), `:837-855` (`demo_excitation`) | Shipped CLI/TUI command | **WB1** (`research/records/2026-09-01_WB1_...md:18`: "bounded `demo-open` through the sole Soulkiller boundary with cold/insufficiency lanes departed") | **Synthetic**: `0x3f80/0x4000`, `0x4000/0x4040`, `0x4080/0x40a0`, `source_occurrence: "workbench-demo/{event}"` (`runtime.rs:311-320, 837-855`) |

P3's blast radius inside the workbench is larger than the one function: `runtime.rs:231-263` (`execute_demo`, the scripted `diagnostic demo` flow) calls `athena_demo_open` at `:233`; `runtime.rs:136-181` (`recommended_demo_return_command`) is gated on `bounded_demo` at `:140`, a flag set only by `athena_demo_open` (`:329`) and threaded through `:462, 498, 519, 537, 566, 584`. Command-surface plumbing: `command.rs:82-84`, `cli.rs:60, 177, 331, 395`, `adapters/engine.rs:47`, `runtime.rs:270`.

P2's plumbing: `command.rs:34`, `cli.rs:60, 331`, `adapters/workspace.rs:28-40`, `adapters/engine.rs:45`, `presentation.rs:95`.

### 1.2 Example deeds — 3

| # | Site | Established by | Material |
|---|---|---|---|
| **E1** | `applications/athena-alpha/examples/alpha_cycle.rs:4-11, 16-29, 33-36` — declared `[[example]] name = "alpha-cycle"` at `applications/athena-alpha/Cargo.toml:22-24` | **AAC5** (`2026-09-01_AAC5_...md:35-37`, receipt `:70-78`: `cargo run -q -p athena-alpha --example alpha-cycle`, exit 0 in 2.38 s); re-receipted by **AAC6** | **Synthetic**: `excitation(1, 0x3f80, 0x4000), excitation(2, 0x4040, 0x4080)` (`:35`), `source_occurrence: "cold/{event}"` (`:22`) |
| **E2** | `crates/holonic-engine/examples/lift_gemma4_excitation_into_native_transport_scaffold_scf2.rs:3-10, 18, 25-28` | **SCF2** (`2026-09-01_SCF2_COMPLETE_GEMMA4_EXCITATION_...md:5, 23-29, 36-38`) | **The only real-model lift in the repo** — reads a receipt directory produced by an exterior Python run |
| **E3** | `soma/life/examples/export_native_morphology_package_mvf5.rs:3-10, 24-38` | **MVF5** (`2026-09-01_MVF5_...md:5`) | **Synthetic**: one excitation, `entering_codewords: vec![0x3f80, 0x0000]`, `source_occurrence: "cold/export-control"` |

### 1.3 Test fixtures — 41 test functions across 15 files, all synthetic

Every one of these is inside `#[cfg(test)]` and every one funnels through a single shared fixture builder, so the whole mod dies with lineage A:

**holonic-engine (9 tests)**
- `scaffold_lift.rs:383-518` — 4 tests (`:417, :448, :472, :503`)
- `scaffold_excitation_receipt.rs:233-336` — 2 tests (`:250, :300`)
- `repeated_circulation.rs:252-380` — 3 tests; helper `excitation()` at `:270-283`, codewords `0x3f80/0x4000/0x4040/0x4080` (`:290-292, 349, 373-375`). Established by **SCF4** (`2026-09-01_SCF4_ACTUAL_ADDRESSED_SUCCESSORS_...md`, `established-bounded; implemented-exact; measured`)

**soma/life (21 tests)** — all established by the AAC0–AAC6 / MVF3–MVF5 / SCF3–SCF5 series
- `circulation_diffusion.rs:348+`, helper `session()` `:367`, codewords `:375-376` → 2 tests (`:411, :503`)
- `circulation_session.rs:436+`, helpers `excitation()` `:451`, `session()` `:472`, codewords `:453-455` → 3 tests (`:520, :543, :567`)
- `morphology_commit.rs:429+`, helpers `:447, :462`, codewords `:465` → 2 tests (`:546, :612`)
- `morphology_package.rs:743+`, helper `rest()` `:764`, codewords `:773-774` → 4 tests (`:787, :813, :842, :865`)
- `rest.rs:310+`, codewords `:340-341` → **1 of 2** tests (`:329`; `:324` is independent)
- `scaffold_cultivation.rs:747+`, helper `excitation()` `:761`, codewords `:780, :835-837` → 2 tests (`:776, :830`)
- `world_return.rs:334+`, helpers `:353, :376`, codewords `:361-368` → 4 tests (`:458, :502, :546, :607`)
- `morphology_export/tests.rs:5-29`, helper `package()` `:18`, codewords `:28-29` → 3 tests (`:63, :91, :115`)

**soma/circulation-abi (3 tests)** — `src/lib.rs:591+`, helper `fixture()` `:609`, codewords `:621-634` → 3 tests (`:691, :813, :925`). Established by **AAC4**.

**Integration tests (8)**
- `applications/athena-alpha/tests/alpha_matrix.rs:8, 26-61` — 1 test; synthetic. **AAC6**
- `applications/athena-alpha/tests/gemma_receipt_admission.rs:4, 33-66` — 1 test; synthetic receipt via P1. **VWS0**
- `applications/holonics-application/tests/variant_workspace.rs:7-8, 39-60, 152-180` — 3 tests; both a synthetic receipt (`:41-43`) *and* a direct synthetic dismantling (`:152-180`). **VWS1–VWS6**
- `applications/holonics-workbench/tests/workspace_cli.rs:5, 30-56, 90` — 1 test; synthetic receipt through the real `holonics` binary. **VWS6/WB4**
- `applications/holonics-workbench/src/runtime.rs:885+` — 2 tests (`:896, :1028`) driving `AthenaCommand::DemoOpen` (`:906, :1044`). **WB1**

### 1.4 The real-model founding is not reproducible today

`soma/life/examples/e2/foreign_towers.py` is the **only** producer of `holonics.scf2.complete-gemma4-excitation.v2` in the tree (`:437`). Its output cannot be read by `read_complete_gemma4_excitation_receipt`, confirming the audit record's finding (`2026-09-02_SOULKILLER_AUDIT_...md:62`). Three independent `deny_unknown_fields` violations:

- `WireReceipt` (`scaffold_excitation_receipt.rs:71-79`) accepts only `schema, text, vision, audio, video`; Python emits also `truth_status, model, apparatus` (`foreign_towers.py:436-472`).
- `WireOrgan` (`:81-85`) accepts only `returns`; Python's text/vision/audio organs emit `organ, source_lineage, tensor_count, complete_layer_count, resident_weight_parameters, peak_cuda_allocated_octets, elapsed_nanoseconds, apparatus, returns` (`foreign_towers.py:399-408`).
- `WireReturn` (`:87-99`) accepts 8 fields; Python emits also `family, state, source_incidence_sha256, input_token_count, layer_frontier_sha256, text_space_shape, top5, kv_cache_used` (`foreign_towers.py:380-398`).

No receipt directory exists in the working tree (`find . -name receipt.json` → only `output/wrd4/receipt.json`, unrelated). **E2 is currently unrunnable.** Every runnable use of lineage A in the repository today is a synthetic-codeword fixture.

---

## 2. What "productive closure" means here

The repository has **no abstract definition**. It has one operational one and one type-level one.

**Operational (HNA5 release receipt).** `applications/athena-alpha/examples/full_application_matrix_hna5.rs:110-112`:

```rust
let counterexample_return_paths_absent_from_productive_imports = forbidden_return_paths
    .iter()
    .all(|path| !driver_source.contains(path));
```

with `driver_source = include_str!("full_application_matrix_hna5.rs")` (`:81`) and `forbidden_return_paths` at `:83-90` (`material_ingress`, `material_codec`, `world_return`, `world_application`, `lattice_mouth`, `lean_mathematics::candidates`). **"Productive closure" is operationalized as a textual scan of the release driver's own source for named retracted paths** — not a crate- or module-graph analysis. Its governing clause is `blueprint/THE_HOLONIC_NEURAL_ATHENA_...md:371-372` ("the counterexample HNA source and retracted template/source-lookup paths are absent from the productive closure") and `:300` for HNA2.

**Type-level (Soulkiller).** `blueprint/THE_SOULKILLER_...md:96-100`: "A productive Soulkiller lane is a `FaithfulLocalSectionLift` on the declared family… A `DismantlingReturn` whose productive lane does not carry that obligation is a manifestation and is refused the name." Formal owner: `soma/formal/.../HolonicExcitationFoundedQuotient.lean:291-292`.

### Is lineage A inside the productive closure?

| Closure | Verdict | Evidence |
|---|---|---|
| **(a) athena-alpha application** | **Yes, at module grain; no, at driver grain.** `applications/athena-alpha/src/application.rs:1-8` imports four lineage-A symbols into the crate's *productive source*, and `:52-75` is public API. But the HNA5/SKE release drivers (`full_application_matrix_hna5.rs:1-11`, `condensation_seal_ske4.rs:24-37`) import only `AthenaTokenApplication` and resident-operator symbols — no lineage A. Under the receipt's own textual test lineage A is absent; under a Rust import-graph test it is present in the crate that the driver imports. | as cited |
| **(b) workbench** | **Yes, unambiguously.** `runtime.rs:8-15` is a productive `use`; `:307-337` is a live shipped command reachable from `holonics diagnostic demo` and `holonics diagnostic athena demo-open`. Transitively also via `lift-gemma-receipt` → `workspace.rs:352` → `application.rs:59-68`. | as cited |
| **(c) HNA/SKE release** | **No, at the grain the release actually measures.** The SKE lane's productive type is `NativeConeRestrictedEcology` (`operative_condensation.rs:105-116, 197`), a *different* type from lineage A's `NativeTransportScaffold` (`scaffold_lift.rs:90`). No SKE record names any lineage-A symbol. | `operative_condensation.rs:1-46`; SKE0–SKE3 records |

**Decisive import-graph evidence for the boundary itself:** the uncommitted working tree has already removed lineage A from the Soulkiller boundary's own witness. `git diff crates/holonic-engine/src/soulkiller/boundary.rs` deletes `admitted::<Bf16ExcitationDismantling>();` and the test `generic_reachable_and_bf16_charts_enter_one_public_boundary`, replacing them with `admitted::<ResidentExcitationDismantling>();` and `the_reachable_section_and_the_excited_resident_realization_enter_one_public_boundary` (`boundary.rs:76-88`). The new module doc (`:6-8`) enumerates the admitted productive lanes as "a spool complex from admitted exterior testimony, or the cone-restricted ecology of an excited resident realization" — lineage A is no longer named. Lineage A was kept compiling only by threading the new three-parameter generics through it (`git diff .../scaffold_lift.rs`, +18/−8, purely mechanical).

---

## 3. What is lost, and whether a non-lineage-A founding exists

### 3.1 The three `SoulkillerDismantlingInput` implementors

| Implementor | `type Productive` | Input it needs | Usable as a fixture? |
|---|---|---|---|
| `Bf16ExcitationDismantling` (`scaffold_lift.rs:89-90`) | `NativeTransportScaffold` | `Vec<ForeignBf16Excitation>` — trivially hand-buildable | yes (this is the current founding) |
| `ReachableSectionDismantling` (`soulkiller/scrapyard.rs:64-77`) | `NativeTransportScaffold` | `&ForeignReachableSectionRest`, `&NativeAnatomyRest`, `&ExteriorNativeAnatomyWitness`, plus two testimonies | **No.** Its only construction site (`soma/life/examples/the_soulkiller_returns_native_parametron_spools.rs:66-104`) reads three binary `.rest`/`.witness` artifacts from `output/the_soulkiller_admits_the_reachable_section_k2/` and `output/the_foreign_receiver_descends_into_athena_native_anatomy_k1/` — **neither directory exists in the tree.** Lineage C is unrunnable and has no synthesizable fixture. |
| `ResidentExcitationDismantling` (`operative_condensation.rs:196-197`) | **`NativeConeRestrictedEcology`** | the resident operator + declared family + founded cones | **No — type-incompatible.** `consume_dismantling_return` (`soma/life/src/native_intelligence/rest.rs:29-50`) is bounded `Returned: IntoDismantlingBoundaryReturn<Productive = NativeTransportScaffold>` (`:39`), as is `AthenaAlphaApplication::from_dismantling_return` (`applications/athena-alpha/src/application.rs:94`). The SKE4 lane cannot mount the soma/life lifecycle. |

**So SKE4 does not re-found any lineage-A dependent.** The two campaigns produce different productive types and serve different obligations.

### 3.2 The founding that does exist

`SoulkillerDismantlingReturn` has all-public fields (`soulkiller/boundary.rs:14-19`) and a **blanket** `IntoDismantlingBoundaryReturn` impl over all three parameters (`:41-47`). Therefore any test can write

```rust
SoulkillerDismantlingReturn { native: <hand-built NativeTransportScaffold>, exterior: (), insufficiency: () }
```

and feed it to `consume_dismantling_return` or `from_dismantling_return` **without any `SoulkillerDismantlingInput` at all**. No lineage is needed.

The scaffold literal already exists twice in-repo:
- `crates/holonic-engine/src/native_spool/tests.rs:238-246` (`scaffold()`) over `:161-236` (`spool()`) over `:72-159` (`thread()`) — a validated two-state, two-thread native body.
- `crates/holonic-engine/src/native_spool/tests.rs:922-945` (`FixtureDismantlingReturn`) — a hand-built `DismantlingBoundaryReturn` with `String` cold/insufficiency lanes, used at `:947-961`.

**Blocker:** both are behind `#[cfg(test)]` (`crates/holonic-engine/src/native_spool.rs:37-39`), so unreachable from `soma/life`, `soma/circulation-abi`, `athena-alpha`, `holonics-application`, or the workbench. `FixtureDismantlingReturn` also implements only `DismantlingBoundaryReturn`, not `IntoDismantlingBoundaryReturn`, so it cannot be consumed by `life`. Re-use requires promoting one of these to a `pub` (or feature-gated) fixture — a real, if small, decision.

### 3.3 Would re-founding on `scaffold()` be an alias? **No — it is a different founding.** Argument from code shape:

| | `dismantle_bf16_excitations` | `native_spool::tests::scaffold()` |
|---|---|---|
| generators | one per event, `|generators| = |events|` (`scaffold_lift.rs:170-174`) | **one generator `InputId(7)` shared by two threads** (`tests.rs:165`) |
| descent | one step, `open_domain` = all states minus the entering one, i.e. defined at exactly one state (`:271-289`) | **two steps forming a closed cycle 0→1→0, `open_domain: BTreeSet::new()` — total** (`tests.rs:193-207`) |
| states vs. occurrences | states derived from section keys; every event contributes its own thread | **2 states, 2 occurrences, both states revisited**; two `serial_pullbacks` (`tests.rs:171-192`) |
| origin of native structure | **decoded from exterior BF16 codewords** (`:145-146`, `factorize_bf16` `:363-374`) | declared directly in native types; no codec path at all |

Lineage A is a *function from a recorded event list to a native body* — the "one generator per recorded event is the replay the HNA blueprint rejects" that `2026-09-02_SOULKILLER_AUDIT_...md:92-96` grades `counterexample`. `scaffold()` makes no founding claim whatsoever: it declares a native body directly, with generator sharing and a total descent that lineage A cannot produce. **An alias would be a renamed per-event constructor; a fixture is the removal of the founding claim.** The soma/life tests need a *valid `NativeTransportScaffold`*, not a lift — mount, conduct, commit, snapshot, remount, export, ABI. A hand-built scaffold serves them exactly and asserts nothing about excitation.

**Honest caveat:** one test genuinely tests the *boundary*, not the body — `soma/life/src/native_intelligence/rest.rs:328-348`, `dismantling_handoff_consumes_productive_scaffold_and_keeps_cold_testimony_outside_hot_rest`. It needs *a* three-lane return, which `SoulkillerDismantlingReturn { .. }` supplies directly (§3.2). Also lost with lineage A, and not replaceable by a fixture: the BF16 codeword→exact-rational decode path (`factorize_bf16`, `scaffold_lift.rs:363-374`) and its collision-separation test (`:472-501`), and the receipt reader's path-containment/unknown-field refusals (`scaffold_excitation_receipt.rs:202-214, 300-336`). Those are the only *capabilities* in the two files that no other owner covers.

---

## 4. Records that established lineage A, and what the retraction record says

### 4.1 What each record claims

| Record | Grade | Claim | Lineage A material |
|---|---|---|---|
| `2026-09-01_SCF2_COMPLETE_GEMMA4_EXCITATION_FOUNDED_THE_SOURCE_NEUTRAL_TRANSPORT_SCAFFOLD.md:5` | `established-bounded; implemented-exact; source-inspected; measured` | Real Gemma 4 E4B run (42 text / 16 vision / 12 audio layers, 7,324 + 8,138 CUDA events); 14 codeword populations → 20 native states, 14 threads, 266 open generator faces, 29,315-octet scaffold wire. Names `scaffold_lift.rs` at `:24` | **Real model.** Self-narrowed at `:7-13` by MVF1 |
| `2026-09-01_MVF1_...md:5` | same | Fresh real Gemma 4 E4B lift: 976,896 exact section coordinates, 20 states, 10 threads, 21,029,446-octet wire; replaces SCF2's alternating-sum endpoint | **Real model** |
| `2026-09-01_MVF2_...md:5` | same | `soulkiller::dismantle` becomes the sole entry; `Bf16ExcitationDismantling` named at `:14` | Type-plumbing only |
| `2026-09-01_SCF6_...md:5` | same, with `[counterexample]` at `:7-14` | Five modality experiments through one chain; **video family retracted to reused stills, "interleaving" retracted to a re-sort** | Real receipt, narrowed |
| `2026-09-01_VWS0_...md:4-6` | `established-bounded` / `implemented-exact, source-inspected, process-audit, measured` | `from_complete_gemma4_receipt` composes reader→dismantling→boundary→mount | **Fixture** (`:20-22`) |
| `2026-09-01_VWS1_VWS5_...:4-8`, `VWS6:4-7` | `established-bounded` | Persistent workspace lifecycle over receipts | **"actual receipt fixture"** (VWS1:24) |
| `2026-09-01_AAC5_...md:4-7` | `established-bounded` | First named Athena application: gen 0 → event 100 → cone commit → gen 1 → snapshot → remount. Deed is `alpha_cycle.rs` (`:35-37`, receipt `:70-78`) | **Synthetic**, two codewords |
| `2026-09-01_AAC6_...md:4-8` | `established-bounded` / +`formal-checked` | AAC0–AAC6 released; explicit disclaimer at `:137-141` | **Synthetic** |
| `2026-09-01_MVF5_...md:5` | `established-bounded; implemented-exact; source-inspected; measured` | Safetensors/ONNX export lenses; artifacts 5,937 / 5,995 octets | **Synthetic**, one two-codeword excitation |
| `2026-09-01_WB1_...md:18` | `established-bounded; implemented-exact` | "bounded `demo-open` through the sole Soulkiller boundary with cold/insufficiency lanes departed" | **Synthetic**, three one-codeword excitations |
| `2026-09-01_SCF3/SCF4/SCF5:5` | `established-bounded; implemented-exact; measured` (SCF5 narrowed at `:7`) | hot rest, repeated successors, source-detached remount | Synthetic chains |

### 4.2 The retraction record — verbatim entries touching lineage A

`AGENTS.md:96` opens "Capability and retraction record". Relevant entries:

**`AGENTS.md:164-169`** (the lineage-A-adjacent one):
> "2026-09-02: the HNA1 'Soulkiller return' is a manifestation: the resident exact foreign operator with its names removed, exciting nothing, carrying no insufficiency, never crossing the Soulkiller boundary. Soulkiller is founded by excitation and returns the signature quotient of a declared family as cone-restricted ecologies; the resident realization is its apparatus"

**`AGENTS.md:170-176`**:
> "2026-09-03: the SKE2 and SKE3 cones over the 1,595,392 output coordinates are withdrawn as cones… the HNA session's per-operation passage and host readout is the renamed instruction loop of 2026-08-18 and grades nothing; the SKE4 construction at the coordinate grain is withdrawn as the deed."

**`AGENTS.md:144-146`**:
> "the SCF alternating-sum section identity was replaced by complete factorized sections and carries no broad exactness theorem (`2026-09-01_MVF1_COMPLETE_FACTORIZED_GEMMA_SECTIONS_REPLACED_THE_ALTERNATING_SUM_IDENTITY.md`)."

**Finding — nothing in `AGENTS.md`'s retraction record retracts lineage A.** No entry mentions `scaffold_lift`, `scaffold_excitation_receipt`, "per-event", "replay", or "transition table". To the contrary, `AGENTS.md:185-187` lists lineage A's founding record under **standing**:

> "the Soulkiller Complex-Parametron bundle and **the complete Gemma excitation scaffold** (`2026-08-25_SOULKILLER_DISMANTLES_...md`, **`2026-09-01_SCF2_COMPLETE_GEMMA4_EXCITATION_FOUNDED_THE_SOURCE_NEUTRAL_TRANSPORT_SCAFFOLD.md`**)"

and `:188` adds "and the exact lifecycle apparatus of HIF, **SCF, MVF, AAC**, and VWS."

The adverse grading of lineage A lives **only** in two places, neither of which is the retraction record: `research/records/2026-09-02_SOULKILLER_AUDIT_...md:92-96` (`[counterexample; source-inspected]`, "the right intake grade and the wrong condensation… one generator per recorded event is the replay the HNA blueprint rejects… Its reader is also broken against that receipt") and `blueprint/THE_SOULKILLER_...md:145-147` ("Not reusable as the return"). The blueprint's phrasing is precise and narrow: **"not reusable *as the return*"** — it retires lineage A as a *Soulkiller lift*, and `:139-141` explicitly keeps "the Soulkiller boundary type and **the insufficiency lane of the excitation lineage**" as reusable. It does not grade the AAC/MVF/VWS/WB lifecycle deeds that merely used it as fixture material.

---

## 5. Bounded departure plan — options with exact blast radius

Precedent for the phrase: `blueprint/THE_ROADMAP.md:627` records that "SCF1 replaced the whole-object Rust vocabulary with `NativeTransportScaffold` across Soulkiller, profiles, Athena rest, and conduct **without an alias or compatibility decoder**", and MVF2 (`2026-09-01_MVF2_...md`) did the same for four public surfaces. Precedent exists for total removal with no shim.

### Option 1 — Boundary-only departure (smallest)
Remove lineage A from the *Soulkiller boundary's admitted set* only; leave the files as an application-side fixture builder. **This is already done in the working tree**, unstaged, at `crates/holonic-engine/src/soulkiller/boundary.rs:76-88`.

- **Blast radius:** 0 further files. Already compiles (the `git diff` on `scaffold_lift.rs` is mechanical generics threading).
- **Does not satisfy `:270`** — lineage A remains in athena-alpha's and the workbench's productive imports.
- **Requires Brandon:** no.

### Option 2 — Depart the construction, re-found the tests (satisfies `:260` and `:270`)
Delete both files (856 lines) + the `mod`/`pub use` at `holonic_intelligence.rs:59-62, 92-93`. Re-found every dependent on a promoted `NativeTransportScaffold` fixture (§3.2/§3.3).

**Exact blast radius:**

*Source, must be rewritten or removed (3 files):*
- `applications/athena-alpha/src/application.rs` — delete `:52-75` and 4 imports at `:3-4`; `AthenaAlphaAdmission<Bf16ExcitationColdWitness, …>` at `:56` goes with it. `mount` (`:77-84`) and `from_dismantling_return` (`:86-113`) are lineage-neutral and survive untouched.
- `applications/holonics-application/src/workspace.rs:335-...` — `lift_gemma_receipt` loses its only implementation.
- `applications/holonics-workbench/src/runtime.rs` — `:307-337`, `:837-855` removed; `:231-263`, `:136-181`, and the `bounded_demo` flag at `:39, 140, 329, 462, 498, 519, 537, 566, 584` all collapse.

*New apparatus required (1 file):* promote `native_spool/tests.rs:161-246` (`spool()`/`scaffold()`) out of `#[cfg(test)]` — e.g. a `pub` fixture module or a `test-fixtures` feature on `holonic-engine`. Without this, none of the downstream crates can re-found.

*Tests to re-found (41 functions in 15 files):* the full list in §1.3. Mechanical: replace `dismantle(Bf16ExcitationDismantling{..})` with `SoulkillerDismantlingReturn { native: scaffold_fixture(), exterior: (), insufficiency: () }`. Two exceptions that cannot be re-founded and must simply depart: `scaffold_lift.rs:472-501` (BF16 collision separation) and `scaffold_excitation_receipt.rs:300-336` (containment/unknown-field refusals).

*Examples to delete (3):* `alpha_cycle.rs` (+ `applications/athena-alpha/Cargo.toml:22-24`), `lift_gemma4_excitation_into_native_transport_scaffold_scf2.rs`, `export_native_morphology_package_mvf5.rs`.

*Command surface to remove (2 commands, 8 files):* `demo-open` and `lift-gemma-receipt` from `command.rs:34, 82-84`, `cli.rs:60, 177, 331, 395`, `adapters/workspace.rs:28-40`, `adapters/engine.rs:45, 47`, `presentation.rs:95`, `runtime.rs:270`, and the CLI test `applications/holonics-workbench/tests/workspace_cli.rs`.

*Docs requiring correction (7 files, 13 sites):*
- `UNIVERSAL_CATALOG.md:66, 73` (both name `scaffold_lift.rs` / `scaffold_excitation_receipt.rs` as the standing implementation), `:126` (the VWS row's pipeline)
- `blueprint/THE_VARIANT_WORKSPACE_...md:60-66` (the symbol chain), `:69-72`, `:176`
- `applications/holonics-workbench/WORKBENCH.md:38, 82`
- `applications/holonics-workbench/README.md:26, 126`
- `applications/holonics-workbench/PRODUCT.md:45, 57`
- `blueprint/THE_ROADMAP.md:962`

*Records affected (evidence, never edited — but their deeds become non-reproducible):* SCF2, SCF6, MVF1, MVF2, MVF5, AAC5, AAC6, VWS0, VWS1–VWS5, VWS6, WB1. Note that SCF2's and MVF1's deeds are **already** non-reproducible (§1.4), so departure changes nothing for them.

### Option 3 — Depart the construction, keep the receipt reader
Delete `scaffold_lift.rs` (the per-event construction the blueprint names) and keep `scaffold_excitation_receipt.rs` as an exterior admission reader.

- **Blast radius:** everything in Option 2 *except* the receipt reader's own 2 tests. But `read_complete_gemma4_excitation_receipt` returns `Vec<ForeignBf16Excitation>` (`:26, 170`), a type defined in `scaffold_lift.rs:24`. The reader would have to be re-typed against something, and it has **no consumer left** once `Bf16ExcitationDismantling` is gone.
- **Assessment on the evidence:** this option leaves a reader that is (a) broken against its only producer (§1.4) and (b) consumer-less. I record it for completeness; the evidence does not support it.

### Decisions requiring Brandon

1. **The workbench's product surface.** `demo-open` / `diagnostic demo` is a *shipped, released* command with no owning product document — `WORKBENCH.md:82-90` demotes it to a "diagnostic probe", `PRODUCT.md:45` lists "a demo mistaken for model construction" as an anti-reference, and the only literal naming is the WB1 *record* at `:18`. Whether the workbench keeps a demo path at all (re-founded on a native fixture, which is strictly more honest since the current one is synthetic anyway) or loses the command is a product decision, not a construction one. Same question, separately, for `lift-gemma-receipt`, which `blueprint/THE_VARIANT_WORKSPACE_...md:160` lists among the workbench's **primary** commands and which is the VWS campaign's entire admitted-source boundary.

2. **The AAC5 deed's standing.** AAC5 is graded `established-bounded` and is **not retracted** by `AGENTS.md`'s record. Its deed is wholly `alpha_cycle.rs` (`2026-09-01_AAC5_...md:70-78`). Deleting that example makes a standing, unretracted receipt non-reproducible. Options: re-found the example on a native fixture (preserves the lifecycle claim, drops the "two independent inherited excitation sections entered Soulkiller" phrasing at `:35-36`), or delete it and narrow AAC5 by a new record. The same question applies to MVF5's deed (`export_native_morphology_package_mvf5.rs`) and to the VWS receipts.

3. **Promoting a test fixture to `pub`.** §3.2 shows no departure is possible without exposing a `NativeTransportScaffold` fixture across crate boundaries. `CLAUDE.md`'s construction clause treats a new shared apparatus file as presumptively a missing abstraction; whether this is a legitimate small apparatus or a hidden foreman is a judgment call worth putting to Brandon before writing it.

4. **Whether `AGENTS.md`'s retraction record should gain a lineage-A entry.** As it stands, `AGENTS.md:185-187` lists SCF2 as standing while `blueprint/THE_SOULKILLER_...md:146` calls its construction not reusable. These are consistent (standing *as a lift receipt*, retired *as the Soulkiller return*), but a future session reading only `AGENTS.md` would not learn that lineage A is departing. That is exactly the failure mode `CLAUDE.md`'s `[historical]` clause was written to prevent.


