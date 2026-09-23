# R2 membrane owner and caller audit

Source-backed R2 owner map, 2026-09-23. The initial audit followed `.agents/bin/prior-art 'membrane|SparseStanding|LiveCurrentMachine|live current|standing storage'`; its matches are navigation evidence, so dispositions below rest on named owners and callers. The ERST plate cut passed its focused and workspace gates, recorded in `docs/VERIFICATION_RECEIPTS.tsv`. The later replay-wrapper cut moved sparse and ranked witnesses to live body/membrane owners; its focused body/membrane and locked workspace gates also passed.

## Decision

`soma-membrane` cannot be retired in isolation: `holonic-life` has production, test, and CUDA consumers of its live receive machine and its state types. Move the live execution cluster into the substantive `holonics` library and update the life consumers as part of the move. The generic `CausalMembrane` trait already belongs to `holonic-structure::membrane` and should be imported from its owner until the `holonics` merge consolidates that owner. Do not copy generic standing/descent laws into the runtime cluster.

`holon-plate`'s membrane-specific ERST schema has been removed with its deed adapter, registry/export entries, fixtures, and direct dependency. ERST `.holon` plates are no longer read by this application. This disposition concerns the plate adapter; `LiveCurrentRestImage` remains a runtime rest representation and is not changed by this cut.

## Live module and consumer matrix

| Source owner / exported surface | Classification | Source-backed consumers / disposition |
|---|---|---|
| `src/live_current.rs`: `LiveCurrentMachine`, typed event and relation inputs, executors, receipts, rest image and receive/continuation operations; exported in `src/lib.rs:45-57` | Unique executable receive and successor operation; formal analogues are partial and do not replace the Rust runtime | Used throughout life: `current_world.rs:15`; `synchronized_occurrence.rs:30`; `coupled_informant_current.rs:30`; `causal_language.rs:24`; `live_current_cuda.rs:23`, including CUDA executor/mount code (e.g. `live_current_cuda/executor.rs:702`, `:864`). Used by plate ERST at `schemas/current.rs:24-27`. Move with consumers into `holonics`. |
| `src/live_constituent.rs`: cells, incidence, pins, paths, boundary transitions, interface capabilities, receiver fibre identity and support operations; re-exported in `src/lib.rs:38-44` | Reusable executable relation/geometry representation; related Lean material exists, but this Rust structure is actively used and not an interchangeable generic retention law | `synchronized_occurrence.rs:33` consumes `ReceiverFiberIdentity` and related live types; `suffix_ecology.rs:18` consumes `ReceiverFiberIdentity`; current/causal/morphological consumers use the same types. Move with `live_current`. |
| `src/sparse_standing.rs`: `SparseStandingSurface`, `StandingCell`, immutable persistent constituent multiset and successor handling; re-exported in `src/lib.rs:58-59` | Runtime standing representation and transition; **not** duplicate of `holonic-core::standing` or `Foundation/Standing.lean`, which state future-sufficiency/quotient laws rather than this sparse physical runtime carrier | Life calls `SparseStandingSurface` throughout, e.g. `causal_language.rs:26`, `synchronized_occurrence/tests.rs:3`, and CUDA paths. Move with machine. |
| `src/chart_address.rs`: rank-qualified dyadic `ChartAddress`, zero-extension, projection to flat grips; re-exported in `src/lib.rs:32` | Exact coordinate/storage chart supporting the sparse standing geometry | Used internally by `sparse_standing.rs` and `live_current.rs` encode/decode paths (e.g. `live_current.rs:1557-1565`, `:1738-1758`). Move as a dependency of standing/rest, not as an independent top-level law. |
| `src/support_family.rs`: `LiveSupportFamily`, `LiveSupportSection`; re-exported in `src/lib.rs:61` but module itself private | Factorized support/lineage representation used by live constituents; execution representation rather than independent physical law | `live_constituent.rs` imports and stores these families. Move with constituent. |
| `src/live_carrier.rs`, `src/growing_carrier.rs`: `LiveCarrierSnapshot`, `GrowingCarrier`; re-exported in `src/lib.rs:33,37` | Exact growing carrier and native rest chart implementing the body storage seam; not a generic Holon law | Live-current inputs/results use them (`live_current.rs:1895-1915`, `:2234-2245`); CUDA executor constructs snapshots (`live_current_cuda/executor.rs:1514`). Move only the pieces required by live runtime, updating imports. |
| `src/growing_ranked.rs`, `src/growing_sparse.rs`: `GrowingRankedOwn`, `RankedOwnCell`, `GrowingSparseOwn`; re-exported in `src/lib.rs:34-35` | Storage adapters over `body::manifold::{RankedOwnStorage,SparseOwnStorage}` | `live_carrier` tests use `GrowingSparseOwn`; CUDA executor uses `RankedOwnCell` (`executor.rs:1477`). Move the used adapters/types alongside the runtime and retain only if post-move production callers remain. |
| `src/ranked_surface.rs`, `src/sparse_surface.rs`: `RankedFeltSurface`, `SparseFeltSurface` and related errors; formerly re-exported in `src/lib.rs:58-60` | Retired: unconsumed replay wrappers over body-owned ranked/sparse OWN state; not the live standing surface | Source search found no consumer beyond the two modules' own tests; no life or plate caller. Removed both wrappers and their exports. Preserved discriminating sparse transition evidence in `holonic-body/src/manifold/tests_carrier.rs`; sparse wrapper hand/deed-extent guards remain documented boundary transaction history, not a body transition law. `SparseStandingSurface`/`live_current` stay. |
| `crates/holonic-surface` wgpu implementation | Separate device surface API and crate; no edge to the replay wrappers or live `live_current` | The membrane wrappers use CPU `Vec`/body OWN state and dense parity fixtures. `holonic-surface` is a separate workspace member and its current workspace caller search returns none. Its future retirement/move is a separate R2 cut; do not treat this membrane deletion as removing or replacing the wgpu owner. |
| `holonic-structure/src/membrane.rs`: `CausalMembrane` trait (`:7-22`), re-exported by membrane `src/lib.rs:36` | Duplicate re-export, not membrane-owned implementation | `AgenticLanguageEcology` implements the trait (`holonic-life/src/agentic_language/ecology.rs:1686`); its documentation references the method at `:767`. Change the import to `holonic-structure` (or merged `holonics`) when removing the re-export. |

The manifest edges are explicit: `crates/holonic-life/Cargo.toml:23` and `applications/holon-plate/Cargo.toml:21`. The source search found no additional Cargo manifest consumers of `soma-membrane` beyond those two and the crate itself (archive excluded from live workspace).

## Exact `holon-plate` ERST cut

The ERST schema is specifically the plate adapter for membrane rest bytes, not a generic plate facility:

* `applications/holon-plate/src/schemas/current.rs:1-20,22-27` documents the `ERST` form owner and binds to `LiveCurrentRestImage`, `LiveCurrentMachine`, and `ContemporaryEvent`.
* The retired `schemas/current.rs` had owned `CurrentSchema::relight`, `CurrentBody::{form,census,present}`, and ERST-specific `CurrentDeed::{encode,decode}`. That file is deleted.
* The `CURRENT_SCHEMA` registry entry and schema exports are removed. `holon-plate/Cargo.toml` no longer depends on `soma-membrane`; the unused direct `body` and `soma-abi` edges were removed with the adapter.
* ERST example branches and ERST-only test fixtures are removed. Generic plate round-trip, content-address, census, deed-dispatch and CLI laws remain exercised through HTEC/CDER/RBIN.
* The incidental comparison in `schemas/rebase.rs` was rewritten without naming ERST.

The former plate-only carrier regression assertion now belongs with its runtime owner at
`crates/holonic-membrane/src/live_current.rs::tests::continuing_cell_advances_two_depth_one_lineages_without_growing_their_carriers` (test begins at line 5342). It reproduces two rank-6 attached lineages, settles both through cell relations 13, 29, and 17, then continues both through relation 71. It asserts native carrier extent remains 720 words while each lineage cursor advances from 3 to 4. This preserves the August 15, 2026, 720-to-1272 regression witness at the live-current boundary instead of keeping a machine assertion in a plate adapter. Source inspection shows the test calls existing test helpers and public `LiveCurrentMachine` methods; the focused live-current test passed after the cut.

The deleted `CurrentSchema` zero-action refusal is covered at its typed owner: `crates/holonic-abi/src/active.rs:1101-1102` asserts `ActionCurrent::new(Cog::ZERO) == None` and rejects the zero-word action representation. The focused ABI test passed; no duplicate membrane test was added.

This cut retires the ERST plate reader/deed workflow, not `LiveCurrentRestImage::{encode_native_bytes,from_native_bytes}` or its native rest image. Those remain used by life rest/remount pathways (e.g. `holonic-life/src/synchronized_occurrence/ecology.rs:520`) and travel with the machine when its owner moves.

## Why move into `holonics`

The restructure’s target is a substantive, backend-neutral main `holonics` library that absorbs live `holonic-core`, `holonic-structure`, and the source-neutral engine. `soma-membrane` is not an optional backend: it owns the Rust live current/standing/constituent runtime used by `life`, including the CPU path and CUDA adapters. Moving that runtime with its concrete callers preserves the behavior while removing the historical `soma-membrane` package boundary. Retiring it without moving the machine would remove the current production owner; leaving it as a forwarding crate would violate the no-alias/no-forwarding rule. Keep CUDA execution code at its separate backend boundary and rebind it to the moved core types.

`holonic-core::standing` and Lean `Foundation/Standing.lean` give the general law that a retained quotient is sufficient for the admitted future. `holonic-core/src/restriction/descent.rs:27-37` names the corresponding checked Lean owners and runtime consumers. They do not implement the concrete sparse constituent tree or atomic event transition in `sparse_standing.rs` / `live_current.rs`; the latter is implementation of the consuming operation and belongs with the main Rust library.

## Verification gates for implementation

For the ERST plate cut, the focused live-current and zero-action tests, the complete `holon-plate` suite (32 library, nine CLI, 12 plate-mouth tests), and the locked workspace all-target check passed. On the eventual membrane runtime move:

1. `rg` finds no live workspace `soma-membrane` manifest or source references after the package is removed; confirm the remaining path list with Cargo metadata/workspace membership.
2. Check `holonic-life` with all targets, including its CUDA-feature/device-independent compile paths as supported by the host; its CPU live-current, synchronized occurrence, causal language, and receiver/ecology tests must compile and pass.
3. Check `holon-plate` with all targets after ERST removal; generic plate tests and CLI tests must still pass for the retained schemas.
4. Verify the relocated Rust APIs retain the declared rest-image encode/decode version and round-trip behavior for current runtime callers; verify no ERST schema/deed reader remains in `holon-plate`.
5. If formal declarations/imports change, build the affected Lean owner and its framework/research consumer. The audit does not call for deleting any checked Lean theorem merely because its runtime chart moves.
6. Confirm the wrapper source scan has no live names after the R2 cut, and retain `SparseOwnState` transition tests plus the documented wrapper transaction guards. Keep `SparseStandingSurface` and `live_current` covered by the app and all-target checks; do not infer that their “surface” name makes them the retired replay API.

The sparse transition test scope is one accepted `(position, FeltTerm)` deposited into one
current-local OWN REGISTER, before any integration into receiver standing. A zero resultant with
either winding arm nonzero stays occupied; release requires both resultant coordinates and both
arms to be zero. A release can narrow only when occupancy and all live founders lie in the exact
zero section of the narrower gauge. Sparse storage reserves at most the admitted deed count and
stores/visits only the live prefix, rather than allocating the receiver's `axis × axis` chart.
The existing body test `live_sparse_own_is_the_dense_register_without_the_axis_square` is the
executable resource witness; the new direct tests cover occupancy, narrowing and ranked parity.
The removed wrapper additionally checked `FeltEmission::hand_is_exact` and the admitted deed
extent before calling body state; those checks leave state untouched on refusal. They are wrapper
transaction boundaries (source: accepted emission stream; receiver: disposable replay chart), not
properties the body-level `(position, FeltTerm)` API can express. Preserve them here as historical
contract evidence. The body test does not claim a runtime refusal path for malformed wrapper
emissions.
