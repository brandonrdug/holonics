# R2 membrane owner and caller audit

Read-only source audit, 2026-09-23. No Cargo builds or tests were run. The audit follows `.agents/bin/prior-art 'membrane|SparseStanding|LiveCurrentMachine|live current|standing storage'`; its results are navigation evidence, so dispositions below are grounded in the owners and callers listed here.

## Decision

`soma-membrane` cannot be retired in isolation: `holonic-life` has production, test, and CUDA consumers of its live receive machine and its state types. Move the live execution cluster into the substantive `holonics` library and update the life consumers as part of the move. The generic `CausalMembrane` trait already belongs to `holonic-structure::membrane` and should be imported from its owner until the `holonics` merge consolidates that owner. Do not copy generic standing/descent laws into the runtime cluster.

`holon-plate` has one membrane-specific schema, ERST. Its purpose is to read/write a `.holon` plate whose form contains `LiveCurrentRestImage` bytes. Given the restructure rule against old save-format readers, retire ERST as a plate schema rather than preserving this reader in the new library. This disposition concerns the plate adapter; the runtime rest-image codec remains part of the moved live machine unless a separate, explicit construction decision retires it.

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
| `src/ranked_surface.rs`, `src/sparse_surface.rs`: `RankedFeltSurface`, `SparseFeltSurface` and related errors; re-exported in `src/lib.rs:58-60` | Felt/deed surface application charts, separate from the production standing surface | Search found their uses only among membrane modules/tests (`ranked_surface.rs:100,142-143` and their own implementations); no life or plate production caller appeared in the audited call search. **UNRESOLVED** pending full build-confirmed caller census: do not classify as retire solely from static search. If no external consumer is found, retire with their private substrate-only adapters; otherwise move the actual caller with the owner. |
| `holonic-structure/src/membrane.rs`: `CausalMembrane` trait (`:7-22`), re-exported by membrane `src/lib.rs:36` | Duplicate re-export, not membrane-owned implementation | `AgenticLanguageEcology` implements the trait (`holonic-life/src/agentic_language/ecology.rs:1686`); its documentation references the method at `:767`. Change the import to `holonic-structure` (or merged `holonics`) when removing the re-export. |

The manifest edges are explicit: `crates/holonic-life/Cargo.toml:23` and `applications/holon-plate/Cargo.toml:21`. The source search found no additional Cargo manifest consumers of `soma-membrane` beyond those two and the crate itself (archive excluded from live workspace).

## Exact `holon-plate` ERST cut

The ERST schema is specifically the plate adapter for membrane rest bytes, not a generic plate facility:

* `applications/holon-plate/src/schemas/current.rs:1-20,22-27` documents the `ERST` form owner and binds to `LiveCurrentRestImage`, `LiveCurrentMachine`, and `ContemporaryEvent`.
* `CurrentSchema::relight` at `current.rs:70-76` decodes/rest-mounts the form; `CurrentBody::form` at `:83-90` re-encodes it; `CurrentBody::census` at `:92-127` reads standing and lineage state; `CurrentBody::present` at `:129-160` decodes and applies a further event.
* `CurrentDeed::{encode,decode}` at `current.rs:165-184` is ERST-specific deed wire.
* Remove the ERST module/export in `schemas/mod.rs:9,25-28`, the `CURRENT_SCHEMA` registry entry in `registry.rs:19,23-29`, and the four-current-schema table/export in `lib.rs:135-139` as applicable. Keep generic `deposit`, `resume`, `inspect`, `seal`, `open`, census, and schema dispatch for the other schemas.
* Remove ERST branches and fixtures in `examples/emit_form.rs` (documented command at `:2,6`; current imports and dispatch at `:35,45-50,59,63,173`) and the ERST-only plate round-trip tests/fixtures in `src/tests.rs` and `tests/plate_mouth.rs` (current imports at `src/tests.rs:30-40`, `plate_mouth.rs:58-70`; current form creator at `plate_mouth.rs:135-146`). Preserve tests that exercise the generic plate container through other schemas.
* `schemas/rebase.rs` mentions ERST only as a comparison/example (`:98`), so update that prose when deleting the schema; it is not a runtime dependency.

This cut retires the ERST plate reader/deed workflow, not `LiveCurrentRestImage::{encode_native_bytes,from_native_bytes}` or its native rest image. Those are used by life rest/remount pathways (e.g. `holonic-life/src/synchronized_occurrence/ecology.rs:520`) and must travel with the machine unless their consumers are independently retired.

## Why move into `holonics`

The restructure’s target is a substantive, backend-neutral main `holonics` library that absorbs live `holonic-core`, `holonic-structure`, and the source-neutral engine. `soma-membrane` is not an optional backend: it owns the Rust live current/standing/constituent runtime used by `life`, including the CPU path and CUDA adapters. Moving that runtime with its concrete callers preserves the behavior while removing the historical `soma-membrane` package boundary. Retiring it without moving the machine would remove the current production owner; leaving it as a forwarding crate would violate the no-alias/no-forwarding rule. Keep CUDA execution code at its separate backend boundary and rebind it to the moved core types.

`holonic-core::standing` and Lean `Foundation/Standing.lean` give the general law that a retained quotient is sufficient for the admitted future. `holonic-core/src/restriction/descent.rs:27-37` names the corresponding checked Lean owners and runtime consumers. They do not implement the concrete sparse constituent tree or atomic event transition in `sparse_standing.rs` / `live_current.rs`; the latter is implementation of the consuming operation and belongs with the main Rust library.

## Verification gates for implementation

No gates were run for this read-only audit. On the eventual move/cut:

1. `rg` finds no live workspace `soma-membrane` manifest or source references after the package is removed; confirm the remaining path list with Cargo metadata/workspace membership.
2. Check `holonic-life` with all targets, including its CUDA-feature/device-independent compile paths as supported by the host; its CPU live-current, synchronized occurrence, causal language, and receiver/ecology tests must compile and pass.
3. Check `holon-plate` with all targets after ERST removal; generic plate tests and CLI tests must still pass for the retained schemas.
4. Verify the relocated Rust APIs retain the declared rest-image encode/decode version and round-trip behavior for current runtime callers; verify no ERST schema/deed reader remains in `holon-plate`.
5. If formal declarations/imports change, build the affected Lean owner and its framework/research consumer. The audit does not call for deleting any checked Lean theorem merely because its runtime chart moves.
6. Resolve the felt-surface rows only after inspecting all Rust callers and workspace target membership; until then leave their disposition explicitly unresolved.
