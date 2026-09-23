# R2/M1 edge map: `life::native_intelligence`

Read-only source audit for R2 and M1. This note identifies current edges and a first migration
slice; it is not a cut list. File names and public re-exports alone do not establish a live or dead
law. The governing disposition is [the repository restructure, §0.1–0.4 and §3](../THE_REPOSITORY_RESTRUCTURE.md).

## Current boundary and consumers

[`native_intelligence/mod.rs`](../../../crates/holonic-life/src/native_intelligence/mod.rs) is a
facade over dozens of internal modules, not a separable mathematical library. `life` also combines
engine/core, body/structure/language, ABI/membrane/mount, and serialization/I/O dependencies in
[`Cargo.toml`](../../../crates/holonic-life/Cargo.toml). Keep internal call chains in view when
assessing modules; a missing direct import is not proof of an orphan.

| Consumer | Current edge |
|---|---|
| `holonics-hna` | [`application.rs`](../../../crates/holonics-hna/src/application.rs) composes `NativeCirculationSession` into `AthenaAlphaApplication`: mount, conduct, continue, commit/decline, diffuse, snapshot/remount and commit withdrawal/replay. [`diffusion.rs`](../../../crates/holonics-hna/src/diffusion.rs) adapts a native scaffold to a diffusion law. [`receivers.rs`](../../../crates/holonics-hna/src/receivers.rs), [`world_application.rs`](../../../crates/holonics-hna/src/world_application.rs), and [`material_codec.rs`](../../../crates/holonics-hna/src/material_codec.rs) consume boundary/commit, world face, and material emission types. |
| `holonics-workspace` | [`workspace.rs`](../../../crates/holonics-workspace/src/workspace.rs) reads/mounts artifacts and snapshots and handles export, boundary and commit; [`evaluation.rs`](../../../crates/holonics-workspace/src/evaluation.rs) consumes boundaries/snapshots; [`manifest.rs`](../../../crates/holonics-workspace/src/manifest.rs) consumes morphology manifests. |
| Workbench | [`runtime.rs`](../../../applications/holonics-workbench/src/runtime.rs) orchestrates the HNA/workspace lifecycle. [`adapters/engine.rs`](../../../applications/holonics-workbench/src/adapters/engine.rs) and [`adapters/workspace.rs`](../../../applications/holonics-workbench/src/adapters/workspace.rs) bridge artifact and workspace APIs. |
| Tests | HNA `tests/alpha_matrix.rs`, `hna_material_cycle.rs`, `hna_receiver_matrix.rs`; workspace `tests/variant_workspace.rs`; workbench `tests/adapters.rs` and `tests/workspace_cli.rs` import public `life::native_intelligence` APIs. |

No direct `life::native_intelligence` references were found in `accelerators/`, `holonic-mount`,
or `holonic-engine`. Device execution is indirect: `life` calls resident APIs owned by
`holonic-engine`; the resident kernels/driver and their launch/section ownership move to
`holonics-cuda` under M1. For example,
[`source_neutral_relational/realization.rs`](../../../crates/holonic-life/src/native_intelligence/source_neutral_relational/realization.rs#L1036)
conducts addressed complex junctions in the resident apparatus, and
[`source_neutral_rest/resident.rs`](../../../crates/holonic-life/src/native_intelligence/source_neutral_rest/resident.rs)
mounts and evaluates resident structures. The life-side source/morphology binding is an adapter,
not the device kernel.

## Law versus Soma adapter

### Exact diffusion

[`circulation_diffusion.rs`](../../../crates/holonic-life/src/native_intelligence/circulation_diffusion.rs)
contains a useful separation point:

- Lines 88–189 validate exact positive capacities, nonnegative conductances, complete native
  incidence and boundary coverage, then translate spool/native IDs into an exact diffusion
  complex. This ID translation is Soma/scaffold adaptation.
- Lines 191–233 adapt standing to/from the engine law.
- Lines 244–355 execute the law through `NativeCirculationSession`, check conservation and the
  source/conduction/time-step energy balance, and assemble `NativeDiffusiveBoundary` with session
  configuration, receiver, generation and open-exterior testimony. This is a product boundary.

The reusable mathematical owner is `holonic_engine::diffusion::{DiffusionComplex,
ExactDiffusionLaw, DiffusionStanding, DiffusionEvent, DiffusionReceipt}`: exact constitutive
diffusion and its balance receipt. Under M1 it should be owned by
`holonics::physics::diffusion`; it should not depend on `life`, Soma schemas, or spool labels.
Keep `NativeDiffusionLaw` only as an HNA boundary adapter if the current Athena path remains.
Do not transfer `NativeCirculationEvent` or the native diffusion schema as core API.

### Situated generator and receiver

[`circulation_session.rs`](../../../crates/holonic-life/src/native_intelligence/circulation_session.rs)
is a move-owned product session over `NativeMorphologyArtifact`. Its `conduct` at lines 318–390
calls `conduct_native_inference` and constructs a product receipt containing plural future faces,
reconstruction fibres, lineage, actual successor requests, and open obligations. `continue_from`
at lines 393–409 accepts only a returned successor and checks its predecessor occurrence.

The core operation is the typed situated generator/action relation: source address/family,
requested receiver, emitted face, plural reconstruction fibre, and typed refusal when the requested
successor is false. That law and receiver-relative return belong in `holonics::hnn`, paired with
Lean. Session configuration strings, morphology packaging, product schema, snapshot/commit
history and exterior-world adapters do not become core Holon API. The source audit
[`2026-09-21_SITUATED_GENERATORS_RETAIN_MODES_AND_RELEASE_ACTION.md`](../../../research/records/2026-09-21_SITUATED_GENERATORS_RETAIN_MODES_AND_RELEASE_ACTION.md)
and generator-session record
[`2026-09-21_ORDERED_SOURCE_AND_PHASE_RECEIVING_ENTER_THE_PUBLIC_GENERATOR_SESSION.md`](../../../research/records/2026-09-21_ORDERED_SOURCE_AND_PHASE_RECEIVING_ENTER_THE_PUBLIC_GENERATOR_SESSION.md)
require preserving source, receiving phase/frame, and unresolved fibre through this extraction;
they do not license replacing it with a scalar output.

## Wire/storage and disposition

`NativeCirculationBoundary`, `NativeCirculationSnapshot`, `NativeMorphologyArtifact`, export and
manifest structures are consumed by the HNA/workspace/workbench lifecycle above. Their serialization
and I/O role is application/storage boundary, not the mathematical owner. The current snapshot
and artifact readers are in active callers (for example workspace remount in
[`workspace.rs`](../../../crates/holonics-workspace/src/workspace.rs#L241)); whether each is a
current format or a superseded save reader is **unresolved** in this bounded audit. Determine that
at the concrete producer and consumer before applying §0.2. Remove old-format readers; do not
preserve aliases or legacy decoders. No blanket retirement of the lifecycle follows from this
note.

Several implementation layers are internally reachable through `NativeCirculationSession`,
resident ecology, morphology cultivation, and package/export composition. A direct-import scan
cannot classify these as duplicates or orphans. This audit found no safely established duplicate
orphan within the subtree; record candidates individually with their internal call graph and law
owner before retiring.

## Smallest caller-preserving first slice and gates

Move the generic exact diffusion operator from `holonic_engine::diffusion` to
`holonics::physics::diffusion` as one M1 law slice. Its public API should retain the typed operator
and exact receipts:

```rust
DiffusionComplex::new(nodes, branches)
ExactDiffusionLaw::with_boundary(complex, boundary)
law.initial_standing(content)
law.enact(&standing, &DiffusionEvent { interval, source })
receipt.energy_balance()
```

Core IDs should be typed complex-node/branch IDs; no `NativeStateId`, `EventId`, spool string,
Soma schema, or HNA boundary belongs in the core signature. In the same slice, adapt
`holonics_hna::declared_diffusion_law` and `AthenaAlphaApplication::diffuse` if that app lane stays.
If its product event/boundary is retired, retire its caller and integration branch coherently
instead of retaining a forwarding API.

Focused evidence to preserve or relocate:

- `circulation_diffusion.rs::addressed_and_diffusive_conduct_share_one_event_family` currently
  checks exact conservation and energy closure, plus transfer factorization reuse.
- `circulation_diffusion.rs::incomplete_capacity_and_surface_free_ingress_refuse_or_leave_law_fixed`
  checks incomplete coverage refusal.
- `holonics-hna/tests/alpha_matrix.rs::exact_alpha_matrix_returns_the_complete_dynamic_lifecycle`
  exercises HNA diffusion wiring at lines 159–221; keep this as the product integration gate only
  while that boundary remains.
- The moved law needs focused checks for exact conservation residual, exact energy residual,
  invalid capacity/conductance/boundary refusal, and repeated transfer reuse.

This is a proposed first slice, not a report that code has moved or that these gates have run.
