# R2 workspace and workbench owner edge

Source-backed disposition for the `holonics-workspace` edge in R2. This is an owner audit, not a
retirement authorization or implementation. The source snapshot inspected was the R2 surface tip.

## Finding

`holonics-workspace` is application persistence and orchestration. It contains no independent
Holonic mathematical law. Its work is to call existing HNN/circulation operations and persist their
receipts and state in a filesystem workspace. Its natural target is a private workbench module,
such as `applications/holonics-workbench/src/workspace/`, rather than the main `holonics` library.
The latter should own mathematical objects and reusable computation; explicit filesystem roots,
CLI workflow, manifests and artifact paths belong at the application boundary.

The workspace crate's direct dependencies show the current ownership split:

| Dependency | Current workspace use | Migration blocker |
|---|---|---|
| `holonics-hna` | `addressed_ingress`, `AthenaAlphaApplication`, remount/conduct/continue/stage/commit/decline/snapshot operations | HNN's backend-neutral and CUDA owners have not yet replaced the current package owner. Preserve its consuming operation while the HNN move is done. |
| `holonic-engine` | `NativeInferenceAddress`, `NativeInferenceRequest`, `ReceiverId`, `EventId` | These are engine-owned application/native types today; R2 must resolve their target owners before removing engine dependency. |
| `life` | circulation snapshots/boundaries, world face/stage, cultivation candidate/commit/decline, morphology artifact/manifest and ONNX/Safetensors export | Workspace persistence cannot be moved intact until the `life::native_intelligence` owners and their wire types have been dispositioned. |
| filesystem/Serde | explicit-root artifact store, manifest and run records, JSON receipts | Application concerns; these can move into workbench without entering `holonics`. |

The workbench is the only Rust crate consumer of `holonics-workspace`: its manifest has the path
dependency, and `src/adapters/workspace.rs` imports `VariantWorkspace` and `WorkspaceReturn`. The
CLI defines `WorkspaceCommand` in `src/command.rs`, parses its verbs in `src/cli.rs`, and dispatches
through `src/runtime.rs` to `adapters::workspace::execute`. The adapter translates each command
into one workspace operation and returns an `AdapterReturn`. `tests/workspace_cli.rs` exercises the
public command path; `tests/adapters.rs` and CLI unit tests cover adjacent protocol/parse behavior.
There are no other Rust call sites in the repository.

## API and persisted charts

The crate-root public API in `crates/holonics-workspace/src/lib.rs` exports:

- `ApplicationError`.
- Evaluation: `BoundaryEvaluation`, `VariantEvaluationReceipt`.
- Manifest: `ArtifactKind`, `ArtifactReference`, `CompletedRunReference`, `CurrentVariant`,
  `ExperimentReference`, `LiftReference`, `RunReference`, `VariantWorkspaceManifest`,
  `VARIANT_WORKSPACE_SCHEMA`.
- Workspace: `VariantExperimentSpec`, `VariantRunBoundary`, `VariantRunRecord`,
  `VariantRunState`, `VariantWorkspace`, `VariantWorkspaceInspection`, `WorkspaceReturn`,
  `VARIANT_EXPERIMENT_SCHEMA`, `VARIANT_RUN_SCHEMA`.

`VariantWorkspace` exposes `create`, `open`, `root`, `manifest`, `inspect`, `import_snapshot`,
`define_experiment`, `conduct`, `continue_active`, `stage_world_return`, `commit`, `decline`,
`evaluate` and `export`. `VariantWorkspaceManifest` exposes `empty`, `allocate`, `validate` and
`artifacts`. `WorkspaceExportReceipt` and `WORKSPACE_EXPORT_SCHEMA` are public within the private
`workspace` module but are not re-exported by `lib.rs`.

The crate emits/reads these persisted charts:

| Chart | Shape/role |
|---|---|
| `workspace.json`, schema `org.holonics.variant-workspace.v1` | `VariantWorkspaceManifest`: current snapshot/morphology, lift and experiment references, active/completed runs, evaluations, exports, capability notes and ordinal. |
| Experiment JSON, `org.holonics.variant-experiment.v1` | Stable name plus resolved native ingress address and receiver. |
| Run JSON, `org.holonics.variant-run.v1` | Predecessor snapshot, boundary history and tagged `Boundary` / `Candidate` / `Committed` / `Declined` state. |
| Evaluation JSON, `org.holonics.variant-evaluation.v1` | Current, withdrawn and replay-restored boundary readings and exactness/separation flags. |
| Export receipt JSON, `org.holonics.workspace-export.v1` | Generation, codec, media type/opset, receiver family, round-trip result and artifact reference. |
| Native snapshot/boundary/candidate/commit/decline JSON | Current `life` wire types written as workspace artifacts; snapshots are also accepted by `import_snapshot`. |
| ONNX/Safetensors files | Exported package containers emitted by `export`. |

`ArtifactStore` enforces explicit-root path containment, refuses traversal/symlink escapes and
immutable-artifact overwrite, and replaces mutable JSON control files via temporary write and
rename. This is useful app policy, not a mathematical law. `workspace.json` is the live manifest
filename; the crate README's documented `runs/run-N` layout is stale relative to code, which
currently writes run artifacts under `.local/runs/run-N`.

## §0.2 reader constraint

The restructure plan's §0.2 says every old save-format reader goes: old saved artifacts are
superseded prototypes, with no legacy decoder. Therefore an intact file move must not retain
compatibility readers for these formats. In particular:

- `VariantWorkspace::open` decodes the v1 `workspace.json`, referenced v1 run records and
  experiment specs, plus current snapshot/package and active boundary data.
- `import_snapshot` decodes the existing serialized `NativeCirculationSnapshot` wire.
- `commit` reads the persisted cultivation candidate; evaluation reads and replays the current
  snapshot/commit data; export reads `snapshot.package_wire` as a `NativeMorphologyArtifact`.
- Reopening active runs and evaluating withdrawn/restored generations depends on those persisted
  charts, not merely on writing them.

Do not preserve those decoders under the moved crate-private module or hide them behind renamed
aliases. If equivalent workflow persistence is still a desired product capability, define its
current format in a separately scoped construction with explicit new-format ownership; it is not
a compatibility exception to §0.2. Otherwise retire the workspace command and its workflow tests
along with the crate.

## Smallest target routes

### Preserve the current command surface, subject to §0.2

After R2 migrates the required `life` and HNN/native type owners, move the workspace source into a
private workbench module, switch the adapter to `crate::workspace`, remove the crate from the
workspace and workbench dependencies, and keep the existing `WorkspaceCommand` / CLI/runtime
dispatch. First remove all superseded-format readers and adjust workflow behavior/tests to the
newly authorized current-format contract. This preserves command names only where their behavior
has a valid current owner and format; it does not justify old-format reopening or import.

### Retire the command as part of old persistence

If the saved-workspace capability itself is superseded, remove `WorkspaceCommand`, CLI subcommands,
runtime dispatch, the adapter, integration tests, crate member and stale docs together. Do not leave
a public command whose only implementation depends on readers retired under §0.2.

Neither route moves the code into `holonics`. The decision to retain a new persistent application
workflow is a product/construction choice, while the current crate's classification as app-level
is clear from its operations and direct consumer.

## Verification gates for whichever route is selected

For the caller-preserving route, after old-format readers have been removed or replaced by a
separately specified current format:

1. Move/retire `crates/holonics-workspace/tests/variant_workspace.rs` coverage into workbench tests
   corresponding to the behaviors still supported; do not retain tests that require old formats.
2. Run focused gates: `cargo test -p holonics-workbench --test workspace_cli`,
   `cargo test -p holonics-workbench --lib`, and
   `cargo check -p holonics-workbench --all-targets`.
3. Search for zero `holonics_workspace` / `holonics-workspace` references, remove the crate from
   workspace membership/dependency declarations, and update the repository map, architecture map
   and workbench documentation.

For command retirement, run the workbench library/CLI tests and all-target check after removing
the command path, plus the same zero-reference and workspace-membership checks. These are proposed
gates for the future R2 cut; no build was run during this audit.

## Source pointers

- [Restructure decisions, especially §0.2 and R2 phase](../THE_REPOSITORY_RESTRUCTURE.md)
- `crates/holonics-workspace/Cargo.toml`
- `crates/holonics-workspace/src/lib.rs`
- `crates/holonics-workspace/src/workspace.rs`
- `crates/holonics-workspace/src/manifest.rs`
- `crates/holonics-workspace/src/artifact.rs`
- `crates/holonics-workspace/src/evaluation.rs`
- `crates/holonics-workspace/tests/variant_workspace.rs`
- `applications/holonics-workbench/Cargo.toml`
- `applications/holonics-workbench/src/command.rs`, `cli.rs`, `runtime.rs`
- `applications/holonics-workbench/src/adapters/workspace.rs`
- `applications/holonics-workbench/tests/workspace_cli.rs`
- `docs/ARCHITECTURE_MAP.md` (persistent morphology-variant workspace entry)
- `docs/REPOSITORY.md` and `crates/README.md` (current layout references)
