# Holonics command application: variant workspaces first, diagnostics second

**Date:** 2026-09-01
**Kind:** completed application disposition composed by
[`../../blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md).
**Current position:** NONE.

## 0. Corrected application boundary

[definition] The released `holonics` command is an exterior application over existing engine
owners. Its primary surface is the explicit-root variant workspace implemented by
[`../holonics-application`](../holonics-application) under the active VWS contract. The older
in-process Workbench runtime remains available only beneath `diagnostic`; it is not a model
workspace, model manager, inference product, or second machine ontology.

[counterexample; source-inspected; measured] WB0--WB6 returned callable low-level mechanisms and
two successive Ratatui presentations, but direct operator review showed that neither presentation
constituted a useful model-construction application. The UI body has therefore been deleted. Its
screenshots, render tests, and historical receipts do not schedule its restoration.

[definition] The current composition is:

```text
holonics workspace ...
  -> WorkspaceCommand
  -> VariantWorkspace at an explicit root
  -> existing Soulkiller / native circulation / cultivation / export owners
  -> WorkspaceReturn { workspace_root, current_snapshot, written_artifacts, value }

holonics diagnostic ...
  -> DiagnosticCommand
  -> bounded in-process WorkbenchRuntime
  -> WorkbenchEvent / WorkbenchResponse
```

## 1. Primary variant-workspace surface

[definition] The primary commands are `workspace create`, `inspect`, `lift-gemma-receipt`,
`import-snapshot`, `define-experiment`, `conduct`, `continue`, `stage-return`, `commit`, `decline`,
`evaluate`, and `export`. Every mutating command reopens the same explicit root, validates its
manifest and referenced artifacts, performs one owner composition, persists the complete return,
and advances `workspace.json` only after the new immutable artifacts exist.

[definition] The workspace lifecycle is:

```text
actual returned excitation receipt or native snapshot
  -> source-neutral generation 0
  -> resolved experiment
  -> persisted conduct / actual continuation
  -> staged exterior return
  -> commit or decline
  -> current / withdrawn / restored evaluation
  -> exact rested-inference export
```

[definition] `stage-return` and `commit` are separate operations. A staged candidate is testimony,
not current morphology. `commit` advances one generation; `decline` preserves the current snapshot
byte-exactly. Evaluation is non-mutating and compares conduct through current, latest-withdrawn,
and replay-restored morphology.

[definition] Workspace storage has no hidden default. Creation names one explicit root; subsequent
commands resolve `--root PATH` or use the current directory. `workspace.json`, lifts, snapshots,
experiments, runs, candidates, decisions, evaluations, exports, and export receipts all live
beneath that root. Successful returns display the absolute root, absolute current snapshot, and
every newly written absolute artifact path.

## 2. Structured I/O

[definition] `WorkbenchCommand` is the one serializable exterior request family. Its primary
variant is `Workspace`; `Diagnostic` is explicitly subordinate. Direct CLI arguments and a
versioned JSON `WorkbenchRequest` both execute through the same command owner. Human, JSON, and
JSONL formats are projections of the same response rather than distinct implementations.

[established-bounded; implemented-exact; source-inspected] The current wire schemas are
`org.holonics.workbench.request.v3`, `org.holonics.workbench.response.v3`, and
`org.holonics.workbench.event.v4`. Running `holonics` without arguments prints high-level help and
exits successfully; it never opens a terminal UI.

## 3. Diagnostic boundary

[definition] `diagnostic status`, `capabilities`, `demo`, `athena`, `eros`, `soulkiller`, and
`engine` expose bounded owner inspection and mechanism probes. Diagnostic Athena sessions are
process-memory fixtures. Diagnostic Soulkiller inspection reads exterior configuration/index/ONNX
charts. Diagnostic Eros constructs bounded material mouths/atlases. None of these creates or
refines a persistent variant workspace.

[definition] A diagnostic probe remains a probe. Its output, repeated execution, exact bytes, or
human inspection does not grade qualitative intelligence and does not become a release gate unless
the direct user request or live roadmap explicitly says so.

## 4. Honest capability boundary

[established-bounded; implemented-exact; source-inspected; measured] The released application can
found a source-neutral Athena morphology from a complete returned Gemma excitation receipt or an
existing native snapshot; persist experiment circulation and staged cultivation across processes;
commit, decline, withdraw, replay, and compare structural conduct; and round-trip exact
rested-inference ONNX and Safetensors exports.

[open; source-inspected] Direct arbitrary model-directory execution/lift, qualitative
text/image/audio emission, and persistently configurable diffusion experiments remain open. The
bounded diagnostic demo, configuration inspection, and exact structural evaluation do not stand in
for those capabilities.

## 5. Historical WB receipts and disposition

[established-bounded; implemented-exact; source-inspected; measured] WB0--WB2 retain their bounded
grades for the serializable command/event protocol, low-level owner adapters, and CLI execution:
[`WB0`](../../research/records/2026-09-01_WB0_HOLONICS_WORKBENCH_SHARED_COMMAND_EVENT_PROTOCOL_RETURNED.md),
[`WB1`](../../research/records/2026-09-01_WB1_WORKBENCH_ATHENA_SESSIONS_COMMIT_DIFFUSION_SNAPSHOT_AND_EXPORT_RETURNED.md),
and
[`WB2`](../../research/records/2026-09-01_WB2_EROS_SOULKILLER_ENGINE_AND_CLI_RETURNED_ONE_EVENT_SURFACE.md).

[established-bounded; source-inspected; process-audit] WB3--WB6 remain superseded historical
evidence of two rejected
terminal-interface iterations and their local controls:
[`WB3`](../../research/records/2026-09-01_WB3_RATATUI_RENDERED_THE_SAME_WORKBENCH_COMMAND_EVENTS.md),
[`WB4`](../../research/records/2026-09-01_WB4_HOLONICS_WORKBENCH_CLI_RATATUI_RELEASED.md),
[`WB5`](../../research/records/2026-09-01_WB5_WORKBENCH_RETURNED_GUIDED_RESOURCES_CONTEXT_ACTIONS_AND_STANDARD_IO.md),
and
[`WB6`](../../research/records/2026-09-01_WB6_WORKBENCH_RETURNED_SESSION_FIRST_TYPED_RECEIPTS_AND_SCROLLABLE_DIFFUSION.md).
Their render/UI pass claims retain only the evidence they actually measured; they no longer describe
the released source tree or product boundary.

[definition] This file is descriptive application context, never a construction scheduler. The
sole current order and position remain the root roadmap and construction state.
