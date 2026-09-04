# Holonics command application

**Current interface:** 2026-09-04. The [Athena guide](../../docs/ATHENA.md) owns the native
training/inference contract; [interoperability](../../docs/INTEROPERABILITY.md) owns the artifact
and target-execution distinctions. This application composes those owners, not another engine.

## Command families

| Family | Implementation and scope |
|---|---|
| `holonics hna` | [established-bounded; implemented-exact] `run`, `inspect`, `infer` and `train` use the public `holonics::hna` seam over the full resident native operator or restricted SKE material. Ordered occurrences share one continuing session. |
| `holonics workspace` | [established-bounded; implemented-exact] Explicit-root persistent workspaces over the earlier snapshot/circulation artifact family. Their staged-return/commit protocol does not define HNA recurrence. |
| `holonics diagnostic` | [established-bounded; implemented-exact] Bounded owner inspection and probes, including exterior model configuration/index/ONNX charts. These are not production quality claims. |

[definition] A native run receipt, an earlier workspace snapshot, a package stored in
Safetensors/ONNX and a standard executable model are different artifacts. The current native
training command retains cultivation during the session and returns a receipt; it does not yet
persist the complete cultivated operator. `hna infer` returns one selected face, not a complete
chat response. The user guides name the exact implemented and open boundaries.

## Invocation and I/O

```sh
cargo build -p holonics-workbench --bin holonics
target/debug/holonics hna --help
target/debug/holonics --format json hna run request.json
target/debug/holonics workspace --help
target/debug/holonics diagnostic --help
```

[established-bounded; source-inspected] CLI arguments and structured `WorkbenchRequest` input
share `WorkbenchCommand` and the same runtime dispatch. Human, JSON and JSONL are projections of
the returned result. Existing workbench request/response/event schemas remain versioned; the
native result carries `org.holonics.hna.run.v1`. Running without arguments prints help, not a TUI.

[definition] Workspace mutations retain explicit-root storage and their existing atomic artifact
protocol. Diagnostics remain scoped observations. No old probe or archived validation script
becomes an acceptance criterion merely by appearing in the application history.

## Historical disposition

[historical] The September 1 workspace-first disposition and its WB/VWS receipts are retained in
[the prior application document](../../archive/operations/WORKBENCH_BEFORE_HNA_CONSOLIDATION.md).
The rejected Ratatui interface and removed per-event Gemma lift are not revived. The native HNA
command now supplies the previously missing full-operator application seam without claiming the
older workspace stores its device overlays.
