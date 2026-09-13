# Building and developing Holonics

[definition] Use the root Cargo workspace for host Rust code. Device-only targets under
`accelerators/` keep their declared toolchains. Lean and Typst are verification/exposition
apparatus; they are not dependencies that schedule native inference.

## Mathematical implementation and continuation

[project-postulate] Begin each increment from the requested consequence and the mathematical
unknown it exposes. Holonics' breadth supplies candidate constructions: exact preimages and
factorization, group/phase transport, recurrence and modal closure, adjoint/normalization,
boundary/current laws, analytic generators and source-specific physical models. Recover and
compose the relevant existing relations before introducing another runtime cabinet.

[definition] The working chain is

`requested consequence -> situated source and unknown -> reusable construction -> consuming operation -> returned comparison -> next inference or repair`.

This is a dependency account, not a sequence of universal approval stages. Exact construction,
empirical formation, native execution and application inspection may proceed together. The
source, coefficient ring, phase/clock, receiver, admitted future and cost chart state what a
particular construction means. Only the information required by its actual consumers is retained.

[project-postulate] The agent's continuing brief keeps six things visible: the human objective;
the latest corrections; the mathematical relation currently being constructed; the owners and
usable returns already available; the exact consuming map or obstruction; and the next check
whose outcome changes the construction. Carry this brief into a compaction or handoff in prose
or the existing position record. It is not a new public type, manifest or generated registry.
Links replace completed narratives, while the objective and causal reason for the next action
remain explicit. Read unchanged authority once and recover only what a new question requires.

[project-postulate] Progress is the returned mathematical or product consequence. A proof can
unlock a cheaper algorithm; an exact solver can return a coefficient family; a native application
can expose a previously hidden phase; an unsuccessful language reply can identify a wrong source
relation. State that content directly. A changed state, successful round-trip, test count or
larger exposure does not by itself explain the learned relation or establish usefulness.

[definition] Diagnose prolonged work at its actual consumer. Whole-prefix reevaluation calls
for an economical sufficient continuation. Dense future tuples call for a factor/modal form
when the requested receiver permits it. Early source acknowledgement calls for repairing the
source-to-successor transaction. A wrong conditional law calls for changed source/condition
construction. More state machinery, a generic cache or another theorem count does not resolve
all four. A returned failure should change the hypothesis, representation, owner or next check.

[project-postulate] Consolidate the construction into its mathematical owner and update its
consumers in the same increment. Generic matrix or polynomial inference belongs with the
existing algebra, not inside a fixed example. A public application invokes that owner and
declares its source, output and costs. Preserve compatibility only where there is an actual
consumer, and keep differences in source/ownership or wire semantics when they are material.

[definition] Repository-wide review means following the live roots, subject boundaries and
critical source-to-application maps, then repairing the in-scope contradictions found. Record
the inspected aperture and validation performed. It is not a claim that every theorem, archived
experiment, backend or external model was rerun. A fresh source census or universal validation
gate supplies no substitute for the requested construction.

## Rust and CUDA

The current native engine/HNN build is Linux/CUDA-bound, including generated PTX and CUDA
linkage. A Mac checkout does not yet provide an executable engine backend; see
[hardware and modality boundaries](HARDWARE_AND_MODALITY_BOUNDARIES.md) for the exact dependency
seam and MLX comparison. Repository documentation and exterior data tools are independent of
that native runtime. The current native runtime uses the NVIDIA CUDA driver and toolkit. Make `nvcc` available on
`PATH` (this workstation uses `/opt/cuda/bin`). The kernel builder declares its architecture;
the driver can JIT the admitted PTX on the actual device. Model material is supplied separately.

```sh
export PATH=/opt/cuda/bin:$PATH
cargo check --workspace --lib --bins
cargo build -p holonics-workbench --bin holonics
target/debug/holonics --help
target/debug/holonics hna --help
```

For Rust clients, the local `crates/holonics` package exposes `structure` and `geometry` even
with default features disabled. Default `native` also exposes `engine`, `hna`, `soulkiller`
and `interop`, preserving the existing runtime API. The [Rust framework guide](RUST_FRAMEWORK.md)
states the dependency and implementation boundaries. The facade re-exports its owners.

## Training and inference

```sh
target/debug/holonics hna infer /path/to/supported/model 'Explain holonics briefly.'
target/debug/holonics --format json hna train /path/to/supported/model sequence.json
target/debug/holonics --format json hna run request.json
target/debug/holonics hna inspect /path/to/native.rest
```

The [native guide](NATIVE_HNA.md) gives the current ground-up phase-session recipes. The
commands above use the earlier inherited-operator chart, whose campaign remains paused.
The [Athena guide](ATHENA.md) defines those request and artifact scopes. The current training
command consumes a continuing prefix sequence and returns a run receipt. A checkpoint/export
must not be inferred from that receipt.

## Formal work and papers

```sh
bash tools/lean_check.sh
bash tools/lean_check.sh ElementaryHolonics.RH.CriticalChart
```

[established-bounded; source-inspected] `formal/elementary-holonics/lean-toolchain` and
`lake-manifest.json` pin the formal dependencies. The default `ElementaryHolonics.Framework`
target presents the reusable mathematical subjects;
`ElementaryHolonics` is the complete research umbrella and RH targets may be checked independently.
The package-local `check.sh` forwards here without updating pinned dependencies. `.lake/` caches
remain ignored and retained.
Authored Typst work is under `research/papers/source/`; compile it when editing or using those
papers. It is not a required check for unrelated Rust work.

## Verification cadence

[definition] CUDA controls that measure allocation granularity require an isolated allocation
reading. Run the explicit resident-return controls with `--test-threads=1`; concurrent contexts
can invalidate that calibration before the numerical test starts. This is an observer/apparatus
condition, not a production worker limit or a reason to serialize independent native currents.

```sh
cargo test -p holonics-hna --lib hna
cargo test -p holonics-workbench --lib adapters::hna
cargo test --workspace --lib --bins --tests
cargo check --workspace --examples
```

[definition] The workspace commands above are appropriate for a workspace-wide source move;
ordinary changes use their affected owner tests. Supervise productive compilation and diagnose
an unfinished check before resuming it. Retain successful unaffected checks. The blanket gate,
document/index tools and source-size ledger are archived; do not recreate them or compile every
example/paper after each edit. Review source cohesion and verify behavior directly.

[definition] `CONSTRUCTION_STATE.md` records the current position and
`docs/plans/THE_ROADMAP.md` orders construction. AGENTS.md is the shared agent operating
contract; CLAUDE.md is its pointer. The [repository guide](REPOSITORY.md) explains historical
paths and backup recovery. Keep exact raw runtime evidence in dated research receipts, and
private reproducible working data in `.local/`.
