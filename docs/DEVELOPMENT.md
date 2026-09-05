# Building and developing Holonics

[definition] Use the root Cargo workspace for host Rust code. Device-only targets under
`accelerators/` keep their declared toolchains. Lean and Typst are verification/exposition
apparatus; they are not dependencies that schedule native inference.

## Rust and CUDA

The current native runtime uses the NVIDIA CUDA driver and toolkit. Make `nvcc` available on
`PATH` (this workstation uses `/opt/cuda/bin`). The kernel builder declares its architecture;
the driver can JIT the admitted PTX on the actual device. Model material is supplied separately.

```sh
export PATH=/opt/cuda/bin:$PATH
cargo check --workspace --lib --bins
cargo build -p holonics-workbench --bin holonics
target/debug/holonics --help
target/debug/holonics hna --help
```

For Rust clients, depend on the local `crates/holonics` package and use
`holonics::{hna,soulkiller,interop}`. The framework re-exports its implementation owners; it
does not create a second neural engine.

## Training and inference

```sh
target/debug/holonics hna infer /path/to/supported/model 'Explain holonics briefly.'
target/debug/holonics --format json hna train /path/to/supported/model sequence.json
target/debug/holonics --format json hna run request.json
target/debug/holonics hna inspect /path/to/native.rest
```

The [Athena guide](ATHENA.md) defines the request and artifact scopes. The current training
command consumes a continuing prefix sequence and returns a run receipt. A checkpoint/export
must not be inferred from that receipt.

## Formal work and papers

```sh
bash tools/lean_check.sh
bash tools/lean_check.sh ElementaryHolonics.RH.CriticalChart
```

[established-bounded; source-inspected] `formal/elementary-holonics/lean-toolchain` and
`lake-manifest.json` pin the formal dependencies. The default live engine umbrella and the
independent RH target are separate declared checks. `.lake/` caches remain ignored and retained.
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
