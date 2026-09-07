# Building and developing Holonics

[definition] Use the root Cargo workspace for host Rust code. Device-only targets under
`accelerators/` keep their declared toolchains. Lean and Typst are verification/exposition
apparatus; they are not dependencies that schedule native inference.

## Rust and CUDA

[established-bounded; implemented-exact] The native phase session runs through CUDA on Linux
and direct Metal on macOS. The Metal realization covers the local constitutive fibre,
circulation and rechart operation, with the same native state/checkpoint owners. The shared complete
constitutive field and its rechart also run on Metal; that field has no rest/remount product yet.
The [field record](../research/records/2026-09-06_APPLE_ACOUSTIC_FIELDS_AND_HOLONIC_PROFILING.md)
documents its acoustic chart and execution profiler. Broader resident
operations and inherited-model readout remain CUDA-only and return named unsupported-operation
errors on Apple. The [platform specification](plans/HOLONICS_ON_APPLE_SILICON.md) records scope.

[definition] Linux development needs the NVIDIA driver and toolkit. Make `nvcc` available on
`PATH` (the desktop uses `/opt/cuda/bin`). The kernel builder declares its architecture; the
driver can JIT admitted PTX on the actual device. Model material is supplied separately.

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

## Apple silicon development

[established-bounded; process-audit] The September 6 MacBook setup installed Rust 1.98.1,
Lean 4.33.0 and 4.27.0 through elan, and MLX/MLX Metal 0.32.2 in
`.local/venvs/apple-silicon`. Xcode first-launch repair and Metal Toolchain download completed.
The [setup record](../research/records/2026-09-06_APPLE_SILICON_SPECIFICATION_AND_MAC_SETUP.md)
contains the M1 Pro apparatus and actual check scopes. The
[platform specification](plans/HOLONICS_ON_APPLE_SILICON.md) keeps MLX apparatus distinct from
the implemented native Metal phase backend.

[definition] For another Apple checkout, use a Rust release supporting this workspace and let
elan select the committed formal project versions. Do not update `lean-toolchain` or Mathlib
merely because a newer release exists. Lean remains separate verification apparatus.

```sh
rustup update stable
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
elan toolchain install leanprover/lean4:v4.33.0
elan toolchain install leanprover/lean4:v4.27.0
uv venv --python 3.12 .local/venvs/apple-silicon
uv pip install --python .local/venvs/apple-silicon/bin/python -r research/experiments/apple_silicon/requirements.txt
.local/venvs/apple-silicon/bin/python research/experiments/apple_silicon/check_mlx_device.py
cargo check -p relational-geometry --lib --locked
```

[definition] Install elan using the [official installer](https://lean-lang.org/install/manual/)
if absent. Xcode provides the SDK and native compilers; `xcodebuild -runFirstLaunch` completes
its system setup, and `xcodebuild -downloadComponent MetalToolchain` installs the separately
distributed Metal compiler when needed. Do not reinstall an already-working toolchain.

[established-bounded; measured] The public HNA library compiles on this Mac. The existing 28
engine phase tests and 15 public native-session tests passed against Metal, including exact
reference comparisons, refusal recovery, recharting, remounting and stream continuation.

```sh
cargo check -p holonics-hna --lib --locked
cargo test -p holonic-engine --lib native_ecology::constitutive_fibre::tests:: -- --include-ignored --test-threads=1
cargo test -p holonic-engine --lib native_ecology::constitutive_fibre::circulation:: -- --include-ignored --test-threads=1
cargo test -p holonic-engine --lib native_ecology::constitutive_fibre::field::tests:: -- --include-ignored --test-threads=1
cargo test -p holonics-hna --lib native:: -- --include-ignored --test-threads=1
cargo test -p holonics-workbench --test native_checkpoint_process -- --ignored --test-threads=1
```

[definition] Historical GPU tests still use `#[ignore]` to keep device initialization explicit.
The phase tests run on the selected platform backend. The field command covers the ordinary
Metal field and the refusal boundary for unported junctions. Desktop `6ef7bf9d` adds resident
conditional-current, whole-fibre receiver and paired/material junction tests that need their
corresponding Metal kernels; the complete constitutive test filter is therefore not a Mac parity
suite. Follow the [conditional-generator handoff](HARDWARE_AND_MODALITY_BOUNDARIES.md#conditional-generator-port-for-the-mac-workflow)
for that remaining port. CUDA-only tests remain unavailable on Mac.
Lean dependencies are fetched when relevant formal work requires them; no proof assistant enters
the native runtime.

[definition] Curated audio stays outside Git. Install the pinned experiment requirements above,
then run `research/experiments/apple_silicon/fetch_esc50.py` with the isolated Python interpreter.
It fetches WAV files without executing a dataset loader and records the Hugging Face revision,
source attribution, format and bytes in `.local/datasets/esc50/acquisition.json`.

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

## Apple sound applications

[established-bounded; implemented-exact] `cargo build -p holonics-workbench --bins` builds
`holonics`, `holonics-acoustic` and `holonics-speech`. The latter two use the same native phase
session; the [acoustic guide](ACOUSTIC_EXPERIMENTS.md) documents their source charts, digital
return law, complete checkpoints and cold receiver. The
[implementation record](../research/records/2026-09-06_APPLE_NATIVE_PHASE_AND_ACOUSTIC_COMPOSITION.md)
contains the measured Mac return. The Swift audio apparatus builds independently with
`applications/holonics-audio/build.sh`; no microphone is needed for the curated dataset recipes.
