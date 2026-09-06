# Apple silicon specification and Mac development setup

[definition] This return establishes the Mac branch, deposited implementation contract and
development apparatus. It does not claim a completed Apple HNA backend or sound-learning product.
Source base: `b16e6bc0`; branch: `codex/apple-silicon`; date: September 6, 2026.
The [specification](../../docs/plans/HOLONICS_ON_APPLE_SILICON.md),
[roadmap](../../docs/plans/THE_ROADMAP.md) and
[position](../../CONSTRUCTION_STATE.md) separate this track from desktop Athena-alpha cultivation.

## Direct intent and review

[historical; process-audit] Brandon's direct request in Codex task
`01a078d8-09b0-7db0-a13a-a57765ca850c` describes importing the repository onto his MacBook,
the desktop's active Athena-alpha session with desktop conversation data, and asks for a review
so specifications can be deposited and the “MLX” branch constructed. He permits a more fitting
name and authorizes necessary toolchain installation. In the same task he selects
“Sound perception and generation, then speech.” These are paraphrased instructions except for
the quoted branch label and acoustic answer. No private desktop logs or datasets were transferred.

[established-bounded; source-inspected] The existing hardware/modality guide already articulates
the shared recurrence, native exactness, residency, source/receiver lineage, MLX comparison and
acoustic codec boundaries. The new contract makes device ownership, complete-operation parity,
public continuation, acoustic attachment and live I/O deliverables explicit. The primary agent
read the governing sources and integrated a bounded Luna source audit; agent testimony does not
establish a capability or supersede direct instructions.

[established-bounded; source-inspected] Exact source owners inspected at the base revision:

- `crates/holonics-hna/src/native.rs::with_native_session` directly mounts `ResidentReadout` and
  `ResidentSurface`; it owns the current phase session and emitted-handle delivery.
- `crates/holonic-engine/src/native_ecology/constitutive_fibre/circulation.rs` owns signed-word
  phase admission, the continuing ecology and historical source/receiver relation.
- `crates/holonic-engine/{Cargo.toml,build.rs}` and
  `src/{lib,cuda_refine,cuda_realizer_search,embedding_fiber,resident_section}.rs` expose the
  unconditional CUDA closure and non-Linux PTX generation skip.
- `crates/holonic-mount/src/{ffi,cuda}.rs` retain CUDA driver linkage;
  `native_spool/scaffold.rs` directly constructs `CudaRefineExecutor`.
- `crates/holonic-life/src/mathematical_source/acoustic.rs::ExactAcousticOccurrence` retains
  complete PCM16 samples and exact chronology beside a folded receiver section.
- `crates/holonic-life/src/synchronized_occurrence.rs` retains clock transports, timed receiver
  cells and declared interactions. Co-presence alone is not contact.
- `crates/holonic-life/src/native_intelligence/membrane_acoustic.rs::AcousticProductRest`
  embeds `RecurrentGranularReturnedAffineEcologyRest`; `NativeAcousticRadiationInput` consumes
  actual outward-port/open-world-tube returns. The current phase session does not return that type.
- `membrane_acoustic/potential_formation.rs` keeps exact native potential and an explicit cold
  floating/trigonometric PCM16 projection. A renderer does not establish native perception.

[definition] Consequently AS1 must factor the existing native device boundary; AS4 must attach
acoustic material and outward current to the current ecology. Neither a trait implementation in
the small parity vocabulary nor reusing an older acoustic body by name closes these relations.

## Machine and changes

[established-bounded; measured] Local system reports: arm64 MacBook Pro, Apple M1 Pro, 8 CPU
cores (6 performance/2 efficiency), 14 GPU cores, 16 GiB unified memory; macOS 26.5 build 25F71.
These identify apparatus, not measured power, usable-model capacity or semantic limits.

| Tool | Before | Returned setup |
|---|---|---|
| Rust/Cargo | 1.78.0; cannot parse the workspace's Rust 2024 edition | `rustup update stable` installed Rust/Cargo 1.98.1 for aarch64-apple-darwin; rustfmt, clippy and rust-src available. |
| Lean | elan/lean/lake absent from initial command lookup | elan installed; repository-pinned 4.33.0 and 4.27.0 installed. No global Lean default or formal-source change. |
| Xcode | Xcode 26.6 build 17F113 present; Metal shim present but toolchain absent | `xcodebuild -runFirstLaunch` repaired required system components; Metal Toolchain 17F109 downloaded; `xcrun metal --version` returned compiler 32023.883. |
| Python/MLX | Python and uv already available | Isolated CPython 3.12.13 environment with `mlx==0.32.2` and `mlx-metal==0.32.2`; no global Python packages changed. |
| Other tools | Git, Homebrew, ffmpeg and Typst already present | Retained; no unrelated upgrade, cache deletion or CMake/Ninja installation was needed for this setup. |

[established-bounded; process-audit] Initial `xcodebuild -downloadComponent MetalToolchain`
failed with exit 70: `IDESimulatorFoundation` expected a missing `DVTDownloads` symbol. The
tool's recommended `xcodebuild -runFirstLaunch` completed successfully; the subsequent component
download exited 0. The Metal compiler then executed. This was a repaired local installation
failure, not an HNA source defect. An unrelated Homebrew cask trust error occurred during broad
inventory; no trust was granted or cask changed because it was unnecessary for this work.

[definition] Reproduction commands are in [development](../../docs/DEVELOPMENT.md#apple-silicon-development).
Local installation/build logs remain under `.local/setup/apple-silicon/`; the small portable
device receipt below is committed without hardware identifiers or private source material.
Lean dependencies/caches are fetched when needed for actual proof work. No Lean kernel enters
the native application as part of this installation.

## Actual checks

[established-bounded; computational-witness] The committed
[MLX device probe](../experiments/apple_silicon/check_mlx_device.py) compiled and executed a custom
Metal kernel using two `u32` limbs for unsigned 64-bit addition, retaining a separate overflow
word. Eight declared values (zero, one, limb boundaries, signed boundary and maximum values)
produced 64 ordered operand pairs. A second GPU stream consumed the first result and added one
without intermediate host readback. All 128 returned results and per-dispatch overflow flags
matched Python integer observer arithmetic. Exit 0; the
[raw device receipt](2026-09-06_apple_silicon_receipts/mlx-device.json) retains the apparatus return.
The one-thread threadgroup is a smoke-test choice, not a production tuning rule.

[definition] This witnesses only the declared unsigned arithmetic and dependency case. It does
not implement signed rational operations, native incidence, current formation, rechart, lineage,
successor commit or checkpointing. It measures no HNA throughput or energy. The returned memory
recommendation is MLX/device testimony, not a reserved application budget or a semantic bound.

[established-bounded; process-audit] `cargo check -p relational-geometry --lib --locked` passed
in 6.17 seconds on the updated compiler. Both installed Lean versions returned their version;
the formal projects' committed pins remain unchanged. No proof/import was changed and no full
Lean build or unrelated CUDA regression was claimed.

[counterexample; process-audit] `cargo check -p holonics-hna --lib --locked` exited 101 after
reaching the engine: four missing generated PTX files (`exact_quartic_realizers`, `refine_shell`,
`exact_embedding_fiber`, `exact_resident_section`) and six unresolved imports of Linux-gated
`cuda_aperture`/`hardware_cover` from the resident, embedding, front-passage, partition and
token-invariance owners. This refutes a claim that the base checkout already compiles native HNA
on this Mac. Linkage was not reached, so no successful CUDA-free link or native run is claimed.
The source port is specified work, not repaired by toolchain installation or empty PTX stubs.

## Return boundary

[established-bounded; process-audit] AS0 returned specifications, branch setup, working Rust and
formal toolchain executables, repaired Metal development tools and a verified custom-kernel
apparatus probe. Current guides now link the Mac work and name the exact acoustic attachment.
No native runtime, proof or desktop cultivation source was modified by this return.

[open] AS1 native device factoring is next, followed by complete resident Apple parity and
public continuation. Acoustic perception/generation and subsequent speech remain the specified
product work. The desktop's Athena-alpha position is preserved as last known at the branch base;
this record makes no claim about unobserved progress in its running session.
