# Device-only targets

[definition] These targets have independent Rust-GPU or NVPTX toolchains and are excluded from
the host Cargo workspace. Their committed SPIR-V/PTX boundary artifacts remain available to
the host owners. The native engine's main CUDA source remains beside its Rust owner under
`crates/holonic-engine/kernels/`.

- `rust-gpu/`: the prior Rust-GPU kernel and builder.
- `cuda-kernel/`: Rust NVPTX kernel target.
- `cuda-smoke/`: device boundary smoke target.

Read each target's own manifest/build instructions before rebuilding an artifact. Their
toolchain constraints do not define HNA's internal topology or constitute a second runtime.
