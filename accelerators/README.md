# Device-only targets

[definition] These device-only NVPTX targets have independent toolchains and are excluded from
the host Cargo workspace. Their committed PTX boundary artifacts remain available to the mount
owners. The native engine's main CUDA source remains beside its Rust owner under
`crates/holonic-engine/kernels/`. The former Vulkan/Rust-GPU surface path was retired: its host
crate had no caller and its SPIR-V artifact had no consumer outside that crate. Historical M4
measurements remain in their dated research records.

- `cuda-kernel/`: Rust NVPTX kernel target.
- `cuda-smoke/`: device boundary smoke target.

Read each target's own manifest/build instructions before rebuilding an artifact. Their
toolchain constraints do not define HNN's internal topology or constitute a second runtime.
