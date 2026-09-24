# M1 CUDA apparatus owner move

**Campaign:** #69, Rust cut. **Source:** `crates/holonic-mount` at parent `29e001c3`.

Moved the complete driver, allocation/transfer, committed PTX inclusion, device section layout,
launch laws, gates, and smoke binaries into `crates/holonics-cuda`. The Cargo package is
`holonics-cuda`; the Rust library is `holonics_cuda`. Engine and life depend on and import this
owner directly. There is no package alias or forwarding crate. The engine's NVCC build script,
CUDA kernels, resident-section implementation, and HNA implementation remain in their existing
owners for their later M1 cuts.

The committed PTX file, include path relative to the new crate, binary target names, section API,
and serialized/wire names are unchanged. Current source and owner references were updated; dated
R0 census rows and historical artifacts continue to describe their recorded snapshot.

## Verification

See `docs/VERIFICATION_RECEIPTS.tsv` for the focused CUDA-owner tests, locked workspace all-target
check, and package checks recorded for this commit.

## Scope boundary

This is the apparatus owner move only. It does not move resident HNN, engine kernels/build.rs,
life/HNA device implementations, or consolidate `body`, `soma-abi`, and `holonic-words` into the
planned portable leaf. GPU execution tests require an available CUDA device; compile and host
owner tests establish only their stated scope.
