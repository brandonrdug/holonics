# Device-only targets

These builds are excluded from the host workspace; each pins its own toolchain.

`cuda-smoke/` is the `nvptx64-nvidia-cuda` crate of the driver smoke kernel (`fill_identity`,
`atomic_fold`). `build-ptx.sh` builds it for `sm_89` (RTX 4080 SUPER) and validates the result with
`ptxas`; the committed `mount_smoke_kernel.ptx` is what `crates/holonics-cuda`'s `mount-smoke`
binary includes, so the workspace builds without the nvptx target. The HNN's kernels are rebuilt
per law in rebuild step 5 ([THE_REBUILD](../docs/plans/THE_REBUILD.md)).
