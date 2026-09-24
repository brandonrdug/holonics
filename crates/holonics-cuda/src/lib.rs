//! mount — CUDA Driver API boundary scaffolding for soma's headless production mount.
//!
//! Vulkan is convicted for production (headless Xid faults on the big genesis); the recut keeps the
//! law in Rust: `rustc` emits PTX for `nvptx64-nvidia-cuda`, and this crate loads/launches it over
//! the CUDA Driver API (libcuda). CUDA C is NOT selected. Nothing here is engine law — it is the
//! mount's boundary: a thin, safe wrapper and a smoke that proves the full path once.
//!
//! Layout: `ffi` holds the whole raw libcuda surface; `cuda` builds the safe typed layer
//! (`Device`, `Context`, `Module`, `Function`, `DeviceBuffer<T>`) with driver-named `Result`s.

pub mod cuda;
pub mod ffi;
// D1/D2 of the exact device law: a launch is a passage that owes a receipt, and exclusive access
// is a type. Paired with `ElementaryHolonics/Foundation/DeviceLaunchLaw.lean`.
pub mod launch_law;
// D3 of the exact device law: a declared incidence generates the gather, the residency and the
// scatter. Paired with `ElementaryHolonics/Foundation/SectionLayout.lean`.
pub mod section_layout;

pub use cuda::{
    BorrowedContext, Context, CudaError, Device, DeviceAttribute, DeviceBuffer, Dim3, Event,
    Function, Graph, GraphCensus, GraphExec, LinearLaunch, MemoryInfo, Module, PinnedHost, Result,
    Stream, VirtualDeviceBuffer, VirtualDeviceGrowth,
};
pub use launch_law::{
    Access, AliasAudit, ArgumentReceipt, ArgumentRequirement, ArgumentSpan, BlockConstraint,
    Coverage, DeferredReceipt, DeviceReadSpan, DeviceWriteSpan, DisjointPartition, Extent,
    FullyProvedReceipt, InFlightWrite, Lawful, LaunchClause, LaunchEvidence, LaunchLimits,
    LaunchReceipt, LaunchRefusal, LaunchRequirement, LaunchShape, LawfulLaunch, OpenWrite,
    PartitionClause, PartitionRefusal, PartitionedWrite, Partitioned, ProofScope, Residency,
    ScalarArgument, ScalarReceipt, ScalarRequirement, ScalarWidth, ScatterLaw, Settles,
    SharedRequirement, StreamIdentity, StreamRequirement,
};


/// The odd fold constant the `atomic_fold` kernel adds once per thread (mirrors the kernel's
/// `FOLD_CONSTANT`; kept here so the cpu's exact check needs no re-derivation). 2^61 - 1.
pub const FOLD_CONSTANT: u64 = 2_305_843_009_213_693_951;

#[cfg(test)]
mod tests {
    /// The committed PTX boundary artifact, checked cpu-side (no GPU) so the workspace test
    /// gates that the artifact is present, sm_89, and carries both entry points.
    const SMOKE_PTX: &[u8] = include_bytes!("../../../accelerators/cuda-smoke/mount_smoke_kernel.ptx");
    /// The CUDA smoke boundary. This check is deliberately static: it validates
    /// the committed artifact without loading a driver or rebuilding PTX behind the user's back.
    #[test]
    fn ptx_artifact_is_sm89_with_both_entries() {
        let text = std::str::from_utf8(SMOKE_PTX).expect("PTX is text");
        assert!(text.contains(".target sm_89"), "PTX must target sm_89");
        assert!(
            text.contains(".entry fill_identity"),
            "PTX must expose fill_identity"
        );
        assert!(
            text.contains(".entry atomic_fold"),
            "PTX must expose atomic_fold"
        );
        // The exact 64-bit atomic lowering the mount depends on.
        assert!(
            text.contains("atom.global.add.u64"),
            "expected atom.add.u64"
        );
        assert!(
            text.contains("atom.global.max.u64"),
            "expected atom.max.u64"
        );
    }
}
