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
