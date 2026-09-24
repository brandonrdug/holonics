//! The CUDA realization of Holonics. It currently holds the device driver: context, module,
//! stream, allocation and transfer completion. The HNN's resident realization is rebuilt here
//! over the main library's laws (see `docs/plans/THE_REBUILD.md`).

pub mod cuda;
pub mod ffi;

pub use cuda::{
    BorrowedContext, Context, CudaError, Device, DeviceAttribute, DeviceBuffer, Dim3, Event,
    Function, Graph, GraphCensus, GraphExec, LinearLaunch, MemoryInfo, Module, PinnedHost, Result,
    Stream,
};

/// The odd fold constant the smoke kernel's `atomic_fold` adds once per thread. 2^61 - 1.
pub const FOLD_CONSTANT: u64 = 2_305_843_009_213_693_951;
