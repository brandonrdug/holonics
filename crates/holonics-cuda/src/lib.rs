//! The CUDA realization of Holonics: the device driver (context, module, stream, allocation,
//! transfer completion and graphs; [`cuda`], [`ffi`]) and the resident HNN over the main library's
//! laws ([`hnn`]; rebuild step 5, `docs/plans/THE_REBUILD.md`).
//!
//! [`hnn`] holds the card's ownership of its context and buffers, its census and the launches
//! derived from it, the exact integer core (`kernels/exact_integer.cuh`), the lattice read and the
//! resident moment's ingest, each with its host-parity test, and, in its header, the device
//! execution-port plan: what of `holonics::hnn::ExecutionPort` runs resident, what stays on the
//! host, and what crosses the bus per window, together with the port records for #76.

pub mod cuda;
pub mod ffi;
pub mod hnn;

pub use cuda::{
    BorrowedContext, Context, CudaError, Device, DeviceAttribute, DeviceBuffer, Dim3, Event,
    Function, Graph, GraphCensus, GraphExec, LinearLaunch, MemoryInfo, Module, PinnedHost, Result,
    Stream,
};

/// The odd fold constant the smoke kernel's `atomic_fold` adds once per thread. 2^61 - 1.
pub const FOLD_CONSTANT: u64 = 2_305_843_009_213_693_951;
