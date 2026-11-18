//! The engine's card realization (docs/plans/THE_CONSOLIDATION.md, D1 and §6): the driver (`cuda`, `ffi`), the card
//! (`hnn::card`) and the field's resident realization (`hnn::field`), with the field's kernels (`kernels/field.cu` and its two
//! headers). C3 of the consolidation (#603) moved them here from `crates/holonics-cuda` whole; that crate imports them back under
//! their old paths for as long as it stands. C5 cuts them as the law is (§6).

pub mod cuda;
pub mod ffi;
pub mod hnn;

pub use cuda::{
    Context, CudaError, Device, DeviceAttribute, DeviceBuffer, Dim3, Function, MemoryInfo, Module,
    Result, Stream,
};
