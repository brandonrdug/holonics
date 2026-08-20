//! Source-detached native rest and its bounded file-backed remount.
//!
//! The owners are deliberately separated: [`types`] carries the wire-facing vocabulary,
//! [`seal_stream`] composes admitted source material, [`manifest`] validates the sealed
//! continuation, and [`mounted`] owns bounded file access.  None of these owners conducts a
//! resident law; they only preserve the returned rest and its lineage.

mod manifest;
mod mounted;
mod seal_stream;
mod types;

pub use crate::operation_correspondence::NativeGraphIdentity;
pub use manifest::{NativePayloadDescriptor, NativePopulationDescriptor, NativeRest};
pub use mounted::MountedNativeRest;
pub use types::{
    NativeLawIdentity, NativeOperation, NativeOwnerIdentity, NativePopulation,
    NativePopulationPayload, NativeRestInput, NativeRestRefusal, NativeSourceIdentity,
    NativeTestimony, NativeTopology,
};

/// Versioned wire prefix; an unrelated exterior form must never mount as a native rest.
/// Version two authenticates the exact manifest bytes before parsing them.
pub const NATIVE_REST_PREFIX: &[u8] = b"HOLONIC-NATIVE-REST\0\x02";

/// Framing is `prefix | little-endian manifest length | SHA-256(manifest) | manifest | payload`.
pub const MANIFEST_DIGEST_OCTETS: usize = 32;

#[cfg(test)]
mod tests;
