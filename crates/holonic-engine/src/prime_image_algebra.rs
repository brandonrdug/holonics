//! **The certified prime-image reading of an exact rational map** — owned by `holonic_core::prime_image_algebra`.
//!
//! [definition] Moved into the Holon core (`crates/holonic-core`) with the exact linear base it
//! belongs to; every public item is re-exported here at its existing path, explicitly, so each
//! `holonic_engine::prime_image_algebra::X` name, and any crate-root name it had, is unchanged. The module
//! documentation, the laws and their tests live with the owner.

pub use holonic_core::prime_image_algebra::{
    BadChart, DECLARED_IMAGE_EXTENT_CEILING, DECLARED_PRIME_CEILING, DECLARED_PRIME_FLOOR,
    DECLARED_PRIME_MODULUS_CEILING, DECLARED_PROFILE_RETRIES, ImageCost, ImagePlacement,
    IntegralPresentation, KernelCertificate, PRIME_IMAGE_SCHEMA, PrimeChart, PrimeImageRefusal,
    account, certified_fibre, certified_fibre_over, certified_kernel, certified_kernel_over,
};

#[cfg(test)]
mod tests;
