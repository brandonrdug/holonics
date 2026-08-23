//! R6's first bounded Athena production rest.
//!
//! This owner composes the admitted I5 and R2--R5 rests. It adds no solver, inference engine,
//! context manager, modality router, or scheduler. Its only new law is the addressed product
//! junction: one inquiry crosses the retained boundary, returned morphology, and joint-media
//! section; a genuine world return may change the junction; exact withdrawal restores the same
//! predecessor owner.

mod components;
mod inquiry;
mod rest;
mod types;
mod wire;

pub use types::{
    ProductionAthenaError, ProductionAthenaRest, ProductionComponentIdentity, ProductionDecision,
    ProductionFibreBinding, ProductionInquiry, ProductionInquiryFace,
    ProductionInquiryPresentation, ProductionReceiver, ProductionReconstructionBoundary,
    ProductionStandingJunction, ProductionWithdrawalReceipt, ProductionWorldReturn,
};

pub const PRODUCTION_JUNCTION_SCHEMA: &str = "holonics.r6.production-junction.v1";
pub const PRODUCTION_FIBRES_SCHEMA: &str = "holonics.r6.production-reconstruction-boundary.v1";
pub const PRODUCTION_INQUIRY_SCHEMA: &str = "holonics.r6.production-inquiry.v1";

pub(super) const STANDING_MAGIC: &[u8; 8] = b"HPA6S001";
pub(super) const DECODER_MAGIC: &[u8; 8] = b"HPA6D001";
pub(super) const FIBRES_MAGIC: &[u8; 8] = b"HPA6F001";

#[cfg(test)]
mod tests;
