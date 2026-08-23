//! R6's first bounded Athena production rest.
//!
//! This owner composes the admitted I5 and R2--R5 rests. It adds no solver, inference engine,
//! context manager, modality router, or scheduler. Its only new law is the addressed product
//! junction: one inquiry crosses the retained boundary, returned morphology, and joint-media
//! section; a genuine world return may change the junction; exact withdrawal restores the same
//! predecessor owner.

mod components;
mod family;
mod family_types;
mod inquiry;
mod laboratory;
mod laboratory_types;
mod rest;
mod types;
mod wire;

pub use types::{
    ProductionAthenaError, ProductionAthenaRest, ProductionComponentIdentity, ProductionDecision,
    ProductionFibreBinding, ProductionInquiry, ProductionInquiryFace,
    ProductionInquiryPresentation, ProductionReceiver, ProductionReconstructionBoundary,
    ProductionStandingJunction, ProductionWithdrawalReceipt, ProductionWorldReturn,
};
pub use family::{
    FAMILY_CULTIVATION_DECODER_SCHEMA, FAMILY_CULTIVATION_FIBRES_SCHEMA,
    FAMILY_CULTIVATION_STANDING_SCHEMA, FAMILY_INQUIRY_SCHEMA,
};
pub use family_types::{
    FamilyCultivatedAthenaRest, FamilyCultivationDecoder, FamilyCultivationError,
    FamilyCultivationOccurrence, FamilyCultivationReconstruction, FamilyCultivationStanding,
    FamilyInquiry, FamilyWithdrawalReceipt, FamilyWorldReturn, FixedSectionPlate,
};
pub use laboratory::{
    LABORATORY_CHRONOLOGY_SCHEMA, LABORATORY_DECODER_SCHEMA, LABORATORY_FIBRES_SCHEMA,
    LABORATORY_INQUIRY_SCHEMA, LABORATORY_JUNCTION_SCHEMA,
};
pub use laboratory_types::{
    LaboratoryAthenaError, LaboratoryAthenaRest, LaboratoryChronology,
    LaboratoryCommitOccurrence, LaboratoryComponentIdentity, LaboratoryDecision,
    LaboratoryInquiry, LaboratoryMorphologyDelta, LaboratoryPartition, LaboratoryPartitionKind,
    LaboratoryReconstructionBoundary, LaboratoryRouteDecoder, LaboratorySourceChange,
    LaboratoryStandingJunction, LaboratoryWithdrawalReceipt, LaboratoryWorldReturn,
};

pub const PRODUCTION_JUNCTION_SCHEMA: &str = "holonics.r6.production-junction.v1";
pub const PRODUCTION_FIBRES_SCHEMA: &str = "holonics.r6.production-reconstruction-boundary.v1";
pub const PRODUCTION_INQUIRY_SCHEMA: &str = "holonics.r6.production-inquiry.v1";

pub(super) const STANDING_MAGIC: &[u8; 8] = b"HPA6S001";
pub(super) const DECODER_MAGIC: &[u8; 8] = b"HPA6D001";
pub(super) const FIBRES_MAGIC: &[u8; 8] = b"HPA6F001";

#[cfg(test)]
mod tests;
