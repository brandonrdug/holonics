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
mod native_consequence;
mod native_consequence_types;
mod native_family;
mod native_family_types;
mod native_terrain;
mod native_terrain_types;
mod rest;
mod types;
mod wire;

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
    LaboratoryAthenaError, LaboratoryAthenaRest, LaboratoryChronology, LaboratoryCommitOccurrence,
    LaboratoryComponentIdentity, LaboratoryDecision, LaboratoryInquiry, LaboratoryMorphologyDelta,
    LaboratoryPartition, LaboratoryPartitionKind, LaboratoryReconstructionBoundary,
    LaboratoryRouteDecoder, LaboratorySourceChange, LaboratoryStandingJunction,
    LaboratoryWithdrawalReceipt, LaboratoryWorldReturn,
};
pub use native_consequence::{
    NATIVE_MATHEMATICAL_CONSEQUENCE_SCHEMA, NATIVE_MATHEMATICAL_INQUIRY_SCHEMA,
};
pub use native_consequence_types::{
    NativeAddressedConsequenceSpan, NativeApparatusReceipt, NativeCodec, NativeCodecProjection,
    NativeConsequenceExterior, NativeConsequenceLineage, NativeConsequenceReconstruction,
    NativeConstraintCell, NativeDerivationTransport, NativeDeviceRouteFibre,
    NativeExactConsequenceFace, NativeGeometryCell, NativeGeometryVertex,
    NativeMathematicalComplex, NativeMathematicalConsequence, NativeMathematicalConsequenceError,
    NativeMathematicalInquiry, NativeMathematicalPort, NativeMathematicalReceiver,
    NativeOperationCell, NativeReturnedObstruction,
};
pub use native_family::{
    NATIVE_HEXIS_DECODER_SCHEMA, NATIVE_HEXIS_FIBRES_SCHEMA, NATIVE_HEXIS_INQUIRY_SCHEMA,
    NATIVE_HEXIS_STANDING_SCHEMA,
};
pub use native_family_types::{
    FactorizationStatus, NativeCarrierChart, NativeCollapsedPopulation, NativeGeneratorRelation,
    NativeHexisAthenaRest, NativeHexisDecoder, NativeHexisError, NativeHexisInquiry,
    NativeHexisReconstruction, NativeHexisStanding, NativeNaturalityReceipt,
    NativeOrientedGenerator, NativeShortestSeparator, NativeSuccessorHistory,
    ReceiverHistoryFactorization,
};
pub use native_terrain::{
    NATIVE_TERRAIN_DECODER_SCHEMA, NATIVE_TERRAIN_FIBRES_SCHEMA, NATIVE_TERRAIN_INQUIRY_SCHEMA,
    NATIVE_TERRAIN_STANDING_SCHEMA,
};
pub use native_terrain_types::{
    NativeTerrainAthenaRest, NativeTerrainCultivation, NativeTerrainDecoder, NativeTerrainError,
    NativeTerrainInquiry, NativeTerrainReconstruction, NativeTerrainStanding,
    NativeTerrainWithdrawalReceipt, NativeTerrainWorldReturn,
};
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
