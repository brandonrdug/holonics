//! Cross-codec material factorization, presented as one explicit owner facade.
//!
//! The implementation and its owner-local tests live in separate conventional modules.  The
//! reexport surface is intentionally explicit so callers retain the established API without
//! compatibility aliases or a second semantic owner.

mod core;

pub use core::{
    compare_material_factorizations, AddressedMaterialOccurrence, CausalOperationInvariant,
    CausalOperationWorldReturn, CausalPopulationLaw, CausalResultCell,
    ExteriorWorldReturnTestimony, HierarchicalOpticalConstraintBinding,
    HierarchicalOpticalMaterialCandidates, HierarchicalOpticalMaterialReturn,
    MaterialAffineCellTransportReceipt, MaterialAffineTransportReceipt, MaterialCandidateSection,
    MaterialFactorizationAperture, MaterialFactorizationError, MaterialFactorizationReturn,
    MaterialFactorizationStanding, MaterialIntegratedResidentApparatusReceipt,
    MaterialNativeFactorization, MaterialNaturalityReceipt, MaterialReceiverChart,
    MaterialReceiverChartAxis, MaterialReceiverInsufficiency, MaterialShortestSeparator,
    SituatedMaterialFactorSupport, MATERIAL_AFFINE_TRANSPORT_SCHEMA,
    MATERIAL_NATIVE_FACTORIZATION_SCHEMA, MATERIAL_RECEIVER_INSUFFICIENCY_SCHEMA,
};
