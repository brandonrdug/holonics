//! Native ecology conduct, cultivation, membranes, and product-specific compositions.
//!
//! The owner composes the admitted native laboratory body, receiver-history quotient, anatomical
//! quotient, and terminal potential through exact shared occurrence lineage. No foreign executor
//! or source coordinate is present in its conduct closure.

mod conduct;
mod cultivated;
mod exchange_cultivation;
mod exchange_realization;
mod exchange_situated_product;
mod exterior_relational_witness;
mod granular_cultivation;
mod granular_potential;
mod laboratory_cultivation;
mod material_factorization;
mod material_source_realization;
mod membrane_acoustic;
mod membrane_cultivation;
mod membrane_interior;
mod membrane_optical;
mod membrane_radiation;
mod membrane_transport;
mod native_factor_deposit;
mod native_material_circulation;
mod native_relational_potential;
mod perspective_emanation;
mod product_receiver;
mod rest;
mod returned_difference_deposit;
mod scaffold_cultivation;
mod situated_cultivation;
mod situated_difference;
mod source_neutral_cold;
mod source_neutral_relational;
mod source_neutral_rest;
mod types;

pub use cultivated::{
    CultivatedConductConsequence, CultivatedConductPassage, CultivatedEcologyRest,
    CultivationMutation, CultivationWithdrawal, NativeCultivatedPotentialComplex,
    NativeCultivatedPotentialCoordinate, ResidentCultivatedEcology, WithdrawnNativeFactor,
};
pub use exchange_cultivation::{
    CompactBoundaryAssemblyReceipt, CompleteExchangeCultivationCover, ExchangeDefectBasisFace,
    ExchangeDefectSectionReceipt, SourceColumnAddress,
};
pub use exchange_realization::{
    CompleteExchangeNativeRealizationPassage, HistoryOnlyExchangeFront,
    HistoryOnlyExchangeOccurrence, NativeCandidateProductState, ReturnedExchangeSection,
    SealedNativeCandidateFront, SealedNativeCandidateSection,
};
pub use exchange_situated_product::{
    CompressedSituatedDifference, ExactExchangeFaceCurrent, ExchangeCandidateLineage,
    ExchangeGeneratorSquareReceipt, ExchangeProductAddress, ExchangeProductMaterial,
    ExchangeReturnedNativeSection, ExchangeSituatedLocal, ExchangeSituatedProduct,
    ExchangeSituatedProductError, K3PullbackBranch, MixedConstitutiveInteractionFamily,
    NativeReceiverConstitutiveForm, NativeStateExchangeCover, ReturnEventInterventionLocal,
    ReturnEventInterventionReceipt,
};
pub use exterior_relational_witness::{
    sever_source_bearing_ecology, transduce_source_neutral_exterior, ExteriorRelationalWitness,
    SourceNeutralExteriorIngressWitness, SourceNeutralSeveringError, SourceNeutralSeveringReceipt,
    EXTERIOR_RELATIONAL_WITNESS_SCHEMA, SOURCE_NEUTRAL_EXTERIOR_INGRESS_WITNESS_SCHEMA,
    SOURCE_NEUTRAL_SEVERING_RECEIPT_SCHEMA,
};
pub use granular_cultivation::{
    GranularAffineEcologyRest, GranularCultivationError, GranularCultivationReceipt,
    GranularCultivationWithdrawal, GranularEcologyRest, GranularFactorLineageProjection,
    GranularReturnedAffineEcologyRest, GranularSourceNeutralCompositionReceipt,
    RecurrentGranularRelationalCellWithdrawal, RecurrentGranularReturnedAffineDifferenceWithdrawal,
    RecurrentGranularReturnedAffineEcologyRest, RecurrentGranularReturnedAffinePredecessor,
    GRANULAR_CULTIVATION_WITHDRAWAL_SCHEMA, GRANULAR_ECOLOGY_REST_SCHEMA,
    GRANULAR_FACTOR_LINEAGE_SCHEMA, GRANULAR_SOURCE_NEUTRAL_COMPOSITION_SCHEMA,
};
pub use granular_potential::{
    GranularAddressedHigherBoundaryFace, GranularBoundaryBranch, GranularBoundaryEmanation,
    GranularBoundarySupport, GranularExposureLineage, GranularExteriorPort,
    GranularExteriorProjectiveContext, GranularExteriorProjectiveCurrent,
    GranularExteriorProjectiveFibre, GranularExteriorProjectivePassage, GranularFactorAction,
    GranularFactorCurrent, GranularFactorFace, GranularFactorGenerator, GranularFactorReceiver,
    GranularHigherBoundaryFace, GranularNativeProjectiveCurrent,
    GranularQuadraticMomentContextAxis, GranularReceiverActionCurrent, GranularReconstructionNode,
    GranularSignedFactorCurrent, MountedNativeGranularPotential, NativeGranularPotential,
    NativeGranularPotentialBuilder, NativeGranularPotentialError, NATIVE_GRANULAR_POTENTIAL_SCHEMA,
};
pub use laboratory_cultivation::{
    AdmittedAffineLaboratoryRestWitness, AdmittedReturnedAffineLaboratoryRestWitness,
    AffineLaboratoryAblationAtlas, AffineLaboratoryCellWithdrawal, AffineLaboratoryCultivatedRest,
    AffineLaboratoryCultivationWithdrawal, LaboratoryCellAffineSection, LaboratoryCultivationError,
    LaboratoryCultivationReceipt, LaboratoryCycleFibreAddress, LaboratoryFactorCycleCorrespondence,
    LaboratoryParticipantEmanation, LaboratoryParticipantIngress,
    RecurrentReturnedAffineDifferenceWithdrawal, RecurrentReturnedAffineLaboratoryRest,
    RecurrentReturnedAffinePredecessor, ResidentAffineLaboratoryEcology,
    ResidentRecurrentAffineLaboratoryEcology, ReturnedAffineLaboratoryDifferenceWithdrawal,
    ReturnedAffineLaboratoryRest,
};
pub use material_factorization::{
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
pub use material_source_realization::{
    realize_material_source, MaterialSourceBoundaryDefect, MaterialSourceBoundaryWorldReturn,
    MaterialSourceCodec, MaterialSourceRealization, MaterialSourceRealizationError,
    MaterialSourceRevisionReceipt, MATERIAL_SOURCE_REALIZATION_SCHEMA,
};
pub use membrane_acoustic::{
    AcousticProductRest, AcousticRelationalCellWithdrawal, NativeAcousticAudibleProjection,
    NativeAcousticCultivationReceipt, NativeAcousticOrganCompositionReceipt,
    NativeAcousticPcm16Projection, NativeAcousticPotentialComplex,
    NativeAcousticProductionMorphology, NativeAcousticProductionSection,
    NativeAcousticProjectiveCurrent, NativeAcousticRadiationInput, NativeAcousticRadiationOrder,
    NativeAcousticReceiverChart, NativeAcousticReceiverCurrent, NativeAcousticSpectralIncidence,
    NativeAcousticStandingMutation, WithdrawnNativeAcousticProduction,
    NATIVE_ACOUSTIC_PRODUCTION_MORPHOLOGY_SCHEMA,
};
pub use membrane_cultivation::{
    DetachedMembraneCultivation, MembraneCultivationError, MembraneCultivationReceipt,
    StagedMembraneCultivation, DETACHED_MEMBRANE_CULTIVATION_SCHEMA, MEMBRANE_CULTIVATION_SCHEMA,
};
pub use membrane_interior::{
    AffineMembraneCochain, ConstitutiveFamilyContact, ExactLocalReconstructionFibre,
    FactorSupportBoundaryCurrent, FoundedInteriorContact, InteriorConstitutionReceipt,
    InteriorContactConsequence, MembraneInteriorError, MorphologyDerivedInterior,
    SharedSupportObstruction, MEMBRANE_INTERIOR_SCHEMA,
};
pub use membrane_optical::{
    NativeHierarchicalOpticalFormation, NativeHierarchicalOpticalFormationSection,
    NativeHierarchicalOpticalProjection, NativeOpticalAlternativeCover, NativeOpticalCell,
    NativeOpticalCellBounds, NativeOpticalChannelQuotient, NativeOpticalCultivationReceipt,
    NativeOpticalError, NativeOpticalOrganCompositionReceipt, NativeOpticalPotentialField,
    NativeOpticalProductionMorphology, NativeOpticalRasterProjection,
    NativeOpticalReceiverIntervention, NativeOpticalScaleCover, NativeOpticalStandingMutation,
    OpticalProductRest, OpticalRelationalCellWithdrawal, WithdrawnNativeOpticalProduction,
    NATIVE_OPTICAL_PRODUCTION_MORPHOLOGY_SCHEMA,
};
pub use membrane_radiation::{
    ExteriorActionCurrent, ExteriorRadiationSurface, FactoredReceiverHistoryGateReceipt,
    GeneratedPortProjectiveOccurrence, GeneratedPortProjectivePassage, GranularEmanativeResponse,
    GranularEmanativeTerminal, GranularProjectiveEmanativeReturn,
    GranularProjectiveRadiationReturn, GranularRadiationBranch, GranularRadiationSection,
    NativeOpenWorldTubeCurrentReturn, NativeOpenWorldTubeOrder, NativeOpenWorldTubeReceipt,
    NativeOpenWorldTubeReturn, NativeOpenWorldTubeTerminal, NativeOutwardPortReturn,
    NativeRadiationAperture, NativeRadiationError, NativeRadiationSection, NATIVE_RADIATION_SCHEMA,
    OPEN_WORLD_TUBE_RADIATION_SCHEMA,
};
pub use membrane_transport::{
    AdmittedMembraneStanding, ExactMembraneChartPassage, ExteriorOccurrenceAddress,
    ExteriorOccurrenceFibre, ExteriorOccurrenceTransducer, GranularMembraneStanding,
    MembraneConsequence, MembraneCrossingReceipt, MembraneError, MembraneOccurrence,
    MembraneReturn, MembraneStanding, MembraneTransductionError, MorphologyDerivedCurrentSection,
    NativeCausalMembrane, NativeMembraneBindingInsufficiency, NativeMembraneDefect,
    NativeMembraneInsufficiency, ReturnedMembraneDifference, MEMBRANE_CROSSING_SCHEMA,
};
pub use native_factor_deposit::{
    NativeCultivationMorphology, NativeFactorCandidateLimb, NativeFactorDeposit,
    NativeFactorDepositError, NativeFactorReconstructionFibre, NativeFactorReturnedLimb,
};
pub use native_material_circulation::{
    NativeCirculationAlternative, NativeCirculationConsequence, NativeCirculationError,
    NativeCirculationInsufficiency, NativeCirculationPassage, NativeCirculationRest,
    NativeCirculationStep, NativeRelationalStandingMutation, ResidentNativeCirculation,
    WithdrawnNativeRelationalStanding,
};
pub use perspective_emanation::{
    AddressedEmanationIngress, AddressedEmanationWorldReturn, EmanationCondensationReceipt,
    EmanationDeed, EmanationError, EmanationParticipant, EmanationParticipantFace,
    EmanationParticipantRole, EmanationSurface, EmanationVoice, NativePotentialCell,
    NativePotentialCellBody, NativePotentialCellKind, NativePotentialContact,
    NativePotentialContactKind, NativeProsePotentialComplex, PerspectiveChart,
    SituatedEmanationDifference, SituatedEmanationPassage,
};
pub use product_receiver::{
    ProductSituatedCurrentEmanation, ProductTechnicalHistoryEmanation, ResidentProductEcology,
};
pub use rest::{consume_dismantling_return, DepartedDismantlingLanes};
pub use scaffold_cultivation::{
    ReleasedScaffoldCultivation, ReturnedScaffoldInteraction, ScaffoldCultivatedConsequence,
    ScaffoldCultivatedRest, ScaffoldCultivationError, ScaffoldReleaseReceipt,
};
pub use situated_cultivation::{
    CompleteSituatedCultivationWithdrawal, LaboratoryCultivatedRest,
    RecurrentLaboratoryCultivatedRest, RecurrentLaboratoryPredecessor,
    RecurrentSituatedDifferenceWithdrawal, ResidentLaboratoryCultivatedEcology,
    ResidentSituatedCultivatedEcology, SituatedCultivatedConductReturn,
    SituatedCultivatedConductedFactor, SituatedCultivatedEcologyRest, SituatedCultivationBranch,
    SituatedCultivationError, SituatedCultivationWithdrawal, SituatedInheritedThreadWithdrawal,
    SituatedRadicalWithdrawal, SituatedReturnedDifferenceDeposit,
    SituatedReturnedDifferenceWithdrawal,
};
pub use situated_difference::{
    AffineReconstructionFibre, CausalAdjointStep, CausalAdjointStepInput, CausalAdjointWord,
    ComplexParametronDifference, DependentDifferenceChart, InverseTransportReceipt,
    ReturnedCovectorSection, SituatedDifferenceError, SituatedDifferenceInput,
    SituatedDifferenceSection,
};
pub use source_neutral_relational::{
    SourceNeutralAddressedResponsePairCurrent, SourceNeutralExteriorRealizationComplexSiteCurrent,
    SourceNeutralExteriorRealizationFactorCurrent, SourceNeutralExteriorRealizationMorphology,
    SourceNeutralExteriorRealizationOrientedFactorCurrent, SourceNeutralExteriorRealizationPassage,
    SourceNeutralExteriorRealizationSiteCurrent, SourceNeutralExteriorRealizationTargetCurrent,
    SourceNeutralExteriorRealizationTransition,
    SourceNeutralExteriorRealizationTransportContribution,
    SourceNeutralExteriorRealizationTransportObstruction, SourceNeutralPhasePopulation,
    SourceNeutralRelationalCell, SourceNeutralRelationalError, SourceNeutralRelationalFace,
    SourceNeutralRelationalIncidence, SourceNeutralRelationalMorphology,
    SOURCE_NEUTRAL_EXTERIOR_REALIZATION_MORPHOLOGY_SCHEMA,
    SOURCE_NEUTRAL_EXTERIOR_REALIZATION_PASSAGE_SCHEMA,
    SOURCE_NEUTRAL_RELATIONAL_MORPHOLOGY_SCHEMA,
};
pub use source_neutral_rest::{
    ResidentSourceNeutralEcology, SourceNeutralAcknowledgedExteriorCirculation,
    SourceNeutralAcousticMorphology, SourceNeutralCultivationBranch, SourceNeutralEcologyError,
    SourceNeutralEcologyRest, SourceNeutralExteriorCirculation, SourceNeutralExteriorCodecOrder,
    SourceNeutralExteriorCodecPassage, SourceNeutralExteriorCultivationReturn,
    SourceNeutralExteriorDeliveryReturn, SourceNeutralExteriorEmission,
    SourceNeutralExteriorInferenceReturn, SourceNeutralExteriorRadiation,
    SourceNeutralExteriorRadiationTerminal, SourceNeutralExteriorStep,
    SourceNeutralExteriorTerminalReturn, SourceNeutralFactorWindingConstitutiveChart,
    SourceNeutralFactoredRadiationSection, SourceNeutralInheritedThreadAblation,
    SourceNeutralNativeRadiationObstruction, SourceNeutralOpticalMorphology,
    SourceNeutralPendingExteriorEmission, SourceNeutralRadiationBranch,
    SourceNeutralRadicalConductPreservationReceipt, SourceNeutralRadicalDirectionAblation,
    SourceNeutralResidentRadiationSection, SourceNeutralReturnedCurrentDescent,
    SourceNeutralReturnedDeposit, SourceNeutralReturnedDifferenceReceipt,
    SourceNeutralReturnedDifferenceWithdrawal, SourceNeutralReturnedEcology,
    SourceNeutralReturnedExteriorCirculation, SourceNeutralSituatedDifferenceReceipt,
    SourceNeutralWindingBranchFunctional, SourceNeutralWindingDifference,
    SOURCE_NEUTRAL_ECOLOGY_REST_SCHEMA,
};
pub use types::{
    NativeBatchSectionAddress, NativeConductBatchPassage, NativeConductConsequence,
    NativeConductPassage, NativeConductedSection, NativeEcologyError, NativeEcologyRest,
    NativeSectionAddress, NativeThreadResidentBatchReturn, ReceiverHistoryRealizationPassage,
};

// K0 reachability boundary.
//
// The former H2/H3 experiment promoted hashed exterior text marks, surfaces, and adjacent
// incidences into a `NativeFeatureAtlas`, selected and retained source sentences, and flattened a
// multi-face lexicographic receiver into scalar interval incidence. Those sources and their
// receipts remain in the repository as counterexample evidence, but they are deliberately not
// modules of the live Athena product. A later construction must enter through the standing native
// occurrence/transport/morphology owners; it may not regain reachability by re-exporting the
// experimental atlas or cultivated-text types from here.
