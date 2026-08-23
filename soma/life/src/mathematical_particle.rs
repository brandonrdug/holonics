//! M1's mathematical particle: one owner-local composition of standing exact owners.
//!
//! The particle is not a token, syntax tree, solver, or universal tensor value. It owns an M0
//! source/layout body, a ported operation complex, ordered typed words, port-local mathematical
//! typing, exact returns from existing owners, plural presentation/reconstruction fibres, and a
//! fixed typed sameness panel. Names and source spellings are lineage only; every attachment is
//! checked against an actual source occurrence, [`BoundaryId`], or [`EvolutionLawId`].

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::category::BoundaryId;
use holonic_engine::causal::EventId;
use holonic_engine::evolution::EvolutionLawId;
use holonic_engine::exact_owner_testimony::{
    ExactOwnerLicense, ExactOwnerOccurrence, ExactOwnerWitnessRefusal,
};
use holonic_engine::exact_value::ExactValue;
use holonic_engine::front_passage::ExactOwnerDeedReceipt;
use holonic_engine::interaction::{InteractionTemporality, OccurrencePort};
use holonic_engine::ported_operation::PortedOperationComplex;
use holonic_engine::quantity::Cast;
use holonic_engine::source_occurrence::BindingValidation;
use serde::Serialize;

pub use holonic_engine::exact_owner_testimony::{
    TensorSlot, TensorSlotRole, TensorVariance, TypedMathematicalBoundary,
};

use crate::mathematical_source::{ArtifactIdentity, CoTestimonyFiber, SourceLayoutTestimony};

mod active_transport;
mod admission;
mod intake;
mod lineage;
mod methods;
mod morphology;
mod multimodal_transport;
mod production_aperture;
mod recurrence;
mod retained_boundary;
mod sameness;
#[cfg(test)]
mod tests;
mod validation;

pub use active_transport::{
    return_active_transport_family, unchanged_control, ActiveOverlapNerveCell,
    ActiveTransportFamily, ActiveTransportOccurrence, ActiveTransportRefusal, ApparatusActivity,
    CellRun, CellSeparator, ExactResponseCochain, ExcitationPassage, FaceDifference,
    OpenTransportFibre, PressurePartitionActivity, PullbackLegAddress,
    RealizationPathParticipation, RealizationPhase, ReceiverHistoryAddress, ReceiverVisibleSupport,
    ResidencyActivity, ResidentStandingAddress, ResponseCochain, ResponseFaceReceipt,
    ReturnedActiveTransportFamily, SwitchingCalibration, UnchangedControl,
};
pub use admission::{
    OpenParticleFiber, ParticleAdmission, ParticleAdmissionInput, ParticleProposal,
    ParticleRefusal, PresentationFiberOccurrence, ProposalRefusal,
};
pub use intake::{MaterialOperationWorldTube, MaterialOperationWorldTubeInput, RecordFacePassage};
pub use lineage::{
    AddressedPassage, AddressedPassageOccurrence, PassageCompositeOccurrence, PassageEndpoint,
    PassageEquivalence, PassageRelationalShadow, PullbackJoinOccurrence,
};
pub use methods::{
    conduct_exact_linear, conduct_exact_linear_population, conduct_exact_quantity,
    ExactLinearOwnerReturn, ExactLinearStepReceipt, ExactQuantityOwnerReturn, PassageBranchId,
    TypedConstructionStep, TypedPassage, TypedPassageRef,
};
pub use morphology::{
    CausingForwardLineage, ConstitutiveActionChange, ConstraintReceiver, CultivationHolonomy,
    DynamicMorphologyCandidate, DynamicMorphologyError, DynamicMorphologyRest,
    ExactSupportSubcomplex, ExactWithdrawal, LocalMorphologyDelta, MorphologyCompatibilityReceipt,
    MorphologyDecision, ReconstructionFibreChange, ReturnedConstraintOccurrence,
    ReturnedReceiverAdjoint, WithdrawalReceipt, DYNAMIC_MORPHOLOGY_SCHEMA,
};
pub use multimodal_transport::{
    AnchorSection, ExactMediaAxis, ExactSpatialDeclaration, FamilyCorrespondenceFibre,
    JointMediaDecoder, JointMediaFibres, JointMediaStanding, MathematicalMediaPort,
    MediaCandidatePair, MediaNaturalitySquare, MediaPortDeclaration, MediaSourceFamily,
    MediaSourceInterior, MultimodalTransportRefusal, MultimodalTransportRest,
    NativeMediaConsequence, NativeMediaFibre, ProductLineage, SharedMediaContact,
    SharedMediaHigherCell, SharedMediaSubcomplex, SharedMediaVertex, UnmatchedMediaMember,
    JOINT_MEDIA_DECODER_SCHEMA, JOINT_MEDIA_FIBRES_SCHEMA, JOINT_MEDIA_STANDING_SCHEMA,
};
pub use production_aperture::{
    FactorizationStatus, FamilyCultivatedAthenaRest, FamilyCultivationDecoder,
    FamilyCultivationError, FamilyCultivationOccurrence, FamilyCultivationReconstruction,
    FamilyCultivationStanding, FamilyInquiry, FamilyWithdrawalReceipt, FamilyWorldReturn,
    FixedSectionPlate, LaboratoryAthenaError, LaboratoryAthenaRest, LaboratoryChronology,
    LaboratoryCommitOccurrence, LaboratoryComponentIdentity, LaboratoryDecision, LaboratoryInquiry,
    LaboratoryMorphologyDelta, LaboratoryPartition, LaboratoryPartitionKind,
    LaboratoryReconstructionBoundary, LaboratoryRouteDecoder, LaboratorySourceChange,
    LaboratoryStandingJunction, LaboratoryWithdrawalReceipt, LaboratoryWorldReturn,
    NativeAddressedConsequenceSpan, NativeApparatusReceipt, NativeCarrierChart, NativeCodec,
    NativeCodecProjection, NativeCollapsedPopulation, NativeConsequenceExterior,
    NativeConsequenceLineage, NativeConsequenceReconstruction, NativeConstraintCell,
    NativeDerivationTransport, NativeDeviceRouteFibre, NativeExactConsequenceFace,
    NativeGeneratorRelation, NativeGeometryCell, NativeGeometryVertex, NativeHexisAthenaRest,
    NativeHexisDecoder, NativeHexisError, NativeHexisInquiry, NativeHexisReconstruction,
    NativeHexisStanding, NativeMathematicalComplex, NativeMathematicalConsequence,
    NativeMathematicalConsequenceError, NativeMathematicalInquiry, NativeMathematicalPort,
    NativeMathematicalReceiver, NativeNaturalityReceipt, NativeOperationCell,
    NativeOrientedGenerator, NativeReturnedObstruction, NativeShortestSeparator,
    NativeSuccessorHistory, NativeTerrainAthenaRest, NativeTerrainCultivation,
    NativeTerrainDecoder, NativeTerrainError, NativeTerrainInquiry, NativeTerrainReconstruction,
    NativeTerrainStanding, NativeTerrainWithdrawalReceipt, NativeTerrainWorldReturn,
    ProductionAthenaError, ProductionAthenaRest,
    ProductionComponentIdentity, ProductionDecision, ProductionFibreBinding, ProductionInquiry,
    ProductionInquiryFace, ProductionInquiryPresentation, ProductionReceiver,
    ProductionReconstructionBoundary, ProductionStandingJunction, ProductionWithdrawalReceipt,
    ProductionWorldReturn, ReceiverHistoryFactorization, FAMILY_CULTIVATION_DECODER_SCHEMA,
    FAMILY_CULTIVATION_FIBRES_SCHEMA, FAMILY_CULTIVATION_STANDING_SCHEMA, FAMILY_INQUIRY_SCHEMA,
    LABORATORY_CHRONOLOGY_SCHEMA, LABORATORY_DECODER_SCHEMA, LABORATORY_FIBRES_SCHEMA,
    LABORATORY_INQUIRY_SCHEMA, LABORATORY_JUNCTION_SCHEMA, NATIVE_HEXIS_DECODER_SCHEMA,
    NATIVE_HEXIS_FIBRES_SCHEMA, NATIVE_HEXIS_INQUIRY_SCHEMA, NATIVE_HEXIS_STANDING_SCHEMA,
    NATIVE_MATHEMATICAL_CONSEQUENCE_SCHEMA, NATIVE_MATHEMATICAL_INQUIRY_SCHEMA,
    NATIVE_TERRAIN_DECODER_SCHEMA, NATIVE_TERRAIN_FIBRES_SCHEMA, NATIVE_TERRAIN_INQUIRY_SCHEMA,
    NATIVE_TERRAIN_STANDING_SCHEMA,
    PRODUCTION_FIBRES_SCHEMA, PRODUCTION_INQUIRY_SCHEMA, PRODUCTION_JUNCTION_SCHEMA,
};
pub use recurrence::{
    DerivationDecoderFibre, DerivationFibreMember, DerivationHigherCell, DerivationRecurrenceError,
    DerivationRecurrenceRest, DerivationSeparator, DerivationSourceEdge, DerivationSourceState,
    MaterialDerivationPassage, RequestedReceiverFactor, DERIVATION_RECURRENCE_SCHEMA,
};
pub use retained_boundary::{
    AddressedHistorySystem, BoundaryRecurrence, CultivatedActionLineage, HistoricalInterior,
    HistoricalSourceMember, LongHorizonBoundaryError, LongHorizonRetainedBoundary,
    OrderedBoundaryHolonomy, RetainedBoundaryDecoder, RetainedBoundaryFibres,
    RetainedBoundaryStanding, RicherReceiverReopening, LONG_HORIZON_DECODER_SCHEMA,
    LONG_HORIZON_FIBRES_SCHEMA, LONG_HORIZON_STANDING_SCHEMA,
};
pub use sameness::{
    ByteRelation, ByteRelationReceipt, CarrierEqualityRelation, ClassificationReceiverReturn,
    ClassificationRelation, DigestRelation, DoctrineEquivalenceRelation, MarkedDiagramRelation,
    OccurrenceRelation, PresentationRelation, ReceiverFaceRelation, ReceiverHistoryRelation,
    ReceiverHistoryReturn, RelationWitness, SimilarityReceiverReturn, SimilarityRelation,
    TypedSamenessFamily, TypedSamenessReceipt,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct CarrierId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BinderId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HypothesisId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BranchId(pub u64);

/// One declared carrier occurrence. The equality law is retained as lineage and never dispatched
/// by this module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarrierOccurrence {
    pub id: CarrierId,
    pub source_occurrences: BTreeSet<String>,
    /// The carrier identity exact-owner licenses bind at resident ports.
    pub owner_carrier: String,
    pub equality_law_lineage: String,
}

/// A binder is a relation between admitted source occurrences and actual ports/laws.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinderScope {
    pub id: BinderId,
    pub source_occurrences: BTreeSet<String>,
    pub ports: BTreeSet<BoundaryId>,
    pub laws: BTreeSet<EvolutionLawId>,
}

/// Mathematical typing attached to one real operation boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedPort {
    pub boundary: TypedMathematicalBoundary,
    pub carrier: CarrierId,
    pub unit_frame: Vec<Cast>,
    pub exposed: bool,
}

/// Arity and licenses belong to a law, not to a printed operator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedOperation {
    pub law: EvolutionLawId,
    pub input_arity: usize,
    pub output_arity: usize,
    pub hypotheses: BTreeSet<HypothesisId>,
    pub branches: BTreeSet<BranchId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HypothesisLicense {
    pub id: HypothesisId,
    pub source_occurrences: BTreeSet<String>,
    pub licenses: BTreeSet<EvolutionLawId>,
    pub branches: BTreeSet<BranchId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationWordStep {
    pub event: EventId,
    pub law: EvolutionLawId,
    pub inputs: Vec<BoundaryId>,
    pub outputs: Vec<BoundaryId>,
}

/// A general ordered operation word. It carries no implementation; existing exact owners enact
/// their own laws and return through [`TypedPassage`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedOperationWord {
    pub occurrence: String,
    pub steps: Vec<OperationWordStep>,
}

impl TypedOperationWord {
    pub fn found(
        occurrence: impl Into<String>,
        steps: Vec<OperationWordStep>,
        operation: &PortedOperationComplex,
    ) -> Result<Self, MathematicalParticleError> {
        let occurrence = occurrence.into();
        if occurrence.is_empty() || steps.is_empty() {
            return Err(MathematicalParticleError::EmptyWord);
        }
        for step in &steps {
            let occurrence = operation
                .shape
                .occurrences
                .get(&step.event)
                .ok_or(MathematicalParticleError::UnknownEvent(step.event))?;
            if occurrence.law != step.law {
                return Err(MathematicalParticleError::EventLawDisagrees {
                    event: step.event,
                    law: step.law,
                });
            }
            let law = operation
                .shape
                .laws
                .get(&step.law)
                .ok_or(MathematicalParticleError::UnknownLaw(step.law))?;
            if law.inputs != step.inputs || law.outputs != step.outputs {
                return Err(MathematicalParticleError::WordStepOutsideLaw(step.law));
            }
        }
        for pair in steps.windows(2) {
            if pair[0].outputs != pair[1].inputs {
                return Err(MathematicalParticleError::WordPortsDoNotCompose {
                    emitted: pair[0].outputs.clone(),
                    admitted: pair[1].inputs.clone(),
                });
            }
            let carries = pair[0]
                .outputs
                .iter()
                .enumerate()
                .zip(pair[1].inputs.iter().enumerate())
                .all(|((left_ordinal, boundary), (right_ordinal, _))| {
                    let source = OccurrencePort::output(pair[0].event, left_ordinal);
                    let target = OccurrencePort::input(pair[1].event, right_ordinal);
                    operation.shape.interactions.values().any(|interaction| {
                        interaction.temporality == InteractionTemporality::CarriesPrecedence
                            && interaction.boundary == *boundary
                            && interaction
                                .bonds
                                .iter()
                                .any(|bond| bond.source == source && bond.target == target)
                    })
                });
            if !carries {
                return Err(MathematicalParticleError::WordInteractionAbsent {
                    before: pair[0].event,
                    after: pair[1].event,
                });
            }
        }
        let layers = operation
            .fronts()
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
        let layer_of = layers
            .iter()
            .flat_map(|front| {
                front
                    .occurrences
                    .iter()
                    .map(move |event| (*event, front.depth))
            })
            .collect::<BTreeMap<_, _>>();
        for pair in steps.windows(2) {
            if layer_of[&pair[0].event] >= layer_of[&pair[1].event] {
                return Err(MathematicalParticleError::WordEventsDoNotAdvance {
                    before: pair[0].event,
                    after: pair[1].event,
                });
            }
        }
        Ok(Self { occurrence, steps })
    }

    pub fn source_port(&self) -> BoundaryId {
        self.steps[0].inputs[0]
    }

    pub fn target_port(&self) -> BoundaryId {
        self.steps[self.steps.len() - 1].outputs[0]
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnalyticBranch {
    pub id: BranchId,
    pub passage: PassageSelection,
    pub hypotheses: BTreeSet<HypothesisId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageSelection {
    pub(super) passage: String,
    pub(super) branches: BTreeSet<PassageBranchId>,
}

impl PassageSelection {
    pub fn posed(passage: impl Into<String>, branches: BTreeSet<PassageBranchId>) -> Self {
        Self {
            passage: passage.into(),
            branches,
        }
    }

    pub fn passage(&self) -> &str {
        &self.passage
    }

    pub fn branches(&self) -> &BTreeSet<PassageBranchId> {
        &self.branches
    }
}

/// A proposal is exterior testimony. It is never promoted into the admitted particle by being
/// present in this population.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueReceiverReturn {
    pub(super) occurrence: String,
    pub(super) port: BoundaryId,
    pub(super) source_occurrences: BTreeSet<String>,
    pub(super) values: Vec<ExactValue>,
}

impl ValueReceiverReturn {
    pub fn found(
        occurrence: impl Into<String>,
        port: BoundaryId,
        source_occurrences: BTreeSet<String>,
        values: Vec<ExactValue>,
    ) -> Result<Self, MathematicalParticleError> {
        let occurrence = occurrence.into();
        if occurrence.is_empty() || source_occurrences.is_empty() || values.is_empty() {
            return Err(MathematicalParticleError::MalformedValueReceiver);
        }
        Ok(Self {
            occurrence,
            port,
            source_occurrences,
            values,
        })
    }

    pub fn occurrence(&self) -> &str {
        &self.occurrence
    }
    pub fn port(&self) -> BoundaryId {
        self.port
    }
    pub fn values(&self) -> &[ExactValue] {
        &self.values
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RenderingReceiverReturn {
    pub(super) occurrence: String,
    pub(super) port: BoundaryId,
    pub(super) source_occurrences: BTreeSet<String>,
    /// The addressed rendering already admitted by M0. No bytes are regenerated here.
    pub(super) artifact_occurrence: String,
}

impl RenderingReceiverReturn {
    pub fn found(
        occurrence: impl Into<String>,
        port: BoundaryId,
        source_occurrences: BTreeSet<String>,
        artifact_occurrence: impl Into<String>,
    ) -> Result<Self, MathematicalParticleError> {
        let occurrence = occurrence.into();
        let artifact_occurrence = artifact_occurrence.into();
        if occurrence.is_empty() || source_occurrences.is_empty() || artifact_occurrence.is_empty()
        {
            return Err(MathematicalParticleError::MalformedRenderingReceiver);
        }
        Ok(Self {
            occurrence,
            port,
            source_occurrences,
            artifact_occurrence,
        })
    }

    pub fn occurrence(&self) -> &str {
        &self.occurrence
    }
    pub fn port(&self) -> BoundaryId {
        self.port
    }
    pub fn artifact_occurrence(&self) -> &str {
        &self.artifact_occurrence
    }
}

/// Construction input kept separate so proposal, refusal, and open-fibre populations cannot be
/// mistaken for admitted typing.
pub struct MathematicalParticleInput {
    pub occurrence: String,
    pub source_testimonies: Vec<SourceLayoutTestimony>,
    pub exterior_artifacts: Vec<ArtifactIdentity>,
    pub presentation_fibres: Vec<PresentationFiberOccurrence>,
    pub operation: PortedOperationComplex,
    pub carriers: Vec<CarrierOccurrence>,
    pub binders: Vec<BinderScope>,
    pub ports: Vec<TypedPort>,
    pub operations: Vec<TypedOperation>,
    pub hypotheses: Vec<HypothesisLicense>,
    pub passages: Vec<TypedPassage>,
    pub branches: Vec<AnalyticBranch>,
    pub linear_returns: Vec<ExactLinearOwnerReturn>,
    pub quantity_returns: Vec<ExactQuantityOwnerReturn>,
    pub value_receivers: Vec<ValueReceiverReturn>,
    pub rendering_receivers: Vec<RenderingReceiverReturn>,
    pub classification_receivers: Vec<ClassificationReceiverReturn>,
    pub similarity_receivers: Vec<SimilarityReceiverReturn>,
    pub receiver_history_returns: Vec<ReceiverHistoryReturn>,
    pub sameness: Vec<TypedSamenessFamily>,
    pub proposals: Vec<ParticleProposal>,
    pub refusals: Vec<ParticleRefusal>,
    pub open_fibres: Vec<OpenParticleFiber>,
    pub admission: ParticleAdmissionInput,
}

/// One continuing M1 particle. Intentionally not `Clone`: its M0 and operation bodies have one
/// owner, while alternative proposals own only their local testimony.
#[derive(Debug)]
pub struct MathematicalParticle {
    occurrence: String,
    source_testimonies: Vec<SourceLayoutTestimony>,
    exterior_artifacts: Vec<ArtifactIdentity>,
    presentation_fibres: Vec<PresentationFiberOccurrence>,
    operation: PortedOperationComplex,
    carriers: Vec<CarrierOccurrence>,
    binders: Vec<BinderScope>,
    ports: Vec<TypedPort>,
    operations: Vec<TypedOperation>,
    hypotheses: Vec<HypothesisLicense>,
    passages: Vec<TypedPassage>,
    branches: Vec<AnalyticBranch>,
    linear_returns: Vec<ExactLinearOwnerReturn>,
    quantity_returns: Vec<ExactQuantityOwnerReturn>,
    value_receivers: Vec<ValueReceiverReturn>,
    rendering_receivers: Vec<RenderingReceiverReturn>,
    classification_receivers: Vec<ClassificationReceiverReturn>,
    similarity_receivers: Vec<SimilarityReceiverReturn>,
    receiver_history_returns: Vec<ReceiverHistoryReturn>,
    sameness: Vec<TypedSamenessFamily>,
    proposals: Vec<ParticleProposal>,
    refusals: Vec<ParticleRefusal>,
    open_fibres: Vec<OpenParticleFiber>,
    admission: ParticleAdmission,
}

impl MathematicalParticle {
    pub fn occurrence(&self) -> &str {
        &self.occurrence
    }
    pub fn source_testimonies(&self) -> &[SourceLayoutTestimony] {
        &self.source_testimonies
    }
    pub fn exterior_artifacts(&self) -> &[ArtifactIdentity] {
        &self.exterior_artifacts
    }
    pub fn presentation_fibres(&self) -> &[PresentationFiberOccurrence] {
        &self.presentation_fibres
    }
    pub fn operation(&self) -> &PortedOperationComplex {
        &self.operation
    }
    pub fn carriers(&self) -> &[CarrierOccurrence] {
        &self.carriers
    }
    pub fn binders(&self) -> &[BinderScope] {
        &self.binders
    }
    pub fn ports(&self) -> &[TypedPort] {
        &self.ports
    }
    pub fn operations(&self) -> &[TypedOperation] {
        &self.operations
    }
    pub fn hypotheses(&self) -> &[HypothesisLicense] {
        &self.hypotheses
    }
    pub fn passages(&self) -> &[TypedPassage] {
        &self.passages
    }
    pub fn branches(&self) -> &[AnalyticBranch] {
        &self.branches
    }
    pub fn linear_returns(&self) -> &[ExactLinearOwnerReturn] {
        &self.linear_returns
    }
    pub fn quantity_returns(&self) -> &[ExactQuantityOwnerReturn] {
        &self.quantity_returns
    }
    pub fn value_receivers(&self) -> &[ValueReceiverReturn] {
        &self.value_receivers
    }
    pub fn rendering_receivers(&self) -> &[RenderingReceiverReturn] {
        &self.rendering_receivers
    }
    pub fn classification_receivers(&self) -> &[ClassificationReceiverReturn] {
        &self.classification_receivers
    }
    pub fn similarity_receivers(&self) -> &[SimilarityReceiverReturn] {
        &self.similarity_receivers
    }
    pub fn receiver_history_returns(&self) -> &[ReceiverHistoryReturn] {
        &self.receiver_history_returns
    }
    pub fn sameness(&self) -> &[TypedSamenessFamily] {
        &self.sameness
    }
    pub fn proposals(&self) -> &[ParticleProposal] {
        &self.proposals
    }
    pub fn refusals(&self) -> &[ParticleRefusal] {
        &self.refusals
    }
    pub fn open_fibres(&self) -> &[OpenParticleFiber] {
        &self.open_fibres
    }
    pub fn admission(&self) -> &ParticleAdmission {
        &self.admission
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MathematicalParticleError {
    EmptyParticle,
    EmptyWord,
    EmptySourceLineage,
    EmptyCarrierLaw(CarrierId),
    EmptyProposal,
    MissingExactOwnerReturn,
    OwnersDoNotSharePassage,
    BranchTerminalsNotDistinct,
    BranchTerminalsNotCoPresent,
    StagingConstructionInvalid(EventId),
    StagingDoesNotFeedBranch(EventId),
    StagingNotCoPresent,
    StagingDoesNotPrecedeBranches,
    MissingReceiverOrSameness,
    OperationShapeOpen,
    LicensedOccurrencesNotTotal,
    MalformedValueReceiver,
    MalformedRenderingReceiver,
    DuplicateCarrier,
    DuplicateBinder,
    DuplicateHypothesis,
    DuplicateBranch,
    DuplicateWord,
    DuplicatePassage,
    DuplicatePortTyping,
    DuplicateOperationTyping,
    UnknownSourceOccurrence(String),
    UnknownPort(BoundaryId),
    UnknownLaw(EvolutionLawId),
    UnknownEvent(EventId),
    EventLawDisagrees {
        event: EventId,
        law: EvolutionLawId,
    },
    UnknownCarrier(CarrierId),
    UnknownBinder(BinderId),
    BinderScopeDoesNotCover {
        binder: BinderId,
        port: BoundaryId,
    },
    UnknownHypothesis(HypothesisId),
    UnknownBranch(BranchId),
    UnknownWord(String),
    UnknownPassage(String),
    UnknownPassageBranch(PassageBranchId),
    WordStepOutsideLaw(EvolutionLawId),
    WordPortsDoNotCompose {
        emitted: Vec<BoundaryId>,
        admitted: Vec<BoundaryId>,
    },
    WordEventsDoNotAdvance {
        before: EventId,
        after: EventId,
    },
    WordInteractionAbsent {
        before: EventId,
        after: EventId,
    },
    PortTypingNotTotal,
    OperationTypingNotTotal,
    ArityDisagrees(EvolutionLawId),
    CarrierLicenseDisagrees(BoundaryId),
    AdmissionNotCausallyLinked,
    MissingExactOwnerLicense,
    MissingResidentPassageReceipt,
    RecordFacePopulationDisagrees,
    RecordFaceOccurrenceDisagrees,
    RecordFaceCarrierAbsent,
    RecordFaceContentDisagrees,
    ReceiverOccurrenceUnknown(String),
    MaterialOperationBoundaryIncomplete,
    AddressedPassageEmpty,
    AddressedOccurrenceKeyDisagrees,
    AddressedBoundaryOutsideLaw(EventId),
    PullbackOccurrenceUnknown(EventId),
    PullbackOccurrenceAbsent {
        left: EventId,
        right: EventId,
    },
    PullbackBoundaryDisagrees {
        left: EventId,
        right: EventId,
    },
    PullbackInteractionAbsent {
        left: EventId,
        right: EventId,
    },
    PassageEquivalenceNotBijective,
    PassageRebracketingInvalid,
    PassageEquivalenceMovesBoundary {
        left: EventId,
        right: EventId,
    },
    OwnerTypingDisagrees(BoundaryId),
    ConflictingBoundaryLicense(BoundaryId),
    ExactOwnerReturnDisagrees(EvolutionLawId),
    MalformedRefusal(String),
    MalformedProposalAttempt,
    TypingProposalDidNotRefuse,
    MalformedOpenFiber(String),
    MalformedRelation(&'static str),
    Method(String),
}

impl std::fmt::Display for MathematicalParticleError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for MathematicalParticleError {}
