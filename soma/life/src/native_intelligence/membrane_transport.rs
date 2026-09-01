//! The singular exterior mouth of the cultivated Athena ecology.
//!
//! Apparatuses differ in retained geometry, not in the native law they select. Each admitted
//! source object moves through an [`ExteriorOccurrenceTransducer`] before type erasure; the
//! concrete object remains recoverable in the fibre and no media tag enters the native crossing.
use std::any::Any;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use holonic_engine::{
    cuda_refine::{
        ResidentAddressedCurrentPassageReturn, ResidentAddressedFactoredReceiverFrameReturn,
        ResidentCurrentAddress, ResidentFactoredMomentAddress,
        ResidentFactoredMomentFoundationReturn, ResidentFactoredMomentReceiverReturn,
        ResidentMembraneInteriorReturn, ResidentMembraneInteriorWord, ResidentQuadraticMomentFront,
        ResidentQuadraticMomentReturn,
    },
    native_spool::{
        NativeCollapsedFibre, NativeIncidenceTerm, NativeParametronCell, NativeSituatedSpoolBundle,
        NativeThread, NativeThreadOccurrence,
    },
    quantity::Dimension,
    receiver_history_compression::{
        membrane_addressed_factored_receiver_complex, AddressedFactoredIntegralReceiverComplex,
    },
    AddressedCurrentSection, BoundaryId, EventId, ExactComplexWaveCurrent, ExactUnitConicPhase,
    OccurrencePort,
};
use holonic_structure::CausalMembrane;
use num_bigint::BigUint;
use serde::Serialize;
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::mathematical_source::{
    ExactAcousticOccurrence, ExactOpticalOccurrence, HierarchicalOpticalPassage,
};
use crate::synchronized_occurrence::ExactSynchronizedOccurrenceFibre;

use super::{
    AddressedMaterialOccurrence, AffineLaboratoryCultivatedRest, LaboratoryCellAffineSection,
    LaboratoryFactorCycleCorrespondence, MaterialSourceRealization, MembraneInteriorError,
    MorphologyDerivedInterior, NativeConductedSection, NativeGranularPotential,
    NativeSectionAddress, ReceiverHistoryRealizationPassage, SituatedCultivationBranch,
};

mod binding;

pub const MEMBRANE_CROSSING_SCHEMA: &str = "soma-life.membrane-crossing.v1";

/// The minimal standing seen by the singular membrane.  Predecessor and cultivated successors
/// implement the same physical boundary without erasing their distinct type states.
pub trait MembraneStanding {
    fn validate_membrane_standing(&self) -> Result<(), String>;
    fn membrane_identity(&self) -> &str;
    fn membrane_ecology(&self) -> &NativeSituatedSpoolBundle;
    fn membrane_realization(&self) -> &ReceiverHistoryRealizationPassage;
    fn membrane_branches(&self) -> &[SituatedCultivationBranch];
    fn membrane_correspondences(&self) -> &[LaboratoryFactorCycleCorrespondence];
    fn membrane_affine_cells(&self) -> &[LaboratoryCellAffineSection];
}

/// A move-owned standing whose complete cold wire validation has already been admitted for this
/// exact identity.  Membrane constitution still checks every factor, cell, incidence, capacity,
/// and reconstruction fibre it consumes; it does not replay an unrelated whole-rest validation
/// before each hot deed.  The only constructors live beside the concrete admitted-wire witnesses,
/// so an arbitrary digest cannot manufacture this state.
pub struct AdmittedMembraneStanding<Standing> {
    standing: Standing,
    admitted_identity_sha256: String,
    complete_validation_receipt_sha256: String,
}

impl<Standing: MembraneStanding> AdmittedMembraneStanding<Standing> {
    pub(super) fn from_validated_wire(
        standing: Standing,
        admitted_identity_sha256: impl Into<String>,
        complete_validation_receipt_sha256: impl Into<String>,
    ) -> Result<Self, String> {
        let admitted_identity_sha256 = admitted_identity_sha256.into();
        let complete_validation_receipt_sha256 = complete_validation_receipt_sha256.into();
        if standing.membrane_identity() != admitted_identity_sha256
            || !is_sha256(&admitted_identity_sha256)
            || !is_sha256(&complete_validation_receipt_sha256)
        {
            return Err(
                "the admitted membrane standing does not match its validated wire receipt"
                    .to_owned(),
            );
        }
        Ok(Self {
            standing,
            admitted_identity_sha256,
            complete_validation_receipt_sha256,
        })
    }

    pub fn into_inner(self) -> Standing {
        self.standing
    }

    pub fn standing(&self) -> &Standing {
        &self.standing
    }

    pub fn complete_validation_receipt_sha256(&self) -> &str {
        &self.complete_validation_receipt_sha256
    }
}

impl<Standing: MembraneStanding> MembraneStanding for AdmittedMembraneStanding<Standing> {
    fn validate_membrane_standing(&self) -> Result<(), String> {
        if self.standing.membrane_identity() != self.admitted_identity_sha256
            || !is_sha256(&self.complete_validation_receipt_sha256)
        {
            Err(
                "the admitted membrane standing departed from its exact validation receipt"
                    .to_owned(),
            )
        } else {
            Ok(())
        }
    }

    fn membrane_identity(&self) -> &str {
        self.standing.membrane_identity()
    }
    fn membrane_ecology(&self) -> &NativeSituatedSpoolBundle {
        self.standing.membrane_ecology()
    }
    fn membrane_realization(&self) -> &ReceiverHistoryRealizationPassage {
        self.standing.membrane_realization()
    }
    fn membrane_branches(&self) -> &[SituatedCultivationBranch] {
        self.standing.membrane_branches()
    }
    fn membrane_correspondences(&self) -> &[LaboratoryFactorCycleCorrespondence] {
        self.standing.membrane_correspondences()
    }
    fn membrane_affine_cells(&self) -> &[LaboratoryCellAffineSection] {
        self.standing.membrane_affine_cells()
    }
}

/// A later morphology which owns fine receiver-history incidence in addition to the admitted
/// Athena membrane.  The predecessor standing does not pretend to carry this organ and therefore
/// keeps its already-admitted rest identity and wire unchanged.
pub trait GranularMembraneStanding: MembraneStanding {
    fn membrane_granular_potential(&self) -> &NativeGranularPotential;
}

/// One exact future-equivalent current derived from a complete native section front.
/// Equal sparse factor currents are condensed only after their carrying occurrences and complete
/// reconstruction fibres have been retained here.  The section is native morphology; no exterior
/// label, token, media kind, or caller-selected cell participates in its address.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MorphologyDerivedCurrentSection {
    pub current: AddressedCurrentSection,
    pub carrying_occurrences: Vec<NativeSectionAddress>,
    pub reconstruction_fibre: Vec<EventId>,
}

/// Cold address and reconstruction testimony shared by every exterior source object.
///
/// `cold_lineage` is deliberately absent from every contact and transport decision.  It may name
/// a locator, codec face, or delivery face for exterior audit without becoming native anatomy.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorOccurrenceAddress {
    pub occurrence: String,
    pub predecessor: Option<String>,
    /// A finite engine-address projection.  The full occurrence and moved source fibre remain the
    /// identity, so this coordinate is never treated as globally injective.
    pub event_projection: EventId,
    pub source_identity_sha256: String,
    pub incidence_identity_sha256: String,
    pub caused_population: u64,
    pub cold_lineage: Vec<String>,
    pub open_exterior: Vec<String>,
}

/// One moved concrete source object beside its cold address.
///
/// The erased object is not serialized and cannot be consulted by the hot law.  It is retained so
/// a receiver can recover the exact optical complex, PCM population, authenticated source body, or
/// material occurrence after the crossing rather than receiving a lossy common wrapper.
pub struct ExteriorOccurrenceFibre {
    address: ExteriorOccurrenceAddress,
    source: Box<dyn Any + Send>,
}

impl fmt::Debug for ExteriorOccurrenceFibre {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ExteriorOccurrenceFibre")
            .field("address", &self.address)
            .field("source_retained", &true)
            .finish()
    }
}

impl ExteriorOccurrenceFibre {
    pub fn address(&self) -> &ExteriorOccurrenceAddress {
        &self.address
    }

    pub fn source_is<T: Any>(&self) -> bool {
        self.source.is::<T>()
    }

    /// Recover the moved source object.  On a type mismatch ownership of the complete fibre is
    /// returned, so inspection cannot destroy it.
    pub fn recover<T: Any + Send>(self) -> Result<T, Self> {
        let Self { address, source } = self;
        match source.downcast::<T>() {
            Ok(source) => Ok(*source),
            Err(source) => Err(Self { address, source }),
        }
    }
}

/// Exterior-only conversion into the common mouth.  Implementations may authenticate and retain
/// source geometry; they cannot choose a native section, receiver, constitutive law, or response.
pub trait ExteriorOccurrenceTransducer: Any + Send + Sized {
    fn into_exterior_fibre(self) -> Result<ExteriorOccurrenceFibre, MembraneTransductionError>;
}

impl ExteriorOccurrenceTransducer for AddressedMaterialOccurrence {
    fn into_exterior_fibre(self) -> Result<ExteriorOccurrenceFibre, MembraneTransductionError> {
        let incidence = serde_json::to_vec(&(
            "soma-life.addressed-material-incidence.v1",
            &self.occurrence,
            &self.predecessor_occurrence,
            &self.payload_sha256,
            self.payload_octets,
        ))
        .map_err(|error| MembraneTransductionError::Source(error.to_string()))?;
        let address = ExteriorOccurrenceAddress {
            occurrence: self.occurrence.clone(),
            predecessor: self.predecessor_occurrence.clone(),
            event_projection: event_projection(&self.occurrence),
            source_identity_sha256: self.payload_sha256.clone(),
            incidence_identity_sha256: hex_sha256(&incidence),
            caused_population: self.payload_octets,
            cold_lineage: self.delivery_faces.clone(),
            open_exterior: self.open_exterior.clone(),
        };
        validate_exterior_address(&address)?;
        Ok(ExteriorOccurrenceFibre {
            address,
            source: Box::new(self),
        })
    }
}

impl ExteriorOccurrenceTransducer for ExactAcousticOccurrence {
    fn into_exterior_fibre(self) -> Result<ExteriorOccurrenceFibre, MembraneTransductionError> {
        let caused_population =
            u64::try_from(self.samples.len()).map_err(|_| MembraneTransductionError::Extent)?;
        let address = ExteriorOccurrenceAddress {
            occurrence: self.occurrence.clone(),
            predecessor: None,
            event_projection: event_projection(&self.occurrence),
            source_identity_sha256: self.source_sha256.clone(),
            incidence_identity_sha256: self.incidence_sha256.clone(),
            caused_population,
            cold_lineage: vec![self.locator.clone()],
            open_exterior: self.open_exterior.clone(),
        };
        validate_exterior_address(&address)?;
        if self.samples.is_empty() || self.frames.is_empty() || self.section.is_empty() {
            return Err(MembraneTransductionError::Source(
                "the acoustic occurrence has no exact sample/frame/section fibre".to_owned(),
            ));
        }
        Ok(ExteriorOccurrenceFibre {
            address,
            source: Box::new(self),
        })
    }
}

impl ExteriorOccurrenceTransducer for HierarchicalOpticalPassage {
    fn into_exterior_fibre(self) -> Result<ExteriorOccurrenceFibre, MembraneTransductionError> {
        self.validate()
            .map_err(|error| MembraneTransductionError::Source(error.to_string()))?;
        let caused_population =
            u64::try_from(self.holons.len()).map_err(|_| MembraneTransductionError::Extent)?;
        let mut open_exterior = self.native_consequence.open_exterior.clone();
        open_exterior.push(
            "the predecessor raster bytes remain exterior to the exact hierarchical potential complex"
                .to_owned(),
        );
        let address = ExteriorOccurrenceAddress {
            occurrence: self.occurrence.clone(),
            predecessor: Some(self.predecessor_occurrence.clone()),
            event_projection: event_projection(&self.occurrence),
            source_identity_sha256: self.predecessor_source_sha256.clone(),
            incidence_identity_sha256: self.relation_receipt.complete_relation_words_sha256.clone(),
            caused_population,
            cold_lineage: Vec::new(),
            open_exterior,
        };
        validate_exterior_address(&address)?;
        Ok(ExteriorOccurrenceFibre {
            address,
            source: Box::new(self),
        })
    }
}

impl ExteriorOccurrenceTransducer for ExactOpticalOccurrence {
    fn into_exterior_fibre(self) -> Result<ExteriorOccurrenceFibre, MembraneTransductionError> {
        self.validate()
            .map_err(|error| MembraneTransductionError::Source(error.to_string()))?;
        let caused_population = u64::try_from(self.hierarchy.holons.len())
            .map_err(|_| MembraneTransductionError::Extent)?;
        let address = ExteriorOccurrenceAddress {
            occurrence: self.occurrence.clone(),
            predecessor: Some(self.hierarchy.predecessor_occurrence.clone()),
            event_projection: event_projection(&self.occurrence),
            source_identity_sha256: self.source_sha256.clone(),
            incidence_identity_sha256: self
                .hierarchy
                .relation_receipt
                .complete_relation_words_sha256
                .clone(),
            caused_population,
            cold_lineage: vec![self.locator.clone()],
            open_exterior: self.open_exterior.clone(),
        };
        validate_exterior_address(&address)?;
        Ok(ExteriorOccurrenceFibre {
            address,
            source: Box::new(self),
        })
    }
}

impl ExteriorOccurrenceTransducer for ExactSynchronizedOccurrenceFibre {
    fn into_exterior_fibre(self) -> Result<ExteriorOccurrenceFibre, MembraneTransductionError> {
        self.validate()
            .map_err(|error| MembraneTransductionError::Source(error.to_string()))?;
        let caused_population = u64::try_from(self.encoded_source.len())
            .map_err(|_| MembraneTransductionError::Extent)?;
        let address = ExteriorOccurrenceAddress {
            occurrence: self.occurrence_address.clone(),
            predecessor: self.predecessor_occurrence.clone(),
            event_projection: event_projection(&self.occurrence_address),
            source_identity_sha256: self.source_identity_sha256.clone(),
            incidence_identity_sha256: self.incidence_identity_sha256.clone(),
            caused_population,
            cold_lineage: vec![self.locator.clone()],
            open_exterior: self.open_exterior.clone(),
        };
        validate_exterior_address(&address)?;
        Ok(ExteriorOccurrenceFibre {
            address,
            source: Box::new(self),
        })
    }
}

impl ExteriorOccurrenceTransducer for MaterialSourceRealization {
    fn into_exterior_fibre(self) -> Result<ExteriorOccurrenceFibre, MembraneTransductionError> {
        self.validate()
            .map_err(|error| MembraneTransductionError::Source(error.to_string()))?;
        let address = ExteriorOccurrenceAddress {
            occurrence: self.factorization_occurrence.clone(),
            predecessor: None,
            event_projection: event_projection(&self.factorization_occurrence),
            source_identity_sha256: self.payload_sha256.clone(),
            incidence_identity_sha256: self.native_operation_identity_sha256.clone(),
            caused_population: self.payload_octets,
            cold_lineage: vec![self.media_type.clone(), self.suggested_extension.clone()],
            open_exterior: self.open_exterior.clone(),
        };
        validate_exterior_address(&address)?;
        Ok(ExteriorOccurrenceFibre {
            address,
            source: Box::new(self),
        })
    }
}

/// An exact chart square at the membrane.  Both transported faces are supplied as testimony and
/// recomputed from the presented faces and phase; a false square cannot enter as a boolean claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactMembraneChartPassage {
    pub exterior_dimension: Dimension,
    pub interior_dimension: Dimension,
    pub presented_section: ExactComplexWaveCurrent,
    pub presented_current: ExactComplexWaveCurrent,
    pub phase: ExactUnitConicPhase,
    pub transported_section: ExactComplexWaveCurrent,
    pub transported_current: ExactComplexWaveCurrent,
}

impl ExactMembraneChartPassage {
    pub fn identity(
        dimension: Dimension,
        presented_section: ExactComplexWaveCurrent,
        presented_current: ExactComplexWaveCurrent,
    ) -> Self {
        Self {
            exterior_dimension: dimension.clone(),
            interior_dimension: dimension,
            transported_section: presented_section.clone(),
            transported_current: presented_current.clone(),
            presented_section,
            presented_current,
            phase: ExactUnitConicPhase::identity(),
        }
    }

    pub(super) fn validate(&self) -> Result<(), NativeMembraneDefect> {
        if self.exterior_dimension != self.interior_dimension {
            return Err(NativeMembraneDefect::IncompatibleQuantityLine {
                exterior: self.exterior_dimension.to_string(),
                interior: self.interior_dimension.to_string(),
            });
        }
        let section = self
            .presented_section
            .rotate(&self.phase.cosine, &self.phase.sine);
        let current = self
            .presented_current
            .rotate(&self.phase.cosine, &self.phase.sine);
        if section != self.transported_section || current != self.transported_current {
            return Err(NativeMembraneDefect::NoncommutingChartSquare {
                expected_section: section,
                returned_section: self.transported_section.clone(),
                expected_current: current,
                returned_current: self.transported_current.clone(),
            });
        }
        Ok(())
    }
}

/// One source-owned crossing request.  The exterior object, both boundary maps, native occurrence,
/// chart passage, chronology, and open exterior travel together.
pub struct MembraneOccurrence {
    pub exterior: ExteriorOccurrenceFibre,
    pub exterior_boundary: BoundaryId,
    pub exterior_port: OccurrencePort,
    pub rested_identity_sha256: String,
    pub native: NativeConductedSection,
    pub chart: ExactMembraneChartPassage,
    pub open_exterior: Vec<String>,
}

impl fmt::Debug for MembraneOccurrence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("MembraneOccurrence")
            .field("exterior", &self.exterior)
            .field("exterior_boundary", &self.exterior_boundary)
            .field("exterior_port", &self.exterior_port)
            .field("rested_identity_sha256", &self.rested_identity_sha256)
            .field("native", &self.native)
            .field("chart", &self.chart)
            .field("open_exterior", &self.open_exterior)
            .finish()
    }
}

/// Exact returned potential/current differences.  These are the productive membrane consequence;
/// any later scalar loss, confidence, or probability is only a receiver face of this section.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnedMembraneDifference {
    pub section: ExactComplexWaveCurrent,
    pub current: ExactComplexWaveCurrent,
    pub stored_response: ExactComplexWaveCurrent,
}

/// Serializable crossing testimony beside the moved complete occurrence fibre.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MembraneCrossingReceipt {
    pub schema: String,
    pub rested_identity_sha256: String,
    pub exterior_occurrence: String,
    pub exterior_boundary: BoundaryId,
    pub exterior_port: OccurrencePort,
    pub interior_boundary: BoundaryId,
    pub interior_port: OccurrencePort,
    pub native_occurrence: holonic_engine::EventId,
    pub native_ordered_word: Vec<holonic_engine::receiver_exact_compression::InputId>,
    pub returned_difference: ReturnedMembraneDifference,
    pub exact_source_fibre_retained: bool,
    pub cold_lineage_did_not_select_contact: bool,
    pub open_exterior: Vec<String>,
}

pub struct MembraneReturn {
    pub occurrence: MembraneOccurrence,
    pub receipt: MembraneCrossingReceipt,
}

impl fmt::Debug for MembraneReturn {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("MembraneReturn")
            .field("occurrence", &self.occurrence)
            .field("receipt", &self.receipt)
            .finish()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "defect", rename_all = "kebab-case")]
pub enum NativeMembraneDefect {
    RestIdentity {
        expected: String,
        supplied: String,
    },
    NativeSectionOutsideEcology,
    ReceiverOutsideEcology,
    NativeSectionIncidence,
    ExteriorPortIncidence,
    IncompatibleQuantityLine {
        exterior: String,
        interior: String,
    },
    NoncommutingChartSquare {
        expected_section: ExactComplexWaveCurrent,
        returned_section: ExactComplexWaveCurrent,
        expected_current: ExactComplexWaveCurrent,
        returned_current: ExactComplexWaveCurrent,
    },
}

/// A refusal retains the complete move-owned occurrence, so a failed contact never destroys the
/// source fibre or asks the body to roll back a partial mutation.
pub struct NativeMembraneInsufficiency {
    pub defect: NativeMembraneDefect,
    pub occurrence: MembraneOccurrence,
}

impl fmt::Debug for NativeMembraneInsufficiency {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("NativeMembraneInsufficiency")
            .field("defect", &self.defect)
            .field("occurrence", &self.occurrence)
            .finish()
    }
}

/// A contact that cannot be founded returns the exact exterior and chart populations. Nothing has
/// entered the continuing body at this point.
pub struct NativeMembraneBindingInsufficiency {
    pub defect: NativeMembraneDefect,
    pub exterior: ExteriorOccurrenceFibre,
    pub chart: ExactMembraneChartPassage,
}

impl fmt::Debug for NativeMembraneBindingInsufficiency {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("NativeMembraneBindingInsufficiency")
            .field("defect", &self.defect)
            .field("exterior", &self.exterior)
            .field("chart", &self.chart)
            .finish()
    }
}

#[derive(Debug)]
pub enum MembraneConsequence {
    Returned(MembraneReturn),
    Insufficient(NativeMembraneInsufficiency),
}

/// The only owner of the continuing affine Athena ecology while exterior current crosses.
pub struct NativeCausalMembrane<Standing = AffineLaboratoryCultivatedRest> {
    rest: Standing,
    interior: Option<MorphologyDerivedInterior>,
    resident_interior: Option<ResidentMembraneInteriorWord>,
    receiver_history_constitution: Option<ReceiverHistoryConstitution>,
}

struct ReceiverHistoryConstitution {
    factor_capacity: Vec<u64>,
    family_orientation: Vec<i8>,
    factor_receiver_classes: Vec<u32>,
    receiver_class_counts: Vec<u32>,
    generators: Vec<Vec<u32>>,
}

impl<Standing: MembraneStanding> NativeCausalMembrane<Standing> {
    pub fn mount(rest: Standing) -> Self {
        Self {
            rest,
            interior: None,
            resident_interior: None,
            receiver_history_constitution: None,
        }
    }

    /// Compile the already-owned ecology into its exact membrane constitution.  This consumes and
    /// returns the singular mouth so neither the rest nor its compiled constitutive view can be
    /// forked during admission.
    pub fn constitute_interior(mut self) -> Result<Self, MembraneInteriorError> {
        let began = std::time::Instant::now();
        self.interior = Some(MorphologyDerivedInterior::derive(&self.rest)?);
        if holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace {
            eprintln!("membrane constitute-interior {:?}", began.elapsed());
        }
        Ok(self)
    }

    pub fn interior(&self) -> Option<&MorphologyDerivedInterior> {
        self.interior.as_ref()
    }

    pub(crate) fn rested_body(&self) -> &Standing {
        &self.rest
    }

    pub fn rested_identity(&self) -> &str {
        self.rest.membrane_identity()
    }

    /// Restrict the complete admitted ingress population to the standing affine factor quotient.
    /// Incidence magnitude is current, reconstruction population is quadratic weight, and literal
    /// equality of the whole sparse section is the sole condensation law.  This is the compact
    /// native boundary of the one body, not an enumeration of its affine-cell pairs.
    pub fn complete_ingress_current_sections(
        &self,
    ) -> Result<Vec<MorphologyDerivedCurrentSection>, MembraneInteriorError> {
        self.complete_current_sections(
            &self.rest.membrane_realization().ingress_sections,
            "ingress",
        )
    }

    /// Return the exact current of every open terminal section in the rested realization.  A
    /// section is on this frontier precisely when no admitted occurrence names it as predecessor;
    /// no exterior payload, media face, or host-selected cell participates in that boundary.
    pub fn complete_frontier_current_sections(
        &self,
    ) -> Result<Vec<MorphologyDerivedCurrentSection>, MembraneInteriorError> {
        let realization = self.rest.membrane_realization();
        let mut continued = BTreeSet::<EventId>::new();
        for address in &realization.sections {
            let admitted = native_contact_view(&self.rest, address).ok_or_else(|| {
                MembraneInteriorError::MalformedStanding(
                    "an admitted address lost its native carrying occurrence".to_owned(),
                )
            })?;
            if let Some(predecessor) = admitted.occurrence.predecessor {
                continued.insert(predecessor);
            }
        }
        let frontier = realization
            .sections
            .iter()
            .filter(|address| !continued.contains(&address.occurrence))
            .cloned()
            .collect::<Vec<_>>();
        self.complete_current_sections(&frontier, "frontier")
    }

    fn complete_current_sections(
        &self,
        addresses: &[NativeSectionAddress],
        boundary: &str,
    ) -> Result<Vec<MorphologyDerivedCurrentSection>, MembraneInteriorError> {
        let correspondences = self.rest.membrane_correspondences();
        let mut condensed = BTreeMap::<
            Vec<(u32, BigUint)>,
            (BigUint, Vec<NativeSectionAddress>, BTreeSet<EventId>),
        >::new();
        for address in addresses {
            let admitted = native_contact_view(&self.rest, address).ok_or_else(|| {
                MembraneInteriorError::MalformedStanding(format!(
                    "an admitted {boundary} address lost its native carrying occurrence"
                ))
            })?;
            let factors = correspondences
                .iter()
                .filter(|correspondence| {
                    correspondence.native == admitted.occurrence.entering_native
                        || correspondence.native == admitted.occurrence.emitting_native
                })
                .map(|correspondence| correspondence.factor)
                .collect::<BTreeSet<_>>();
            let magnitude = admitted.incidence.coefficient.unsigned_abs();
            if factors.is_empty() || magnitude == 0 {
                return Err(MembraneInteriorError::MalformedStanding(format!(
                    "an admitted {boundary} occurrence has no nonzero affine factor current"
                )));
            }
            let factor_current = factors
                .into_iter()
                .map(|factor| (factor, BigUint::from(magnitude)))
                .collect::<Vec<_>>();
            let population = u64::try_from(admitted.reconstruction_fibre.occurrences.len())
                .map_err(|_| MembraneInteriorError::CapacityOverflow)?;
            if population == 0 {
                return Err(MembraneInteriorError::MalformedStanding(format!(
                    "an admitted {boundary} occurrence lost its reconstruction population"
                )));
            }
            let entry = condensed.entry(factor_current).or_default();
            entry.0 += BigUint::from(population);
            entry.1.push(address.clone());
            entry
                .2
                .extend(admitted.reconstruction_fibre.occurrences.iter().copied());
        }
        if condensed.is_empty() {
            return Err(MembraneInteriorError::MalformedStanding(format!(
                "the native body has no admitted {boundary} current"
            )));
        }
        Ok(condensed
            .into_iter()
            .map(
                |(factor_current, (quadratic_weight, carrying_occurrences, fibre))| {
                    MorphologyDerivedCurrentSection {
                        current: AddressedCurrentSection {
                            boundary_state: None,
                            quadratic_weight,
                            factor_current,
                        },
                        carrying_occurrences,
                        reconstruction_fibre: fibre.into_iter().collect(),
                    }
                },
            )
            .collect())
    }

    /// Place the constituted interior on one card.  Mounting consumes and returns the singular
    /// membrane so the resident word cannot be detached from a sibling owner of the same rest.
    pub fn mount_resident_interior(mut self) -> Result<Self, MembraneInteriorError> {
        let began = std::time::Instant::now();
        let interior = self
            .interior
            .as_ref()
            .ok_or(MembraneInteriorError::InteriorAbsent)?;
        self.resident_interior = Some(interior.mount_resident(&self.rest)?);
        if holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace {
            eprintln!("membrane mount-resident-interior {:?}", began.elapsed());
        }
        Ok(self)
    }

    pub fn conduct_resident_interior(
        &mut self,
        left_cell: &str,
        right_cell: &str,
        injected_boundary_current: &ExactComplexWaveCurrent,
    ) -> Result<ResidentMembraneInteriorReturn, MembraneInteriorError> {
        let interior = self
            .interior
            .as_ref()
            .ok_or(MembraneInteriorError::InteriorAbsent)?;
        let left = *interior
            .affine_cell_index(left_cell)
            .ok_or_else(|| MembraneInteriorError::MissingAffineCell(left_cell.to_owned()))?;
        let right = *interior
            .affine_cell_index(right_cell)
            .ok_or_else(|| MembraneInteriorError::MissingAffineCell(right_cell.to_owned()))?;
        self.resident_interior
            .as_mut()
            .ok_or(MembraneInteriorError::ResidentInteriorAbsent)?
            .conduct(left as u32, right as u32, injected_boundary_current)
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))
    }

    pub(crate) fn conduct_resident_quadratic_moment_front(
        &mut self,
        front: &ResidentQuadraticMomentFront,
        port_population: usize,
        entering_current: &ExactComplexWaveCurrent,
        materialize_moment_field: bool,
    ) -> Result<ResidentQuadraticMomentReturn, MembraneInteriorError> {
        self.resident_interior
            .as_mut()
            .ok_or(MembraneInteriorError::ResidentInteriorAbsent)?
            .conduct_quadratic_moment_front(
                front,
                port_population,
                entering_current,
                materialize_moment_field,
            )
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))
    }

    /// Open one new exterior-current section through the already-mounted resident ecology.  This
    /// releases only the prior occurrence's transient current/image addresses; the singular
    /// membrane, its morphology, and every invariant resident axis remain in place.
    pub(crate) fn begin_resident_factored_current_occurrence(
        &mut self,
    ) -> Result<(), MembraneInteriorError> {
        self.resident_interior
            .as_mut()
            .ok_or(MembraneInteriorError::ResidentInteriorAbsent)?
            .begin_factored_current_occurrence()
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))
    }

    pub(crate) fn continue_resident_addressed_current_passage(
        &mut self,
        source_address: &ResidentCurrentAddress,
        contexts: &[AddressedCurrentSection],
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<ResidentAddressedCurrentPassageReturn, MembraneInteriorError> {
        self.resident_interior
            .as_mut()
            .ok_or(MembraneInteriorError::ResidentInteriorAbsent)?
            .continue_addressed_current_passage(
                source_address,
                contexts,
                generator_targets,
                generator_count,
            )
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))
    }

    pub(crate) fn mount_resident_addressed_factored_receivers(
        &mut self,
        complexes: &[AddressedFactoredIntegralReceiverComplex],
        support_receiver_classes: &[u32],
        support_quadratic_scales: &[num_bigint::BigUint],
        occurrence_ports: &[u32],
    ) -> Result<ResidentAddressedFactoredReceiverFrameReturn, MembraneInteriorError> {
        self.resident_interior
            .as_mut()
            .ok_or(MembraneInteriorError::ResidentInteriorAbsent)?
            .mount_addressed_factored_receiver_complexes(
                complexes,
                support_receiver_classes,
                support_quadratic_scales,
                occurrence_ports,
            )
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))
    }

    pub(crate) fn mount_resident_factored_moment_foundation(
        &mut self,
        contexts: &[AddressedCurrentSection],
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<ResidentFactoredMomentFoundationReturn, MembraneInteriorError> {
        self.resident_interior
            .as_mut()
            .ok_or(MembraneInteriorError::ResidentInteriorAbsent)?
            .mount_factored_moment_foundation(contexts, generator_targets, generator_count)
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))
    }

    pub(crate) fn continue_resident_factored_moment_passage(
        &mut self,
        source_address: &ResidentFactoredMomentAddress,
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<ResidentFactoredMomentReceiverReturn, MembraneInteriorError> {
        let trace = holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace;
        let began = std::time::Instant::now();
        let resident = self
            .resident_interior
            .as_mut()
            .ok_or(MembraneInteriorError::ResidentInteriorAbsent)?;
        let transport = resident
            .stage_resident_factored_moment_transport(
                source_address,
                generator_targets,
                generator_count,
            )
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))?;
        if trace {
            eprintln!("mem6-image transport-enqueued {:?}", began.elapsed());
        }
        let rank = resident
            .stage_resident_factored_moment_rank(&transport)
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))?;
        if trace {
            eprintln!("mem6-image rank-enqueued {:?}", began.elapsed());
        }
        let coordinates = resident
            .stage_resident_factored_moment_coordinates(&rank)
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))?;
        if trace {
            eprintln!("mem6-image reconstruction-enqueued {:?}", began.elapsed());
        }
        let descent = resident
            .stage_resident_factored_moment_descent(&coordinates)
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))?;
        if trace {
            eprintln!("mem6-image exact-squares-enqueued {:?}", began.elapsed());
        }
        let receivers = resident
            .stage_resident_factored_moment_addressed_receivers(&descent)
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))?;
        if trace {
            eprintln!(
                "mem6-image addressed-receivers-enqueued {:?}",
                began.elapsed()
            );
        }
        let returned = resident
            .complete_resident_factored_moment_receivers(&receivers)
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))?;
        if trace {
            eprintln!("mem6-image terminal-return {:?}", began.elapsed());
        }
        Ok(returned)
    }

    pub fn into_rest(self) -> Standing {
        let Self {
            resident_interior,
            interior,
            receiver_history_constitution,
            rest,
        } = self;
        drop(resident_interior);
        drop(interior);
        drop(receiver_history_constitution);
        rest
    }

    fn cross(&self, occurrence: MembraneOccurrence) -> MembraneConsequence {
        if occurrence.rested_identity_sha256 != self.rest.membrane_identity() {
            let supplied = occurrence.rested_identity_sha256.clone();
            return insufficient(
                occurrence,
                NativeMembraneDefect::RestIdentity {
                    expected: self.rest.membrane_identity().to_owned(),
                    supplied,
                },
            );
        }
        if !self
            .rest
            .membrane_realization()
            .sections
            .contains(&occurrence.native.address)
        {
            return insufficient(
                occurrence,
                NativeMembraneDefect::NativeSectionOutsideEcology,
            );
        }
        let native = &occurrence.native;
        if native.address.occurrence != native.incidence.occurrence
            || native.entering_port.event != native.address.occurrence
            || native.emitting_port.event != native.address.occurrence
            || native.incidence.from != native.entering_native
            || native.incidence.to != native.emitting_native
        {
            return insufficient(occurrence, NativeMembraneDefect::NativeSectionIncidence);
        }
        if occurrence.exterior_port.hand != holonic_engine::PortHand::Output
            || occurrence.exterior_port.event != occurrence.exterior.address().event_projection
        {
            return insufficient(occurrence, NativeMembraneDefect::ExteriorPortIncidence);
        }
        if !native_section_matches(&self.rest, &occurrence.native) {
            return insufficient(occurrence, NativeMembraneDefect::NativeSectionIncidence);
        }
        if let Err(defect) = occurrence.chart.validate() {
            return insufficient(occurrence, defect);
        }

        let returned_difference = ReturnedMembraneDifference {
            section: native
                .entering_section
                .subtract(&occurrence.chart.transported_section),
            current: native
                .entering_current
                .subtract(&occurrence.chart.transported_current),
            stored_response: native
                .constitutive_response
                .stored
                .subtract(&occurrence.chart.transported_current),
        };
        let mut open_exterior = occurrence.exterior.address().open_exterior.clone();
        open_exterior.extend(native.open_exterior.iter().cloned());
        open_exterior.extend(occurrence.open_exterior.iter().cloned());
        open_exterior.sort();
        open_exterior.dedup();
        let receipt = MembraneCrossingReceipt {
            schema: MEMBRANE_CROSSING_SCHEMA.to_owned(),
            rested_identity_sha256: self.rest.membrane_identity().to_owned(),
            exterior_occurrence: occurrence.exterior.address().occurrence.clone(),
            exterior_boundary: occurrence.exterior_boundary,
            exterior_port: occurrence.exterior_port,
            interior_boundary: native.entering_boundary,
            interior_port: native.entering_port,
            native_occurrence: native.address.occurrence,
            native_ordered_word: native.ordered_word.clone(),
            returned_difference,
            exact_source_fibre_retained: true,
            cold_lineage_did_not_select_contact: true,
            open_exterior,
        };
        MembraneConsequence::Returned(MembraneReturn {
            occurrence,
            receipt,
        })
    }
}

impl<Standing: GranularMembraneStanding> NativeCausalMembrane<Standing> {
    /// Place the source-detached complete receiver face of every native factor beside the
    /// resident constitutive interior. The map crosses once; later boundary currents retain only
    /// factor coordinates and meet these invariant observation axes on the card.
    pub fn mount_resident_factor_receiver_faces(mut self) -> Result<Self, MembraneInteriorError> {
        let began = std::time::Instant::now();
        let restriction_atlas = self
            .rest
            .membrane_granular_potential()
            .boundary_restriction_atlas()
            .map_err(|error| MembraneInteriorError::MalformedStanding(error.to_string()))?;
        let factor_faces = self.rest.membrane_granular_potential().factor_faces();
        let first = factor_faces.first().ok_or_else(|| {
            MembraneInteriorError::MalformedStanding(
                "the granular factor receiver family is empty".to_owned(),
            )
        })?;
        let receiver_ids = first
            .receiver_factors
            .iter()
            .map(|receiver| receiver.receiver.0)
            .collect::<Vec<_>>();
        if receiver_ids.is_empty() || receiver_ids.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(MembraneInteriorError::MalformedStanding(
                "the granular receiver axes are not one complete ordered family".to_owned(),
            ));
        }
        let mut observations =
            Vec::with_capacity(factor_faces.len().saturating_mul(receiver_ids.len()));
        for (factor, face) in factor_faces.iter().enumerate() {
            if face.factor as usize != factor
                || face.receiver_factors.len() != receiver_ids.len()
                || face
                    .receiver_factors
                    .iter()
                    .zip(&receiver_ids)
                    .any(|(receiver, expected)| receiver.receiver.0 != *expected)
            {
                return Err(MembraneInteriorError::MalformedStanding(
                    "a native factor did not carry the complete common receiver face".to_owned(),
                ));
            }
            observations.extend(
                face.receiver_factors
                    .iter()
                    .map(|receiver| receiver.observation.0),
            );
        }

        // Found the production quotient from the same standing axes that are mounted below.  No
        // prompt, output target, or exterior material participates in this closure.
        let receiver_count = receiver_ids.len();
        let mut receiver_classes = vec![0_u32; observations.len()];
        let mut receiver_class_counts = Vec::with_capacity(receiver_count);
        for receiver in 0..receiver_count {
            let mut classes = BTreeMap::<u64, u32>::new();
            for factor in 0..factor_faces.len() {
                let at = factor * receiver_count + receiver;
                let observation = observations[at];
                let next = classes.len() as u32;
                receiver_classes[at] = *classes.entry(observation).or_insert(next);
            }
            receiver_class_counts.push(classes.len() as u32);
        }
        let (factor_capacity, family_orientation) = self
            .interior
            .as_ref()
            .ok_or(MembraneInteriorError::InteriorAbsent)?
            .receiver_history_constitution();
        let generators = self
            .rest
            .membrane_granular_potential()
            .receiver_history_generator_targets();
        self.receiver_history_constitution = Some(ReceiverHistoryConstitution {
            factor_capacity,
            family_orientation,
            factor_receiver_classes: receiver_classes,
            receiver_class_counts,
            generators,
        });
        self.resident_interior
            .as_mut()
            .ok_or(MembraneInteriorError::ResidentInteriorAbsent)?
            .mount_factor_receiver_faces(&receiver_ids, &observations)
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))?;
        self.resident_interior
            .as_mut()
            .ok_or(MembraneInteriorError::ResidentInteriorAbsent)?
            .mount_boundary_restriction_atlas(&restriction_atlas)
            .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))?;
        if holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace {
            eprintln!("membrane mount-factor-receiver-faces {:?}", began.elapsed());
        }
        Ok(self)
    }

    pub(crate) fn found_addressed_present_receiver_complex(
        &self,
        restriction: &[(u32, num_bigint::BigUint)],
    ) -> Result<AddressedFactoredIntegralReceiverComplex, MembraneInteriorError> {
        let constitution = self.receiver_history_constitution.as_ref().ok_or_else(|| {
            MembraneInteriorError::MalformedStanding(
                "the receiver-history constitution has not crossed its mounted axes".to_owned(),
            )
        })?;
        membrane_addressed_factored_receiver_complex(
            restriction,
            &constitution.factor_capacity,
            &constitution.family_orientation,
            &constitution.factor_receiver_classes,
            &constitution.receiver_class_counts,
            &constitution.generators,
        )
        .map_err(|error| MembraneInteriorError::MalformedStanding(error.to_string()))
    }

    pub(crate) fn receiver_history_generators(&self) -> Result<&[Vec<u32>], MembraneInteriorError> {
        self.receiver_history_constitution
            .as_ref()
            .map(|constitution| constitution.generators.as_slice())
            .ok_or_else(|| {
                MembraneInteriorError::MalformedStanding(
                    "the receiver-history constitution has not crossed its mounted axes".to_owned(),
                )
            })
    }
}

impl<Standing: MembraneStanding> CausalMembrane for NativeCausalMembrane<Standing> {
    type Standing = Standing;
    type Occurrence<'a>
        = MembraneOccurrence
    where
        Standing: 'a;
    type Return = MembraneConsequence;
    type Error = MembraneError;

    fn standing(&self) -> &Self::Standing {
        &self.rest
    }

    fn receive_occurrence<'a>(
        &mut self,
        occurrence: Self::Occurrence<'a>,
    ) -> Result<Self::Return, Self::Error>
    where
        Self: 'a,
    {
        Ok(self.cross(occurrence))
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum MembraneTransductionError {
    #[error("the exterior occurrence is malformed")]
    Address,
    #[error("the exterior source occurrence refused: {0}")]
    Source(String),
    #[error("the exterior occurrence extent cannot be represented")]
    Extent,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum MembraneError {
    #[error("the Athena membrane invariant failed: {0}")]
    Invariant(String),
}

fn insufficient(
    occurrence: MembraneOccurrence,
    defect: NativeMembraneDefect,
) -> MembraneConsequence {
    MembraneConsequence::Insufficient(NativeMembraneInsufficiency { defect, occurrence })
}

fn validate_exterior_address(
    address: &ExteriorOccurrenceAddress,
) -> Result<(), MembraneTransductionError> {
    if address.occurrence.is_empty()
        || address.caused_population == 0
        || !is_sha256(&address.source_identity_sha256)
        || !is_sha256(&address.incidence_identity_sha256)
        || address.predecessor.as_ref().is_some_and(String::is_empty)
        || address.event_projection != event_projection(&address.occurrence)
        || address.cold_lineage.iter().any(String::is_empty)
        || address.open_exterior.iter().any(String::is_empty)
    {
        return Err(MembraneTransductionError::Address);
    }
    Ok(())
}

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn event_projection(occurrence: &str) -> EventId {
    let digest = Sha256::digest(occurrence.as_bytes());
    let mut coordinate = [0u8; 8];
    coordinate.copy_from_slice(&digest[..8]);
    EventId(u64::from_le_bytes(coordinate))
}

fn native_section_matches(rest: &impl MembraneStanding, native: &NativeConductedSection) -> bool {
    let Some(admitted) = native_contact_view(rest, &native.address) else {
        return false;
    };
    let occurrence = admitted.occurrence;
    let thread = admitted.thread;
    let response = thread.constitutive_responses.iter().find(|response| {
        response.native == occurrence.emitting_native && response.receiver == native.receiver
    });
    let observation = thread.receiver_consequences.iter().find(|consequence| {
        consequence.native == occurrence.emitting_native && consequence.receiver == native.receiver
    });
    native.predecessor == occurrence.predecessor
        && native.entering_boundary == thread.entering_boundary
        && native.emitting_boundary == thread.emitting_boundary
        && native.entering_port == occurrence.entering_port
        && native.emitting_port == occurrence.emitting_port
        && native.entering_native == occurrence.entering_native
        && native.emitting_native == occurrence.emitting_native
        && &native.incidence == admitted.incidence
        && native.entering_section == admitted.entering_parametron.section
        && native.entering_current == admitted.entering_parametron.current
        && native.emitting_section == admitted.emitting_parametron.section
        && native.emitting_current == admitted.emitting_parametron.current
        && native.relative_phase == admitted.emitting_parametron.relative_phase
        && native.hand == admitted.emitting_parametron.hand
        && response == Some(&native.constitutive_response)
        && observation.is_some_and(|consequence| consequence.observation == native.observation)
        && native.ordered_word == admitted.thread.chronology
        && native.reconstruction_fibre == admitted.reconstruction_fibre.occurrences
}

struct NativeContactView<'a> {
    spool: &'a holonic_engine::native_spool::NativeSpool,
    thread: &'a NativeThread,
    occurrence: &'a NativeThreadOccurrence,
    incidence: &'a NativeIncidenceTerm,
    entering_parametron: &'a NativeParametronCell,
    emitting_parametron: &'a NativeParametronCell,
    reconstruction_fibre: &'a NativeCollapsedFibre,
}

/// Borrow an occurrence from a rest whose constructor already established its invariant.  This is
/// deliberately not a second validator: replaying `NativeSpoolBundle::validate` at every hot
/// contact was the measured whole-rest remount defect which the admitted-wire witness removes.
fn native_contact_view<'a>(
    rest: &'a impl MembraneStanding,
    address: &NativeSectionAddress,
) -> Option<NativeContactView<'a>> {
    let spool = rest
        .membrane_ecology()
        .native()
        .spools
        .iter()
        .find(|spool| spool.address == address.spool)?;
    let thread = spool
        .threads
        .iter()
        .find(|thread| thread.address == address.thread)?;
    let occurrence = thread
        .occurrences
        .iter()
        .find(|occurrence| occurrence.occurrence == address.occurrence)?;
    let incidence = thread
        .incidence
        .iter()
        .find(|incidence| incidence.occurrence == occurrence.occurrence)?;
    let entering_parametron = thread
        .parametrons
        .iter()
        .find(|cell| cell.native == occurrence.entering_native)?;
    let emitting_parametron = thread
        .parametrons
        .iter()
        .find(|cell| cell.native == occurrence.emitting_native)?;
    let reconstruction_fibre = spool.reconstruction_fibres.iter().find(|fibre| {
        fibre.native == occurrence.emitting_native
            && fibre.occurrences.contains(&occurrence.occurrence)
    })?;
    Some(NativeContactView {
        spool,
        thread,
        occurrence,
        incidence,
        entering_parametron,
        emitting_parametron,
        reconstruction_fibre,
    })
}

use holonic_engine::is_sha256_digest as is_sha256;

#[cfg(test)]
mod tests {
    use holonic_engine::quantity::BaseUnits;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    use super::*;

    fn rat(value: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(value))
    }

    #[test]
    fn material_crossing_retains_the_concrete_source_without_a_media_tag() {
        let material = AddressedMaterialOccurrence::found(
            "outside/7",
            b"caused material",
            Some("outside/6".to_owned()),
            vec!["renamable delivery face".to_owned()],
            vec!["an unrequested exterior receiver remains open".to_owned()],
        )
        .expect("material occurrence");
        let fibre = material
            .into_exterior_fibre()
            .expect("common exterior fibre");
        assert!(fibre.source_is::<AddressedMaterialOccurrence>());
        assert_eq!(fibre.address().occurrence, "outside/7");
        let restored = fibre
            .recover::<AddressedMaterialOccurrence>()
            .expect("exact moved source object");
        assert_eq!(restored.payload_octets, 15);
    }

    #[test]
    fn cold_delivery_renaming_and_reordering_do_not_change_the_exterior_incidence() {
        let material = AddressedMaterialOccurrence::found(
            "outside/8",
            b"same caused material",
            Some("outside/7".to_owned()),
            vec!["first".to_owned(), "second".to_owned()],
            vec!["one open receiver".to_owned()],
        )
        .expect("material occurrence");
        let renamed = material.without_delivery_faces();
        let reordered = material.with_reordered_delivery_faces();
        let original = material
            .into_exterior_fibre()
            .expect("original exterior fibre");
        let renamed = renamed
            .into_exterior_fibre()
            .expect("renamed exterior fibre");
        let reordered = reordered
            .into_exterior_fibre()
            .expect("reordered exterior fibre");
        assert_eq!(
            original.address().event_projection,
            renamed.address().event_projection
        );
        assert_eq!(
            original.address().incidence_identity_sha256,
            renamed.address().incidence_identity_sha256
        );
        assert_eq!(
            original.address().incidence_identity_sha256,
            reordered.address().incidence_identity_sha256
        );
    }

    #[test]
    fn the_chart_square_is_computed_and_quantity_mismatch_refuses() {
        let base = BaseUnits::declare(["carrier"]).expect("base");
        let line = base.unit("carrier").expect("line");
        let presented_section = ExactComplexWaveCurrent::new(rat(2), rat(3));
        let presented_current = ExactComplexWaveCurrent::new(rat(5), rat(7));
        let chart = ExactMembraneChartPassage::identity(
            line.clone(),
            presented_section.clone(),
            presented_current.clone(),
        );
        assert!(chart.validate().is_ok());

        let mut false_square = chart.clone();
        false_square.transported_section = ExactComplexWaveCurrent::zero();
        assert!(matches!(
            false_square.validate(),
            Err(NativeMembraneDefect::NoncommutingChartSquare { .. })
        ));

        let mut incompatible = chart;
        incompatible.interior_dimension = base.dimensionless();
        assert!(matches!(
            incompatible.validate(),
            Err(NativeMembraneDefect::IncompatibleQuantityLine { .. })
        ));
    }

    #[test]
    fn every_admitted_exterior_body_implements_the_same_transducer() {
        fn assert_transducer<T: ExteriorOccurrenceTransducer>() {}
        assert_transducer::<AddressedMaterialOccurrence>();
        assert_transducer::<ExactAcousticOccurrence>();
        assert_transducer::<ExactOpticalOccurrence>();
        assert_transducer::<HierarchicalOpticalPassage>();
        assert_transducer::<MaterialSourceRealization>();
    }
}
