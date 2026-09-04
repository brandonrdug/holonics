//! Recurrent coupling of heterogeneous receiver sections.
//!
//! This law does not turn optical, spectral, chronological, and atmospheric
//! testimony into one source chart.  It receives an already generated
//! optical relation and the complete atmospheric resolution which collocates
//! that relation with its native spectral sections and vertical fibers.  A
//! declared comparison membrane then exposes one exact phase-difference face
//! for every still possible branch.  Returned receiver cells condition that
//! face only after a prior generation has been graded.
//!
//! Production traverses the sparse relation horizon emitted by the source
//! ecology.  It does not scan the complete occurrence-pair product.  Plural
//! scan/fiber branches remain plural, missing sections remain obstructions,
//! and an aggregate relation is forced only when every surviving branch
//! agrees.

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroUsize;
use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    AtmosphericInverseResolution, CpuExecutionError, CpuExecutionReceipt, CpuExecutor, EventId,
    EventSuccessor, ExactDifferenceVector, ExactEventLaw, LogicalResourceReceipt, ReceiverGradeId,
    ReceiverPredictionId, ReceiverRelationState, ReceiverTestimonyId, ReturnedCellId,
    ReturnedReceiverPartition, SpectralBandId, SpectralScanId,
};

const STANDING_SCHEMA: &str = "holonic-engine.coupled-informant-standing.v2";
const MORPHOLOGY_SCHEMA: &str = "holonic-engine.coupled-informant-morphology.v2";
const PREDICTION_SCHEMA: &str = "holonic-engine.coupled-informant-prediction.v2";
const GRADE_SCHEMA: &str = "holonic-engine.coupled-informant-grade.v2";
const RADIATION_SCHEMA: &str = "holonic-engine.coupled-informant-radiation.v2";

pub const COUPLED_PHASE_EXTENT: usize = 18;
pub const COUPLED_SPECTRAL_BANDS: [SpectralBandId; 5] = [
    SpectralBandId(8),
    SpectralBandId(9),
    SpectralBandId(10),
    SpectralBandId(11),
    SpectralBandId(13),
];

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CoupledInformantPredictionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CoupledInformantGradeId(pub u64);

/// The named coordinates of the receiver comparison face.
///
/// The first four coordinates are transported from the prior optical
/// relation.  The remaining coordinates are derived only after the ABI and
/// atmospheric sections have met that relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum CoupledPhaseCoordinateKind {
    OpticalDifference {
        coordinate: u32,
    },
    BandTemperatureDifference {
        band: SpectralBandId,
    },
    SpectralChordDifference {
        band: SpectralBandId,
        reference: SpectralBandId,
    },
    ScanDepartureDifference,
    VerticalLowerDifference,
    VerticalUpperDifference,
    VerticalExtentDifference,
    ScanIdentityDifference,
}

pub fn coupled_phase_coordinate_kinds() -> Vec<CoupledPhaseCoordinateKind> {
    let mut kinds = (0_u32..4)
        .map(|coordinate| CoupledPhaseCoordinateKind::OpticalDifference { coordinate })
        .collect::<Vec<_>>();
    kinds.extend(
        COUPLED_SPECTRAL_BANDS
            .into_iter()
            .map(|band| CoupledPhaseCoordinateKind::BandTemperatureDifference { band }),
    );
    kinds.extend(COUPLED_SPECTRAL_BANDS[..4].iter().copied().map(|band| {
        CoupledPhaseCoordinateKind::SpectralChordDifference {
            band,
            reference: SpectralBandId(13),
        }
    }));
    kinds.extend([
        CoupledPhaseCoordinateKind::ScanDepartureDifference,
        CoupledPhaseCoordinateKind::VerticalLowerDifference,
        CoupledPhaseCoordinateKind::VerticalUpperDifference,
        CoupledPhaseCoordinateKind::VerticalExtentDifference,
        CoupledPhaseCoordinateKind::ScanIdentityDifference,
    ]);
    debug_assert_eq!(kinds.len(), COUPLED_PHASE_EXTENT);
    kinds
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct CoupledPhaseVector(pub Vec<Rat>);

impl CoupledPhaseVector {
    fn componentwise_le(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .zip(&other.0)
                .all(|(left, right)| left <= right)
    }

    fn validate(&self) -> Result<(), CoupledInformantError> {
        if self.0.len() != COUPLED_PHASE_EXTENT || self.0.iter().any(Signed::is_negative) {
            return Err(CoupledInformantError::MalformedPhaseVector);
        }
        Ok(())
    }
}

/// The recurrent intermediate body conditioned by earlier complete returns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoupledInformantMorphology {
    pub schema: String,
    pub coordinate_kinds: Vec<CoupledPhaseCoordinateKind>,
    pub positive_maxima: Vec<CoupledPhaseVector>,
    /// Exact returned-apart phase fibers.  A repeated equal fiber may conduct
    /// separation.  It is not expanded into an unproved global law.
    pub negative_witnesses: BTreeMap<CoupledPhaseVector, u64>,
    /// Minimal witnesses retain the receiver-relative upward obstruction
    /// envelope.  Outside positive support this envelope remains OPEN; it
    /// cannot by itself force a new separation.
    pub negative_minima: Vec<CoupledPhaseVector>,
    pub admitted_events: BTreeSet<EventId>,
    pub returned_together_branches: u64,
    pub returned_apart_branches: u64,
}

impl Default for CoupledInformantMorphology {
    fn default() -> Self {
        Self {
            schema: MORPHOLOGY_SCHEMA.to_owned(),
            coordinate_kinds: coupled_phase_coordinate_kinds(),
            positive_maxima: Vec::new(),
            negative_witnesses: BTreeMap::new(),
            negative_minima: Vec::new(),
            admitted_events: BTreeSet::new(),
            returned_together_branches: 0,
            returned_apart_branches: 0,
        }
    }
}

impl CoupledInformantMorphology {
    fn classify(&self, vector: &CoupledPhaseVector) -> CoupledInformantRelationState {
        let positive = self
            .positive_maxima
            .iter()
            .any(|maximum| vector.componentwise_le(maximum));
        let recurrent_negative = self.negative_witnesses.get(vector).copied().unwrap_or(0) >= 2;
        let negative_obstruction = self
            .negative_minima
            .iter()
            .any(|minimum| minimum.componentwise_le(vector));
        match (positive, recurrent_negative, negative_obstruction) {
            (true, true, _) | (true, false, true) => CoupledInformantRelationState::Conflicted,
            (true, false, false) => CoupledInformantRelationState::ForcedTogether,
            (false, true, _) => CoupledInformantRelationState::ForcedApart,
            (false, false, _) => CoupledInformantRelationState::Open,
        }
    }

    fn validate(&self) -> Result<(), CoupledInformantError> {
        if self.schema != MORPHOLOGY_SCHEMA
            || self.coordinate_kinds != coupled_phase_coordinate_kinds()
            || !is_maximal_front(&self.positive_maxima)
            || !is_minimal_front(&self.negative_minima)
            || self
                .negative_witnesses
                .values()
                .any(|multiplicity| *multiplicity == 0)
        {
            return Err(CoupledInformantError::MalformedMorphology);
        }
        for vector in self
            .positive_maxima
            .iter()
            .chain(self.negative_witnesses.keys())
            .chain(&self.negative_minima)
        {
            vector.validate()?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum CoupledInformantRelationState {
    ForcedTogether,
    ForcedApart,
    Open,
    Conflicted,
    MissingSection,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum CoupledRelationOrigin {
    OpticalHorizon,
    SpectralLocalStar,
    OpticalAndSpectral,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoupledPhaseBranch {
    pub scans: [SpectralScanId; 2],
    /// Dense vertical-fiber ordinals in the source atmospheric resolution.
    pub vertical_fibers: [u64; 2],
    pub phase: CoupledPhaseVector,
    pub state: CoupledInformantRelationState,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoupledGeneratedRelation {
    pub members: [ReceiverTestimonyId; 2],
    pub origin: CoupledRelationOrigin,
    pub base_state: ReceiverRelationState,
    pub branches: Vec<CoupledPhaseBranch>,
    pub state: CoupledInformantRelationState,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoupledInformantPrediction {
    pub schema: String,
    pub id: CoupledInformantPredictionId,
    pub caused_by: EventId,
    pub source_prediction: ReceiverPredictionId,
    pub source_grade_precondition: Option<ReceiverGradeId>,
    pub atmospheric_resolution: crate::AtmosphericResolutionId,
    pub chronology: u64,
    pub morphology_before: CoupledInformantMorphology,
    pub relations: Vec<CoupledGeneratedRelation>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoupledInformantGradeCounts {
    pub returned_together_relations: u64,
    pub returned_apart_relations: u64,
    pub forced_together_correct: u64,
    pub forced_apart_correct: u64,
    pub returned_together_open: u64,
    pub returned_apart_open: u64,
    pub returned_together_forced_apart: u64,
    pub returned_apart_forced_together: u64,
    pub conflicted_relations: u64,
    pub missing_section_relations: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum CoupledInformantObstructionKind {
    ReturnedTogetherButForcedApart,
    ReturnedApartButForcedTogether,
    ReturnedTogetherButOpen,
    ReturnedApartButOpen,
    ConflictedMorphology,
    MissingParticipatingSection,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct CoupledInformantObstruction {
    pub kind: CoupledInformantObstructionKind,
    pub members: [ReceiverTestimonyId; 2],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoupledInformantGrade {
    pub schema: String,
    pub id: CoupledInformantGradeId,
    pub caused_by: EventId,
    pub prediction: CoupledInformantPredictionId,
    pub returned: Arc<ReturnedReceiverPartition>,
    pub counts: CoupledInformantGradeCounts,
    pub obstructions: Vec<CoupledInformantObstruction>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoupledInformantWork {
    pub source_relations: u64,
    pub optical_horizon_relations: u64,
    pub spectral_local_star_relations: u64,
    pub shared_horizon_relations: u64,
    pub phase_branches: u64,
    pub missing_section_relations: u64,
    pub cpu_tasks: u64,
    pub cpu_workers_used: u64,
    pub cpu_antichains: u64,
    pub cpu_joins: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoupledInformantStanding {
    pub schema: String,
    pub morphology: CoupledInformantMorphology,
    pub predictions: BTreeMap<CoupledInformantPredictionId, Arc<CoupledInformantPrediction>>,
    pub grades: BTreeMap<CoupledInformantGradeId, Arc<CoupledInformantGrade>>,
    pub admitted_grades: BTreeSet<CoupledInformantGradeId>,
    used_events: BTreeSet<EventId>,
    next_prediction: u64,
    next_grade: u64,
}

impl Default for CoupledInformantStanding {
    fn default() -> Self {
        Self {
            schema: STANDING_SCHEMA.to_owned(),
            morphology: CoupledInformantMorphology::default(),
            predictions: BTreeMap::new(),
            grades: BTreeMap::new(),
            admitted_grades: BTreeSet::new(),
            used_events: BTreeSet::new(),
            next_prediction: 1,
            next_grade: 1,
        }
    }
}

impl CoupledInformantStanding {
    pub fn validate(&self) -> Result<(), CoupledInformantError> {
        if self.schema != STANDING_SCHEMA {
            return Err(CoupledInformantError::MalformedStanding);
        }
        self.morphology.validate()?;
        if self
            .admitted_grades
            .iter()
            .any(|grade| !self.grades.contains_key(grade))
        {
            return Err(CoupledInformantError::MalformedStanding);
        }
        for prediction in self.predictions.values() {
            if prediction.schema != PREDICTION_SCHEMA {
                return Err(CoupledInformantError::MalformedStanding);
            }
            prediction.morphology_before.validate()?;
            for relation in &prediction.relations {
                if relation.branches.is_empty()
                    != (relation.state == CoupledInformantRelationState::MissingSection)
                {
                    return Err(CoupledInformantError::MalformedStanding);
                }
                for branch in &relation.branches {
                    branch.phase.validate()?;
                }
            }
        }
        if self.grades.values().any(|grade| {
            grade.schema != GRADE_SCHEMA || !self.predictions.contains_key(&grade.prediction)
        }) {
            return Err(CoupledInformantError::MalformedStanding);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CoupledInformantEvent {
    Generate {
        event: EventId,
        chronology: u64,
        source_grade_precondition: Option<ReceiverGradeId>,
        resolution: Arc<AtmosphericInverseResolution>,
    },
    GradeReturnedPartition {
        event: EventId,
        prediction: CoupledInformantPredictionId,
        returned: ReturnedReceiverPartition,
    },
    AdmitGradedReturn {
        event: EventId,
        grade: CoupledInformantGradeId,
    },
}

impl CoupledInformantEvent {
    fn event(&self) -> EventId {
        match self {
            Self::Generate { event, .. }
            | Self::GradeReturnedPartition { event, .. }
            | Self::AdmitGradedReturn { event, .. } => *event,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CoupledInformantRadiationKind {
    PredictionGenerated,
    ReturnGraded,
    GradedReturnAdmitted,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoupledInformantRadiation {
    pub schema: String,
    pub event: EventId,
    pub kind: CoupledInformantRadiationKind,
    pub prediction: Option<Arc<CoupledInformantPrediction>>,
    pub grade: Option<Arc<CoupledInformantGrade>>,
    pub work: CoupledInformantWork,
}

#[derive(Clone, Debug)]
pub struct CoupledInformantLaw {
    cpu: CpuExecutor,
}

impl CoupledInformantLaw {
    pub const fn serial() -> Self {
        Self {
            cpu: CpuExecutor::serial(),
        }
    }

    pub const fn multicore(workers: NonZeroUsize) -> Self {
        Self {
            cpu: CpuExecutor::multicore(workers),
        }
    }
}

impl Default for CoupledInformantLaw {
    fn default() -> Self {
        let workers = std::thread::available_parallelism()
            .unwrap_or_else(|_| NonZeroUsize::new(1).expect("one is nonzero"));
        Self::multicore(workers)
    }
}

impl ExactEventLaw for CoupledInformantLaw {
    type Standing = CoupledInformantStanding;
    type Event = CoupledInformantEvent;
    type Radiation = CoupledInformantRadiation;
    type Error = CoupledInformantError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        standing_before.validate()?;
        let event_id = event.event();
        if standing_before.used_events.contains(&event_id) {
            return Err(CoupledInformantError::RepeatedEvent(event_id));
        }
        let mut standing_after = standing_before.clone();
        let mut work = CoupledInformantWork::default();
        let (kind, prediction, grade, laws) = match event {
            CoupledInformantEvent::Generate {
                chronology,
                source_grade_precondition,
                resolution,
                ..
            } => {
                let id = CoupledInformantPredictionId(standing_after.next_prediction);
                standing_after.next_prediction = standing_after
                    .next_prediction
                    .checked_add(1)
                    .ok_or(CoupledInformantError::CarrierOverflow)?;
                let (body, generated_work) = generate_prediction(
                    id,
                    event_id,
                    *chronology,
                    *source_grade_precondition,
                    resolution,
                    &standing_after.morphology,
                    &self.cpu,
                )?;
                work = generated_work;
                let body = Arc::new(body);
                standing_after.predictions.insert(id, Arc::clone(&body));
                (
                    CoupledInformantRadiationKind::PredictionGenerated,
                    Some(body),
                    None,
                    &[
                        "restrict-sparse-source-horizon",
                        "collocate-native-receiver-sections",
                        "emit-plural-phase-branches",
                    ][..],
                )
            }
            CoupledInformantEvent::GradeReturnedPartition {
                prediction,
                returned,
                ..
            } => {
                let prediction_body = standing_after
                    .predictions
                    .get(prediction)
                    .cloned()
                    .ok_or(CoupledInformantError::MissingPrediction(*prediction))?;
                if standing_after
                    .grades
                    .values()
                    .any(|grade| grade.prediction == *prediction)
                {
                    return Err(CoupledInformantError::PredictionAlreadyGraded(*prediction));
                }
                let id = CoupledInformantGradeId(standing_after.next_grade);
                standing_after.next_grade = standing_after
                    .next_grade
                    .checked_add(1)
                    .ok_or(CoupledInformantError::CarrierOverflow)?;
                let body = Arc::new(grade_prediction(id, event_id, &prediction_body, returned)?);
                standing_after.grades.insert(id, Arc::clone(&body));
                (
                    CoupledInformantRadiationKind::ReturnGraded,
                    None,
                    Some(body),
                    &["receive-later-partition", "grade-before-admission"][..],
                )
            }
            CoupledInformantEvent::AdmitGradedReturn { grade, .. } => {
                let grade_body = standing_after
                    .grades
                    .get(grade)
                    .cloned()
                    .ok_or(CoupledInformantError::MissingGrade(*grade))?;
                if standing_after.admitted_grades.contains(grade) {
                    return Err(CoupledInformantError::GradeAlreadyAdmitted(*grade));
                }
                let prediction = standing_after
                    .predictions
                    .get(&grade_body.prediction)
                    .cloned()
                    .ok_or(CoupledInformantError::MissingPrediction(
                        grade_body.prediction,
                    ))?;
                condition_morphology(
                    &mut standing_after.morphology,
                    event_id,
                    &prediction,
                    &grade_body.returned,
                )?;
                standing_after.admitted_grades.insert(*grade);
                (
                    CoupledInformantRadiationKind::GradedReturnAdmitted,
                    None,
                    None,
                    &[
                        "admit-returned-difference",
                        "reform-intermediate-morphology",
                    ][..],
                )
            }
        };
        standing_after.used_events.insert(event_id);
        standing_after.validate()?;
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![CoupledInformantRadiation {
                schema: RADIATION_SCHEMA.to_owned(),
                event: event_id,
                kind,
                prediction,
                grade,
                work,
            }],
            logical_resources: Some(logical_receipt(laws)?),
            physical_resources: None,
        })
    }
}

#[derive(Clone)]
struct OccurrencePhase {
    scan: SpectralScanId,
    vertical_fiber: u64,
    temperatures: [Rat; 5],
    chords: [Rat; 4],
    scan_departure: Rat,
    vertical_lower: Rat,
    vertical_upper: Rat,
}

#[derive(Clone)]
struct CandidateRelationInput {
    members: [ReceiverTestimonyId; 2],
    origin: CoupledRelationOrigin,
    base_state: ReceiverRelationState,
    difference: ExactDifferenceVector,
}

fn generate_prediction(
    id: CoupledInformantPredictionId,
    event: EventId,
    chronology: u64,
    source_grade_precondition: Option<ReceiverGradeId>,
    resolution: &AtmosphericInverseResolution,
    morphology: &CoupledInformantMorphology,
    cpu: &CpuExecutor,
) -> Result<(CoupledInformantPrediction, CoupledInformantWork), CoupledInformantError> {
    let phases = Arc::new(index_occurrence_phases(resolution)?);
    let morphology = Arc::new(morphology.clone());
    if resolution.spectral_occurrences.is_empty() {
        return Err(CoupledInformantError::EmptyResolution);
    }
    // Atmospheric resolutions retain only forced source relations in their
    // lifted carrier.  The complete sparse horizon therefore travels with
    // the resolution as source lineage.
    let prior = &resolution.source_prediction;
    let source_prediction = prior.id;
    if prior.id != resolution.prediction {
        return Err(CoupledInformantError::IncompatibleResolution);
    }
    let relation_inputs = candidate_relation_inputs(resolution)?;
    let optical_horizon_relations = relation_inputs
        .iter()
        .filter(|relation| {
            matches!(
                relation.origin,
                CoupledRelationOrigin::OpticalHorizon | CoupledRelationOrigin::OpticalAndSpectral
            )
        })
        .count();
    let spectral_local_star_relations = relation_inputs
        .iter()
        .filter(|relation| {
            matches!(
                relation.origin,
                CoupledRelationOrigin::SpectralLocalStar
                    | CoupledRelationOrigin::OpticalAndSpectral
            )
        })
        .count();
    let shared_horizon_relations = relation_inputs
        .iter()
        .filter(|relation| relation.origin == CoupledRelationOrigin::OpticalAndSpectral)
        .count();
    let (relations, receipt) = cpu
        .execute_indexed(&relation_inputs, {
            let phases = Arc::clone(&phases);
            let morphology = Arc::clone(&morphology);
            move |_index, relation| {
                let mut branches = Vec::new();
                let left = phases
                    .get(&relation.members[0])
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                let right = phases
                    .get(&relation.members[1])
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                for left_phase in left {
                    for right_phase in right {
                        let phase =
                            coupled_phase_vector(&relation.difference.0, left_phase, right_phase)?;
                        let state = morphology.classify(&phase);
                        branches.push(CoupledPhaseBranch {
                            scans: [left_phase.scan, right_phase.scan],
                            vertical_fibers: [
                                left_phase.vertical_fiber,
                                right_phase.vertical_fiber,
                            ],
                            phase,
                            state,
                        });
                    }
                }
                branches.sort_by(|left, right| {
                    (left.scans, left.vertical_fibers, &left.phase, left.state).cmp(&(
                        right.scans,
                        right.vertical_fibers,
                        &right.phase,
                        right.state,
                    ))
                });
                branches.dedup();
                let state = aggregate_branch_state(&branches);
                Ok(CoupledGeneratedRelation {
                    members: relation.members,
                    origin: relation.origin,
                    base_state: relation.base_state,
                    branches,
                    state,
                })
            }
        })
        .map_err(map_cpu_error)?;
    let mut work = CoupledInformantWork {
        source_relations: usize_to_u64(relations.len())?,
        optical_horizon_relations: usize_to_u64(optical_horizon_relations)?,
        spectral_local_star_relations: usize_to_u64(spectral_local_star_relations)?,
        shared_horizon_relations: usize_to_u64(shared_horizon_relations)?,
        phase_branches: relations.iter().try_fold(0_u64, |total, relation| {
            total
                .checked_add(usize_to_u64(relation.branches.len())?)
                .ok_or(CoupledInformantError::CarrierOverflow)
        })?,
        missing_section_relations: usize_to_u64(
            relations
                .iter()
                .filter(|relation| relation.state == CoupledInformantRelationState::MissingSection)
                .count(),
        )?,
        ..CoupledInformantWork::default()
    };
    accumulate_cpu(&mut work, &receipt)?;
    Ok((
        CoupledInformantPrediction {
            schema: PREDICTION_SCHEMA.to_owned(),
            id,
            caused_by: event,
            source_prediction,
            source_grade_precondition,
            atmospheric_resolution: resolution.id,
            chronology,
            morphology_before: morphology.as_ref().clone(),
            relations,
        },
        work,
    ))
}

fn candidate_relation_inputs(
    resolution: &AtmosphericInverseResolution,
) -> Result<Vec<CandidateRelationInput>, CoupledInformantError> {
    let mut candidates = BTreeMap::<[ReceiverTestimonyId; 2], CandidateRelationInput>::new();
    for relation in &resolution.source_prediction.candidate_relations {
        let members = ordered_members(relation.members);
        candidates.insert(
            members,
            CandidateRelationInput {
                members,
                origin: CoupledRelationOrigin::OpticalHorizon,
                base_state: relation.state,
                difference: relation.difference.clone(),
            },
        );
    }

    let selections = resolution
        .contact_selections
        .iter()
        .map(|selection| {
            (
                selection.testimony,
                selection
                    .selected_scans
                    .iter()
                    .copied()
                    .collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let occurrences = resolution
        .spectral_occurrences
        .iter()
        .map(|occurrence| (occurrence.testimony, occurrence))
        .collect::<BTreeMap<_, _>>();
    let mut local_stars =
        BTreeMap::<(SpectralScanId, u32, u32), Vec<(Rat, ReceiverTestimonyId)>>::new();
    for occurrence in &resolution.spectral_occurrences {
        let selected = selections
            .get(&occurrence.testimony)
            .ok_or(CoupledInformantError::MalformedResolution)?;
        for contact in &occurrence.contacts {
            if selected.contains(&contact.scan)
                && COUPLED_SPECTRAL_BANDS.iter().all(|band| {
                    contact.data_quality_flags.get(band).copied() == Some(0)
                        && contact.brightness_temperature_kelvin.contains_key(band)
                })
            {
                local_stars
                    .entry((contact.scan, contact.row, contact.column))
                    .or_default()
                    .push((occurrence.clock.clone(), occurrence.testimony));
            }
        }
    }
    for star in local_stars.values_mut() {
        star.sort();
        star.dedup();
        for pair in star.windows(2) {
            if pair[0].1 == pair[1].1 {
                continue;
            }
            let members = ordered_members([pair[0].1, pair[1].1]);
            let left = occurrences
                .get(&members[0])
                .ok_or(CoupledInformantError::MalformedResolution)?;
            let right = occurrences
                .get(&members[1])
                .ok_or(CoupledInformantError::MalformedResolution)?;
            let difference = ExactDifferenceVector(vec![
                absolute_difference(&left.latitude_degree, &right.latitude_degree),
                absolute_difference(&left.longitude_degree, &right.longitude_degree),
                absolute_difference(&left.clock, &right.clock),
                absolute_difference(&left.radiant_energy, &right.radiant_energy),
            ]);
            match candidates.get_mut(&members) {
                Some(existing) => {
                    if existing.difference != difference {
                        return Err(CoupledInformantError::IncompatibleSourceCharts);
                    }
                    existing.origin = CoupledRelationOrigin::OpticalAndSpectral;
                }
                None => {
                    candidates.insert(
                        members,
                        CandidateRelationInput {
                            members,
                            origin: CoupledRelationOrigin::SpectralLocalStar,
                            base_state: ReceiverRelationState::Open,
                            difference,
                        },
                    );
                }
            }
        }
    }
    Ok(candidates.into_values().collect())
}

fn ordered_members(members: [ReceiverTestimonyId; 2]) -> [ReceiverTestimonyId; 2] {
    if members[0] <= members[1] {
        members
    } else {
        [members[1], members[0]]
    }
}

fn index_occurrence_phases(
    resolution: &AtmosphericInverseResolution,
) -> Result<BTreeMap<ReceiverTestimonyId, Vec<OccurrencePhase>>, CoupledInformantError> {
    let selections = resolution
        .contact_selections
        .iter()
        .map(|selection| (selection.testimony, selection))
        .collect::<BTreeMap<_, _>>();
    let fibers = resolution
        .vertical_fibers
        .iter()
        .enumerate()
        .map(|(ordinal, fiber)| {
            Ok((
                fiber.testimony,
                (
                    usize_to_u64(ordinal)?,
                    fiber.scan,
                    fiber.scan_departure_seconds.clone(),
                    fiber.support.enclosure(),
                ),
            ))
        })
        .collect::<Result<Vec<_>, CoupledInformantError>>()?;
    let mut fibers_by_occurrence = BTreeMap::<
        ReceiverTestimonyId,
        Vec<(u64, SpectralScanId, Rat, crate::ExactInterval)>,
    >::new();
    for (testimony, fiber) in fibers {
        fibers_by_occurrence
            .entry(testimony)
            .or_default()
            .push(fiber);
    }
    let mut phases = BTreeMap::new();
    for occurrence in &resolution.spectral_occurrences {
        let selected = selections
            .get(&occurrence.testimony)
            .ok_or(CoupledInformantError::MalformedResolution)?;
        let selected = selected
            .selected_scans
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let mut occurrence_phases = Vec::new();
        for contact in &occurrence.contacts {
            if !selected.contains(&contact.scan)
                || COUPLED_SPECTRAL_BANDS.iter().any(|band| {
                    contact.data_quality_flags.get(band).copied() != Some(0)
                        || !contact.brightness_temperature_kelvin.contains_key(band)
                })
            {
                continue;
            }
            let temperatures = std::array::from_fn(|index| {
                contact.brightness_temperature_kelvin[&COUPLED_SPECTRAL_BANDS[index]].clone()
            });
            let chords = std::array::from_fn(|index| {
                &temperatures[index] - &temperatures[COUPLED_SPECTRAL_BANDS.len() - 1]
            });
            for (fiber, scan, departure, support) in fibers_by_occurrence
                .get(&occurrence.testimony)
                .map(Vec::as_slice)
                .unwrap_or(&[])
            {
                if *scan != contact.scan {
                    continue;
                }
                occurrence_phases.push(OccurrencePhase {
                    scan: contact.scan,
                    vertical_fiber: *fiber,
                    temperatures: temperatures.clone(),
                    chords: chords.clone(),
                    scan_departure: departure.clone(),
                    vertical_lower: support.lower.clone(),
                    vertical_upper: support.upper.clone(),
                });
            }
        }
        occurrence_phases.sort_by(|left, right| {
            (
                left.scan,
                left.vertical_fiber,
                &left.temperatures,
                &left.chords,
            )
                .cmp(&(
                    right.scan,
                    right.vertical_fiber,
                    &right.temperatures,
                    &right.chords,
                ))
        });
        occurrence_phases.dedup_by(|left, right| {
            left.scan == right.scan
                && left.vertical_fiber == right.vertical_fiber
                && left.temperatures == right.temperatures
                && left.chords == right.chords
        });
        phases.insert(occurrence.testimony, occurrence_phases);
    }
    Ok(phases)
}

fn coupled_phase_vector(
    optical: &[Rat],
    left: &OccurrencePhase,
    right: &OccurrencePhase,
) -> Result<CoupledPhaseVector, CoupledInformantError> {
    if optical.len() != 4 {
        return Err(CoupledInformantError::IncompatibleOpticalDifference);
    }
    let mut values = optical.to_vec();
    values.extend(
        left.temperatures
            .iter()
            .zip(&right.temperatures)
            .map(|(left, right)| absolute_difference(left, right)),
    );
    values.extend(
        left.chords
            .iter()
            .zip(&right.chords)
            .map(|(left, right)| absolute_difference(left, right)),
    );
    values.push(absolute_difference(
        &left.scan_departure,
        &right.scan_departure,
    ));
    values.push(absolute_difference(
        &left.vertical_lower,
        &right.vertical_lower,
    ));
    values.push(absolute_difference(
        &left.vertical_upper,
        &right.vertical_upper,
    ));
    values.push(absolute_difference(
        &(&left.vertical_upper - &left.vertical_lower),
        &(&right.vertical_upper - &right.vertical_lower),
    ));
    values.push(Rat::from_integer(BigInt::from(u8::from(
        left.scan != right.scan,
    ))));
    let vector = CoupledPhaseVector(values);
    vector.validate()?;
    Ok(vector)
}

fn aggregate_branch_state(branches: &[CoupledPhaseBranch]) -> CoupledInformantRelationState {
    let Some(first) = branches.first() else {
        return CoupledInformantRelationState::MissingSection;
    };
    if branches
        .iter()
        .any(|branch| branch.state == CoupledInformantRelationState::Conflicted)
    {
        return CoupledInformantRelationState::Conflicted;
    }
    let states = branches
        .iter()
        .map(|branch| branch.state)
        .collect::<BTreeSet<_>>();
    if states.len() == 1 {
        first.state
    } else if states.contains(&CoupledInformantRelationState::ForcedTogether)
        && states.contains(&CoupledInformantRelationState::ForcedApart)
    {
        CoupledInformantRelationState::Conflicted
    } else {
        CoupledInformantRelationState::Open
    }
}

fn grade_prediction(
    id: CoupledInformantGradeId,
    event: EventId,
    prediction: &CoupledInformantPrediction,
    returned: &ReturnedReceiverPartition,
) -> Result<CoupledInformantGrade, CoupledInformantError> {
    let cells = returned_cell_index(returned)?;
    let predicted = prediction
        .relations
        .iter()
        .flat_map(|relation| relation.members)
        .collect::<BTreeSet<_>>();
    if predicted
        .iter()
        .any(|testimony| !cells.contains_key(testimony))
    {
        return Err(CoupledInformantError::IncompleteReturnedPopulation);
    }
    let mut counts = CoupledInformantGradeCounts::default();
    let mut obstructions = Vec::new();
    for relation in &prediction.relations {
        let together = cells[&relation.members[0]] == cells[&relation.members[1]];
        if together {
            counts.returned_together_relations =
                checked_increment(counts.returned_together_relations)?;
        } else {
            counts.returned_apart_relations = checked_increment(counts.returned_apart_relations)?;
        }
        let obstruction = match (together, relation.state) {
            (true, CoupledInformantRelationState::ForcedTogether) => {
                counts.forced_together_correct = checked_increment(counts.forced_together_correct)?;
                None
            }
            (false, CoupledInformantRelationState::ForcedApart) => {
                counts.forced_apart_correct = checked_increment(counts.forced_apart_correct)?;
                None
            }
            (true, CoupledInformantRelationState::ForcedApart) => {
                counts.returned_together_forced_apart =
                    checked_increment(counts.returned_together_forced_apart)?;
                Some(CoupledInformantObstructionKind::ReturnedTogetherButForcedApart)
            }
            (false, CoupledInformantRelationState::ForcedTogether) => {
                counts.returned_apart_forced_together =
                    checked_increment(counts.returned_apart_forced_together)?;
                Some(CoupledInformantObstructionKind::ReturnedApartButForcedTogether)
            }
            (true, CoupledInformantRelationState::Open) => {
                counts.returned_together_open = checked_increment(counts.returned_together_open)?;
                Some(CoupledInformantObstructionKind::ReturnedTogetherButOpen)
            }
            (false, CoupledInformantRelationState::Open) => {
                counts.returned_apart_open = checked_increment(counts.returned_apart_open)?;
                Some(CoupledInformantObstructionKind::ReturnedApartButOpen)
            }
            (_, CoupledInformantRelationState::Conflicted) => {
                counts.conflicted_relations = checked_increment(counts.conflicted_relations)?;
                Some(CoupledInformantObstructionKind::ConflictedMorphology)
            }
            (_, CoupledInformantRelationState::MissingSection) => {
                counts.missing_section_relations =
                    checked_increment(counts.missing_section_relations)?;
                Some(CoupledInformantObstructionKind::MissingParticipatingSection)
            }
        };
        if let Some(kind) = obstruction {
            obstructions.push(CoupledInformantObstruction {
                kind,
                members: relation.members,
            });
        }
    }
    Ok(CoupledInformantGrade {
        schema: GRADE_SCHEMA.to_owned(),
        id,
        caused_by: event,
        prediction: prediction.id,
        returned: Arc::new(returned.clone()),
        counts,
        obstructions,
    })
}

fn condition_morphology(
    morphology: &mut CoupledInformantMorphology,
    event: EventId,
    prediction: &CoupledInformantPrediction,
    returned: &ReturnedReceiverPartition,
) -> Result<(), CoupledInformantError> {
    let cells = returned_cell_index(returned)?;
    let mut positive = Vec::new();
    let mut negative = Vec::new();
    for relation in &prediction.relations {
        let left_cell = cells
            .get(&relation.members[0])
            .ok_or(CoupledInformantError::IncompleteReturnedPopulation)?;
        let right_cell = cells
            .get(&relation.members[1])
            .ok_or(CoupledInformantError::IncompleteReturnedPopulation)?;
        let together = left_cell == right_cell;
        for branch in &relation.branches {
            if together {
                positive.push(branch.phase.clone());
            } else {
                negative.push(branch.phase.clone());
            }
        }
    }
    morphology.returned_together_branches = morphology
        .returned_together_branches
        .checked_add(usize_to_u64(positive.len())?)
        .ok_or(CoupledInformantError::CarrierOverflow)?;
    morphology.returned_apart_branches = morphology
        .returned_apart_branches
        .checked_add(usize_to_u64(negative.len())?)
        .ok_or(CoupledInformantError::CarrierOverflow)?;
    positive.append(&mut morphology.positive_maxima);
    for witness in &negative {
        let multiplicity = morphology
            .negative_witnesses
            .entry(witness.clone())
            .or_default();
        *multiplicity = multiplicity
            .checked_add(1)
            .ok_or(CoupledInformantError::CarrierOverflow)?;
    }
    negative.append(&mut morphology.negative_minima);
    morphology.positive_maxima = canonical_maximal_front(positive);
    morphology.negative_minima = canonical_minimal_front(negative);
    morphology.admitted_events.insert(event);
    morphology.validate()
}

fn returned_cell_index(
    returned: &ReturnedReceiverPartition,
) -> Result<BTreeMap<ReceiverTestimonyId, ReturnedCellId>, CoupledInformantError> {
    let mut cells = BTreeMap::new();
    for cell in &returned.cells {
        for testimony in &cell.members {
            if cells.insert(*testimony, cell.id).is_some() {
                return Err(CoupledInformantError::OverlappingReturnedCells(*testimony));
            }
        }
    }
    Ok(cells)
}

fn canonical_maximal_front(mut candidates: Vec<CoupledPhaseVector>) -> Vec<CoupledPhaseVector> {
    candidates.sort_by(|left, right| right.cmp(left));
    candidates.dedup();
    let mut front = Vec::<CoupledPhaseVector>::new();
    for candidate in candidates {
        if !front
            .iter()
            .any(|existing| candidate.componentwise_le(existing))
        {
            front.push(candidate);
        }
    }
    front.sort();
    front
}

fn canonical_minimal_front(mut candidates: Vec<CoupledPhaseVector>) -> Vec<CoupledPhaseVector> {
    candidates.sort();
    candidates.dedup();
    let mut front = Vec::<CoupledPhaseVector>::new();
    for candidate in candidates {
        if !front
            .iter()
            .any(|existing| existing.componentwise_le(&candidate))
        {
            front.push(candidate);
        }
    }
    front
}

fn is_maximal_front(front: &[CoupledPhaseVector]) -> bool {
    front.iter().enumerate().all(|(left_index, left)| {
        front
            .iter()
            .enumerate()
            .all(|(right_index, right)| left_index == right_index || !left.componentwise_le(right))
    })
}

fn is_minimal_front(front: &[CoupledPhaseVector]) -> bool {
    front.iter().enumerate().all(|(left_index, left)| {
        front
            .iter()
            .enumerate()
            .all(|(right_index, right)| left_index == right_index || !right.componentwise_le(left))
    })
}

fn absolute_difference(left: &Rat, right: &Rat) -> Rat {
    (left - right).abs()
}

fn logical_receipt(laws: &[&str]) -> Result<LogicalResourceReceipt, CoupledInformantError> {
    let mut diagram = crate::CausalDiagram::default();
    let events = laws
        .iter()
        .map(|law| diagram.add_event(*law))
        .collect::<Vec<_>>();
    for pair in events.windows(2) {
        diagram.precedes(pair[0], pair[1])?;
    }
    Ok(LogicalResourceReceipt::from_diagram(&diagram)?)
}

fn accumulate_cpu(
    work: &mut CoupledInformantWork,
    receipt: &CpuExecutionReceipt,
) -> Result<(), CoupledInformantError> {
    work.cpu_tasks = receipt
        .tasks
        .to_u64()
        .ok_or(CoupledInformantError::CarrierOverflow)?;
    work.cpu_workers_used = receipt
        .workers_used
        .to_u64()
        .ok_or(CoupledInformantError::CarrierOverflow)?;
    work.cpu_antichains = u64::from(!receipt.tasks.is_zero());
    work.cpu_joins = receipt
        .joins
        .to_u64()
        .ok_or(CoupledInformantError::CarrierOverflow)?;
    Ok(())
}

fn map_cpu_error(error: CpuExecutionError<CoupledInformantError>) -> CoupledInformantError {
    match error {
        CpuExecutionError::Operation(error) => error,
        CpuExecutionError::WorkerPanicked => CoupledInformantError::PhysicalWorkerPanicked,
    }
}

fn usize_to_u64(value: usize) -> Result<u64, CoupledInformantError> {
    u64::try_from(value).map_err(|_| CoupledInformantError::CarrierOverflow)
}

fn checked_increment(value: u64) -> Result<u64, CoupledInformantError> {
    value
        .checked_add(1)
        .ok_or(CoupledInformantError::CarrierOverflow)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CoupledInformantError {
    #[error("coupled-informant standing is malformed")]
    MalformedStanding,
    #[error("coupled-informant morphology is malformed")]
    MalformedMorphology,
    #[error("a coupled phase vector is malformed")]
    MalformedPhaseVector,
    #[error("atmospheric resolution is empty")]
    EmptyResolution,
    #[error("atmospheric resolution is malformed")]
    MalformedResolution,
    #[error("atmospheric resolution and its source prediction disagree")]
    IncompatibleResolution,
    #[error("the source optical difference is not the declared four-coordinate face")]
    IncompatibleOpticalDifference,
    #[error("optical and spectral receiver charts disagree on a shared occurrence pair")]
    IncompatibleSourceCharts,
    #[error("coupled-informant event {0:?} has already entered standing")]
    RepeatedEvent(EventId),
    #[error("coupled-informant prediction {0:?} is absent")]
    MissingPrediction(CoupledInformantPredictionId),
    #[error("coupled-informant prediction {0:?} has already been graded")]
    PredictionAlreadyGraded(CoupledInformantPredictionId),
    #[error("coupled-informant grade {0:?} is absent")]
    MissingGrade(CoupledInformantGradeId),
    #[error("coupled-informant grade {0:?} has already entered morphology")]
    GradeAlreadyAdmitted(CoupledInformantGradeId),
    #[error("returned cells overlap at testimony {0:?}")]
    OverlappingReturnedCells(ReceiverTestimonyId),
    #[error("the returned partition omits a predicted testimony")]
    IncompleteReturnedPopulation,
    #[error("a coupled-informant carrier overflowed")]
    CarrierOverflow,
    #[error("a coupled-informant CPU worker panicked")]
    PhysicalWorkerPanicked,
    #[error(transparent)]
    Diagram(#[from] crate::DiagramError),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn vector(values: &[i64]) -> CoupledPhaseVector {
        CoupledPhaseVector(
            values
                .iter()
                .map(|value| Rat::from_integer(BigInt::from(*value)))
                .collect(),
        )
    }

    #[test]
    fn plural_branches_do_not_force_an_aggregate_when_they_disagree() {
        let together = CoupledPhaseBranch {
            scans: [SpectralScanId(1), SpectralScanId(1)],
            vertical_fibers: [0, 1],
            phase: vector(&[0; COUPLED_PHASE_EXTENT]),
            state: CoupledInformantRelationState::ForcedTogether,
        };
        let mut apart = together.clone();
        apart.state = CoupledInformantRelationState::ForcedApart;
        assert_eq!(
            aggregate_branch_state(&[together, apart]),
            CoupledInformantRelationState::Conflicted
        );
    }

    #[test]
    fn morphology_retains_componentwise_positive_and_negative_fronts() {
        let mut morphology = CoupledInformantMorphology::default();
        morphology.positive_maxima = canonical_maximal_front(vec![
            vector(&[1; COUPLED_PHASE_EXTENT]),
            vector(&[2; COUPLED_PHASE_EXTENT]),
        ]);
        morphology.negative_minima = canonical_minimal_front(vec![
            vector(&[5; COUPLED_PHASE_EXTENT]),
            vector(&[6; COUPLED_PHASE_EXTENT]),
        ]);
        morphology
            .negative_witnesses
            .insert(vector(&[5; COUPLED_PHASE_EXTENT]), 2);
        morphology.validate().unwrap();
        assert_eq!(
            morphology.classify(&vector(&[0; COUPLED_PHASE_EXTENT])),
            CoupledInformantRelationState::ForcedTogether
        );
        assert_eq!(
            morphology.classify(&vector(&[7; COUPLED_PHASE_EXTENT])),
            CoupledInformantRelationState::Open
        );
        assert_eq!(
            morphology.classify(&vector(&[5; COUPLED_PHASE_EXTENT])),
            CoupledInformantRelationState::ForcedApart
        );
        assert_eq!(
            morphology.classify(&vector(&[3; COUPLED_PHASE_EXTENT])),
            CoupledInformantRelationState::Open
        );
    }
}
