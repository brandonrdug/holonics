//! Receiver testimony, learned relation fibers, and return-before-admission.
//!
//! This module does not identify sensor addresses with world cells.  A
//! [`ReceiverTestimony`] is an inherited occurrence in one declared local
//! chart.  A returned partition is likewise testimony emitted by a named
//! external algorithm or receiver.  Production learns a translation-free
//! relation fiber from complete returned cells, predicts the relations of an
//! unpartitioned batch, grades the later partition against that prior fiber,
//! and only then permits the returned batch to condition standing.
//!
//! The learned relation is deliberately plural.  Exact coordinate
//! differences may be forced together, forced apart, unresolved, or
//! obstructed by mutually incompatible lineage.  Connected components of
//! forced-together relations are a receiver quotient only; they are not
//! promoted into physical channels or world objects.

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroUsize;
use std::sync::Arc;
#[cfg(target_os = "linux")]
use std::sync::Mutex;

use num_bigint::{BigInt, BigUint};
use num_traits::{Signed, ToPrimitive, Zero};
use relational_geometry::{Rat, ReceiverId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CpuExecutionError, CpuExecutionMode, CpuExecutionReceipt, CpuExecutor, EquivalenceClosure,
    EventId, EventSuccessor, ExactEventLaw, ExactModeSignature, ExistingReceiverBatch,
    LogicalResourceReceipt, MemoryTier, ModeAdmissionLedger, PhysicalResourceReceipt,
    ReceiverCellReturn, ReceiverEcologyError, ReceiverGrainQuotient, ReceiverGrainQuotientId,
    ReceiverMorphologySummary, ReturnedReceiverCellAddress, Traffic, receiver_morphology_summary,
};
#[cfg(target_os = "linux")]
use crate::{
    CudaClassifiedRelation, CudaExactRelationExecutor, CudaRelationObstruction,
    CudaRelationReceipt, CudaSparseGrade, CudaSparseRelations, PackedRelationFront,
    PackedRelationPair, PackedRelationWindow,
};
#[cfg(test)]
use crate::{ReceiverHorizonTopology, ReceiverPerspectiveAddress, ReceiverPerspectiveSpec};

const STANDING_SCHEMA: &str = "holonic-engine.observation-ecology-standing.v1";
const FAMILY_SCHEMA: &str = "holonic-engine.receiver-coordinate-family.v1";
const CHART_SCHEMA: &str = "holonic-engine.receiver-affine-chart.v1";
const RELATION_SCHEMA: &str = "holonic-engine.learned-partition-relation.v1";
const PREDICTION_SCHEMA: &str = "holonic-engine.receiver-relation-prediction.v1";
const GRADE_SCHEMA: &str = "holonic-engine.receiver-relation-grade.v1";
const RADIATION_SCHEMA: &str = "holonic-engine.observation-ecology-radiation.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverCoordinateFamilyId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverChartId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverLineageId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverTestimonyId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReturnedAlgorithmId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReturnedCellId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverPredictionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverGradeId(pub u64);

/// A receiver-local coordinate family.
///
/// The family supplies names and selects coordinates used for relation and
/// co-presence comparison.  It does not assert an ambient world dimension.
/// Different charts may transport different raw carrier dimensions into the
/// same comparison family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverCoordinateFamily {
    pub schema: String,
    pub id: ReceiverCoordinateFamilyId,
    pub coordinates: Vec<String>,
    pub relation_coordinates: Vec<u32>,
    pub stratum_coordinates: Vec<u32>,
}

impl ReceiverCoordinateFamily {
    pub fn new(
        id: ReceiverCoordinateFamilyId,
        coordinates: Vec<String>,
        relation_coordinates: Vec<u32>,
        stratum_coordinates: Vec<u32>,
    ) -> Result<Self, ObservationEcologyError> {
        let family = Self {
            schema: FAMILY_SCHEMA.to_owned(),
            id,
            coordinates,
            relation_coordinates,
            stratum_coordinates,
        };
        family.validate()?;
        Ok(family)
    }

    fn validate(&self) -> Result<(), ObservationEcologyError> {
        if self.schema != FAMILY_SCHEMA
            || self.coordinates.is_empty()
            || self.relation_coordinates.is_empty()
            || self.stratum_coordinates.is_empty()
        {
            return Err(ObservationEcologyError::MalformedCoordinateFamily(self.id));
        }
        let extent = self.coordinates.len();
        let mut all_selected = BTreeSet::new();
        for coordinate in self
            .relation_coordinates
            .iter()
            .chain(&self.stratum_coordinates)
        {
            let coordinate = usize::try_from(*coordinate)
                .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
            if coordinate >= extent || !all_selected.insert(coordinate) {
                return Err(ObservationEcologyError::MalformedCoordinateFamily(self.id));
            }
        }
        Ok(())
    }
}

/// One exact affine transport from an inherited integer carrier into a
/// receiver coordinate family:
///
/// `received = offset + basis * raw`.
///
/// The basis need not be square or invertible.  A receiver is allowed to
/// collapse or omit world directions; that loss remains part of its
/// transduction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverAffineChart {
    pub schema: String,
    pub id: ReceiverChartId,
    pub receiver: ReceiverId,
    pub family: ReceiverCoordinateFamilyId,
    pub source: String,
    pub raw_coordinates: Vec<String>,
    pub offset: Vec<Rat>,
    pub basis: Vec<Vec<Rat>>,
}

impl ReceiverAffineChart {
    pub fn new(
        id: ReceiverChartId,
        receiver: ReceiverId,
        family: ReceiverCoordinateFamilyId,
        source: impl Into<String>,
        raw_coordinates: Vec<String>,
        offset: Vec<Rat>,
        basis: Vec<Vec<Rat>>,
    ) -> Result<Self, ObservationEcologyError> {
        let chart = Self {
            schema: CHART_SCHEMA.to_owned(),
            id,
            receiver,
            family,
            source: source.into(),
            raw_coordinates,
            offset,
            basis,
        };
        chart.validate_shape()?;
        Ok(chart)
    }

    fn validate_shape(&self) -> Result<(), ObservationEcologyError> {
        let raw_extent = self.raw_coordinates.len();
        if self.schema != CHART_SCHEMA
            || self.source.is_empty()
            || raw_extent == 0
            || self.offset.is_empty()
            || self.basis.len() != self.offset.len()
            || self.basis.iter().any(|row| row.len() != raw_extent)
        {
            return Err(ObservationEcologyError::MalformedChart(self.id));
        }
        Ok(())
    }

    pub fn receive(&self, raw: &[i64]) -> Result<Vec<Rat>, ObservationEcologyError> {
        if raw.len() != self.raw_coordinates.len() {
            return Err(ObservationEcologyError::RawCoordinateDimension {
                chart: self.id,
                expected: self.raw_coordinates.len(),
                received: raw.len(),
            });
        }
        Ok(self
            .basis
            .iter()
            .zip(&self.offset)
            .map(|(row, offset)| {
                row.iter()
                    .zip(raw)
                    .fold(offset.clone(), |value, (coefficient, raw)| {
                        value + coefficient * Rat::from_integer(BigInt::from(*raw))
                    })
            })
            .collect())
    }

    fn receive_coordinate(
        &self,
        raw: &[i64],
        coordinate: usize,
    ) -> Result<Rat, ObservationEcologyError> {
        if raw.len() != self.raw_coordinates.len() {
            return Err(ObservationEcologyError::RawCoordinateDimension {
                chart: self.id,
                expected: self.raw_coordinates.len(),
                received: raw.len(),
            });
        }
        let row = self
            .basis
            .get(coordinate)
            .ok_or(ObservationEcologyError::MalformedChart(self.id))?;
        Ok(row.iter().zip(raw).fold(
            self.offset[coordinate].clone(),
            |value, (coefficient, raw)| value + coefficient * Rat::from_integer(BigInt::from(*raw)),
        ))
    }
}

/// Convert the exact finite IEEE-754 value carried by `bits` into a rational.
///
/// This function never parses the formatted decimal presentation of a
/// floating value and never leaves a float in engine standing.
pub fn exact_rational_from_f32_bits(bits: u32) -> Result<Rat, ObservationEcologyError> {
    let sign = (bits >> 31) != 0;
    let exponent = (bits >> 23) & 0xff;
    let fraction = bits & 0x7f_ffff;
    if exponent == 0xff {
        return Err(ObservationEcologyError::NonfiniteReportedValue);
    }
    if exponent == 0 && fraction == 0 {
        return Ok(Rat::zero());
    }
    let (significand, power) = if exponent == 0 {
        (u64::from(fraction), -149_i32)
    } else {
        (
            u64::from((1_u32 << 23) | fraction),
            i32::try_from(exponent).expect("eight-bit exponent fits i32") - 127 - 23,
        )
    };
    rational_from_binary_parts(sign, BigUint::from(significand), power)
}

/// Exact counterpart of [`exact_rational_from_f32_bits`] for binary64.
pub fn exact_rational_from_f64_bits(bits: u64) -> Result<Rat, ObservationEcologyError> {
    let sign = (bits >> 63) != 0;
    let exponent = (bits >> 52) & 0x7ff;
    let fraction = bits & 0x000f_ffff_ffff_ffff;
    if exponent == 0x7ff {
        return Err(ObservationEcologyError::NonfiniteReportedValue);
    }
    if exponent == 0 && fraction == 0 {
        return Ok(Rat::zero());
    }
    let (significand, power) = if exponent == 0 {
        (BigUint::from(fraction), -1074_i32)
    } else {
        (
            BigUint::from((1_u64 << 52) | fraction),
            i32::try_from(exponent).expect("eleven-bit exponent fits i32") - 1023 - 52,
        )
    };
    rational_from_binary_parts(sign, significand, power)
}

fn rational_from_binary_parts(
    negative: bool,
    significand: BigUint,
    power: i32,
) -> Result<Rat, ObservationEcologyError> {
    let magnitude = BigInt::from(significand);
    let numerator = if negative { -magnitude } else { magnitude };
    if power >= 0 {
        let shift = usize::try_from(power).map_err(|_| ObservationEcologyError::CarrierOverflow)?;
        Ok(Rat::from_integer(numerator << shift))
    } else {
        let shift = usize::try_from(power.unsigned_abs())
            .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
        Ok(Rat::new(numerator, BigInt::from(1_u8) << shift))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverTestimony {
    pub id: ReceiverTestimonyId,
    pub receiver: ReceiverId,
    pub lineage: ReceiverLineageId,
    pub chart: ReceiverChartId,
    /// Identity supplied by the source product.  It is inherited testimony,
    /// not the identity of a world cell.
    pub source_identity: u64,
    pub raw: Vec<i64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCoordinateInterval {
    pub coordinate: u32,
    pub lower: Rat,
    pub upper: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverBatch {
    pub family: ReceiverCoordinateFamilyId,
    pub chronology: u64,
    pub source: String,
    /// Receiver restriction in family coordinates.  An empty vector means
    /// that this occurrence supplied no additional finite aperture.
    pub aperture: Vec<ExactCoordinateInterval>,
    pub occurrences: Vec<ReceiverTestimony>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReturnedCellCoverage {
    /// Every occurrence is carried by exactly one returned cell.
    CompleteExclusive,
    /// Cells may overlap and need not cover the batch.  Such returns remain
    /// inspectable but do not currently train the exclusive partition fiber.
    PartialOverlapping,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReturnedReceiverCell {
    pub id: ReturnedCellId,
    pub members: BTreeSet<ReceiverTestimonyId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReturnedReceiverPartition {
    pub algorithm: ReturnedAlgorithmId,
    pub coverage: ReturnedCellCoverage,
    pub cells: Vec<ReturnedReceiverCell>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ExactDifferenceVector(pub Vec<Rat>);

impl ExactDifferenceVector {
    fn componentwise_le(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .zip(&other.0)
                .all(|(left, right)| left <= right)
    }
}

/// Translation-free relation learned from returned cells.
///
/// `positive_maxima` presents the maximal observed whole-cell spans.  Their
/// componentwise downward closure is compatible with a returned cell.
/// `negative_minima` presents minimal observed cross-cell boundary witnesses;
/// their componentwise upward closure is incompatible.  Overlap of these two
/// regions is retained as obstruction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LearnedPartitionRelation {
    pub schema: String,
    pub family: ReceiverCoordinateFamilyId,
    pub algorithm: ReturnedAlgorithmId,
    pub positive_maxima: Vec<ExactDifferenceVector>,
    pub negative_minima: Vec<ExactDifferenceVector>,
    pub testimony_events: BTreeSet<EventId>,
    pub returned_cells: u64,
}

impl LearnedPartitionRelation {
    fn new(family: ReceiverCoordinateFamilyId, algorithm: ReturnedAlgorithmId) -> Self {
        Self {
            schema: RELATION_SCHEMA.to_owned(),
            family,
            algorithm,
            positive_maxima: Vec::new(),
            negative_minima: Vec::new(),
            testimony_events: BTreeSet::new(),
            returned_cells: 0,
        }
    }

    fn positive_contains(&self, difference: &ExactDifferenceVector) -> bool {
        self.positive_maxima
            .iter()
            .any(|maximum| difference.componentwise_le(maximum))
    }

    fn negative_contains(&self, difference: &ExactDifferenceVector) -> bool {
        self.negative_minima
            .iter()
            .any(|minimum| minimum.componentwise_le(difference))
    }

    fn classify(&self, difference: &ExactDifferenceVector) -> ReceiverRelationState {
        match (
            self.positive_contains(difference),
            self.negative_contains(difference),
        ) {
            (true, false) => ReceiverRelationState::ForcedTogether,
            (false, true) => ReceiverRelationState::ForcedApart,
            (false, false) => ReceiverRelationState::Open,
            (true, true) => ReceiverRelationState::Conflicted,
        }
    }

    fn extend_positive(&mut self, candidates: Vec<ExactDifferenceVector>) {
        let mut complete = std::mem::take(&mut self.positive_maxima);
        complete.extend(candidates);
        self.positive_maxima = canonical_maximal_front(complete);
    }

    fn extend_negative(&mut self, candidates: Vec<ExactDifferenceVector>) {
        let mut complete = std::mem::take(&mut self.negative_minima);
        complete.extend(candidates);
        self.negative_minima = canonical_minimal_front(complete);
    }

    fn validate(&self, relation_extent: usize) -> Result<(), ObservationEcologyError> {
        if self.schema != RELATION_SCHEMA
            || self
                .positive_maxima
                .iter()
                .chain(&self.negative_minima)
                .any(|difference| {
                    difference.0.len() != relation_extent
                        || difference.0.iter().any(|value| value.is_negative())
                })
            || !is_maximal_front(&self.positive_maxima)
            || !is_minimal_front(&self.negative_minima)
        {
            return Err(ObservationEcologyError::MalformedLearnedRelation {
                family: self.family,
                algorithm: self.algorithm,
            });
        }
        Ok(())
    }
}

fn canonical_maximal_front(
    mut candidates: Vec<ExactDifferenceVector>,
) -> Vec<ExactDifferenceVector> {
    candidates.sort_by(|left, right| right.cmp(left));
    candidates.dedup();
    let mut front = Vec::<ExactDifferenceVector>::new();
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

fn canonical_minimal_front(
    mut candidates: Vec<ExactDifferenceVector>,
) -> Vec<ExactDifferenceVector> {
    candidates.sort();
    candidates.dedup();
    let mut front = Vec::<ExactDifferenceVector>::new();
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

fn merge_minimal_front(
    front: &mut Vec<ExactDifferenceVector>,
    candidates: Vec<ExactDifferenceVector>,
) {
    let mut complete = std::mem::take(front);
    complete.extend(candidates);
    *front = canonical_minimal_front(complete);
}

fn is_maximal_front(front: &[ExactDifferenceVector]) -> bool {
    front.iter().enumerate().all(|(left_index, left)| {
        front
            .iter()
            .enumerate()
            .all(|(right_index, right)| left_index == right_index || !left.componentwise_le(right))
    })
}

fn is_minimal_front(front: &[ExactDifferenceVector]) -> bool {
    front.iter().enumerate().all(|(left_index, left)| {
        front
            .iter()
            .enumerate()
            .all(|(right_index, right)| left_index == right_index || !right.componentwise_le(left))
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ReceiverRelationState {
    ForcedTogether,
    ForcedApart,
    Open,
    Conflicted,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PredictedReceiverRelation {
    pub members: [ReceiverTestimonyId; 2],
    pub difference: ExactDifferenceVector,
    pub state: ReceiverRelationState,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverRelationPrediction {
    pub schema: String,
    pub id: ReceiverPredictionId,
    pub caused_by: EventId,
    pub family: ReceiverCoordinateFamilyId,
    pub algorithm: ReturnedAlgorithmId,
    pub chronology: u64,
    pub source: String,
    pub aperture: Vec<ExactCoordinateInterval>,
    pub occurrences: Vec<ReceiverTestimonyId>,
    /// Relations in the learned positive support.  Every omitted pair remains
    /// classifiable from `relation_before`; omission is not forced absence.
    pub candidate_relations: Vec<PredictedReceiverRelation>,
    pub forced_components: Vec<Vec<ReceiverTestimonyId>>,
    pub relation_before: LearnedPartitionRelation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ReceiverRelationObstructionKind {
    ReturnedTogetherButForcedApart,
    ReturnedTogetherButOpen,
    ReturnedApartButForcedTogether,
    ConflictedLineage,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReceiverRelationObstruction {
    pub kind: ReceiverRelationObstructionKind,
    pub members: [ReceiverTestimonyId; 2],
    pub difference: ExactDifferenceVector,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverRelationGradeCounts {
    pub returned_together_pairs: u64,
    pub returned_apart_pairs: u64,
    pub forced_together_correct: u64,
    pub forced_apart_correct: u64,
    pub returned_together_open: u64,
    pub returned_together_forced_apart: u64,
    pub returned_apart_forced_together: u64,
    pub conflicted_pairs: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverRelationGrade {
    pub schema: String,
    pub id: ReceiverGradeId,
    pub caused_by: EventId,
    pub prediction: ReceiverPredictionId,
    pub returned: Arc<ReturnedReceiverPartition>,
    pub counts: ReceiverRelationGradeCounts,
    pub obstructions: Vec<ReceiverRelationObstruction>,
    pub receiver_morphology: ReceiverMorphologySummary,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TestimonyDisposition {
    Admitted { event: EventId },
    PendingPrediction { prediction: ReceiverPredictionId },
    Graded { grade: ReceiverGradeId },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverTestimonyStanding {
    pub occurrence: ReceiverTestimony,
    pub disposition: TestimonyDisposition,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AdmittedReceiverPartition {
    pub event: EventId,
    pub family: ReceiverCoordinateFamilyId,
    pub chronology: u64,
    pub source: String,
    pub partition: Arc<ReturnedReceiverPartition>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservationEcologyStanding {
    pub schema: String,
    pub families: BTreeMap<ReceiverCoordinateFamilyId, ReceiverCoordinateFamily>,
    pub charts: BTreeMap<ReceiverChartId, ReceiverAffineChart>,
    pub testimonies: Arc<BTreeMap<ReceiverTestimonyId, ReceiverTestimonyStanding>>,
    pub relations:
        BTreeMap<(ReceiverCoordinateFamilyId, ReturnedAlgorithmId), LearnedPartitionRelation>,
    pub predictions: Arc<BTreeMap<ReceiverPredictionId, Arc<ReceiverRelationPrediction>>>,
    pub grades: Arc<BTreeMap<ReceiverGradeId, Arc<ReceiverRelationGrade>>>,
    pub admitted_partitions: Arc<Vec<AdmittedReceiverPartition>>,
    pub admitted_grades: BTreeSet<ReceiverGradeId>,
    pub receiver_quotients: BTreeMap<ReceiverGrainQuotientId, ReceiverGrainQuotient>,
    pub receiver_quotient_by_target: BTreeMap<ReceiverTestimonyId, ReceiverGrainQuotientId>,
    used_events: BTreeSet<EventId>,
    next_prediction: u64,
    next_grade: u64,
    next_receiver_quotient: u64,
}

impl Default for ObservationEcologyStanding {
    fn default() -> Self {
        Self {
            schema: STANDING_SCHEMA.to_owned(),
            families: BTreeMap::new(),
            charts: BTreeMap::new(),
            testimonies: Arc::new(BTreeMap::new()),
            relations: BTreeMap::new(),
            predictions: Arc::new(BTreeMap::new()),
            grades: Arc::new(BTreeMap::new()),
            admitted_partitions: Arc::new(Vec::new()),
            admitted_grades: BTreeSet::new(),
            receiver_quotients: BTreeMap::new(),
            receiver_quotient_by_target: BTreeMap::new(),
            used_events: BTreeSet::new(),
            next_prediction: 1,
            next_grade: 1,
            next_receiver_quotient: 1,
        }
    }
}

impl ObservationEcologyStanding {
    pub fn relation(
        &self,
        family: ReceiverCoordinateFamilyId,
        algorithm: ReturnedAlgorithmId,
    ) -> Option<&LearnedPartitionRelation> {
        self.relations.get(&(family, algorithm))
    }

    pub fn admitted_testimony_count(&self) -> usize {
        let admitted_predictions = self
            .admitted_grades
            .iter()
            .filter_map(|grade| self.grades.get(grade))
            .map(|grade| grade.prediction)
            .collect::<BTreeSet<_>>();
        self.testimonies
            .values()
            .filter(|testimony| match &testimony.disposition {
                TestimonyDisposition::Admitted { .. } => true,
                TestimonyDisposition::PendingPrediction { prediction } => {
                    admitted_predictions.contains(prediction)
                }
                TestimonyDisposition::Graded { grade } => self.admitted_grades.contains(grade),
            })
            .count()
    }

    pub fn pending_testimony_count(&self) -> usize {
        self.testimonies.len() - self.admitted_testimony_count()
    }

    pub fn grade_is_admitted(&self, grade: ReceiverGradeId) -> bool {
        self.admitted_grades.contains(&grade)
    }

    pub fn validate(&self) -> Result<(), ObservationEcologyError> {
        let law = ObservationEcologyLaw::default();
        let mut work = ObservationEcologyWork::default();
        validate_standing_with_executor(self, &law.cpu, &mut work)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ObservationEcologyEvent {
    DeclareFamily {
        event: EventId,
        family: ReceiverCoordinateFamily,
    },
    DeclareChart {
        event: EventId,
        chart: ReceiverAffineChart,
    },
    ConditionReturnedBatch {
        event: EventId,
        batch: ReceiverBatch,
        returned: ReturnedReceiverPartition,
    },
    /// Receive every cell of one already-admitted lower partition as one
    /// testimony occurrence in a coarser receiver family.
    ReturnPartitionAsReceivers {
        event: EventId,
        partition_event: EventId,
        upper_batch: ReceiverBatch,
        returns: Vec<ReceiverCellReturn>,
    },
    /// Condition a relation using receiver occurrences which already entered
    /// standing through lower-grain return.
    ConditionExistingReceiverBatch {
        event: EventId,
        batch: ExistingReceiverBatch,
        returned: ReturnedReceiverPartition,
    },
    PredictUnpartitionedBatch {
        event: EventId,
        algorithm: ReturnedAlgorithmId,
        batch: ReceiverBatch,
    },
    /// Emit a prediction over already-admitted coarser receiver occurrences.
    PredictExistingReceiverBatch {
        event: EventId,
        algorithm: ReturnedAlgorithmId,
        batch: ExistingReceiverBatch,
    },
    GradeReturnedPartition {
        event: EventId,
        prediction: ReceiverPredictionId,
        returned: ReturnedReceiverPartition,
    },
    AdmitGradedReturn {
        event: EventId,
        grade: ReceiverGradeId,
    },
}

impl ObservationEcologyEvent {
    fn event(&self) -> EventId {
        match self {
            Self::DeclareFamily { event, .. }
            | Self::DeclareChart { event, .. }
            | Self::ConditionReturnedBatch { event, .. }
            | Self::ReturnPartitionAsReceivers { event, .. }
            | Self::ConditionExistingReceiverBatch { event, .. }
            | Self::PredictUnpartitionedBatch { event, .. }
            | Self::PredictExistingReceiverBatch { event, .. }
            | Self::GradeReturnedPartition { event, .. }
            | Self::AdmitGradedReturn { event, .. } => *event,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ObservationEcologyRadiationKind {
    FamilyDeclared,
    ChartDeclared,
    ReturnedBatchConditioned,
    PartitionReturnedAsReceivers,
    ExistingReceiverBatchConditioned,
    PredictionEmitted,
    ExistingReceiverPredictionEmitted,
    ReturnGraded,
    GradedReturnAdmitted,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservationEcologyWork {
    pub received_occurrences: u64,
    pub decoded_coordinates: u64,
    pub inspected_relations: u64,
    pub retained_positive_generators: u64,
    pub retained_negative_generators: u64,
    pub obstruction_witnesses: u64,
    /// Exact indexed work members submitted to CPU antichains.
    pub cpu_tasks: u64,
    /// Greatest worker population actually joined by one CPU antichain.
    pub cpu_workers_used: u64,
    /// Causally ordered CPU antichains completed by this transition.
    pub cpu_antichains: u64,
    pub cpu_joins: u64,
    /// Pair classifications returned by the exact CUDA relation executor.
    pub cuda_classified_relations: u64,
    /// Sparse relation consequences returned across the device boundary.
    pub cuda_returned_relations: u64,
    /// Card classifications compared address-for-address with the host law.
    pub cuda_parity_relations: u64,
    /// Structurally distinct relation modes admitted by an exact host witness.
    pub cuda_mode_admissions: u64,
    /// Relation occurrences realized by an already admitted card mode.
    pub cuda_mode_reuses: u64,
    /// Number of structurally exact modes resident in the event law afterward.
    pub cuda_resident_modes: u64,
    pub cuda_launches: u64,
    pub cuda_device: Option<String>,
    pub cuda_kernel_sha256: Option<String>,
    pub cuda_host_to_device_octets: u64,
    pub cuda_device_to_host_octets: u64,
    pub cuda_front_uploads: u64,
    pub cuda_allocation_resizes: u64,
    /// General chart strata whose relation cannot enter the packed card law.
    pub host_relation_fallbacks: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservationEcologyRadiation {
    pub schema: String,
    pub event: EventId,
    pub kind: ObservationEcologyRadiationKind,
    pub prediction: Option<Arc<ReceiverRelationPrediction>>,
    pub grade: Option<Arc<ReceiverRelationGrade>>,
    pub work: ObservationEcologyWork,
}

#[cfg(target_os = "linux")]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
struct CudaRelationModeBoundary {
    family: ReceiverCoordinateFamilyId,
    algorithm: ReturnedAlgorithmId,
}

#[cfg(target_os = "linux")]
type CudaRelationMode = ExactModeSignature<CudaRelationModeBoundary, PackedRelationFront, Vec<Rat>>;

#[cfg(target_os = "linux")]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum CudaRelationRealization {
    SparsePositivePrediction,
    SparseGrade,
}

#[cfg(target_os = "linux")]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct CudaModeRealization {
    mode: CudaRelationMode,
    realization: CudaRelationRealization,
}

#[cfg(target_os = "linux")]
#[derive(Clone, Debug, PartialEq, Eq)]
struct CudaModeAdmissionWitness {
    device: String,
    kernel_sha256: String,
    compared_relations: u64,
}

#[cfg(target_os = "linux")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CudaModeUse {
    admitted: bool,
    reused: bool,
    compared_relations: u64,
    resident_modes: u64,
}

#[cfg(target_os = "linux")]
#[derive(Default)]
struct CudaRelationRuntime {
    executor: Option<CudaExactRelationExecutor>,
    admissions: ModeAdmissionLedger<CudaModeRealization, CudaModeAdmissionWitness>,
}

#[cfg(target_os = "linux")]
impl CudaRelationRuntime {
    #[allow(clippy::too_many_arguments)]
    fn classify_positive_windows(
        &mut self,
        mode: CudaRelationMode,
        points: &[i64],
        point_count: u32,
        order: &[u32],
        windows: &[PackedRelationWindow],
        pair_count: u64,
        host_witness: impl FnOnce() -> Result<CudaSparseRelations, ObservationEcologyError>,
    ) -> Result<(CudaSparseRelations, CudaRelationReceipt, CudaModeUse), ObservationEcologyError>
    {
        let realization = CudaModeRealization {
            mode: mode.clone(),
            realization: CudaRelationRealization::SparsePositivePrediction,
        };
        let already_admitted = self.admissions.contains(&realization);
        let executor = self.executor()?;
        let (relations, receipt) = executor.classify_positive_windows(
            points,
            point_count,
            order,
            windows,
            pair_count,
            &mode.coefficients,
        )?;
        self.finish_mode_use(
            realization,
            relations,
            receipt,
            already_admitted,
            pair_count,
            host_witness,
        )
    }

    fn grade_sparse(
        &mut self,
        mode: CudaRelationMode,
        points: &[i64],
        point_count: u32,
        membership: &[u64],
        host_witness: impl FnOnce() -> Result<CudaSparseGrade, ObservationEcologyError>,
    ) -> Result<(CudaSparseGrade, CudaRelationReceipt, CudaModeUse), ObservationEcologyError> {
        let realization = CudaModeRealization {
            mode: mode.clone(),
            realization: CudaRelationRealization::SparseGrade,
        };
        let already_admitted = self.admissions.contains(&realization);
        let executor = self.executor()?;
        let (grade, receipt) =
            executor.grade_all_pairs_sparse(points, point_count, membership, &mode.coefficients)?;
        let compared_relations = receipt.classified_pairs;
        self.finish_mode_use(
            realization,
            grade,
            receipt,
            already_admitted,
            compared_relations,
            host_witness,
        )
    }

    fn executor(&mut self) -> Result<&mut CudaExactRelationExecutor, ObservationEcologyError> {
        if self.executor.is_none() {
            self.executor = Some(CudaExactRelationExecutor::new()?);
        }
        self.executor
            .as_mut()
            .ok_or(ObservationEcologyError::CudaRelationExecutorUnavailable)
    }

    fn finish_mode_use<T: PartialEq>(
        &mut self,
        realization: CudaModeRealization,
        result: T,
        receipt: CudaRelationReceipt,
        already_admitted: bool,
        compared_relations_if_admitted: u64,
        host_witness: impl FnOnce() -> Result<T, ObservationEcologyError>,
    ) -> Result<(T, CudaRelationReceipt, CudaModeUse), ObservationEcologyError> {
        let compared_relations;
        if already_admitted {
            let witness = self
                .admissions
                .admission(&realization)
                .ok_or(ObservationEcologyError::CudaModeRegistryInvariant)?;
            if witness.device != receipt.device || witness.kernel_sha256 != receipt.kernel_sha256 {
                return Err(ObservationEcologyError::CudaKernelChanged);
            }
            let _prior_witness_extent = witness.compared_relations;
            compared_relations = 0;
        } else {
            let host_result = host_witness()?;
            if host_result != result {
                return Err(ObservationEcologyError::CudaRelationParity);
            }
            compared_relations = compared_relations_if_admitted;
            self.admissions
                .admit(
                    realization,
                    CudaModeAdmissionWitness {
                        device: receipt.device.clone(),
                        kernel_sha256: receipt.kernel_sha256.clone(),
                        compared_relations,
                    },
                )
                .map_err(|_| ObservationEcologyError::CudaModeRegistryInvariant)?;
        }
        let resident_modes = u64::try_from(self.admissions.len())
            .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
        Ok((
            result,
            receipt,
            CudaModeUse {
                admitted: !already_admitted,
                reused: already_admitted,
                compared_relations,
                resident_modes,
            },
        ))
    }
}

/// Physical realization policy for one observation ecology.
///
/// Causal event order remains serial. Only the independent members of one
/// event-local antichain may execute concurrently. CUDA is never selected by
/// device presence: callers must construct the explicit CUDA policy.  Its
/// driver context and buffers persist with this law.  A structurally exact
/// mode is compared completely with the host once, then later occurrences of
/// that same mode are realized by the card without a shadow host classifier.
#[derive(Clone)]
pub struct ObservationEcologyLaw {
    cpu: CpuExecutor,
    exact_cuda_relations: bool,
    #[cfg(target_os = "linux")]
    cuda_runtime: Option<Arc<Mutex<CudaRelationRuntime>>>,
}

impl ObservationEcologyLaw {
    pub const fn serial() -> Self {
        Self {
            cpu: CpuExecutor::serial(),
            exact_cuda_relations: false,
            #[cfg(target_os = "linux")]
            cuda_runtime: None,
        }
    }

    pub const fn multicore(workers: NonZeroUsize) -> Self {
        Self {
            cpu: CpuExecutor::multicore(workers),
            exact_cuda_relations: false,
            #[cfg(target_os = "linux")]
            cuda_runtime: None,
        }
    }

    #[cfg(target_os = "linux")]
    pub fn multicore_cuda(workers: NonZeroUsize) -> Self {
        Self {
            cpu: CpuExecutor::multicore(workers),
            exact_cuda_relations: true,
            cuda_runtime: Some(Arc::new(Mutex::new(CudaRelationRuntime::default()))),
        }
    }

    pub const fn cpu_executor(&self) -> CpuExecutor {
        self.cpu
    }

    pub const fn exact_cuda_relations(&self) -> bool {
        self.exact_cuda_relations
    }

    #[cfg(target_os = "linux")]
    fn with_cuda_runtime<T>(
        &self,
        operation: impl FnOnce(&mut CudaRelationRuntime) -> Result<T, ObservationEcologyError>,
    ) -> Result<T, ObservationEcologyError> {
        let runtime = self
            .cuda_runtime
            .as_ref()
            .ok_or(ObservationEcologyError::CudaRelationExecutorUnavailable)?;
        let mut runtime = runtime
            .lock()
            .map_err(|_| ObservationEcologyError::CudaRelationRuntimePoisoned)?;
        operation(&mut runtime)
    }
}

impl std::fmt::Debug for ObservationEcologyLaw {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut body = formatter.debug_struct("ObservationEcologyLaw");
        body.field("cpu", &self.cpu);
        body.field("exact_cuda_relations", &self.exact_cuda_relations);
        #[cfg(target_os = "linux")]
        body.field("cuda_runtime", &self.cuda_runtime.is_some());
        body.finish()
    }
}

impl Default for ObservationEcologyLaw {
    fn default() -> Self {
        let workers = std::thread::available_parallelism()
            .unwrap_or_else(|_| NonZeroUsize::new(1).expect("one is nonzero"));
        Self::multicore(workers)
    }
}

fn execute_cpu_indexed<T, R>(
    executor: &CpuExecutor,
    inputs: &[T],
    work: &mut ObservationEcologyWork,
    operation: impl Fn(usize, &T) -> Result<R, ObservationEcologyError> + Sync,
) -> Result<Vec<R>, ObservationEcologyError>
where
    T: Sync,
    R: Send,
{
    let (outputs, receipt) = executor
        .execute_indexed(inputs, operation)
        .map_err(|error| match error {
            CpuExecutionError::Operation(error) => error,
            CpuExecutionError::WorkerPanicked => ObservationEcologyError::PhysicalWorkerPanicked,
        })?;
    accumulate_cpu_receipt(work, &receipt)?;
    Ok(outputs)
}

fn accumulate_cpu_receipt(
    work: &mut ObservationEcologyWork,
    receipt: &CpuExecutionReceipt,
) -> Result<(), ObservationEcologyError> {
    let tasks = receipt
        .tasks
        .to_u64()
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    let workers = receipt
        .workers_used
        .to_u64()
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    let antichains = u64::from(tasks != 0);
    work.cpu_tasks = work
        .cpu_tasks
        .checked_add(tasks)
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.cpu_workers_used = work.cpu_workers_used.max(workers);
    work.cpu_antichains = work
        .cpu_antichains
        .checked_add(antichains)
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.cpu_joins = work
        .cpu_joins
        .checked_add(
            receipt
                .joins
                .to_u64()
                .ok_or(ObservationEcologyError::CarrierOverflow)?,
        )
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    Ok(())
}

fn cpu_worker_limit(executor: &CpuExecutor) -> usize {
    match executor.mode {
        CpuExecutionMode::Serial => 1,
        CpuExecutionMode::Multicore { workers } => workers.get(),
    }
}

#[cfg(target_os = "linux")]
fn accumulate_cuda_receipt(
    work: &mut ObservationEcologyWork,
    receipt: &CudaRelationReceipt,
) -> Result<(), ObservationEcologyError> {
    work.cuda_classified_relations = work
        .cuda_classified_relations
        .checked_add(receipt.classified_pairs)
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.cuda_returned_relations = work
        .cuda_returned_relations
        .checked_add(receipt.returned_relations)
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.cuda_launches = work
        .cuda_launches
        .checked_add(receipt.launches)
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.cuda_front_uploads = work
        .cuda_front_uploads
        .checked_add(receipt.front_uploads)
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.cuda_allocation_resizes = work
        .cuda_allocation_resizes
        .checked_add(receipt.allocation_resizes)
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.cuda_host_to_device_octets = work
        .cuda_host_to_device_octets
        .checked_add(receipt.host_to_device_octets)
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.cuda_device_to_host_octets = work
        .cuda_device_to_host_octets
        .checked_add(receipt.device_to_host_octets)
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    match &work.cuda_device {
        Some(device) if device != &receipt.device => {
            return Err(ObservationEcologyError::CudaDeviceChanged);
        }
        None => work.cuda_device = Some(receipt.device.clone()),
        _ => {}
    }
    match &work.cuda_kernel_sha256 {
        Some(kernel) if kernel != &receipt.kernel_sha256 => {
            return Err(ObservationEcologyError::CudaKernelChanged);
        }
        None => work.cuda_kernel_sha256 = Some(receipt.kernel_sha256.clone()),
        _ => {}
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn accumulate_cuda_mode_use(
    work: &mut ObservationEcologyWork,
    mode_use: CudaModeUse,
) -> Result<(), ObservationEcologyError> {
    work.cuda_mode_admissions = work
        .cuda_mode_admissions
        .checked_add(u64::from(mode_use.admitted))
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.cuda_mode_reuses = work
        .cuda_mode_reuses
        .checked_add(u64::from(mode_use.reused))
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.cuda_parity_relations = work
        .cuda_parity_relations
        .checked_add(mode_use.compared_relations)
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.cuda_resident_modes = work.cuda_resident_modes.max(mode_use.resident_modes);
    Ok(())
}

impl ExactEventLaw for ObservationEcologyLaw {
    type Standing = ObservationEcologyStanding;
    type Event = ObservationEcologyEvent;
    type Radiation = ObservationEcologyRadiation;
    type Error = ObservationEcologyError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        let mut work = ObservationEcologyWork::default();
        validate_standing_with_executor(standing_before, &self.cpu, &mut work)?;
        let event_id = event.event();
        if standing_before.used_events.contains(&event_id) {
            return Err(ObservationEcologyError::RepeatedEvent(event_id));
        }
        let mut standing_after = standing_before.clone();
        let (kind, prediction, grade) = match event {
            ObservationEcologyEvent::DeclareFamily { family, .. } => {
                family.validate()?;
                if standing_after.families.contains_key(&family.id) {
                    return Err(ObservationEcologyError::RepeatedCoordinateFamily(family.id));
                }
                standing_after.families.insert(family.id, family.clone());
                (ObservationEcologyRadiationKind::FamilyDeclared, None, None)
            }
            ObservationEcologyEvent::DeclareChart { chart, .. } => {
                validate_chart(&standing_after, chart)?;
                if standing_after.charts.contains_key(&chart.id) {
                    return Err(ObservationEcologyError::RepeatedChart(chart.id));
                }
                standing_after.charts.insert(chart.id, chart.clone());
                (ObservationEcologyRadiationKind::ChartDeclared, None, None)
            }
            ObservationEcologyEvent::ConditionReturnedBatch {
                batch, returned, ..
            } => {
                validate_new_batch(&standing_after, batch, self, &mut work)?;
                validate_partition(batch, returned)?;
                insert_batch(
                    &mut standing_after,
                    event_id,
                    batch,
                    TestimonyDisposition::Admitted { event: event_id },
                )?;
                condition_relation(
                    &mut standing_after,
                    event_id,
                    batch,
                    returned,
                    &self.cpu,
                    &mut work,
                )?;
                Arc::make_mut(&mut standing_after.admitted_partitions).push(
                    AdmittedReceiverPartition {
                        event: event_id,
                        family: batch.family,
                        chronology: batch.chronology,
                        source: batch.source.clone(),
                        partition: Arc::new(returned.clone()),
                    },
                );
                (
                    ObservationEcologyRadiationKind::ReturnedBatchConditioned,
                    None,
                    None,
                )
            }
            ObservationEcologyEvent::ReturnPartitionAsReceivers {
                partition_event,
                upper_batch,
                returns,
                ..
            } => {
                validate_new_batch(&standing_after, upper_batch, self, &mut work)?;
                return_partition_as_receivers(
                    &mut standing_after,
                    event_id,
                    *partition_event,
                    upper_batch,
                    returns,
                )?;
                work.received_occurrences = u64::try_from(upper_batch.occurrences.len())
                    .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
                (
                    ObservationEcologyRadiationKind::PartitionReturnedAsReceivers,
                    None,
                    None,
                )
            }
            ObservationEcologyEvent::ConditionExistingReceiverBatch {
                batch, returned, ..
            } => {
                let materialized =
                    materialize_existing_batch(&standing_after, batch, &self.cpu, &mut work)?;
                validate_partition(&materialized, returned)?;
                condition_relation(
                    &mut standing_after,
                    event_id,
                    &materialized,
                    returned,
                    &self.cpu,
                    &mut work,
                )?;
                Arc::make_mut(&mut standing_after.admitted_partitions).push(
                    AdmittedReceiverPartition {
                        event: event_id,
                        family: materialized.family,
                        chronology: materialized.chronology,
                        source: materialized.source.clone(),
                        partition: Arc::new(returned.clone()),
                    },
                );
                (
                    ObservationEcologyRadiationKind::ExistingReceiverBatchConditioned,
                    None,
                    None,
                )
            }
            ObservationEcologyEvent::PredictUnpartitionedBatch {
                algorithm, batch, ..
            } => {
                validate_new_batch(&standing_after, batch, self, &mut work)?;
                let prediction_id = ReceiverPredictionId(standing_after.next_prediction);
                standing_after.next_prediction = standing_after
                    .next_prediction
                    .checked_add(1)
                    .ok_or(ObservationEcologyError::CarrierOverflow)?;
                let prediction = Arc::new(emit_prediction(
                    &standing_after,
                    event_id,
                    prediction_id,
                    *algorithm,
                    batch,
                    self,
                    &mut work,
                )?);
                insert_batch(
                    &mut standing_after,
                    event_id,
                    batch,
                    TestimonyDisposition::PendingPrediction {
                        prediction: prediction_id,
                    },
                )?;
                Arc::make_mut(&mut standing_after.predictions)
                    .insert(prediction_id, Arc::clone(&prediction));
                (
                    ObservationEcologyRadiationKind::PredictionEmitted,
                    Some(prediction),
                    None,
                )
            }
            ObservationEcologyEvent::PredictExistingReceiverBatch {
                algorithm, batch, ..
            } => {
                let materialized =
                    materialize_existing_batch(&standing_after, batch, &self.cpu, &mut work)?;
                let prediction_id = ReceiverPredictionId(standing_after.next_prediction);
                standing_after.next_prediction = standing_after
                    .next_prediction
                    .checked_add(1)
                    .ok_or(ObservationEcologyError::CarrierOverflow)?;
                let prediction = Arc::new(emit_prediction(
                    &standing_after,
                    event_id,
                    prediction_id,
                    *algorithm,
                    &materialized,
                    self,
                    &mut work,
                )?);
                Arc::make_mut(&mut standing_after.predictions)
                    .insert(prediction_id, Arc::clone(&prediction));
                (
                    ObservationEcologyRadiationKind::ExistingReceiverPredictionEmitted,
                    Some(prediction),
                    None,
                )
            }
            ObservationEcologyEvent::GradeReturnedPartition {
                prediction,
                returned,
                ..
            } => {
                let prediction_body = standing_after
                    .predictions
                    .get(prediction)
                    .cloned()
                    .ok_or(ObservationEcologyError::MissingPrediction(*prediction))?;
                if standing_after
                    .grades
                    .values()
                    .any(|grade| grade.prediction == *prediction)
                {
                    return Err(ObservationEcologyError::PredictionAlreadyGraded(
                        *prediction,
                    ));
                }
                let batch = batch_from_prediction(&standing_after, &prediction_body)?;
                validate_partition(&batch, returned)?;
                if returned.algorithm != prediction_body.algorithm {
                    return Err(ObservationEcologyError::ReturnedAlgorithmMismatch {
                        expected: prediction_body.algorithm,
                        received: returned.algorithm,
                    });
                }
                let grade_id = ReceiverGradeId(standing_after.next_grade);
                standing_after.next_grade = standing_after
                    .next_grade
                    .checked_add(1)
                    .ok_or(ObservationEcologyError::CarrierOverflow)?;
                let grade = Arc::new(grade_return(
                    event_id,
                    grade_id,
                    &prediction_body,
                    &batch,
                    returned,
                    &standing_after,
                    self,
                    &mut work,
                )?);
                Arc::make_mut(&mut standing_after.grades).insert(grade_id, Arc::clone(&grade));
                (
                    ObservationEcologyRadiationKind::ReturnGraded,
                    None,
                    Some(grade),
                )
            }
            ObservationEcologyEvent::AdmitGradedReturn { grade, .. } => {
                let grade_body = standing_after
                    .grades
                    .get(grade)
                    .cloned()
                    .ok_or(ObservationEcologyError::MissingGrade(*grade))?;
                if standing_after.admitted_grades.contains(grade) {
                    return Err(ObservationEcologyError::GradeAlreadyAdmitted(*grade));
                }
                let prediction = standing_after
                    .predictions
                    .get(&grade_body.prediction)
                    .cloned()
                    .ok_or(ObservationEcologyError::MissingPrediction(
                        grade_body.prediction,
                    ))?;
                let batch = batch_from_prediction(&standing_after, &prediction)?;
                condition_relation(
                    &mut standing_after,
                    event_id,
                    &batch,
                    &grade_body.returned,
                    &self.cpu,
                    &mut work,
                )?;
                Arc::make_mut(&mut standing_after.admitted_partitions).push(
                    AdmittedReceiverPartition {
                        event: event_id,
                        family: batch.family,
                        chronology: batch.chronology,
                        source: batch.source.clone(),
                        partition: Arc::clone(&grade_body.returned),
                    },
                );
                standing_after.admitted_grades.insert(*grade);
                (
                    ObservationEcologyRadiationKind::GradedReturnAdmitted,
                    None,
                    None,
                )
            }
        };
        standing_after.used_events.insert(event_id);
        validate_standing_with_executor(&standing_after, &self.cpu, &mut work)?;
        let logical_resources = logical_resources(kind, &work);
        let physical_resources = physical_resources(&work)?;
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![ObservationEcologyRadiation {
                schema: RADIATION_SCHEMA.to_owned(),
                event: event_id,
                kind,
                prediction,
                grade,
                work,
            }],
            logical_resources: Some(logical_resources),
            physical_resources: Some(physical_resources),
        })
    }
}

fn validate_chart(
    standing: &ObservationEcologyStanding,
    chart: &ReceiverAffineChart,
) -> Result<(), ObservationEcologyError> {
    chart.validate_shape()?;
    let family = standing.families.get(&chart.family).ok_or(
        ObservationEcologyError::MissingCoordinateFamily(chart.family),
    )?;
    if chart.offset.len() != family.coordinates.len() {
        return Err(ObservationEcologyError::ChartFamilyDimension {
            chart: chart.id,
            chart_dimension: chart.offset.len(),
            family_dimension: family.coordinates.len(),
        });
    }
    Ok(())
}

#[derive(Clone)]
enum PackedApertureValidation {
    Exact(Vec<PackedRawInterval>),
    Impossible,
    General,
}

#[derive(Clone)]
struct PackedRawInterval {
    raw_coordinate: usize,
    lower: i64,
    upper: i64,
}

fn pack_aperture_validation(
    chart: &ReceiverAffineChart,
    aperture: &[ExactCoordinateInterval],
) -> Result<PackedApertureValidation, ObservationEcologyError> {
    let mut packed = Vec::with_capacity(aperture.len());
    for interval in aperture {
        let coordinate = usize::try_from(interval.coordinate)
            .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
        let row = chart
            .basis
            .get(coordinate)
            .ok_or(ObservationEcologyError::MalformedChart(chart.id))?;
        let nonzero = row
            .iter()
            .enumerate()
            .filter(|(_, coefficient)| !coefficient.is_zero())
            .collect::<Vec<_>>();
        if nonzero.is_empty() {
            if chart.offset[coordinate] < interval.lower
                || chart.offset[coordinate] > interval.upper
            {
                return Ok(PackedApertureValidation::Impossible);
            }
            continue;
        }
        if nonzero.len() != 1 {
            return Ok(PackedApertureValidation::General);
        }
        let raw_coordinate = nonzero[0].0;
        let scale = nonzero[0].1;
        let first = (&interval.lower - &chart.offset[coordinate]) / scale;
        let second = (&interval.upper - &chart.offset[coordinate]) / scale;
        let lower_ratio = first.clone().min(second.clone());
        let upper_ratio = first.max(second);
        let lower = rational_ceiling(&lower_ratio);
        let upper = rational_floor(&upper_ratio);
        if lower > BigInt::from(i64::MAX) || upper < BigInt::from(i64::MIN) || lower > upper {
            return Ok(PackedApertureValidation::Impossible);
        }
        packed.push(PackedRawInterval {
            raw_coordinate,
            lower: lower.to_i64().unwrap_or(i64::MIN),
            upper: upper.to_i64().unwrap_or(i64::MAX),
        });
    }
    Ok(PackedApertureValidation::Exact(packed))
}

fn rational_floor(value: &Rat) -> BigInt {
    let quotient = value.numer() / value.denom();
    let remainder = value.numer() % value.denom();
    if value.numer().is_negative() && !remainder.is_zero() {
        quotient - BigInt::from(1_u8)
    } else {
        quotient
    }
}

fn rational_ceiling(value: &Rat) -> BigInt {
    let quotient = value.numer() / value.denom();
    let remainder = value.numer() % value.denom();
    if value.numer().is_positive() && !remainder.is_zero() {
        quotient + BigInt::from(1_u8)
    } else {
        quotient
    }
}

fn validate_new_batch(
    standing: &ObservationEcologyStanding,
    batch: &ReceiverBatch,
    law: &ObservationEcologyLaw,
    work: &mut ObservationEcologyWork,
) -> Result<(), ObservationEcologyError> {
    if batch.source.is_empty() {
        return Err(ObservationEcologyError::EmptyBatchSource);
    }
    let family = standing.families.get(&batch.family).ok_or(
        ObservationEcologyError::MissingCoordinateFamily(batch.family),
    )?;
    let mut aperture_coordinates = BTreeSet::new();
    for interval in &batch.aperture {
        let coordinate = usize::try_from(interval.coordinate)
            .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
        if coordinate >= family.coordinates.len()
            || interval.lower > interval.upper
            || !aperture_coordinates.insert(coordinate)
        {
            return Err(ObservationEcologyError::MalformedReceiverAperture);
        }
    }
    let mut ids = BTreeSet::new();
    for occurrence in &batch.occurrences {
        if !ids.insert(occurrence.id) || standing.testimonies.contains_key(&occurrence.id) {
            return Err(ObservationEcologyError::RepeatedTestimony(occurrence.id));
        }
    }
    let packed_apertures = if law.exact_cuda_relations {
        batch
            .occurrences
            .iter()
            .map(|occurrence| occurrence.chart)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(|chart_id| {
                let chart = standing
                    .charts
                    .get(&chart_id)
                    .ok_or(ObservationEcologyError::MissingChart(chart_id))?;
                Ok((chart_id, pack_aperture_validation(chart, &batch.aperture)?))
            })
            .collect::<Result<BTreeMap<_, _>, ObservationEcologyError>>()?
    } else {
        BTreeMap::new()
    };
    execute_cpu_indexed(&law.cpu, &batch.occurrences, work, |_index, occurrence| {
        let chart = standing
            .charts
            .get(&occurrence.chart)
            .ok_or(ObservationEcologyError::MissingChart(occurrence.chart))?;
        if chart.family != batch.family
            || chart.receiver != occurrence.receiver
            || chart.offset.len() != family.coordinates.len()
            || occurrence.raw.len() != chart.raw_coordinates.len()
        {
            return Err(ObservationEcologyError::OccurrenceChartMismatch(
                occurrence.id,
            ));
        }
        match packed_apertures.get(&chart.id) {
            Some(PackedApertureValidation::Exact(intervals)) => {
                if intervals.iter().any(|interval| {
                    occurrence.raw[interval.raw_coordinate] < interval.lower
                        || occurrence.raw[interval.raw_coordinate] > interval.upper
                }) {
                    return Err(ObservationEcologyError::TestimonyOutsideAperture(
                        occurrence.id,
                    ));
                }
            }
            Some(PackedApertureValidation::Impossible) => {
                return Err(ObservationEcologyError::TestimonyOutsideAperture(
                    occurrence.id,
                ));
            }
            Some(PackedApertureValidation::General) | None => {
                for interval in &batch.aperture {
                    let coordinate = usize::try_from(interval.coordinate)
                        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
                    let received = chart.receive_coordinate(&occurrence.raw, coordinate)?;
                    if received < interval.lower || received > interval.upper {
                        return Err(ObservationEcologyError::TestimonyOutsideAperture(
                            occurrence.id,
                        ));
                    }
                }
            }
        }
        Ok(())
    })?;
    Ok(())
}

fn validate_partition(
    batch: &ReceiverBatch,
    returned: &ReturnedReceiverPartition,
) -> Result<(), ObservationEcologyError> {
    let supplied = batch
        .occurrences
        .iter()
        .map(|occurrence| occurrence.id)
        .collect::<BTreeSet<_>>();
    let mut cell_ids = BTreeSet::new();
    let mut membership = BTreeMap::<ReceiverTestimonyId, usize>::new();
    for cell in &returned.cells {
        if !cell_ids.insert(cell.id) || cell.members.is_empty() {
            return Err(ObservationEcologyError::MalformedReturnedPartition);
        }
        for member in &cell.members {
            if !supplied.contains(member) {
                return Err(ObservationEcologyError::PartitionForeignTestimony(*member));
            }
            *membership.entry(*member).or_default() += 1;
        }
    }
    if returned.coverage == ReturnedCellCoverage::CompleteExclusive
        && (membership.len() != supplied.len()
            || membership.values().any(|multiplicity| *multiplicity != 1))
    {
        return Err(ObservationEcologyError::IncompleteExclusivePartition);
    }
    Ok(())
}

fn insert_batch(
    standing: &mut ObservationEcologyStanding,
    _event: EventId,
    batch: &ReceiverBatch,
    disposition: TestimonyDisposition,
) -> Result<(), ObservationEcologyError> {
    let testimonies = Arc::make_mut(&mut standing.testimonies);
    for occurrence in &batch.occurrences {
        if testimonies
            .insert(
                occurrence.id,
                ReceiverTestimonyStanding {
                    occurrence: occurrence.clone(),
                    disposition: disposition.clone(),
                },
            )
            .is_some()
        {
            return Err(ObservationEcologyError::RepeatedTestimony(occurrence.id));
        }
    }
    Ok(())
}

fn return_partition_as_receivers(
    standing: &mut ObservationEcologyStanding,
    event: EventId,
    partition_event: EventId,
    upper_batch: &ReceiverBatch,
    returns: &[ReceiverCellReturn],
) -> Result<(), ObservationEcologyError> {
    let lower = standing
        .admitted_partitions
        .iter()
        .find(|partition| partition.event == partition_event)
        .cloned()
        .ok_or(ObservationEcologyError::MissingAdmittedPartition(
            partition_event,
        ))?;
    if lower.partition.coverage != ReturnedCellCoverage::CompleteExclusive {
        return Err(ObservationEcologyError::NonexclusiveReceiverReturn);
    }
    if upper_batch.chronology < lower.chronology {
        return Err(
            ObservationEcologyError::ReceiverReturnChronologyRegression {
                lower: lower.chronology,
                upper: upper_batch.chronology,
            },
        );
    }
    let lower_cells = lower
        .partition
        .cells
        .iter()
        .map(|cell| (cell.id, cell))
        .collect::<BTreeMap<_, _>>();
    let upper_occurrences = upper_batch
        .occurrences
        .iter()
        .map(|occurrence| (occurrence.id, occurrence))
        .collect::<BTreeMap<_, _>>();
    if returns.len() != lower_cells.len()
        || returns.len() != upper_occurrences.len()
        || returns
            .iter()
            .map(|relation| relation.source_cell)
            .collect::<BTreeSet<_>>()
            != lower_cells.keys().copied().collect()
        || returns
            .iter()
            .map(|relation| relation.target)
            .collect::<BTreeSet<_>>()
            != upper_occurrences.keys().copied().collect()
    {
        return Err(ObservationEcologyError::IncompleteReceiverReturn);
    }
    for relation in returns {
        let upper = upper_occurrences
            .get(&relation.target)
            .ok_or(ObservationEcologyError::IncompleteReceiverReturn)?;
        if upper.source_identity != relation.source_cell.0 {
            return Err(ObservationEcologyError::ReceiverReturnIdentityMismatch {
                cell: relation.source_cell,
                testimony: relation.target,
            });
        }
        if standing.receiver_quotients.values().any(|quotient| {
            quotient.source
                == (ReturnedReceiverCellAddress {
                    partition_event,
                    cell: relation.source_cell,
                })
        }) || standing
            .receiver_quotient_by_target
            .contains_key(&relation.target)
        {
            return Err(ObservationEcologyError::RepeatedReceiverReturn);
        }
    }
    insert_batch(
        standing,
        event,
        upper_batch,
        TestimonyDisposition::Admitted { event },
    )?;
    for relation in returns {
        let quotient = ReceiverGrainQuotientId(standing.next_receiver_quotient);
        standing.next_receiver_quotient = standing
            .next_receiver_quotient
            .checked_add(1)
            .ok_or(ObservationEcologyError::CarrierOverflow)?;
        standing.receiver_quotients.insert(
            quotient,
            ReceiverGrainQuotient {
                id: quotient,
                caused_by: event,
                source: ReturnedReceiverCellAddress {
                    partition_event,
                    cell: relation.source_cell,
                },
                source_family: lower.family,
                target_family: upper_batch.family,
                target_chronology: upper_batch.chronology,
                target: relation.target,
            },
        );
        standing
            .receiver_quotient_by_target
            .insert(relation.target, quotient);
    }
    Ok(())
}

fn materialize_existing_batch(
    standing: &ObservationEcologyStanding,
    batch: &ExistingReceiverBatch,
    executor: &CpuExecutor,
    work: &mut ObservationEcologyWork,
) -> Result<ReceiverBatch, ObservationEcologyError> {
    if batch.source.is_empty() {
        return Err(ObservationEcologyError::EmptyBatchSource);
    }
    let family = standing.families.get(&batch.family).ok_or(
        ObservationEcologyError::MissingCoordinateFamily(batch.family),
    )?;
    let mut aperture_coordinates = BTreeSet::new();
    for interval in &batch.aperture {
        let coordinate = usize::try_from(interval.coordinate)
            .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
        if coordinate >= family.coordinates.len()
            || interval.lower > interval.upper
            || !aperture_coordinates.insert(coordinate)
        {
            return Err(ObservationEcologyError::MalformedReceiverAperture);
        }
    }
    let mut unique = BTreeSet::new();
    let occurrences = batch
        .occurrences
        .iter()
        .map(|id| {
            if !unique.insert(*id) {
                return Err(ObservationEcologyError::RepeatedTestimony(*id));
            }
            let quotient_id = standing
                .receiver_quotient_by_target
                .get(id)
                .ok_or(ObservationEcologyError::TestimonyIsNotReceiverReturn(*id))?;
            let quotient = standing
                .receiver_quotients
                .get(quotient_id)
                .ok_or(ObservationEcologyError::MalformedStanding)?;
            if quotient.target_family != batch.family
                || quotient.target_chronology != batch.chronology
            {
                return Err(ObservationEcologyError::ReceiverReturnChronologyMismatch {
                    testimony: *id,
                    expected: quotient.target_chronology,
                    received: batch.chronology,
                });
            }
            let body = standing
                .testimonies
                .get(id)
                .ok_or(ObservationEcologyError::MissingTestimony(*id))?;
            if !testimony_is_admitted(standing, &body.disposition) {
                return Err(ObservationEcologyError::TestimonyIsNotAdmitted(*id));
            }
            let chart = standing
                .charts
                .get(&body.occurrence.chart)
                .ok_or(ObservationEcologyError::MissingChart(body.occurrence.chart))?;
            if chart.family != batch.family {
                return Err(ObservationEcologyError::OccurrenceChartMismatch(*id));
            }
            Ok(body.occurrence.clone())
        })
        .collect::<Result<Vec<_>, _>>()?;
    execute_cpu_indexed(executor, &occurrences, work, |_index, occurrence| {
        let chart = standing
            .charts
            .get(&occurrence.chart)
            .ok_or(ObservationEcologyError::MissingChart(occurrence.chart))?;
        for interval in &batch.aperture {
            let coordinate = usize::try_from(interval.coordinate)
                .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
            let received = chart.receive_coordinate(&occurrence.raw, coordinate)?;
            if received < interval.lower || received > interval.upper {
                return Err(ObservationEcologyError::TestimonyOutsideAperture(
                    occurrence.id,
                ));
            }
        }
        Ok(())
    })?;
    Ok(ReceiverBatch {
        family: batch.family,
        chronology: batch.chronology,
        source: batch.source.clone(),
        aperture: batch.aperture.clone(),
        occurrences,
    })
}

fn testimony_is_admitted(
    standing: &ObservationEcologyStanding,
    disposition: &TestimonyDisposition,
) -> bool {
    match disposition {
        TestimonyDisposition::Admitted { .. } => true,
        TestimonyDisposition::PendingPrediction { prediction } => standing
            .admitted_grades
            .iter()
            .filter_map(|grade| standing.grades.get(grade))
            .any(|grade| grade.prediction == *prediction),
        TestimonyDisposition::Graded { grade } => standing.admitted_grades.contains(grade),
    }
}

fn decoded_batch(
    standing: &ObservationEcologyStanding,
    batch: &ReceiverBatch,
    executor: &CpuExecutor,
    work: &mut ObservationEcologyWork,
) -> Result<BTreeMap<ReceiverTestimonyId, Vec<Rat>>, ObservationEcologyError> {
    let received =
        execute_cpu_indexed(executor, &batch.occurrences, work, |_index, occurrence| {
            let chart = standing
                .charts
                .get(&occurrence.chart)
                .ok_or(ObservationEcologyError::MissingChart(occurrence.chart))?;
            Ok((occurrence.id, chart.receive(&occurrence.raw)?))
        })?;
    let mut decoded = BTreeMap::new();
    for (id, coordinates) in received {
        if decoded.insert(id, coordinates).is_some() {
            return Err(ObservationEcologyError::RepeatedTestimony(id));
        }
    }
    Ok(decoded)
}

fn coordinates_at(
    coordinates: &[Rat],
    selected: &[u32],
) -> Result<Vec<Rat>, ObservationEcologyError> {
    selected
        .iter()
        .map(|coordinate| {
            let coordinate = usize::try_from(*coordinate)
                .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
            coordinates
                .get(coordinate)
                .cloned()
                .ok_or(ObservationEcologyError::MalformedStanding)
        })
        .collect()
}

fn difference_at(
    left: &[Rat],
    right: &[Rat],
    selected: &[u32],
) -> Result<ExactDifferenceVector, ObservationEcologyError> {
    Ok(ExactDifferenceVector(
        selected
            .iter()
            .map(|coordinate| {
                let coordinate = usize::try_from(*coordinate)
                    .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
                let left = left
                    .get(coordinate)
                    .ok_or(ObservationEcologyError::MalformedStanding)?;
                let right = right
                    .get(coordinate)
                    .ok_or(ObservationEcologyError::MalformedStanding)?;
                Ok((left - right).abs())
            })
            .collect::<Result<Vec<_>, ObservationEcologyError>>()?,
    ))
}

fn cell_span(
    members: &BTreeSet<ReceiverTestimonyId>,
    decoded: &BTreeMap<ReceiverTestimonyId, Vec<Rat>>,
    selected: &[u32],
) -> Result<ExactDifferenceVector, ObservationEcologyError> {
    let mut span = Vec::with_capacity(selected.len());
    for coordinate in selected {
        let coordinate =
            usize::try_from(*coordinate).map_err(|_| ObservationEcologyError::CarrierOverflow)?;
        let mut values = members.iter().map(|member| {
            decoded
                .get(member)
                .and_then(|coordinates| coordinates.get(coordinate))
                .cloned()
                .ok_or(ObservationEcologyError::MissingTestimony(*member))
        });
        let first = values
            .next()
            .ok_or(ObservationEcologyError::MalformedReturnedPartition)??;
        let mut minimum = first.clone();
        let mut maximum = first;
        for value in values {
            let value = value?;
            minimum = minimum.min(value.clone());
            maximum = maximum.max(value);
        }
        span.push(maximum - minimum);
    }
    Ok(ExactDifferenceVector(span))
}

fn exclusive_membership(
    returned: &ReturnedReceiverPartition,
) -> Result<BTreeMap<ReceiverTestimonyId, ReturnedCellId>, ObservationEcologyError> {
    if returned.coverage != ReturnedCellCoverage::CompleteExclusive {
        return Err(ObservationEcologyError::NonexclusiveRelationTraining);
    }
    let mut membership = BTreeMap::new();
    for cell in &returned.cells {
        for member in &cell.members {
            if membership.insert(*member, cell.id).is_some() {
                return Err(ObservationEcologyError::IncompleteExclusivePartition);
            }
        }
    }
    Ok(membership)
}

fn strata(
    batch: &ReceiverBatch,
    family: &ReceiverCoordinateFamily,
    decoded: &BTreeMap<ReceiverTestimonyId, Vec<Rat>>,
) -> Result<BTreeMap<Vec<Rat>, Vec<ReceiverTestimonyId>>, ObservationEcologyError> {
    let mut strata = BTreeMap::<Vec<Rat>, Vec<ReceiverTestimonyId>>::new();
    for occurrence in &batch.occurrences {
        let coordinates = decoded
            .get(&occurrence.id)
            .ok_or(ObservationEcologyError::MissingTestimony(occurrence.id))?;
        strata
            .entry(coordinates_at(coordinates, &family.stratum_coordinates)?)
            .or_default()
            .push(occurrence.id);
    }
    for members in strata.values_mut() {
        members.sort();
    }
    Ok(strata)
}

#[cfg(target_os = "linux")]
#[derive(Clone)]
struct PackedObservationStratum {
    members: Vec<ReceiverTestimonyId>,
    points: Vec<i64>,
    scales: Vec<Rat>,
    front: PackedRelationFront,
}

#[cfg(target_os = "linux")]
fn cuda_relation_mode(
    family: ReceiverCoordinateFamilyId,
    algorithm: ReturnedAlgorithmId,
    stratum: &PackedObservationStratum,
) -> CudaRelationMode {
    ExactModeSignature::new(
        CudaRelationModeBoundary { family, algorithm },
        stratum.front.clone(),
        stratum.scales.clone(),
    )
}

#[cfg(target_os = "linux")]
fn pack_observation_stratum(
    members: &[ReceiverTestimonyId],
    occurrences: &BTreeMap<ReceiverTestimonyId, &ReceiverTestimony>,
    standing: &ObservationEcologyStanding,
    family: &ReceiverCoordinateFamily,
    relation: &LearnedPartitionRelation,
) -> Result<Option<PackedObservationStratum>, ObservationEcologyError> {
    let Some(first) = members.first() else {
        return Ok(None);
    };
    let first_occurrence = occurrences
        .get(first)
        .ok_or(ObservationEcologyError::MissingTestimony(*first))?;
    let chart = standing.charts.get(&first_occurrence.chart).ok_or(
        ObservationEcologyError::MissingChart(first_occurrence.chart),
    )?;
    if members.iter().any(|member| {
        occurrences
            .get(member)
            .is_none_or(|occurrence| occurrence.chart != chart.id)
    }) {
        return Ok(None);
    }

    let mut raw_coordinates = Vec::with_capacity(family.relation_coordinates.len());
    let mut scales = Vec::with_capacity(family.relation_coordinates.len());
    for coordinate in &family.relation_coordinates {
        let coordinate =
            usize::try_from(*coordinate).map_err(|_| ObservationEcologyError::CarrierOverflow)?;
        let row = chart
            .basis
            .get(coordinate)
            .ok_or(ObservationEcologyError::MalformedChart(chart.id))?;
        let nonzero = row
            .iter()
            .enumerate()
            .filter(|(_, coefficient)| !coefficient.is_zero())
            .collect::<Vec<_>>();
        if nonzero.len() != 1 {
            return Ok(None);
        }
        raw_coordinates.push(nonzero[0].0);
        scales.push(nonzero[0].1.abs());
    }

    let mut points = Vec::with_capacity(
        members
            .len()
            .checked_mul(raw_coordinates.len())
            .ok_or(ObservationEcologyError::CarrierOverflow)?,
    );
    for member in members {
        let occurrence = occurrences
            .get(member)
            .ok_or(ObservationEcologyError::MissingTestimony(*member))?;
        for raw_coordinate in &raw_coordinates {
            points.push(*occurrence.raw.get(*raw_coordinate).ok_or(
                ObservationEcologyError::RawCoordinateDimension {
                    chart: chart.id,
                    expected: chart.raw_coordinates.len(),
                    received: occurrence.raw.len(),
                },
            )?);
        }
    }

    let dimension = u32::try_from(raw_coordinates.len())
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    let mut positive_maxima = Vec::new();
    for maximum in &relation.positive_maxima {
        for (value, scale) in maximum.0.iter().zip(&scales) {
            positive_maxima.push(raw_floor_threshold(value, scale)?);
        }
    }
    let mut negative_minima = Vec::new();
    for minimum in &relation.negative_minima {
        let packed = minimum
            .0
            .iter()
            .zip(&scales)
            .map(|(value, scale)| raw_ceiling_threshold(value, scale))
            .collect::<Result<Option<Vec<_>>, _>>()?;
        if let Some(packed) = packed {
            negative_minima.extend(packed);
        }
    }
    Ok(Some(PackedObservationStratum {
        members: members.to_vec(),
        points,
        scales,
        front: PackedRelationFront {
            dimension,
            positive_maxima,
            negative_minima,
        },
    }))
}

#[cfg(target_os = "linux")]
fn packed_strata(
    batch: &ReceiverBatch,
    standing: &ObservationEcologyStanding,
    family: &ReceiverCoordinateFamily,
    relation: &LearnedPartitionRelation,
) -> Result<Vec<PackedObservationStratum>, ObservationEcologyError> {
    let occurrences = batch
        .occurrences
        .iter()
        .map(|occurrence| (occurrence.id, occurrence))
        .collect::<BTreeMap<_, _>>();
    let mut by_stratum = BTreeMap::<Vec<Rat>, Vec<ReceiverTestimonyId>>::new();
    for occurrence in &batch.occurrences {
        let chart = standing
            .charts
            .get(&occurrence.chart)
            .ok_or(ObservationEcologyError::MissingChart(occurrence.chart))?;
        let key = family
            .stratum_coordinates
            .iter()
            .map(|coordinate| {
                let coordinate = usize::try_from(*coordinate)
                    .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
                chart.receive_coordinate(&occurrence.raw, coordinate)
            })
            .collect::<Result<Vec<_>, ObservationEcologyError>>()?;
        by_stratum.entry(key).or_default().push(occurrence.id);
    }
    by_stratum
        .into_values()
        .map(|mut members| {
            members.sort();
            pack_observation_stratum(&members, &occurrences, standing, family, relation)?
                .ok_or(ObservationEcologyError::CudaRelationChartNotPackable)
        })
        .collect()
}

#[cfg(target_os = "linux")]
fn raw_floor_threshold(value: &Rat, scale: &Rat) -> Result<u64, ObservationEcologyError> {
    if value.is_negative() || scale <= &Rat::zero() {
        return Err(ObservationEcologyError::MalformedPackedRelation);
    }
    let quotient = value / scale;
    let maximum = Rat::from_integer(BigInt::from(u64::MAX));
    if quotient >= maximum {
        return Ok(u64::MAX);
    }
    quotient
        .to_integer()
        .to_u64()
        .ok_or(ObservationEcologyError::MalformedPackedRelation)
}

#[cfg(target_os = "linux")]
fn raw_ceiling_threshold(value: &Rat, scale: &Rat) -> Result<Option<u64>, ObservationEcologyError> {
    if value.is_negative() || scale <= &Rat::zero() {
        return Err(ObservationEcologyError::MalformedPackedRelation);
    }
    let quotient = value / scale;
    let maximum = Rat::from_integer(BigInt::from(u64::MAX));
    if quotient > maximum {
        return Ok(None);
    }
    let floor = quotient.to_integer();
    let ceiling = if quotient == Rat::from_integer(floor.clone()) {
        floor
    } else {
        floor + BigInt::from(1_u8)
    };
    Ok(Some(
        ceiling
            .to_u64()
            .ok_or(ObservationEcologyError::MalformedPackedRelation)?,
    ))
}

#[cfg(target_os = "linux")]
fn packed_relation_state(
    points: &[i64],
    left: usize,
    right: usize,
    front: &PackedRelationFront,
) -> Result<u8, ObservationEcologyError> {
    let dimension =
        usize::try_from(front.dimension).map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    let positive = front
        .positive_maxima
        .chunks_exact(dimension)
        .any(|maximum| {
            maximum.iter().enumerate().all(|(coordinate, maximum)| {
                points[left * dimension + coordinate]
                    .abs_diff(points[right * dimension + coordinate])
                    <= *maximum
            })
        });
    let negative = front
        .negative_minima
        .chunks_exact(dimension)
        .any(|minimum| {
            minimum.iter().enumerate().all(|(coordinate, minimum)| {
                *minimum
                    <= points[left * dimension + coordinate]
                        .abs_diff(points[right * dimension + coordinate])
            })
        });
    Ok(match (positive, negative) {
        (true, false) => 0,
        (false, true) => 1,
        (false, false) => 2,
        (true, true) => 3,
    })
}

#[cfg(target_os = "linux")]
fn packed_difference(
    packed: &PackedObservationStratum,
    left: usize,
    right: usize,
) -> Result<ExactDifferenceVector, ObservationEcologyError> {
    let dimension = usize::try_from(packed.front.dimension)
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    Ok(ExactDifferenceVector(
        (0..dimension)
            .map(|coordinate| {
                let raw = packed.points[left * dimension + coordinate]
                    .abs_diff(packed.points[right * dimension + coordinate]);
                &packed.scales[coordinate] * Rat::from_integer(BigInt::from(raw))
            })
            .collect(),
    ))
}

#[cfg(target_os = "linux")]
fn state_from_wire(state: u8) -> Result<ReceiverRelationState, ObservationEcologyError> {
    match state {
        0 => Ok(ReceiverRelationState::ForcedTogether),
        1 => Ok(ReceiverRelationState::ForcedApart),
        2 => Ok(ReceiverRelationState::Open),
        3 => Ok(ReceiverRelationState::Conflicted),
        _ => Err(ObservationEcologyError::MalformedCudaRelationState(state)),
    }
}

fn condition_relation(
    standing: &mut ObservationEcologyStanding,
    event: EventId,
    batch: &ReceiverBatch,
    returned: &ReturnedReceiverPartition,
    executor: &CpuExecutor,
    work: &mut ObservationEcologyWork,
) -> Result<(), ObservationEcologyError> {
    let family = standing.families.get(&batch.family).cloned().ok_or(
        ObservationEcologyError::MissingCoordinateFamily(batch.family),
    )?;
    let decoded = decoded_batch(standing, batch, executor, work)?;
    let membership = exclusive_membership(returned)?;
    if membership.len() != batch.occurrences.len() {
        return Err(ObservationEcologyError::IncompleteExclusivePartition);
    }
    let strata = strata(batch, &family, &decoded)?;
    let stratum_by_member = strata
        .iter()
        .flat_map(|(stratum, members)| members.iter().map(move |member| (*member, stratum.clone())))
        .collect::<BTreeMap<_, _>>();

    let positive_candidates =
        execute_cpu_indexed(executor, &returned.cells, work, |_index, cell| {
            let cell_strata = cell
                .members
                .iter()
                .map(|member| {
                    stratum_by_member
                        .get(member)
                        .cloned()
                        .ok_or(ObservationEcologyError::MissingTestimony(*member))
                })
                .collect::<Result<BTreeSet<_>, _>>()?;
            if cell_strata.len() != 1 {
                return Err(ObservationEcologyError::ReturnedCellCrossesStrata(cell.id));
            }
            cell_span(&cell.members, &decoded, &family.relation_coordinates)
        })?;
    let positive = canonical_maximal_front(positive_candidates);

    // A cross-cell boundary witness is selected without a scalar metric.
    // For every relation coordinate, adjacent members in its exact order
    // contribute their complete multi-coordinate difference.
    let stratum_members = strata.values().cloned().collect::<Vec<_>>();
    let negative_by_stratum =
        execute_cpu_indexed(executor, &stratum_members, work, |_index, members| {
            let mut stratum_negative = Vec::new();
            for coordinate in &family.relation_coordinates {
                let coordinate = usize::try_from(*coordinate)
                    .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
                let mut ordered = members.clone();
                ordered.sort_by(|left, right| {
                    decoded[left][coordinate]
                        .cmp(&decoded[right][coordinate])
                        .then_with(|| left.cmp(right))
                });
                for pair in ordered.windows(2) {
                    if membership[&pair[0]] != membership[&pair[1]] {
                        stratum_negative.push(difference_at(
                            &decoded[&pair[0]],
                            &decoded[&pair[1]],
                            &family.relation_coordinates,
                        )?);
                    }
                }
            }
            Ok(canonical_minimal_front(stratum_negative))
        })?;
    let mut negative = Vec::new();
    for candidates in negative_by_stratum {
        merge_minimal_front(&mut negative, candidates);
    }

    let relation = standing
        .relations
        .entry((batch.family, returned.algorithm))
        .or_insert_with(|| LearnedPartitionRelation::new(batch.family, returned.algorithm));
    relation.extend_positive(positive);
    relation.extend_negative(negative);
    relation.testimony_events.insert(event);
    relation.returned_cells = relation
        .returned_cells
        .checked_add(
            u64::try_from(returned.cells.len())
                .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
        )
        .ok_or(ObservationEcologyError::CarrierOverflow)?;

    work.received_occurrences = u64::try_from(batch.occurrences.len())
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    work.decoded_coordinates = work
        .received_occurrences
        .checked_mul(
            u64::try_from(family.coordinates.len())
                .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
        )
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.retained_positive_generators = u64::try_from(relation.positive_maxima.len())
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    work.retained_negative_generators = u64::try_from(relation.negative_minima.len())
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    Ok(())
}

struct PredictionStratumResult {
    relations: Vec<PredictedReceiverRelation>,
    inspected: u64,
}

#[cfg(target_os = "linux")]
struct PackedPredictionTraversal {
    order: Vec<u32>,
    windows: Vec<PackedRelationWindow>,
    pair_count: u64,
}

fn emit_prediction(
    standing: &ObservationEcologyStanding,
    event: EventId,
    prediction: ReceiverPredictionId,
    algorithm: ReturnedAlgorithmId,
    batch: &ReceiverBatch,
    law: &ObservationEcologyLaw,
    work: &mut ObservationEcologyWork,
) -> Result<ReceiverRelationPrediction, ObservationEcologyError> {
    let family = standing.families.get(&batch.family).ok_or(
        ObservationEcologyError::MissingCoordinateFamily(batch.family),
    )?;
    let relation = standing
        .relations
        .get(&(batch.family, algorithm))
        .cloned()
        .ok_or(ObservationEcologyError::MissingLearnedRelation {
            family: batch.family,
            algorithm,
        })?;
    #[cfg(target_os = "linux")]
    if law.exact_cuda_relations {
        match emit_packed_prediction(
            standing,
            event,
            prediction,
            algorithm,
            batch,
            family,
            relation.clone(),
            law,
            work,
        ) {
            Ok(prediction) => return Ok(prediction),
            Err(ObservationEcologyError::CudaRelationChartNotPackable) => {}
            Err(error) => return Err(error),
        }
    }
    let decoded = decoded_batch(standing, batch, &law.cpu, work)?;
    let strata = strata(batch, family, &decoded)?;
    if law.exact_cuda_relations {
        work.host_relation_fallbacks = work
            .host_relation_fallbacks
            .checked_add(
                u64::try_from(strata.len())
                    .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
            )
            .ok_or(ObservationEcologyError::CarrierOverflow)?;
    }
    let maximum_first = relation
        .positive_maxima
        .iter()
        .filter_map(|difference| difference.0.first())
        .max()
        .cloned();
    let first_relation_coordinate = usize::try_from(family.relation_coordinates[0])
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    let mut candidate_relations = Vec::new();
    if let Some(maximum_first) = maximum_first {
        let stratum_members = strata.values().cloned().collect::<Vec<_>>();
        let results = execute_cpu_indexed(&law.cpu, &stratum_members, work, |_index, members| {
            let mut ordered = members.clone();
            ordered.sort_by(|left, right| {
                decoded[left][first_relation_coordinate]
                    .cmp(&decoded[right][first_relation_coordinate])
                    .then_with(|| left.cmp(right))
            });
            let mut local_relations = Vec::new();
            let mut inspected = 0_u64;
            for left_index in 0..ordered.len() {
                for right_index in (left_index + 1)..ordered.len() {
                    let left = ordered[left_index];
                    let right = ordered[right_index];
                    let first_difference = (&decoded[&right][first_relation_coordinate]
                        - &decoded[&left][first_relation_coordinate])
                        .abs();
                    if first_difference > maximum_first {
                        break;
                    }
                    inspected = inspected
                        .checked_add(1)
                        .ok_or(ObservationEcologyError::CarrierOverflow)?;
                    let difference = difference_at(
                        &decoded[&left],
                        &decoded[&right],
                        &family.relation_coordinates,
                    )?;
                    let state = relation.classify(&difference);
                    if relation.positive_contains(&difference) {
                        local_relations.push(PredictedReceiverRelation {
                            members: ordered_pair(left, right),
                            state,
                            difference,
                        });
                    }
                }
            }
            Ok(PredictionStratumResult {
                relations: local_relations,
                inspected,
            })
        })?;
        for mut result in results {
            work.inspected_relations = work
                .inspected_relations
                .checked_add(result.inspected)
                .ok_or(ObservationEcologyError::CarrierOverflow)?;
            candidate_relations.append(&mut result.relations);
        }
    }
    candidate_relations.sort_by_key(|relation| relation.members);
    let occurrence_ids = batch
        .occurrences
        .iter()
        .map(|occurrence| occurrence.id)
        .collect::<Vec<_>>();
    let forced_components = forced_components(&occurrence_ids, &candidate_relations)?;

    work.received_occurrences = u64::try_from(batch.occurrences.len())
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    work.decoded_coordinates = work
        .received_occurrences
        .checked_mul(
            u64::try_from(family.coordinates.len())
                .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
        )
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    work.retained_positive_generators = u64::try_from(relation.positive_maxima.len())
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    work.retained_negative_generators = u64::try_from(relation.negative_minima.len())
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    Ok(ReceiverRelationPrediction {
        schema: PREDICTION_SCHEMA.to_owned(),
        id: prediction,
        caused_by: event,
        family: batch.family,
        algorithm,
        chronology: batch.chronology,
        source: batch.source.clone(),
        aperture: batch.aperture.clone(),
        occurrences: occurrence_ids,
        candidate_relations,
        forced_components,
        relation_before: relation,
    })
}

#[cfg(target_os = "linux")]
#[allow(clippy::too_many_arguments)]
fn emit_packed_prediction(
    standing: &ObservationEcologyStanding,
    event: EventId,
    prediction: ReceiverPredictionId,
    algorithm: ReturnedAlgorithmId,
    batch: &ReceiverBatch,
    family: &ReceiverCoordinateFamily,
    relation: LearnedPartitionRelation,
    law: &ObservationEcologyLaw,
    work: &mut ObservationEcologyWork,
) -> Result<ReceiverRelationPrediction, ObservationEcologyError> {
    let packed = packed_strata(batch, standing, family, &relation)?;
    let mut candidate_relations = Vec::new();
    for chunk in packed.chunks(cpu_worker_limit(&law.cpu)) {
        let traversals = execute_cpu_indexed(&law.cpu, chunk, work, |_index, stratum| {
            let dimension = usize::try_from(stratum.front.dimension)
                .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
            let maximum_first = stratum
                .front
                .positive_maxima
                .chunks_exact(dimension)
                .map(|maximum| maximum[0])
                .max();
            let mut order = (0..stratum.members.len()).collect::<Vec<_>>();
            order.sort_by(|left, right| {
                stratum.points[*left * dimension]
                    .cmp(&stratum.points[*right * dimension])
                    .then_with(|| stratum.members[*left].cmp(&stratum.members[*right]))
            });
            let order = order
                .into_iter()
                .map(|point| {
                    u32::try_from(point).map_err(|_| ObservationEcologyError::CarrierOverflow)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let mut windows = Vec::new();
            let mut pair_count = 0_u64;
            if let Some(maximum_first) = maximum_first {
                let mut right_end = 1_usize;
                for left_order in 0..order.len() {
                    right_end = right_end.max(left_order + 1);
                    let left = usize::try_from(order[left_order])
                        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
                    while right_end < order.len() {
                        let right = usize::try_from(order[right_end])
                            .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
                        if stratum.points[left * dimension]
                            .abs_diff(stratum.points[right * dimension])
                            > maximum_first
                        {
                            break;
                        }
                        right_end += 1;
                    }
                    let right_count = right_end - (left_order + 1);
                    if right_count != 0 {
                        windows.push(PackedRelationWindow {
                            prefix: pair_count,
                            left: order[left_order],
                            right_start: u32::try_from(left_order + 1)
                                .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
                            right_count: u32::try_from(right_count)
                                .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
                        });
                        pair_count = pair_count
                            .checked_add(
                                u64::try_from(right_count)
                                    .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
                            )
                            .ok_or(ObservationEcologyError::CarrierOverflow)?;
                    }
                }
            }
            Ok(PackedPredictionTraversal {
                order,
                windows,
                pair_count,
            })
        })?;
        for (stratum, traversal) in chunk.iter().zip(traversals) {
            if traversal.pair_count != 0 {
                let point_count = u32::try_from(stratum.members.len())
                    .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
                let mode = cuda_relation_mode(batch.family, algorithm, stratum);
                let (card_relations, receipt, mode_use) = law.with_cuda_runtime(|runtime| {
                    runtime.classify_positive_windows(
                        mode,
                        &stratum.points,
                        point_count,
                        &traversal.order,
                        &traversal.windows,
                        traversal.pair_count,
                        || packed_host_window_relations(stratum, &traversal),
                    )
                })?;
                accumulate_cuda_receipt(work, &receipt)?;
                accumulate_cuda_mode_use(work, mode_use)?;
                for relation in card_relations.relations {
                    let left = usize::try_from(relation.pair.left)
                        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
                    let right = usize::try_from(relation.pair.right)
                        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
                    candidate_relations.push(PredictedReceiverRelation {
                        members: ordered_pair(stratum.members[left], stratum.members[right]),
                        difference: packed_difference(stratum, left, right)?,
                        state: state_from_wire(relation.state)?,
                    });
                }
            }
            work.inspected_relations = work
                .inspected_relations
                .checked_add(traversal.pair_count)
                .ok_or(ObservationEcologyError::CarrierOverflow)?;
        }
    }
    candidate_relations.sort_by_key(|relation| relation.members);
    let occurrence_ids = batch
        .occurrences
        .iter()
        .map(|occurrence| occurrence.id)
        .collect::<Vec<_>>();
    let forced_components = forced_components(&occurrence_ids, &candidate_relations)?;
    work.received_occurrences = u64::try_from(batch.occurrences.len())
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    work.retained_positive_generators = u64::try_from(relation.positive_maxima.len())
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    work.retained_negative_generators = u64::try_from(relation.negative_minima.len())
        .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    Ok(ReceiverRelationPrediction {
        schema: PREDICTION_SCHEMA.to_owned(),
        id: prediction,
        caused_by: event,
        family: batch.family,
        algorithm,
        chronology: batch.chronology,
        source: batch.source.clone(),
        aperture: batch.aperture.clone(),
        occurrences: occurrence_ids,
        candidate_relations,
        forced_components,
        relation_before: relation,
    })
}

fn forced_components(
    occurrences: &[ReceiverTestimonyId],
    relations: &[PredictedReceiverRelation],
) -> Result<Vec<Vec<ReceiverTestimonyId>>, ObservationEcologyError> {
    let mut closure = EquivalenceClosure::new(occurrences.iter().copied())?;
    for relation in relations {
        if relation.state == ReceiverRelationState::ForcedTogether {
            closure.join(&relation.members[0], &relation.members[1])?;
        }
    }
    Ok(closure.classes())
}

fn batch_from_prediction(
    standing: &ObservationEcologyStanding,
    prediction: &ReceiverRelationPrediction,
) -> Result<ReceiverBatch, ObservationEcologyError> {
    Ok(ReceiverBatch {
        family: prediction.family,
        chronology: prediction.chronology,
        source: prediction.source.clone(),
        aperture: prediction.aperture.clone(),
        occurrences: prediction
            .occurrences
            .iter()
            .map(|id| {
                standing
                    .testimonies
                    .get(id)
                    .map(|body| body.occurrence.clone())
                    .ok_or(ObservationEcologyError::MissingTestimony(*id))
            })
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn grade_return(
    event: EventId,
    grade: ReceiverGradeId,
    prediction: &ReceiverRelationPrediction,
    batch: &ReceiverBatch,
    returned: &ReturnedReceiverPartition,
    standing: &ObservationEcologyStanding,
    law: &ObservationEcologyLaw,
    work: &mut ObservationEcologyWork,
) -> Result<ReceiverRelationGrade, ObservationEcologyError> {
    let family = standing.families.get(&batch.family).ok_or(
        ObservationEcologyError::MissingCoordinateFamily(batch.family),
    )?;
    let membership = exclusive_membership(returned)?;
    let mut counts = ReceiverRelationGradeCounts::default();
    let mut obstructions = BTreeSet::new();
    #[cfg(target_os = "linux")]
    let results = if law.exact_cuda_relations {
        match packed_strata(batch, standing, family, &prediction.relation_before) {
            Ok(packed) => {
                let mut complete = Vec::with_capacity(packed.len());
                for chunk in packed.chunks(cpu_worker_limit(&law.cpu)) {
                    let mut card_grades = Vec::with_capacity(chunk.len());
                    for stratum in chunk {
                        let point_count = u32::try_from(stratum.members.len())
                            .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
                        let packed_membership = stratum
                            .members
                            .iter()
                            .map(|member| {
                                membership
                                    .get(member)
                                    .map(|cell| cell.0)
                                    .ok_or(ObservationEcologyError::MalformedReturnedPartition)
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        let mode = cuda_relation_mode(batch.family, prediction.algorithm, stratum);
                        let (grade, receipt, mode_use) = law.with_cuda_runtime(|runtime| {
                            runtime.grade_sparse(
                                mode,
                                &stratum.points,
                                point_count,
                                &packed_membership,
                                || packed_host_sparse_grade(stratum, &membership),
                            )
                        })?;
                        accumulate_cuda_receipt(work, &receipt)?;
                        accumulate_cuda_mode_use(work, mode_use)?;
                        card_grades.push(grade);
                    }
                    let graded = execute_cpu_indexed(
                        &law.cpu,
                        &card_grades,
                        work,
                        |index, sparse_grade| grade_from_cuda_sparse(&chunk[index], sparse_grade),
                    )?;
                    complete.extend(graded);
                }
                complete
            }
            Err(ObservationEcologyError::CudaRelationChartNotPackable) => {
                let decoded = decoded_batch(standing, batch, &law.cpu, work)?;
                let strata = strata(batch, family, &decoded)?;
                work.host_relation_fallbacks = work
                    .host_relation_fallbacks
                    .checked_add(
                        u64::try_from(strata.len())
                            .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
                    )
                    .ok_or(ObservationEcologyError::CarrierOverflow)?;
                let stratum_members = strata.values().cloned().collect::<Vec<_>>();
                execute_cpu_indexed(&law.cpu, &stratum_members, work, |_index, members| {
                    grade_stratum(
                        members,
                        &membership,
                        &decoded,
                        &family.relation_coordinates,
                        &prediction.relation_before,
                    )
                })?
            }
            Err(error) => return Err(error),
        }
    } else {
        let decoded = decoded_batch(standing, batch, &law.cpu, work)?;
        let strata = strata(batch, family, &decoded)?;
        let stratum_members = strata.values().cloned().collect::<Vec<_>>();
        execute_cpu_indexed(&law.cpu, &stratum_members, work, |_index, members| {
            grade_stratum(
                members,
                &membership,
                &decoded,
                &family.relation_coordinates,
                &prediction.relation_before,
            )
        })?
    };
    #[cfg(not(target_os = "linux"))]
    let results = if law.exact_cuda_relations {
        return Err(ObservationEcologyError::CudaRelationExecutorUnavailable);
    } else {
        let decoded = decoded_batch(standing, batch, &law.cpu, work)?;
        let strata = strata(batch, family, &decoded)?;
        let stratum_members = strata.values().cloned().collect::<Vec<_>>();
        execute_cpu_indexed(&law.cpu, &stratum_members, work, |_index, members| {
            grade_stratum(
                members,
                &membership,
                &decoded,
                &family.relation_coordinates,
                &prediction.relation_before,
            )
        })?
    };
    for result in results {
        work.inspected_relations = work
            .inspected_relations
            .checked_add(result.inspected)
            .ok_or(ObservationEcologyError::CarrierOverflow)?;
        merge_grade_counts(&mut counts, &result.counts)?;
        obstructions.extend(result.obstructions);
    }
    work.obstruction_witnesses =
        u64::try_from(obstructions.len()).map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    let receiver_morphology = receiver_morphology_summary(prediction, returned)?;
    Ok(ReceiverRelationGrade {
        schema: GRADE_SCHEMA.to_owned(),
        id: grade,
        caused_by: event,
        prediction: prediction.id,
        returned: Arc::new(returned.clone()),
        counts,
        obstructions: obstructions.into_iter().collect(),
        receiver_morphology,
    })
}

struct GradeStratumResult {
    counts: ReceiverRelationGradeCounts,
    obstructions: BTreeSet<ReceiverRelationObstruction>,
    inspected: u64,
}

fn grade_stratum(
    members: &[ReceiverTestimonyId],
    membership: &BTreeMap<ReceiverTestimonyId, ReturnedCellId>,
    decoded: &BTreeMap<ReceiverTestimonyId, Vec<Rat>>,
    relation_coordinates: &[u32],
    relation: &LearnedPartitionRelation,
) -> Result<GradeStratumResult, ObservationEcologyError> {
    let total_pairs = choose_two(members.len())?;
    let mut counts = ReceiverRelationGradeCounts::default();
    let mut obstructions = BTreeSet::new();
    let mut inspected = 0_u64;
    for left_index in 0..members.len() {
        for right_index in (left_index + 1)..members.len() {
            let left = members[left_index];
            let right = members[right_index];
            inspected = inspected
                .checked_add(1)
                .ok_or(ObservationEcologyError::CarrierOverflow)?;
            let difference =
                difference_at(&decoded[&left], &decoded[&right], relation_coordinates)?;
            let state = relation.classify(&difference);
            let returned_together = membership[&left] == membership[&right];
            if let Some(kind) = account_grade_state(&mut counts, state, returned_together)? {
                obstructions.insert(ReceiverRelationObstruction {
                    kind,
                    members: ordered_pair(left, right),
                    difference,
                });
            }
        }
    }
    if total_pairs
        != choose_two(
            members
                .iter()
                .filter(|member| membership.contains_key(member))
                .count(),
        )?
    {
        return Err(ObservationEcologyError::MalformedReturnedPartition);
    }
    Ok(GradeStratumResult {
        counts,
        obstructions,
        inspected,
    })
}

#[cfg(target_os = "linux")]
fn packed_host_window_relations(
    packed: &PackedObservationStratum,
    traversal: &PackedPredictionTraversal,
) -> Result<CudaSparseRelations, ObservationEcologyError> {
    let mut relations = Vec::new();
    let mut inspected = 0_u64;
    for window in &traversal.windows {
        for offset in 0..window.right_count {
            let left = usize::try_from(window.left)
                .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
            let right_order = window
                .right_start
                .checked_add(offset)
                .ok_or(ObservationEcologyError::CarrierOverflow)?;
            let right = usize::try_from(
                *traversal
                    .order
                    .get(
                        usize::try_from(right_order)
                            .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
                    )
                    .ok_or(ObservationEcologyError::CarrierOverflow)?,
            )
            .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
            let pair = if left < right {
                PackedRelationPair {
                    left: u32::try_from(left)
                        .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
                    right: u32::try_from(right)
                        .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
                }
            } else {
                PackedRelationPair {
                    left: u32::try_from(right)
                        .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
                    right: u32::try_from(left)
                        .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
                }
            };
            let state = packed_relation_state(&packed.points, left, right, &packed.front)?;
            if state == 0 || state == 3 {
                relations.push(CudaClassifiedRelation { pair, state });
            }
            inspected = inspected
                .checked_add(1)
                .ok_or(ObservationEcologyError::CarrierOverflow)?;
        }
    }
    if inspected != traversal.pair_count {
        return Err(ObservationEcologyError::CarrierOverflow);
    }
    relations.sort();
    Ok(CudaSparseRelations { relations })
}

#[cfg(target_os = "linux")]
fn packed_host_sparse_grade(
    packed: &PackedObservationStratum,
    membership: &BTreeMap<ReceiverTestimonyId, ReturnedCellId>,
) -> Result<CudaSparseGrade, ObservationEcologyError> {
    let pair_count = choose_two(packed.members.len())?;
    let mut counts = ReceiverRelationGradeCounts::default();
    let mut obstructions = Vec::new();
    for left_index in 0..packed.members.len() {
        for right_index in (left_index + 1)..packed.members.len() {
            let left = packed.members[left_index];
            let right = packed.members[right_index];
            let state = state_from_wire(packed_relation_state(
                &packed.points,
                left_index,
                right_index,
                &packed.front,
            )?)?;
            let returned_together = membership[&left] == membership[&right];
            if let Some(kind) = account_grade_state(&mut counts, state, returned_together)? {
                obstructions.push(CudaRelationObstruction {
                    pair: PackedRelationPair {
                        left: u32::try_from(left_index)
                            .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
                        right: u32::try_from(right_index)
                            .map_err(|_| ObservationEcologyError::CarrierOverflow)?,
                    },
                    kind: obstruction_kind_to_wire(kind),
                });
            }
        }
    }
    if counts
        .returned_together_pairs
        .checked_add(counts.returned_apart_pairs)
        .ok_or(ObservationEcologyError::CarrierOverflow)?
        != pair_count
    {
        return Err(ObservationEcologyError::CarrierOverflow);
    }
    obstructions.sort();
    Ok(CudaSparseGrade {
        counts: grade_counts_to_wire(&counts),
        obstructions,
    })
}

#[cfg(target_os = "linux")]
fn grade_from_cuda_sparse(
    packed: &PackedObservationStratum,
    sparse: &CudaSparseGrade,
) -> Result<GradeStratumResult, ObservationEcologyError> {
    let pair_count = choose_two(packed.members.len())?;
    let counts = grade_counts_from_wire(sparse.counts);
    if counts
        .returned_together_pairs
        .checked_add(counts.returned_apart_pairs)
        .ok_or(ObservationEcologyError::CarrierOverflow)?
        != pair_count
    {
        return Err(ObservationEcologyError::CudaRelationParity);
    }
    let expected_obstructions = counts
        .returned_together_forced_apart
        .checked_add(counts.returned_together_open)
        .and_then(|value| value.checked_add(counts.returned_apart_forced_together))
        .and_then(|value| value.checked_add(counts.conflicted_pairs))
        .ok_or(ObservationEcologyError::CarrierOverflow)?;
    if expected_obstructions
        != u64::try_from(sparse.obstructions.len())
            .map_err(|_| ObservationEcologyError::CarrierOverflow)?
    {
        return Err(ObservationEcologyError::CudaRelationParity);
    }
    let mut obstructions = BTreeSet::new();
    for obstruction in &sparse.obstructions {
        let left = usize::try_from(obstruction.pair.left)
            .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
        let right = usize::try_from(obstruction.pair.right)
            .map_err(|_| ObservationEcologyError::CarrierOverflow)?;
        if left >= right || right >= packed.members.len() {
            return Err(ObservationEcologyError::CudaRelationParity);
        }
        if !obstructions.insert(ReceiverRelationObstruction {
            kind: obstruction_kind_from_wire(obstruction.kind)?,
            members: ordered_pair(packed.members[left], packed.members[right]),
            difference: packed_difference(packed, left, right)?,
        }) {
            return Err(ObservationEcologyError::CudaRelationParity);
        }
    }
    Ok(GradeStratumResult {
        counts,
        obstructions,
        inspected: pair_count,
    })
}

#[cfg(target_os = "linux")]
fn grade_counts_to_wire(counts: &ReceiverRelationGradeCounts) -> [u64; 8] {
    [
        counts.returned_together_pairs,
        counts.returned_apart_pairs,
        counts.forced_together_correct,
        counts.forced_apart_correct,
        counts.returned_together_open,
        counts.returned_together_forced_apart,
        counts.returned_apart_forced_together,
        counts.conflicted_pairs,
    ]
}

#[cfg(target_os = "linux")]
fn grade_counts_from_wire(counts: [u64; 8]) -> ReceiverRelationGradeCounts {
    ReceiverRelationGradeCounts {
        returned_together_pairs: counts[0],
        returned_apart_pairs: counts[1],
        forced_together_correct: counts[2],
        forced_apart_correct: counts[3],
        returned_together_open: counts[4],
        returned_together_forced_apart: counts[5],
        returned_apart_forced_together: counts[6],
        conflicted_pairs: counts[7],
    }
}

#[cfg(target_os = "linux")]
fn obstruction_kind_to_wire(kind: ReceiverRelationObstructionKind) -> u8 {
    match kind {
        ReceiverRelationObstructionKind::ReturnedTogetherButForcedApart => 0,
        ReceiverRelationObstructionKind::ReturnedTogetherButOpen => 1,
        ReceiverRelationObstructionKind::ReturnedApartButForcedTogether => 2,
        ReceiverRelationObstructionKind::ConflictedLineage => 3,
    }
}

#[cfg(target_os = "linux")]
fn obstruction_kind_from_wire(
    kind: u8,
) -> Result<ReceiverRelationObstructionKind, ObservationEcologyError> {
    match kind {
        0 => Ok(ReceiverRelationObstructionKind::ReturnedTogetherButForcedApart),
        1 => Ok(ReceiverRelationObstructionKind::ReturnedTogetherButOpen),
        2 => Ok(ReceiverRelationObstructionKind::ReturnedApartButForcedTogether),
        3 => Ok(ReceiverRelationObstructionKind::ConflictedLineage),
        _ => Err(ObservationEcologyError::MalformedCudaRelationObstruction(
            kind,
        )),
    }
}

fn account_grade_state(
    counts: &mut ReceiverRelationGradeCounts,
    state: ReceiverRelationState,
    returned_together: bool,
) -> Result<Option<ReceiverRelationObstructionKind>, ObservationEcologyError> {
    if returned_together {
        counts.returned_together_pairs = counts
            .returned_together_pairs
            .checked_add(1)
            .ok_or(ObservationEcologyError::CarrierOverflow)?;
        match state {
            ReceiverRelationState::ForcedTogether => {
                counts.forced_together_correct = counts
                    .forced_together_correct
                    .checked_add(1)
                    .ok_or(ObservationEcologyError::CarrierOverflow)?;
                Ok(None)
            }
            ReceiverRelationState::ForcedApart => {
                counts.returned_together_forced_apart = counts
                    .returned_together_forced_apart
                    .checked_add(1)
                    .ok_or(ObservationEcologyError::CarrierOverflow)?;
                Ok(Some(
                    ReceiverRelationObstructionKind::ReturnedTogetherButForcedApart,
                ))
            }
            ReceiverRelationState::Open => {
                counts.returned_together_open = counts
                    .returned_together_open
                    .checked_add(1)
                    .ok_or(ObservationEcologyError::CarrierOverflow)?;
                Ok(Some(
                    ReceiverRelationObstructionKind::ReturnedTogetherButOpen,
                ))
            }
            ReceiverRelationState::Conflicted => {
                counts.conflicted_pairs = counts
                    .conflicted_pairs
                    .checked_add(1)
                    .ok_or(ObservationEcologyError::CarrierOverflow)?;
                Ok(Some(ReceiverRelationObstructionKind::ConflictedLineage))
            }
        }
    } else {
        counts.returned_apart_pairs = counts
            .returned_apart_pairs
            .checked_add(1)
            .ok_or(ObservationEcologyError::CarrierOverflow)?;
        match state {
            ReceiverRelationState::ForcedTogether => {
                counts.returned_apart_forced_together = counts
                    .returned_apart_forced_together
                    .checked_add(1)
                    .ok_or(ObservationEcologyError::CarrierOverflow)?;
                Ok(Some(
                    ReceiverRelationObstructionKind::ReturnedApartButForcedTogether,
                ))
            }
            ReceiverRelationState::ForcedApart => {
                counts.forced_apart_correct = counts
                    .forced_apart_correct
                    .checked_add(1)
                    .ok_or(ObservationEcologyError::CarrierOverflow)?;
                Ok(None)
            }
            ReceiverRelationState::Open => Ok(None),
            ReceiverRelationState::Conflicted => {
                counts.conflicted_pairs = counts
                    .conflicted_pairs
                    .checked_add(1)
                    .ok_or(ObservationEcologyError::CarrierOverflow)?;
                Ok(Some(ReceiverRelationObstructionKind::ConflictedLineage))
            }
        }
    }
}

fn merge_grade_counts(
    total: &mut ReceiverRelationGradeCounts,
    part: &ReceiverRelationGradeCounts,
) -> Result<(), ObservationEcologyError> {
    macro_rules! add {
        ($field:ident) => {
            total.$field = total
                .$field
                .checked_add(part.$field)
                .ok_or(ObservationEcologyError::CarrierOverflow)?;
        };
    }
    add!(returned_together_pairs);
    add!(returned_apart_pairs);
    add!(forced_together_correct);
    add!(forced_apart_correct);
    add!(returned_together_open);
    add!(returned_together_forced_apart);
    add!(returned_apart_forced_together);
    add!(conflicted_pairs);
    Ok(())
}

fn choose_two(extent: usize) -> Result<u64, ObservationEcologyError> {
    if extent < 2 {
        return Ok(0);
    }
    let extent = u64::try_from(extent).map_err(|_| ObservationEcologyError::CarrierOverflow)?;
    extent
        .checked_mul(extent - 1)
        .and_then(|value| value.checked_div(2))
        .ok_or(ObservationEcologyError::CarrierOverflow)
}

fn ordered_pair(left: ReceiverTestimonyId, right: ReceiverTestimonyId) -> [ReceiverTestimonyId; 2] {
    if left <= right {
        [left, right]
    } else {
        [right, left]
    }
}

fn validate_standing_with_executor(
    standing: &ObservationEcologyStanding,
    executor: &CpuExecutor,
    work: &mut ObservationEcologyWork,
) -> Result<(), ObservationEcologyError> {
    if standing.schema != STANDING_SCHEMA {
        return Err(ObservationEcologyError::MalformedStanding);
    }
    for (id, family) in &standing.families {
        if id != &family.id {
            return Err(ObservationEcologyError::MalformedStanding);
        }
        family.validate()?;
    }
    for (id, chart) in &standing.charts {
        if id != &chart.id {
            return Err(ObservationEcologyError::MalformedStanding);
        }
        validate_chart(standing, chart)?;
    }
    let testimonies = standing.testimonies.iter().collect::<Vec<_>>();
    execute_cpu_indexed(executor, &testimonies, work, |_index, (id, testimony)| {
        if *id != &testimony.occurrence.id {
            return Err(ObservationEcologyError::MalformedStanding);
        }
        let chart = standing
            .charts
            .get(&testimony.occurrence.chart)
            .ok_or(ObservationEcologyError::MalformedStanding)?;
        if chart.receiver != testimony.occurrence.receiver {
            return Err(ObservationEcologyError::MalformedStanding);
        }
        if testimony.occurrence.raw.len() != chart.raw_coordinates.len() {
            return Err(ObservationEcologyError::MalformedStanding);
        }
        match &testimony.disposition {
            TestimonyDisposition::Admitted { event } => {
                if !standing.used_events.contains(event) {
                    return Err(ObservationEcologyError::MalformedStanding);
                }
            }
            TestimonyDisposition::PendingPrediction { prediction } => {
                if !standing.predictions.contains_key(prediction) {
                    return Err(ObservationEcologyError::MalformedStanding);
                }
            }
            TestimonyDisposition::Graded { grade } => {
                if !standing.grades.contains_key(grade) {
                    return Err(ObservationEcologyError::MalformedStanding);
                }
            }
        }
        Ok(())
    })?;
    for ((family_id, algorithm), relation) in &standing.relations {
        let family = standing
            .families
            .get(family_id)
            .ok_or(ObservationEcologyError::MalformedStanding)?;
        if family_id != &relation.family || algorithm != &relation.algorithm {
            return Err(ObservationEcologyError::MalformedStanding);
        }
        relation.validate(family.relation_coordinates.len())?;
    }
    for (id, prediction) in standing.predictions.iter() {
        if id != &prediction.id
            || prediction.schema != PREDICTION_SCHEMA
            || !standing.families.contains_key(&prediction.family)
        {
            return Err(ObservationEcologyError::MalformedStanding);
        }
        execute_cpu_indexed(
            executor,
            &prediction.occurrences,
            work,
            |_index, occurrence| {
                if standing.testimonies.contains_key(occurrence) {
                    Ok(())
                } else {
                    Err(ObservationEcologyError::MalformedStanding)
                }
            },
        )?;
        let family = &standing.families[&prediction.family];
        prediction
            .relation_before
            .validate(family.relation_coordinates.len())?;
    }
    for (id, grade) in standing.grades.iter() {
        if id != &grade.id
            || grade.schema != GRADE_SCHEMA
            || !standing.predictions.contains_key(&grade.prediction)
            || grade.receiver_morphology.schema != "holonic-engine.receiver-morphology-summary.v1"
        {
            return Err(ObservationEcologyError::MalformedStanding);
        }
    }
    if standing.receiver_quotients.len() != standing.receiver_quotient_by_target.len() {
        return Err(ObservationEcologyError::MalformedStanding);
    }
    for (id, quotient) in &standing.receiver_quotients {
        let partition = standing
            .admitted_partitions
            .iter()
            .find(|partition| partition.event == quotient.source.partition_event)
            .ok_or(ObservationEcologyError::MalformedStanding)?;
        let source_cell = partition
            .partition
            .cells
            .iter()
            .find(|cell| cell.id == quotient.source.cell)
            .ok_or(ObservationEcologyError::MalformedStanding)?;
        let target = standing
            .testimonies
            .get(&quotient.target)
            .ok_or(ObservationEcologyError::MalformedStanding)?;
        if id != &quotient.id
            || quotient.source_family != partition.family
            || quotient.target_chronology < partition.chronology
            || quotient.target_family
                != standing
                    .charts
                    .get(&target.occurrence.chart)
                    .ok_or(ObservationEcologyError::MalformedStanding)?
                    .family
            || source_cell.id.0 != target.occurrence.source_identity
            || standing.receiver_quotient_by_target.get(&quotient.target) != Some(id)
            || !testimony_is_admitted(standing, &target.disposition)
        {
            return Err(ObservationEcologyError::MalformedStanding);
        }
    }
    if standing.next_prediction
        <= standing
            .predictions
            .keys()
            .map(|id| id.0)
            .max()
            .unwrap_or(0)
        || standing.next_grade <= standing.grades.keys().map(|id| id.0).max().unwrap_or(0)
        || standing.next_receiver_quotient
            <= standing
                .receiver_quotients
                .keys()
                .map(|id| id.0)
                .max()
                .unwrap_or(0)
    {
        return Err(ObservationEcologyError::MalformedStanding);
    }
    Ok(())
}

fn logical_resources(
    kind: ObservationEcologyRadiationKind,
    work: &ObservationEcologyWork,
) -> LogicalResourceReceipt {
    let mut events_by_law = BTreeMap::new();
    let (name, span) = match kind {
        ObservationEcologyRadiationKind::FamilyDeclared => ("declare coordinate family", 1_u8),
        ObservationEcologyRadiationKind::ChartDeclared => ("declare receiver chart", 1),
        ObservationEcologyRadiationKind::ReturnedBatchConditioned => {
            ("condition returned relation", 3)
        }
        ObservationEcologyRadiationKind::PartitionReturnedAsReceivers => {
            ("return closed cells as receiver population", 2)
        }
        ObservationEcologyRadiationKind::ExistingReceiverBatchConditioned => {
            ("condition returned receiver relation", 3)
        }
        ObservationEcologyRadiationKind::PredictionEmitted => ("emit relation fiber", 3),
        ObservationEcologyRadiationKind::ExistingReceiverPredictionEmitted => {
            ("emit receiver-population relation fiber", 3)
        }
        ObservationEcologyRadiationKind::ReturnGraded => ("grade returned relation", 2),
        ObservationEcologyRadiationKind::GradedReturnAdmitted => {
            ("admit graded returned relation", 2)
        }
    };
    events_by_law.insert(name.to_owned(), BigUint::from(1_u8));
    let values = [
        work.received_occurrences,
        work.decoded_coordinates,
        work.inspected_relations,
        work.retained_positive_generators,
        work.retained_negative_generators,
        work.obstruction_witnesses,
    ];
    LogicalResourceReceipt {
        schema: "holonic-engine.logical-resource-receipt.v1".to_owned(),
        work: values
            .iter()
            .fold(BigUint::zero(), |sum, value| sum + BigUint::from(*value)),
        causal_span: BigUint::from(span),
        exposed_parallel_width: BigUint::from(
            work.received_occurrences.max(work.inspected_relations),
        ),
        events_by_law,
    }
}

fn physical_resources(
    work: &ObservationEcologyWork,
) -> Result<PhysicalResourceReceipt, ObservationEcologyError> {
    let executor = match &work.cuda_device {
        Some(device) => format!(
            "deterministic CPU antichains ({} workers observed) + mode-admitted exact CUDA relation realization on {device}",
            work.cpu_workers_used
        ),
        None => format!(
            "deterministic CPU antichains ({} workers observed)",
            work.cpu_workers_used
        ),
    };
    let mut receipt = PhysicalResourceReceipt::new(executor);
    if work.cuda_host_to_device_octets != 0
        || work.cuda_device_to_host_octets != 0
        || work.cuda_launches != 0
    {
        receipt.traffic.insert(
            MemoryTier::HostDeviceLink,
            Traffic {
                read_octets: BigUint::from(work.cuda_device_to_host_octets),
                written_octets: BigUint::from(work.cuda_host_to_device_octets),
                messages: BigUint::from(work.cuda_launches),
            },
        );
    }
    receipt.synchronization_events =
        BigUint::from(work.cpu_joins) + BigUint::from(work.cuda_launches);
    Ok(receipt)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ObservationEcologyError {
    #[error("receiver coordinate family {0:?} is absent")]
    MissingCoordinateFamily(ReceiverCoordinateFamilyId),
    #[error("receiver coordinate family {0:?} is malformed")]
    MalformedCoordinateFamily(ReceiverCoordinateFamilyId),
    #[error("receiver coordinate family {0:?} was declared twice")]
    RepeatedCoordinateFamily(ReceiverCoordinateFamilyId),
    #[error("receiver chart {0:?} is absent")]
    MissingChart(ReceiverChartId),
    #[error("receiver chart {0:?} is malformed")]
    MalformedChart(ReceiverChartId),
    #[error("receiver chart {0:?} was declared twice")]
    RepeatedChart(ReceiverChartId),
    #[error(
        "chart {chart:?} has comparison dimension {chart_dimension}, but its family has {family_dimension}"
    )]
    ChartFamilyDimension {
        chart: ReceiverChartId,
        chart_dimension: usize,
        family_dimension: usize,
    },
    #[error("chart {chart:?} expected {expected} raw coordinates but received {received}")]
    RawCoordinateDimension {
        chart: ReceiverChartId,
        expected: usize,
        received: usize,
    },
    #[error("reported IEEE testimony is non-finite")]
    NonfiniteReportedValue,
    #[error("a receiver batch has no source identity")]
    EmptyBatchSource,
    #[error("a receiver aperture is malformed")]
    MalformedReceiverAperture,
    #[error("receiver testimony {0:?} lies outside its declared aperture")]
    TestimonyOutsideAperture(ReceiverTestimonyId),
    #[error("receiver testimony {0:?} was repeated")]
    RepeatedTestimony(ReceiverTestimonyId),
    #[error("receiver testimony {0:?} is absent")]
    MissingTestimony(ReceiverTestimonyId),
    #[error("receiver testimony {0:?} does not inhabit its declared chart")]
    OccurrenceChartMismatch(ReceiverTestimonyId),
    #[error("the returned receiver partition is malformed")]
    MalformedReturnedPartition,
    #[error("returned partition contains foreign testimony {0:?}")]
    PartitionForeignTestimony(ReceiverTestimonyId),
    #[error("a complete exclusive returned partition is not an exact cover")]
    IncompleteExclusivePartition,
    #[error("admitted receiver partition event {0:?} is absent")]
    MissingAdmittedPartition(EventId),
    #[error("only a complete exclusive partition can return as a receiver population")]
    NonexclusiveReceiverReturn,
    #[error("a lower partition and its outer receiver faces do not form a complete bijection")]
    IncompleteReceiverReturn,
    #[error(
        "returned cell {cell:?} and outer receiver testimony {testimony:?} have different source identities"
    )]
    ReceiverReturnIdentityMismatch {
        cell: ReturnedCellId,
        testimony: ReceiverTestimonyId,
    },
    #[error("one returned receiver cell or outer face was already quotiented")]
    RepeatedReceiverReturn,
    #[error(
        "a returned receiver chronology regressed from lower chronology {lower} to upper chronology {upper}"
    )]
    ReceiverReturnChronologyRegression { lower: u64, upper: u64 },
    #[error(
        "receiver-return testimony {testimony:?} belongs to chronology {expected}, not requested chronology {received}"
    )]
    ReceiverReturnChronologyMismatch {
        testimony: ReceiverTestimonyId,
        expected: u64,
        received: u64,
    },
    #[error("testimony {0:?} did not enter as the return of a lower receiver cell")]
    TestimonyIsNotReceiverReturn(ReceiverTestimonyId),
    #[error("receiver-return testimony {0:?} is not yet admitted")]
    TestimonyIsNotAdmitted(ReceiverTestimonyId),
    #[error("returned cell {0:?} crosses declared co-present strata")]
    ReturnedCellCrossesStrata(ReturnedCellId),
    #[error("overlapping or partial returned cells cannot train the exclusive relation fiber")]
    NonexclusiveRelationTraining,
    #[error("no relation was learned for coordinate family {family:?} and algorithm {algorithm:?}")]
    MissingLearnedRelation {
        family: ReceiverCoordinateFamilyId,
        algorithm: ReturnedAlgorithmId,
    },
    #[error("learned relation for {family:?}/{algorithm:?} is malformed")]
    MalformedLearnedRelation {
        family: ReceiverCoordinateFamilyId,
        algorithm: ReturnedAlgorithmId,
    },
    #[error("receiver relation prediction {0:?} is absent")]
    MissingPrediction(ReceiverPredictionId),
    #[error("receiver relation prediction {0:?} has already been graded")]
    PredictionAlreadyGraded(ReceiverPredictionId),
    #[error("returned algorithm {received:?} does not grade predicted algorithm {expected:?}")]
    ReturnedAlgorithmMismatch {
        expected: ReturnedAlgorithmId,
        received: ReturnedAlgorithmId,
    },
    #[error("receiver relation grade {0:?} is absent")]
    MissingGrade(ReceiverGradeId),
    #[error("receiver relation grade {0:?} has already entered training standing")]
    GradeAlreadyAdmitted(ReceiverGradeId),
    #[error("event {0:?} was repeated")]
    RepeatedEvent(EventId),
    #[error("one physical CPU worker failed before returning its exact local section")]
    PhysicalWorkerPanicked,
    #[error("the explicitly requested exact CUDA relation executor is not yet admissible")]
    CudaRelationExecutorUnavailable,
    #[cfg(target_os = "linux")]
    #[error(transparent)]
    CudaRelation(#[from] crate::CudaRelationError),
    #[error(
        "one receiver stratum cannot be carried by the declared exact packed CUDA relation law"
    )]
    CudaRelationChartNotPackable,
    #[error("the CUDA device identity changed inside one exact observation transition")]
    CudaDeviceChanged,
    #[error("the compiled CUDA relation artifact changed inside one exact observation transition")]
    CudaKernelChanged,
    #[error("the persistent CUDA relation runtime lock was poisoned")]
    CudaRelationRuntimePoisoned,
    #[error("the exact CUDA mode-admission ledger violated its append-only invariant")]
    CudaModeRegistryInvariant,
    #[error("the exact CUDA relation state differs from the host state at the same pair address")]
    CudaRelationParity,
    #[error("an exact relation could not be represented by the admitted packed comparison carrier")]
    MalformedPackedRelation,
    #[error("CUDA returned unknown relation-state code {0}")]
    MalformedCudaRelationState(u8),
    #[error("CUDA returned unknown relation-obstruction code {0}")]
    MalformedCudaRelationObstruction(u8),
    #[error("observation ecology standing is malformed")]
    MalformedStanding,
    #[error(transparent)]
    Mode(#[from] crate::ModeError),
    #[error(transparent)]
    ReceiverEcology(#[from] ReceiverEcologyError),
    #[error("an observation ecology carrier overflowed")]
    CarrierOverflow,
}

#[cfg(test)]
mod tests {
    use num_traits::One;

    use super::*;
    use crate::CausalWorld;

    const FAMILY: ReceiverCoordinateFamilyId = ReceiverCoordinateFamilyId(1);
    const CHART: ReceiverChartId = ReceiverChartId(1);
    const ALGORITHM: ReturnedAlgorithmId = ReturnedAlgorithmId(7);

    fn family() -> ReceiverCoordinateFamily {
        ReceiverCoordinateFamily::new(
            FAMILY,
            vec!["local-x".into(), "local-y".into(), "clock".into()],
            vec![0, 1],
            vec![2],
        )
        .unwrap()
    }

    fn chart() -> ReceiverAffineChart {
        ReceiverAffineChart::new(
            CHART,
            ReceiverId(11),
            FAMILY,
            "test identity chart",
            vec!["x-carrier".into(), "y-carrier".into(), "t-carrier".into()],
            vec![Rat::zero(), Rat::zero(), Rat::zero()],
            vec![
                vec![Rat::one(), Rat::zero(), Rat::zero()],
                vec![Rat::zero(), Rat::one(), Rat::zero()],
                vec![Rat::zero(), Rat::zero(), Rat::one()],
            ],
        )
        .unwrap()
    }

    fn occurrence(id: u64, x: i64, y: i64, time: i64) -> ReceiverTestimony {
        ReceiverTestimony {
            id: ReceiverTestimonyId(id),
            receiver: ReceiverId(11),
            lineage: ReceiverLineageId(1),
            chart: CHART,
            source_identity: id,
            raw: vec![x, y, time],
        }
    }

    fn batch(chronology: u64, source: &str, occurrences: Vec<ReceiverTestimony>) -> ReceiverBatch {
        ReceiverBatch {
            family: FAMILY,
            chronology,
            source: source.to_owned(),
            aperture: Vec::new(),
            occurrences,
        }
    }

    fn partition(cells: &[(u64, &[u64])]) -> ReturnedReceiverPartition {
        ReturnedReceiverPartition {
            algorithm: ALGORITHM,
            coverage: ReturnedCellCoverage::CompleteExclusive,
            cells: cells
                .iter()
                .map(|(cell, members)| ReturnedReceiverCell {
                    id: ReturnedCellId(*cell),
                    members: members
                        .iter()
                        .map(|member| ReceiverTestimonyId(*member))
                        .collect(),
                })
                .collect(),
        }
    }

    fn declared_world() -> CausalWorld<ObservationEcologyLaw> {
        let mut world = CausalWorld::new(
            ObservationEcologyLaw::serial(),
            ObservationEcologyStanding::default(),
        );
        world
            .receive(&ObservationEcologyEvent::DeclareFamily {
                event: EventId(1),
                family: family(),
            })
            .unwrap();
        world
            .receive(&ObservationEcologyEvent::DeclareChart {
                event: EventId(2),
                chart: chart(),
            })
            .unwrap();
        world
    }

    #[test]
    fn ieee_carriers_enter_as_exact_binary_rationals() {
        assert_eq!(
            exact_rational_from_f32_bits(0x3f00_0000).unwrap(),
            Rat::new(BigInt::from(1), BigInt::from(2))
        );
        assert_eq!(
            exact_rational_from_f32_bits(0xbf00_0000).unwrap(),
            Rat::new(BigInt::from(-1), BigInt::from(2))
        );
        assert_eq!(
            exact_rational_from_f64_bits(0x3ff0_0000_0000_0000).unwrap(),
            Rat::one()
        );
        assert_eq!(
            exact_rational_from_f64_bits(0x7ff0_0000_0000_0000),
            Err(ObservationEcologyError::NonfiniteReportedValue)
        );
    }

    #[test]
    fn affine_reencoding_preserves_received_coordinates() {
        let first = chart();
        let second = ReceiverAffineChart::new(
            ReceiverChartId(2),
            ReceiverId(11),
            FAMILY,
            "test affine reencoding",
            vec!["u".into(), "v".into(), "clock".into()],
            vec![
                Rat::from_integer(BigInt::from(10)),
                Rat::from_integer(BigInt::from(-5)),
                Rat::zero(),
            ],
            vec![
                vec![Rat::from_integer(BigInt::from(2)), Rat::zero(), Rat::zero()],
                vec![Rat::zero(), Rat::from_integer(BigInt::from(3)), Rat::zero()],
                vec![Rat::zero(), Rat::zero(), Rat::one()],
            ],
        )
        .unwrap();
        assert_eq!(
            first.receive(&[14, 7, 9]).unwrap(),
            second.receive(&[2, 4, 9]).unwrap()
        );
    }

    #[test]
    fn pareto_union_is_canonical_and_order_independent() {
        let vector = |values: [i64; 3]| {
            ExactDifferenceVector(
                values
                    .into_iter()
                    .map(|value| Rat::from_integer(BigInt::from(value)))
                    .collect(),
            )
        };
        let candidates = vec![
            vector([1, 1, 1]),
            vector([2, 2, 2]),
            vector([3, 1, 2]),
            vector([1, 3, 2]),
            vector([2, 2, 2]),
        ];
        let mut reversed = candidates.clone();
        reversed.reverse();
        assert_eq!(
            canonical_maximal_front(candidates.clone()),
            canonical_maximal_front(reversed.clone())
        );
        assert_eq!(
            canonical_maximal_front(candidates),
            vec![vector([1, 3, 2]), vector([2, 2, 2]), vector([3, 1, 2])]
        );
        assert_eq!(canonical_minimal_front(reversed), vec![vector([1, 1, 1])]);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn packed_floor_and_ceiling_are_equivalent_to_the_rational_relation() {
        let scales = [
            Rat::new(BigInt::from(3), BigInt::from(2)),
            Rat::new(BigInt::from(2), BigInt::from(3)),
        ];
        let positive = [
            Rat::new(BigInt::from(7), BigInt::from(3)),
            Rat::new(BigInt::from(5), BigInt::from(2)),
        ];
        let negative = [Rat::new(BigInt::from(8), BigInt::from(3)), Rat::one()];
        let front = PackedRelationFront {
            dimension: 2,
            positive_maxima: positive
                .iter()
                .zip(&scales)
                .map(|(value, scale)| raw_floor_threshold(value, scale).unwrap())
                .collect(),
            negative_minima: negative
                .iter()
                .zip(&scales)
                .map(|(value, scale)| raw_ceiling_threshold(value, scale).unwrap().unwrap())
                .collect(),
        };
        for first in -8_i64..=8 {
            for second in -8_i64..=8 {
                let points = [0_i64, 0_i64, first, second];
                let packed = packed_relation_state(&points, 0, 1, &front).unwrap();
                let differences = [
                    &scales[0] * Rat::from_integer(BigInt::from(first.abs())),
                    &scales[1] * Rat::from_integer(BigInt::from(second.abs())),
                ];
                let in_positive = differences
                    .iter()
                    .zip(&positive)
                    .all(|(difference, maximum)| difference <= maximum);
                let in_negative = differences
                    .iter()
                    .zip(&negative)
                    .all(|(difference, minimum)| minimum <= difference);
                let rational = match (in_positive, in_negative) {
                    (true, false) => 0,
                    (false, true) => 1,
                    (false, false) => 2,
                    (true, true) => 3,
                };
                assert_eq!(packed, rational);
            }
        }
    }

    #[test]
    fn prediction_is_graded_before_its_return_can_condition_standing() {
        let mut world = declared_world();
        world
            .receive(&ObservationEcologyEvent::ConditionReturnedBatch {
                event: EventId(3),
                batch: batch(
                    0,
                    "training",
                    vec![
                        occurrence(1, 0, 0, 0),
                        occurrence(2, 1, 0, 0),
                        occurrence(3, 10, 0, 0),
                    ],
                ),
                returned: partition(&[(1, &[1, 2]), (2, &[3])]),
            })
            .unwrap();
        let training_relation = world.standing().relation(FAMILY, ALGORITHM).unwrap();
        assert_eq!(
            training_relation.positive_maxima,
            vec![ExactDifferenceVector(vec![Rat::one(), Rat::zero()])]
        );
        assert_eq!(
            training_relation.negative_minima,
            vec![ExactDifferenceVector(vec![
                Rat::from_integer(BigInt::from(9)),
                Rat::zero()
            ])]
        );

        let prediction_receipt = world
            .receive(&ObservationEcologyEvent::PredictUnpartitionedBatch {
                event: EventId(4),
                algorithm: ALGORITHM,
                batch: batch(
                    1,
                    "held-out",
                    vec![
                        occurrence(4, 100, 0, 1),
                        occurrence(5, 101, 0, 1),
                        occurrence(6, 120, 0, 1),
                    ],
                ),
            })
            .unwrap();
        let prediction = prediction_receipt.radiation[0].prediction.as_ref().unwrap();
        assert_eq!(prediction.id, ReceiverPredictionId(1));
        assert_eq!(prediction.candidate_relations.len(), 1);
        assert_eq!(
            prediction.candidate_relations[0].state,
            ReceiverRelationState::ForcedTogether
        );
        assert_eq!(
            prediction.forced_components,
            vec![
                vec![ReceiverTestimonyId(4), ReceiverTestimonyId(5)],
                vec![ReceiverTestimonyId(6)]
            ]
        );
        assert_eq!(world.standing().admitted_testimony_count(), 3);
        assert_eq!(world.standing().pending_testimony_count(), 3);

        let grade_receipt = world
            .receive(&ObservationEcologyEvent::GradeReturnedPartition {
                event: EventId(5),
                prediction: prediction.id,
                returned: partition(&[(10, &[4, 5]), (11, &[6])]),
            })
            .unwrap();
        let grade = grade_receipt.radiation[0].grade.as_ref().unwrap();
        assert!(grade.obstructions.is_empty());
        assert_eq!(grade.counts.forced_together_correct, 1);
        assert_eq!(grade.counts.forced_apart_correct, 2);
        assert_eq!(world.standing().admitted_testimony_count(), 3);

        world
            .receive(&ObservationEcologyEvent::AdmitGradedReturn {
                event: EventId(6),
                grade: grade.id,
            })
            .unwrap();
        assert_eq!(world.standing().admitted_testimony_count(), 6);
        assert_eq!(world.standing().pending_testimony_count(), 0);
        assert!(world.standing().grade_is_admitted(grade.id));
        world.standing().validate().unwrap();

        let encoded = ron::to_string(world.standing()).unwrap();
        let remounted: ObservationEcologyStanding = ron::from_str(&encoded).unwrap();
        assert_eq!(&remounted, world.standing());
        remounted.validate().unwrap();
    }

    #[test]
    fn incompatible_projection_lineage_remains_a_structured_conflict() {
        let mut world = declared_world();
        world
            .receive(&ObservationEcologyEvent::ConditionReturnedBatch {
                event: EventId(3),
                batch: batch(
                    0,
                    "ambiguous training",
                    vec![
                        occurrence(1, 0, 0, 0),
                        occurrence(2, 1, 0, 0),
                        occurrence(3, 2, 0, 0),
                    ],
                ),
                returned: partition(&[(1, &[1, 2]), (2, &[3])]),
            })
            .unwrap();
        let prediction = world
            .receive(&ObservationEcologyEvent::PredictUnpartitionedBatch {
                event: EventId(4),
                algorithm: ALGORITHM,
                batch: batch(
                    1,
                    "ambiguous held-out",
                    vec![occurrence(4, 10, 0, 1), occurrence(5, 11, 0, 1)],
                ),
            })
            .unwrap()
            .radiation[0]
            .prediction
            .clone()
            .unwrap();
        assert_eq!(
            prediction.candidate_relations[0].state,
            ReceiverRelationState::Conflicted
        );
        let grade = world
            .receive(&ObservationEcologyEvent::GradeReturnedPartition {
                event: EventId(5),
                prediction: prediction.id,
                returned: partition(&[(9, &[4, 5])]),
            })
            .unwrap()
            .radiation[0]
            .grade
            .clone()
            .unwrap();
        assert_eq!(grade.counts.conflicted_pairs, 1);
        assert_eq!(grade.obstructions.len(), 1);
        assert_eq!(
            grade.obstructions[0].kind,
            ReceiverRelationObstructionKind::ConflictedLineage
        );
    }

    #[test]
    fn closed_cells_return_as_coarser_receivers_with_local_hypervolumes() {
        let mut world = declared_world();
        let upper_family = ReceiverCoordinateFamilyId(2);
        let upper_chart = ReceiverChartId(2);
        world
            .receive(&ObservationEcologyEvent::DeclareFamily {
                event: EventId(3),
                family: ReceiverCoordinateFamily::new(
                    upper_family,
                    vec!["clock".into(), "local-x".into(), "stratum".into()],
                    vec![0, 1],
                    vec![2],
                )
                .unwrap(),
            })
            .unwrap();
        world
            .receive(&ObservationEcologyEvent::DeclareChart {
                event: EventId(4),
                chart: ReceiverAffineChart::new(
                    upper_chart,
                    ReceiverId(12),
                    upper_family,
                    "coarser receiver chart",
                    vec!["clock".into(), "x".into(), "stratum".into()],
                    vec![Rat::zero(), Rat::zero(), Rat::zero()],
                    vec![
                        vec![Rat::one(), Rat::zero(), Rat::zero()],
                        vec![Rat::zero(), Rat::one(), Rat::zero()],
                        vec![Rat::zero(), Rat::zero(), Rat::one()],
                    ],
                )
                .unwrap(),
            })
            .unwrap();
        world
            .receive(&ObservationEcologyEvent::ConditionReturnedBatch {
                event: EventId(5),
                batch: batch(
                    0,
                    "training",
                    vec![
                        occurrence(1, 0, 0, 0),
                        occurrence(2, 1, 0, 0),
                        occurrence(3, 10, 0, 0),
                    ],
                ),
                returned: partition(&[(1, &[1, 2]), (2, &[3])]),
            })
            .unwrap();
        let prediction = world
            .receive(&ObservationEcologyEvent::PredictUnpartitionedBatch {
                event: EventId(6),
                algorithm: ALGORITHM,
                batch: batch(
                    1,
                    "held-out",
                    vec![
                        occurrence(4, 100, 0, 1),
                        occurrence(5, 101, 0, 1),
                        occurrence(6, 120, 0, 1),
                    ],
                ),
            })
            .unwrap()
            .radiation[0]
            .prediction
            .clone()
            .unwrap();
        let grade = world
            .receive(&ObservationEcologyEvent::GradeReturnedPartition {
                event: EventId(7),
                prediction: prediction.id,
                returned: partition(&[(10, &[4, 5]), (11, &[6])]),
            })
            .unwrap()
            .radiation[0]
            .grade
            .clone()
            .unwrap();
        assert_eq!(grade.receiver_morphology.exact_closures, 2);
        world
            .receive(&ObservationEcologyEvent::AdmitGradedReturn {
                event: EventId(8),
                grade: grade.id,
            })
            .unwrap();

        let perspective = world
            .standing()
            .receiver_perspective(
                ReceiverPerspectiveAddress::Returned(ReturnedReceiverCellAddress {
                    partition_event: EventId(8),
                    cell: ReturnedCellId(10),
                }),
                &ReceiverPerspectiveSpec {
                    causal_coordinate: 2,
                    directional_coordinates: vec![0, 1, 2],
                },
            )
            .unwrap();
        assert_eq!(
            perspective.causal_basis,
            BTreeSet::from([ReceiverTestimonyId(4), ReceiverTestimonyId(5)])
        );
        assert_eq!(perspective.pivot, ReceiverTestimonyId(4));
        assert_eq!(perspective.hypervolume.tangent_rank, 1);
        assert_eq!(perspective.hypervolume.directions.len(), 1);
        assert_eq!(
            perspective.hypervolume.horizon,
            ReceiverHorizonTopology::UncertifiedDirectional {
                projective_dimension: 0
            }
        );

        let upper = ReceiverBatch {
            family: upper_family,
            chronology: 1,
            source: "returned upper receivers".to_owned(),
            aperture: Vec::new(),
            occurrences: vec![
                ReceiverTestimony {
                    id: ReceiverTestimonyId(100),
                    receiver: ReceiverId(12),
                    lineage: ReceiverLineageId(2),
                    chart: upper_chart,
                    source_identity: 10,
                    raw: vec![1, 100, 1],
                },
                ReceiverTestimony {
                    id: ReceiverTestimonyId(101),
                    receiver: ReceiverId(12),
                    lineage: ReceiverLineageId(2),
                    chart: upper_chart,
                    source_identity: 11,
                    raw: vec![1, 120, 1],
                },
            ],
        };
        let mut regressive = upper.clone();
        regressive.chronology = 0;
        assert_eq!(
            world
                .receive(&ObservationEcologyEvent::ReturnPartitionAsReceivers {
                    event: EventId(9),
                    partition_event: EventId(8),
                    upper_batch: regressive,
                    returns: vec![
                        ReceiverCellReturn {
                            source_cell: ReturnedCellId(10),
                            target: ReceiverTestimonyId(100),
                        },
                        ReceiverCellReturn {
                            source_cell: ReturnedCellId(11),
                            target: ReceiverTestimonyId(101),
                        },
                    ],
                })
                .unwrap_err(),
            ObservationEcologyError::ReceiverReturnChronologyRegression { lower: 1, upper: 0 }
        );
        world
            .receive(&ObservationEcologyEvent::ReturnPartitionAsReceivers {
                event: EventId(9),
                partition_event: EventId(8),
                upper_batch: upper,
                returns: vec![
                    ReceiverCellReturn {
                        source_cell: ReturnedCellId(10),
                        target: ReceiverTestimonyId(100),
                    },
                    ReceiverCellReturn {
                        source_cell: ReturnedCellId(11),
                        target: ReceiverTestimonyId(101),
                    },
                ],
            })
            .unwrap();
        assert_eq!(world.standing().receiver_quotients.len(), 2);

        let upper_algorithm = ReturnedAlgorithmId(8);
        assert_eq!(
            world
                .receive(&ObservationEcologyEvent::PredictExistingReceiverBatch {
                    event: EventId(10),
                    algorithm: upper_algorithm,
                    batch: ExistingReceiverBatch {
                        family: upper_family,
                        chronology: 2,
                        source: "wrong upper chronology".to_owned(),
                        aperture: Vec::new(),
                        occurrences: vec![ReceiverTestimonyId(100), ReceiverTestimonyId(101)],
                    },
                })
                .unwrap_err(),
            ObservationEcologyError::ReceiverReturnChronologyMismatch {
                testimony: ReceiverTestimonyId(100),
                expected: 1,
                received: 2,
            }
        );
        world
            .receive(&ObservationEcologyEvent::ConditionExistingReceiverBatch {
                event: EventId(10),
                batch: ExistingReceiverBatch {
                    family: upper_family,
                    chronology: 1,
                    source: "upper training".to_owned(),
                    aperture: Vec::new(),
                    occurrences: vec![ReceiverTestimonyId(100), ReceiverTestimonyId(101)],
                },
                returned: ReturnedReceiverPartition {
                    algorithm: upper_algorithm,
                    coverage: ReturnedCellCoverage::CompleteExclusive,
                    cells: vec![ReturnedReceiverCell {
                        id: ReturnedCellId(20),
                        members: BTreeSet::from([
                            ReceiverTestimonyId(100),
                            ReceiverTestimonyId(101),
                        ]),
                    }],
                },
            })
            .unwrap();
        assert!(
            world
                .standing()
                .relation(upper_family, upper_algorithm)
                .is_some()
        );
        world.standing().validate().unwrap();
        let encoded = ron::to_string(world.standing()).unwrap();
        let remounted: ObservationEcologyStanding = ron::from_str(&encoded).unwrap();
        assert_eq!(&remounted, world.standing());
        remounted.validate().unwrap();
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[ignore = "requires a CUDA device"]
    fn multicore_card_admits_one_mode_then_owns_its_later_relation_states() {
        let workers = NonZeroUsize::new(4).unwrap();
        let mut world = CausalWorld::new(
            ObservationEcologyLaw::multicore_cuda(workers),
            ObservationEcologyStanding::default(),
        );
        world
            .receive(&ObservationEcologyEvent::DeclareFamily {
                event: EventId(1),
                family: family(),
            })
            .unwrap();
        world
            .receive(&ObservationEcologyEvent::DeclareChart {
                event: EventId(2),
                chart: chart(),
            })
            .unwrap();
        world
            .receive(&ObservationEcologyEvent::ConditionReturnedBatch {
                event: EventId(3),
                batch: batch(
                    0,
                    "training",
                    vec![
                        occurrence(1, 0, 0, 0),
                        occurrence(2, 1, 0, 0),
                        occurrence(3, 10, 0, 0),
                    ],
                ),
                returned: partition(&[(1, &[1, 2]), (2, &[3])]),
            })
            .unwrap();
        let prediction_receipt = world
            .receive(&ObservationEcologyEvent::PredictUnpartitionedBatch {
                event: EventId(4),
                algorithm: ALGORITHM,
                batch: batch(
                    1,
                    "held-out",
                    vec![
                        occurrence(4, 100, 0, 1),
                        occurrence(5, 101, 0, 1),
                        occurrence(6, 120, 0, 1),
                    ],
                ),
            })
            .unwrap();
        let prediction = prediction_receipt.radiation[0].prediction.clone().unwrap();
        assert_eq!(
            prediction_receipt.radiation[0]
                .work
                .cuda_classified_relations,
            1
        );
        assert_eq!(
            prediction_receipt.radiation[0].work.cuda_parity_relations,
            1
        );
        assert_eq!(
            prediction_receipt.radiation[0].work.cuda_returned_relations,
            1
        );
        assert_eq!(prediction_receipt.radiation[0].work.cuda_mode_admissions, 1);
        assert_eq!(prediction_receipt.radiation[0].work.cuda_mode_reuses, 0);
        assert_eq!(prediction_receipt.radiation[0].work.cuda_front_uploads, 1);
        assert!(
            prediction_receipt.radiation[0].work.cpu_workers_used > 1,
            "the physical receiver event must actually join a CPU antichain"
        );

        let grade_receipt = world
            .receive(&ObservationEcologyEvent::GradeReturnedPartition {
                event: EventId(5),
                prediction: prediction.id,
                returned: partition(&[(10, &[4, 5]), (11, &[6])]),
            })
            .unwrap();
        assert_eq!(grade_receipt.radiation[0].work.cuda_classified_relations, 3);
        assert_eq!(grade_receipt.radiation[0].work.cuda_parity_relations, 3);
        assert_eq!(grade_receipt.radiation[0].work.cuda_returned_relations, 0);
        assert_eq!(grade_receipt.radiation[0].work.cuda_mode_admissions, 1);
        assert_eq!(grade_receipt.radiation[0].work.cuda_mode_reuses, 0);
        assert_eq!(grade_receipt.radiation[0].work.cuda_front_uploads, 0);
        let grade = grade_receipt.radiation[0].grade.as_ref().unwrap();
        assert_eq!(grade.counts.forced_together_correct, 1);
        assert_eq!(grade.counts.forced_apart_correct, 2);

        let second_prediction = world
            .receive(&ObservationEcologyEvent::PredictUnpartitionedBatch {
                event: EventId(6),
                algorithm: ALGORITHM,
                batch: batch(
                    2,
                    "second held-out",
                    vec![
                        occurrence(7, 200, 0, 2),
                        occurrence(8, 201, 0, 2),
                        occurrence(9, 220, 0, 2),
                    ],
                ),
            })
            .unwrap();
        assert_eq!(
            second_prediction.radiation[0]
                .work
                .cuda_classified_relations,
            1
        );
        assert_eq!(second_prediction.radiation[0].work.cuda_parity_relations, 0);
        assert_eq!(second_prediction.radiation[0].work.cuda_mode_admissions, 0);
        assert_eq!(second_prediction.radiation[0].work.cuda_mode_reuses, 1);
        assert_eq!(
            second_prediction.radiation[0].work.cuda_returned_relations,
            1
        );
        let second_prediction_id = second_prediction.radiation[0]
            .prediction
            .as_ref()
            .unwrap()
            .id;
        let second_grade = world
            .receive(&ObservationEcologyEvent::GradeReturnedPartition {
                event: EventId(7),
                prediction: second_prediction_id,
                returned: partition(&[(20, &[7, 8]), (21, &[9])]),
            })
            .unwrap();
        assert_eq!(second_grade.radiation[0].work.cuda_classified_relations, 3);
        assert_eq!(second_grade.radiation[0].work.cuda_parity_relations, 0);
        assert_eq!(second_grade.radiation[0].work.cuda_mode_admissions, 0);
        assert_eq!(second_grade.radiation[0].work.cuda_mode_reuses, 1);
        assert_eq!(second_grade.radiation[0].work.cuda_resident_modes, 2);
    }
}
