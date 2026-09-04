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

/// The declared comparison membrane: which coordinates this receiver compares, and in what order.
///
/// Until 2026-08-09 this organ carried `COUPLED_PHASE_EXTENT: usize = 18` and
/// `COUPLED_SPECTRAL_BANDS: [SpectralBandId; 5]` — the RELAMPAGO fixture's coordinate count and
/// GOES-16 ABI band list, welded into the library that reads experiments.
/// `docs/canon/THE_AUTHORED_LEVEL.md` §5.1 names it: *"one experiment's material fixed into the organ
/// that reads it."* Nothing here is authored now. The extent is a **reading**:
///
/// ```text
///   extent = optical_arity + bands + (bands - 1) + 5
/// ```
///
/// where the five are the scan departure, the two vertical support endpoints, the vertical extent,
/// and the scan identity, each of which is one difference by construction rather than by choice.
/// A caller either declares the chart with [`CoupledPhaseChart::new`] or reads it off the material
/// with [`CoupledPhaseChart::from_resolution`]; the organ supplies neither and has no `Default`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CoupledPhaseChart {
    optical_arity: usize,
    bands: Vec<SpectralBandId>,
    chord_reference: SpectralBandId,
}

/// The scalar difference coordinates every coupled chart carries: one scan departure, two vertical
/// support endpoints, one vertical extent, one scan identity. Written as a slice so that no number
/// is written at all — the extent below reads this list rather than being fitted to it, which is
/// the same repair `CoupledInformantCurrentChannel::ALL` makes one layer out
/// (`docs/canon/THE_AUTHORED_LEVEL.md` §5.4: a fixed-size array is a level the census cannot see).
const COUPLED_SCALAR_COORDINATES: &[CoupledPhaseCoordinateKind] = &[
    CoupledPhaseCoordinateKind::ScanDepartureDifference,
    CoupledPhaseCoordinateKind::VerticalLowerDifference,
    CoupledPhaseCoordinateKind::VerticalUpperDifference,
    CoupledPhaseCoordinateKind::VerticalExtentDifference,
    CoupledPhaseCoordinateKind::ScanIdentityDifference,
];

impl CoupledPhaseChart {
    /// Declare a comparison membrane. The band order is the caller's and is retained; the chord
    /// reference must be one of the declared bands, because a chord against a band this receiver
    /// does not read is a coordinate nothing can supply.
    pub fn new(
        optical_arity: usize,
        bands: Vec<SpectralBandId>,
        chord_reference: SpectralBandId,
    ) -> Result<Self, CoupledInformantError> {
        if optical_arity == 0 || bands.is_empty() {
            return Err(CoupledInformantError::MalformedPhaseChart);
        }
        let distinct = bands.iter().copied().collect::<BTreeSet<_>>();
        if distinct.len() != bands.len() {
            return Err(CoupledInformantError::MalformedPhaseChart);
        }
        if !distinct.contains(&chord_reference) {
            return Err(CoupledInformantError::ChordReferenceOutsideDeclaredBands(
                chord_reference,
            ));
        }
        Ok(Self {
            optical_arity,
            bands,
            chord_reference,
        })
    }

    /// Read the chart off the material instead of declaring it.
    ///
    /// The optical arity is the source prediction's own difference arity, and every candidate
    /// relation must agree on it. The band population is the **intersection** over every spectral
    /// occurrence of the bands that arrive with a zero quality flag and a temperature: a band one
    /// occurrence cannot supply is not in this receiver's chart. The chord reference is the
    /// resolution's own declared `thermal_band`, which is the one this organ used to spell as the
    /// literal `SpectralBandId(13)` while the material was carrying it all along.
    pub fn from_resolution(
        resolution: &AtmosphericInverseResolution,
    ) -> Result<Self, CoupledInformantError> {
        let mut optical_arity: Option<usize> = None;
        for relation in &resolution.source_prediction.candidate_relations {
            let arity = relation.difference.0.len();
            match optical_arity {
                Some(declared) if declared != arity => {
                    return Err(CoupledInformantError::MaterialOpticalArityDisagrees {
                        declared,
                        supplied: arity,
                    });
                }
                _ => optical_arity = Some(arity),
            }
        }
        let optical_arity = optical_arity.ok_or(CoupledInformantError::MalformedPhaseChart)?;
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
        let mut common: Option<BTreeSet<SpectralBandId>> = None;
        for occurrence in &resolution.spectral_occurrences {
            let selected = selections
                .get(&occurrence.testimony)
                .ok_or(CoupledInformantError::MalformedResolution)?;
            for contact in &occurrence.contacts {
                if !selected.contains(&contact.scan) {
                    continue;
                }
                let supplied = contact
                    .brightness_temperature_kelvin
                    .keys()
                    .copied()
                    .filter(|band| contact.data_quality_flags.get(band).copied() == Some(0))
                    .collect::<BTreeSet<_>>();
                common = Some(match common {
                    Some(standing) => standing.intersection(&supplied).copied().collect(),
                    None => supplied,
                });
            }
        }
        let bands = common.unwrap_or_default();
        if bands.is_empty() {
            return Err(CoupledInformantError::MaterialDeclaresNoSpectralBand);
        }
        Self::new(
            optical_arity,
            bands.into_iter().collect(),
            resolution.doctrine.thermal_band,
        )
    }

    pub fn optical_arity(&self) -> usize {
        self.optical_arity
    }

    pub fn bands(&self) -> &[SpectralBandId] {
        &self.bands
    }

    pub fn chord_reference(&self) -> SpectralBandId {
        self.chord_reference
    }

    /// The bands a chord is taken over: every declared band except the reference, in declaration
    /// order. `bands - 1` of them, and that subtraction is the whole reason the extent is not
    /// twice the band population.
    pub fn chord_bands(&self) -> impl Iterator<Item = SpectralBandId> + '_ {
        let reference = self.chord_reference;
        self.bands
            .iter()
            .copied()
            .filter(move |band| *band != reference)
    }

    /// The comparison face's coordinate count. A reading of this chart, never a declaration about
    /// any other.
    pub fn extent(&self) -> usize {
        self.optical_arity + self.bands.len() * 2 - 1 + COUPLED_SCALAR_COORDINATES.len()
    }

    pub fn coordinate_kinds(&self) -> Vec<CoupledPhaseCoordinateKind> {
        let mut kinds = (0..self.optical_arity)
            .map(|coordinate| CoupledPhaseCoordinateKind::OpticalDifference {
                coordinate: coordinate as u32,
            })
            .collect::<Vec<_>>();
        kinds.extend(
            self.bands
                .iter()
                .copied()
                .map(|band| CoupledPhaseCoordinateKind::BandTemperatureDifference { band }),
        );
        kinds.extend(self.chord_bands().map(|band| {
            CoupledPhaseCoordinateKind::SpectralChordDifference {
                band,
                reference: self.chord_reference,
            }
        }));
        kinds.extend(COUPLED_SCALAR_COORDINATES.iter().copied());
        debug_assert_eq!(kinds.len(), self.extent());
        kinds
    }
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

    fn validate(&self, chart: &CoupledPhaseChart) -> Result<(), CoupledInformantError> {
        if self.0.len() != chart.extent() || self.0.iter().any(Signed::is_negative) {
            return Err(CoupledInformantError::MalformedPhaseVector);
        }
        Ok(())
    }
}

/// The recurrent intermediate body conditioned by earlier complete returns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoupledInformantMorphology {
    pub schema: String,
    /// The comparison membrane every retained phase vector is indexed by. Two bodies conditioned
    /// under different charts are not comparable and this is where that is visible.
    pub chart: CoupledPhaseChart,
    /// The chart's coordinate kinds, stated rather than implied, so the standing says its own
    /// shape. [`CoupledInformantMorphology::validate`] refuses one that disagrees with `chart`.
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

impl CoupledInformantMorphology {
    /// An empty morphology on a declared chart. There is no `Default`: a default chart would be
    /// this organ picking one experiment's coordinate count again, with a trait in front of it.
    pub fn new(chart: CoupledPhaseChart) -> Self {
        Self {
            schema: MORPHOLOGY_SCHEMA.to_owned(),
            coordinate_kinds: chart.coordinate_kinds(),
            chart,
            positive_maxima: Vec::new(),
            negative_witnesses: BTreeMap::new(),
            negative_minima: Vec::new(),
            admitted_events: BTreeSet::new(),
            returned_together_branches: 0,
            returned_apart_branches: 0,
        }
    }

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
            || self.coordinate_kinds != self.chart.coordinate_kinds()
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
            vector.validate(&self.chart)?;
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
    /// The comparison face's coordinate count, so the receipt says its own shape. A reader of a
    /// returned work receipt never has to know what the organ's default extent was, because there
    /// is not one.
    pub phase_extent: u64,
    /// The declared optical arity and spectral band population the extent was read from.
    pub optical_arity: u64,
    pub spectral_bands: u64,
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

impl CoupledInformantStanding {
    /// An empty standing on a declared comparison membrane. `Default` is deliberately absent; the
    /// caller declares the chart or reads it off the material with
    /// [`CoupledPhaseChart::from_resolution`].
    pub fn new(chart: CoupledPhaseChart) -> Self {
        Self {
            schema: STANDING_SCHEMA.to_owned(),
            morphology: CoupledInformantMorphology::new(chart),
            predictions: BTreeMap::new(),
            grades: BTreeMap::new(),
            admitted_grades: BTreeSet::new(),
            used_events: BTreeSet::new(),
            next_prediction: 1,
            next_grade: 1,
        }
    }

    /// The chart this body is conditioned under. Every retained phase vector is indexed by it.
    pub fn chart(&self) -> &CoupledPhaseChart {
        &self.morphology.chart
    }

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
            if prediction.morphology_before.chart != self.morphology.chart {
                return Err(CoupledInformantError::MalformedStanding);
            }
            for relation in &prediction.relations {
                if relation.branches.is_empty()
                    != (relation.state == CoupledInformantRelationState::MissingSection)
                {
                    return Err(CoupledInformantError::MalformedStanding);
                }
                for branch in &relation.branches {
                    branch.phase.validate(&self.morphology.chart)?;
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
    /// One reading per declared band, in the chart's declaration order.
    temperatures: Vec<Rat>,
    /// One chord per declared band except the reference: `bands - 1` of them.
    chords: Vec<Rat>,
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
    let chart = Arc::new(morphology.chart.clone());
    let phases = Arc::new(index_occurrence_phases(resolution, &chart)?);
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
    let relation_inputs = candidate_relation_inputs(resolution, &chart)?;
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
            let chart = Arc::clone(&chart);
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
                        let phase = coupled_phase_vector(
                            &chart,
                            &relation.difference.0,
                            left_phase,
                            right_phase,
                        )?;
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
        phase_extent: usize_to_u64(chart.extent())?,
        optical_arity: usize_to_u64(chart.optical_arity())?,
        spectral_bands: usize_to_u64(chart.bands().len())?,
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
    chart: &CoupledPhaseChart,
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
                && chart.bands().iter().all(|band| {
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
            // A spectral local star founds its own optical difference out of the exact scalars a
            // `SpectralReceiverOccurrence` carries. Its arity is that carrier's, not a level: it is
            // four because the occurrence has four scalar coordinates. Where the declared chart
            // asks for a different optical arity this origin cannot supply it, and that is returned
            // by name rather than by padding a vector to fit.
            let difference = ExactDifferenceVector(vec![
                absolute_difference(&left.latitude_degree, &right.latitude_degree),
                absolute_difference(&left.longitude_degree, &right.longitude_degree),
                absolute_difference(&left.clock, &right.clock),
                absolute_difference(&left.radiant_energy, &right.radiant_energy),
            ]);
            if difference.0.len() != chart.optical_arity() {
                return Err(CoupledInformantError::SpectralStarOpticalArity {
                    declared: chart.optical_arity(),
                    supplied: difference.0.len(),
                });
            }
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
    chart: &CoupledPhaseChart,
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
                || chart.bands().iter().any(|band| {
                    contact.data_quality_flags.get(band).copied() != Some(0)
                        || !contact.brightness_temperature_kelvin.contains_key(band)
                })
            {
                continue;
            }
            let temperatures = chart
                .bands()
                .iter()
                .map(|band| contact.brightness_temperature_kelvin[band].clone())
                .collect::<Vec<_>>();
            let reference = contact.brightness_temperature_kelvin[&chart.chord_reference()].clone();
            let chords = chart
                .chord_bands()
                .map(|band| &contact.brightness_temperature_kelvin[&band] - &reference)
                .collect::<Vec<_>>();
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
    chart: &CoupledPhaseChart,
    optical: &[Rat],
    left: &OccurrencePhase,
    right: &OccurrencePhase,
) -> Result<CoupledPhaseVector, CoupledInformantError> {
    if optical.len() != chart.optical_arity() {
        return Err(CoupledInformantError::IncompatibleOpticalDifference {
            declared: chart.optical_arity(),
            supplied: optical.len(),
        });
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
    vector.validate(chart)?;
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
    #[error("a coupled phase chart declares no optical coordinate, no band, or a repeated band")]
    MalformedPhaseChart,
    #[error("chord reference {0:?} is not one of the declared bands")]
    ChordReferenceOutsideDeclaredBands(SpectralBandId),
    #[error(
        "the material's candidate relations disagree on optical arity: {declared} then {supplied}"
    )]
    MaterialOpticalArityDisagrees { declared: usize, supplied: usize },
    #[error("no spectral band arrives with a zero quality flag in every selected contact")]
    MaterialDeclaresNoSpectralBand,
    #[error(
        "a spectral local star founds {supplied} optical coordinates and the chart declares {declared}"
    )]
    SpectralStarOpticalArity { declared: usize, supplied: usize },
    #[error("atmospheric resolution is empty")]
    EmptyResolution,
    #[error("atmospheric resolution is malformed")]
    MalformedResolution,
    #[error("atmospheric resolution and its source prediction disagree")]
    IncompatibleResolution,
    #[error(
        "the source optical difference carries {supplied} coordinates and the chart declares {declared}"
    )]
    IncompatibleOpticalDifference { declared: usize, supplied: usize },
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

    fn level(value: i64, chart: &CoupledPhaseChart) -> CoupledPhaseVector {
        vector(&vec![value; chart.extent()])
    }

    /// The chart the RELAMPAGO run declares: GOES-16 ABI bands 08/09/10/11/13 against the thermal
    /// band 13, and GLM's four optical scalars. Until 2026-08-09 this was `COUPLED_PHASE_EXTENT`
    /// and `COUPLED_SPECTRAL_BANDS` **inside the library**; it is now one fixture among others.
    fn relampago_chart() -> CoupledPhaseChart {
        CoupledPhaseChart::new(
            4,
            vec![
                SpectralBandId(8),
                SpectralBandId(9),
                SpectralBandId(10),
                SpectralBandId(11),
                SpectralBandId(13),
            ],
            SpectralBandId(13),
        )
        .unwrap()
    }

    #[test]
    fn plural_branches_do_not_force_an_aggregate_when_they_disagree() {
        let chart = relampago_chart();
        let together = CoupledPhaseBranch {
            scans: [SpectralScanId(1), SpectralScanId(1)],
            vertical_fibers: [0, 1],
            phase: level(0, &chart),
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
        let chart = relampago_chart();
        let mut morphology = CoupledInformantMorphology::new(chart.clone());
        morphology.positive_maxima =
            canonical_maximal_front(vec![level(1, &chart), level(2, &chart)]);
        morphology.negative_minima =
            canonical_minimal_front(vec![level(5, &chart), level(6, &chart)]);
        morphology.negative_witnesses.insert(level(5, &chart), 2);
        morphology.validate().unwrap();
        assert_eq!(
            morphology.classify(&level(0, &chart)),
            CoupledInformantRelationState::ForcedTogether
        );
        assert_eq!(
            morphology.classify(&level(7, &chart)),
            CoupledInformantRelationState::Open
        );
        assert_eq!(
            morphology.classify(&level(5, &chart)),
            CoupledInformantRelationState::ForcedApart
        );
        assert_eq!(
            morphology.classify(&level(3, &chart)),
            CoupledInformantRelationState::Open
        );
    }

    /// THE DECLARED CONTROL for the `COUPLED_PHASE_EXTENT` excision.
    ///
    /// The old organ could represent exactly one comparison face, of exactly eighteen coordinates,
    /// on exactly five GOES-16 ABI bands. Three charts are declared here and no two agree on the
    /// extent, so the assertions below **could not be written at all** against the pinned organ,
    /// and the first one would have been the tautology `18 == 18`.
    ///
    /// The orbit is non-trivial by construction: the extents are `18`, `7`, and `28`.
    #[test]
    fn the_extent_is_read_off_the_declared_chart_and_no_two_charts_agree() {
        let relampago = relampago_chart();
        assert_eq!(relampago.extent(), 18);
        assert_eq!(relampago.coordinate_kinds().len(), 18);

        // One band, one optical coordinate: a receiver with no chords at all, because the only
        // band it reads *is* the reference. `bands - 1 = 0` is not a special case here.
        let single = CoupledPhaseChart::new(1, vec![SpectralBandId(4)], SpectralBandId(4)).unwrap();
        assert_eq!(single.extent(), 1 + 1 + 0 + 5);
        assert_eq!(single.chord_bands().count(), 0);
        assert_eq!(single.coordinate_kinds().len(), single.extent());

        // A nine-band hyperspectral receiver on a six-coordinate optical face.
        let wide = CoupledPhaseChart::new(
            6,
            (20..29).map(SpectralBandId).collect(),
            SpectralBandId(24),
        )
        .unwrap();
        assert_eq!(wide.extent(), 6 + 9 + 8 + 5);
        assert_eq!(wide.chord_bands().count(), 8);
        assert!(wide.chord_bands().all(|band| band != SpectralBandId(24)));

        let extents = [relampago.extent(), single.extent(), wide.extent()];
        assert_eq!(extents, [18, 7, 28], "the orbit of the excised level");

        // And a morphology is only comparable within its own chart: the same integer level is a
        // different vector under each, and the standing refuses one that does not fit.
        for chart in [&relampago, &single, &wide] {
            let mut morphology = CoupledInformantMorphology::new(chart.clone());
            morphology.positive_maxima = vec![level(1, chart)];
            morphology.validate().unwrap();
            assert_eq!(morphology.chart.extent(), chart.extent());

            let mut foreign = morphology.clone();
            foreign.positive_maxima = vec![level(1, &relampago_chart_of_other_extent(chart))];
            assert_eq!(
                foreign.validate(),
                Err(CoupledInformantError::MalformedPhaseVector),
                "a vector of another chart's extent is refused by name"
            );
        }
    }

    /// A chart whose extent differs from `chart`, so the refusal above cannot be satisfied by
    /// accident on any of the three declarations.
    fn relampago_chart_of_other_extent(chart: &CoupledPhaseChart) -> CoupledPhaseChart {
        let candidate = CoupledPhaseChart::new(
            1,
            vec![SpectralBandId(1), SpectralBandId(2)],
            SpectralBandId(1),
        )
        .unwrap();
        if candidate.extent() == chart.extent() {
            CoupledPhaseChart::new(
                3,
                vec![SpectralBandId(1), SpectralBandId(2), SpectralBandId(3)],
                SpectralBandId(1),
            )
            .unwrap()
        } else {
            candidate
        }
    }

    #[test]
    fn a_chart_refuses_a_reference_it_does_not_read_and_a_repeated_band() {
        assert_eq!(
            CoupledPhaseChart::new(4, vec![SpectralBandId(8)], SpectralBandId(13)),
            Err(CoupledInformantError::ChordReferenceOutsideDeclaredBands(
                SpectralBandId(13)
            ))
        );
        assert_eq!(
            CoupledPhaseChart::new(
                4,
                vec![SpectralBandId(8), SpectralBandId(8)],
                SpectralBandId(8)
            ),
            Err(CoupledInformantError::MalformedPhaseChart)
        );
        assert_eq!(
            CoupledPhaseChart::new(0, vec![SpectralBandId(8)], SpectralBandId(8)),
            Err(CoupledInformantError::MalformedPhaseChart)
        );
        assert_eq!(
            CoupledPhaseChart::new(4, Vec::new(), SpectralBandId(8)),
            Err(CoupledInformantError::MalformedPhaseChart)
        );
    }
}
