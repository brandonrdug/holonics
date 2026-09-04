//! Exact receiver-relative inversion of an atmospheric vertical section.
//!
//! A satellite occurrence does not arrive with a world altitude.  This law
//! receives a prior machine-generated receiver relation, one or more local
//! spectral contacts, and a separately caused atmospheric profile.  Under an
//! explicit opaque-thermal chord doctrine it returns every vertical fiber
//! whose reported profile temperature can carry the reported brightness
//! temperature.  It never chooses one branch, calls the branch a lightning
//! channel, or promotes a raster address into a world cell.
//!
//! The event relation is lifted over the complete candidate population.
//! Consequently the resulting object is a genuinely higher-dimensional
//! receiver ecology: each optical occurrence may carry several alternative
//! altitude fibers, and each prior event relation carries all unresolved
//! combinations.  A later independent altitude receiver may grade those
//! fibers before its testimony is admitted.

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroUsize;
use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::{Rat, ReceiverId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CpuExecutionError, CpuExecutionReceipt, CpuExecutor, EventId, EventSuccessor, ExactEventLaw,
    ExactInterval, ExactValueError, LogicalResourceReceipt, ReceiverPredictionId,
    ReceiverRelationPrediction, ReceiverRelationState, ReceiverTestimonyId,
};

const PROFILE_SCHEMA: &str = "holonic-engine.atmospheric-profile.v1";
const RESOLUTION_SCHEMA: &str = "holonic-engine.atmospheric-inverse-resolution.v1";
const GRADE_SCHEMA: &str = "holonic-engine.atmospheric-altitude-grade.v1";
const STANDING_SCHEMA: &str = "holonic-engine.atmospheric-inverse-standing.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AtmosphericProfileId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AtmosphericLayerId {
    pub profile: AtmosphericProfileId,
    pub lower_level: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AtmosphericResolutionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AtmosphericGradeId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SpectralScanId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SpectralBandId(pub u16);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum AtmosphericVerticalCoordinate {
    /// An independently measured geometric height above a declared reference
    /// surface.  This may participate in a local-gravity identification.
    IndependentGeometricHeight,
    /// Geopotential divided by a conventional reference acceleration.  A
    /// hydrostatic quotient in this coordinate is physically useful but is
    /// not independent evidence for that acceleration.
    GeopotentialHeight,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericProfileLevel {
    pub pressure_pascal: Option<Rat>,
    pub vertical_coordinate_metre: Option<Rat>,
    pub temperature_kelvin: Option<Rat>,
    pub relative_humidity_tenths_percent: Option<Rat>,
    pub dewpoint_depression_kelvin: Option<Rat>,
    pub wind_direction_degree: Option<Rat>,
    pub wind_speed_metre_per_second: Option<Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericProfile {
    pub schema: String,
    pub id: AtmosphericProfileId,
    pub receiver: ReceiverId,
    pub source: String,
    pub chronology: u64,
    pub clock: ExactInterval,
    pub latitude_degree: Rat,
    pub longitude_degree: Rat,
    pub vertical_coordinate: AtmosphericVerticalCoordinate,
    pub levels: Vec<AtmosphericProfileLevel>,
}

impl AtmosphericProfile {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        id: AtmosphericProfileId,
        receiver: ReceiverId,
        source: impl Into<String>,
        chronology: u64,
        clock: ExactInterval,
        latitude_degree: Rat,
        longitude_degree: Rat,
        vertical_coordinate: AtmosphericVerticalCoordinate,
        levels: Vec<AtmosphericProfileLevel>,
    ) -> Result<Self, AtmosphericInverseError> {
        let profile = Self {
            schema: PROFILE_SCHEMA.to_owned(),
            id,
            receiver,
            source: source.into(),
            chronology,
            clock,
            latitude_degree,
            longitude_degree,
            vertical_coordinate,
            levels,
        };
        profile.validate()?;
        Ok(profile)
    }

    fn validate(&self) -> Result<(), AtmosphericInverseError> {
        if self.schema != PROFILE_SCHEMA || self.source.is_empty() || self.levels.len() < 2 {
            return Err(AtmosphericInverseError::MalformedProfile(self.id));
        }
        let complete = self
            .levels
            .iter()
            .filter_map(|level| {
                Some((
                    level.vertical_coordinate_metre.as_ref()?,
                    level.pressure_pascal.as_ref()?,
                    level.temperature_kelvin.as_ref()?,
                ))
            })
            .collect::<Vec<_>>();
        if complete.len() < 2
            || complete.iter().any(|(_, pressure, temperature)| {
                !pressure.is_positive() || !temperature.is_positive()
            })
            || complete
                .windows(2)
                .any(|pair| pair[0].0 >= pair[1].0 || pair[0].1 <= pair[1].1)
        {
            return Err(AtmosphericInverseError::MalformedProfile(self.id));
        }
        Ok(())
    }

    pub fn complete_layers(
        &self,
        doctrine: &OpaqueThermalChordDoctrine,
    ) -> Result<Vec<AtmosphericLayer>, AtmosphericInverseError> {
        self.validate()?;
        doctrine.validate()?;
        let complete = self
            .levels
            .iter()
            .enumerate()
            .filter_map(|(ordinal, level)| {
                Some((
                    ordinal,
                    level.vertical_coordinate_metre.as_ref()?.clone(),
                    level.pressure_pascal.as_ref()?.clone(),
                    level.temperature_kelvin.as_ref()?.clone(),
                    level.clone(),
                ))
            })
            .collect::<Vec<_>>();
        complete
            .windows(2)
            .map(|pair| {
                let (lower_ordinal, lower_height, lower_pressure, lower_temperature, lower) =
                    &pair[0];
                let (_, upper_height, upper_pressure, upper_temperature, upper) = &pair[1];
                let lower_level = u32::try_from(*lower_ordinal)
                    .map_err(|_| AtmosphericInverseError::CarrierOverflow)?;
                let hydrostatic = hydrostatic_chord(
                    lower_pressure,
                    upper_pressure,
                    lower_height,
                    upper_height,
                    lower_temperature,
                    upper_temperature,
                    &doctrine.specific_gas_constant,
                    doctrine.logarithm_terms,
                    self.vertical_coordinate,
                )?;
                Ok(AtmosphericLayer {
                    id: AtmosphericLayerId {
                        profile: self.id,
                        lower_level,
                    },
                    vertical_coordinate: ExactInterval::new(
                        lower_height.clone(),
                        upper_height.clone(),
                    )?,
                    pressure_pascal: ExactInterval::new(
                        upper_pressure.clone(),
                        lower_pressure.clone(),
                    )?,
                    temperature_kelvin: hull(lower_temperature, upper_temperature),
                    lower_temperature_kelvin: lower_temperature.clone(),
                    upper_temperature_kelvin: upper_temperature.clone(),
                    lower_wind_direction_degree: lower.wind_direction_degree.clone(),
                    upper_wind_direction_degree: upper.wind_direction_degree.clone(),
                    lower_wind_speed_metre_per_second: lower.wind_speed_metre_per_second.clone(),
                    upper_wind_speed_metre_per_second: upper.wind_speed_metre_per_second.clone(),
                    hydrostatic,
                })
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericLayer {
    pub id: AtmosphericLayerId,
    pub vertical_coordinate: ExactInterval,
    pub pressure_pascal: ExactInterval,
    pub temperature_kelvin: ExactInterval,
    pub lower_temperature_kelvin: Rat,
    pub upper_temperature_kelvin: Rat,
    pub lower_wind_direction_degree: Option<Rat>,
    pub upper_wind_direction_degree: Option<Rat>,
    pub lower_wind_speed_metre_per_second: Option<Rat>,
    pub upper_wind_speed_metre_per_second: Option<Rat>,
    pub hydrostatic: HydrostaticChordReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HydrostaticChordReceipt {
    pub schema: String,
    pub vertical_coordinate: AtmosphericVerticalCoordinate,
    pub pressure_log_ratio: ExactInterval,
    /// Trapezoidal chord of `integral dz / T` in metre per kelvin.
    pub inverse_temperature_chord: Rat,
    /// `ln(p_lower/p_upper) / integral(dz/T)` in kelvin per metre.
    pub acceleration_over_gas_constant: ExactInterval,
    /// The preceding quotient multiplied by the doctrine's inherited
    /// specific gas constant.
    pub effective_acceleration_metre_per_second_squared: ExactInterval,
    pub specific_gas_constant: Rat,
    pub independent_gravity_testimony: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpaqueThermalChordDoctrine {
    pub thermal_band: SpectralBandId,
    /// Inherited physical parameter.  It remains visible in every
    /// hydrostatic receipt and is not learned from the profile.
    pub specific_gas_constant: Rat,
    /// Number of positive atanh-series terms retained in the exact logarithm
    /// enclosure.  The rational remainder is carried explicitly.
    pub logarithm_terms: u32,
}

impl OpaqueThermalChordDoctrine {
    pub fn validate(&self) -> Result<(), AtmosphericInverseError> {
        if !self.specific_gas_constant.is_positive() {
            return Err(AtmosphericInverseError::NonpositiveGasConstant);
        }
        if self.logarithm_terms == 0 {
            return Err(AtmosphericInverseError::ZeroLogarithmTerms);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpectralReceiverContact {
    pub scan: SpectralScanId,
    pub receiver: ReceiverId,
    pub source: String,
    pub clock: ExactInterval,
    pub row: u32,
    pub column: u32,
    pub address_status: SpectralAddressStatus,
    pub address_doctrine: String,
    /// Native data-quality flags carried independently for each band.  Zero
    /// means that the source product called that band sample good; the engine
    /// does not reinterpret that external claim or collapse distinct bands
    /// into one worst-case flag.
    pub data_quality_flags: BTreeMap<SpectralBandId, u8>,
    pub brightness_temperature_kelvin: BTreeMap<SpectralBandId, Rat>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SpectralAddressStatus {
    SourceDeclaredExact,
    ImportedApproximateLandmark,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpectralReceiverOccurrence {
    pub testimony: ReceiverTestimonyId,
    pub source_identity: u64,
    pub latitude_degree: Rat,
    pub longitude_degree: Rat,
    pub clock: Rat,
    pub radiant_energy: Rat,
    /// Every available receiver section is supplied.  The law selects the
    /// least temporally departed good contact and preserves exact ties.
    pub contacts: Vec<SpectralReceiverContact>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SpectralContactTemporality {
    Concurrent,
    Carried,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum VerticalFiberSupport {
    Point(Rat),
    Layer(ExactInterval),
}

impl VerticalFiberSupport {
    pub fn enclosure(&self) -> ExactInterval {
        match self {
            Self::Point(value) => ExactInterval::point(value.clone()),
            Self::Layer(interval) => interval.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericVerticalFiber {
    pub testimony: ReceiverTestimonyId,
    pub source_identity: u64,
    pub scan: SpectralScanId,
    pub spectral_receiver: ReceiverId,
    pub profile: AtmosphericProfileId,
    pub layer: AtmosphericLayerId,
    pub support: VerticalFiberSupport,
    pub brightness_temperature_kelvin: Rat,
    pub scan_departure_seconds: Rat,
    pub temporality: SpectralContactTemporality,
    pub pressure_pascal: ExactInterval,
    pub layer_temperature_kelvin: ExactInterval,
    pub hydrostatic: HydrostaticChordReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericLiftedRelation {
    pub source_relation_members: [ReceiverTestimonyId; 2],
    pub source_difference: crate::ExactDifferenceVector,
    pub left_fiber: u64,
    pub right_fiber: u64,
    /// Every possible right-minus-left altitude difference.
    pub vertical_departure_metre: ExactInterval,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericReceiverBody {
    pub source_component: u64,
    pub members: Vec<ReceiverTestimonyId>,
    pub vertical_fibers: Vec<u64>,
    pub lifted_relations: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericContactSelection {
    pub testimony: ReceiverTestimonyId,
    pub source_identity: u64,
    pub selected_scans: Vec<SpectralScanId>,
    pub minimum_departure_seconds: Option<Rat>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum AtmosphericObstructionKind {
    MissingOccurrence,
    MissingGoodThermalContact,
    ThermalProfileHasNoIntersection,
    RelationEndpointHasNoVerticalFiber,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericObstruction {
    pub kind: AtmosphericObstructionKind,
    pub testimony: Option<ReceiverTestimonyId>,
    pub relation_members: Option<[ReceiverTestimonyId; 2]>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericInverseWork {
    pub occurrences: u64,
    pub profile_layers: u64,
    pub thermal_layer_comparisons: u64,
    pub selected_spectral_contacts: u64,
    pub vertical_fibers: u64,
    pub lifted_relations: u64,
    pub cpu_tasks: u64,
    pub cpu_workers_used: u64,
    pub cpu_antichains: u64,
    pub cpu_joins: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericInverseResolution {
    pub schema: String,
    pub id: AtmosphericResolutionId,
    pub caused_by: EventId,
    pub profile: AtmosphericProfileId,
    pub prediction: ReceiverPredictionId,
    pub prediction_event: EventId,
    /// Complete generated source horizon.  Keeping the originating
    /// prediction prevents a later heterogeneous law from reconstructing a
    /// relation population from the already-lifted altitude product.
    pub source_prediction: Arc<ReceiverRelationPrediction>,
    pub doctrine: OpaqueThermalChordDoctrine,
    pub occurrences: Vec<ReceiverTestimonyId>,
    /// Complete source-provided spectral lineage.  Selection and generated
    /// vertical fibers remain distinct consequences below.
    pub spectral_occurrences: Vec<SpectralReceiverOccurrence>,
    pub contact_selections: Vec<AtmosphericContactSelection>,
    /// Dense fiber identifiers are the zero-based ordinals in this vector.
    pub vertical_fibers: Vec<AtmosphericVerticalFiber>,
    pub lifted_relations: Vec<AtmosphericLiftedRelation>,
    pub bodies: Vec<AtmosphericReceiverBody>,
    pub obstructions: Vec<AtmosphericObstruction>,
    pub work: AtmosphericInverseWork,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AltitudeReceiverLandmark {
    pub testimony: ReceiverTestimonyId,
    pub receiver: ReceiverId,
    pub source_identity: u64,
    pub vertical_coordinate_metre: ExactInterval,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericAltitudeGradeCounts {
    pub returned_occurrences: u64,
    pub returned_with_compatible_fiber: u64,
    pub returned_with_unique_fiber: u64,
    pub returned_with_ambiguous_fibers: u64,
    pub returned_without_compatible_fiber: u64,
    pub predicted_occurrences_without_return: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericAltitudeObstruction {
    pub testimony: ReceiverTestimonyId,
    pub returned: ExactInterval,
    pub predicted: Vec<ExactInterval>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericAltitudeGrade {
    pub schema: String,
    pub id: AtmosphericGradeId,
    pub caused_by: EventId,
    pub resolution: AtmosphericResolutionId,
    pub receiver: ReceiverId,
    pub source: String,
    pub counts: AtmosphericAltitudeGradeCounts,
    pub obstructions: Vec<AtmosphericAltitudeObstruction>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericInverseStanding {
    pub schema: String,
    pub profiles: BTreeMap<AtmosphericProfileId, AtmosphericProfile>,
    pub resolutions: BTreeMap<AtmosphericResolutionId, Arc<AtmosphericInverseResolution>>,
    pub grades: BTreeMap<AtmosphericGradeId, Arc<AtmosphericAltitudeGrade>>,
    used_events: BTreeSet<EventId>,
    next_resolution: u64,
    next_grade: u64,
}

impl Default for AtmosphericInverseStanding {
    fn default() -> Self {
        Self {
            schema: STANDING_SCHEMA.to_owned(),
            profiles: BTreeMap::new(),
            resolutions: BTreeMap::new(),
            grades: BTreeMap::new(),
            used_events: BTreeSet::new(),
            next_resolution: 1,
            next_grade: 1,
        }
    }
}

impl AtmosphericInverseStanding {
    pub fn validate(&self) -> Result<(), AtmosphericInverseError> {
        validate_standing(self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AtmosphericInverseEvent {
    ReceiveProfile {
        event: EventId,
        profile: Box<AtmosphericProfile>,
    },
    ResolvePrediction {
        event: EventId,
        profile: AtmosphericProfileId,
        prediction: Arc<ReceiverRelationPrediction>,
        occurrences: Vec<SpectralReceiverOccurrence>,
        doctrine: OpaqueThermalChordDoctrine,
    },
    GradeAltitudeReturn {
        event: EventId,
        resolution: AtmosphericResolutionId,
        receiver: ReceiverId,
        source: String,
        landmarks: Vec<AltitudeReceiverLandmark>,
    },
}

impl AtmosphericInverseEvent {
    fn event(&self) -> EventId {
        match self {
            Self::ReceiveProfile { event, .. }
            | Self::ResolvePrediction { event, .. }
            | Self::GradeAltitudeReturn { event, .. } => *event,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AtmosphericInverseRadiationKind {
    ProfileReceived,
    PredictionResolved,
    AltitudeReturnGraded,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtmosphericInverseRadiation {
    pub schema: String,
    pub event: EventId,
    pub kind: AtmosphericInverseRadiationKind,
    pub resolution: Option<Arc<AtmosphericInverseResolution>>,
    pub grade: Option<Arc<AtmosphericAltitudeGrade>>,
    pub work: AtmosphericInverseWork,
}

#[derive(Clone, Debug)]
pub struct AtmosphericInverseLaw {
    cpu: CpuExecutor,
}

impl AtmosphericInverseLaw {
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

    pub const fn cpu_executor(&self) -> CpuExecutor {
        self.cpu
    }
}

impl Default for AtmosphericInverseLaw {
    fn default() -> Self {
        let workers = std::thread::available_parallelism()
            .unwrap_or_else(|_| NonZeroUsize::new(1).expect("one is nonzero"));
        Self::multicore(workers)
    }
}

impl ExactEventLaw for AtmosphericInverseLaw {
    type Standing = AtmosphericInverseStanding;
    type Event = AtmosphericInverseEvent;
    type Radiation = AtmosphericInverseRadiation;
    type Error = AtmosphericInverseError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        validate_standing(standing_before)?;
        let event_id = event.event();
        if standing_before.used_events.contains(&event_id) {
            return Err(AtmosphericInverseError::RepeatedEvent(event_id));
        }
        let mut standing_after = standing_before.clone();
        let mut work = AtmosphericInverseWork::default();
        let (kind, resolution, grade, logical) = match event {
            AtmosphericInverseEvent::ReceiveProfile { profile, .. } => {
                profile.validate()?;
                if standing_after.profiles.contains_key(&profile.id) {
                    return Err(AtmosphericInverseError::RepeatedProfile(profile.id));
                }
                standing_after
                    .profiles
                    .insert(profile.id, profile.as_ref().clone());
                (
                    AtmosphericInverseRadiationKind::ProfileReceived,
                    None,
                    None,
                    logical_receipt(&["receive-atmospheric-profile"])?,
                )
            }
            AtmosphericInverseEvent::ResolvePrediction {
                profile,
                prediction,
                occurrences,
                doctrine,
                ..
            } => {
                let profile_body = standing_after
                    .profiles
                    .get(profile)
                    .ok_or(AtmosphericInverseError::MissingProfile(*profile))?;
                let id = AtmosphericResolutionId(standing_after.next_resolution);
                standing_after.next_resolution = standing_after
                    .next_resolution
                    .checked_add(1)
                    .ok_or(AtmosphericInverseError::CarrierOverflow)?;
                let resolved = Arc::new(resolve_prediction(
                    id,
                    event_id,
                    profile_body,
                    prediction,
                    occurrences,
                    doctrine,
                    &self.cpu,
                )?);
                work = resolved.work.clone();
                standing_after.resolutions.insert(id, resolved.clone());
                (
                    AtmosphericInverseRadiationKind::PredictionResolved,
                    Some(resolved),
                    None,
                    logical_receipt(&[
                        "select-receiver-contact",
                        "restrict-vertical-profile",
                        "lift-generated-relation",
                    ])?,
                )
            }
            AtmosphericInverseEvent::GradeAltitudeReturn {
                resolution,
                receiver,
                source,
                landmarks,
                ..
            } => {
                let resolved = standing_after
                    .resolutions
                    .get(resolution)
                    .ok_or(AtmosphericInverseError::MissingResolution(*resolution))?;
                let id = AtmosphericGradeId(standing_after.next_grade);
                standing_after.next_grade = standing_after
                    .next_grade
                    .checked_add(1)
                    .ok_or(AtmosphericInverseError::CarrierOverflow)?;
                let graded = Arc::new(grade_altitude_return(
                    id, event_id, resolved, *receiver, source, landmarks,
                )?);
                standing_after.grades.insert(id, graded.clone());
                (
                    AtmosphericInverseRadiationKind::AltitudeReturnGraded,
                    None,
                    Some(graded),
                    logical_receipt(&["receive-altitude-return", "grade-before-admission"])?,
                )
            }
        };
        standing_after.used_events.insert(event_id);
        validate_standing(&standing_after)?;
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![AtmosphericInverseRadiation {
                schema: "holonic-engine.atmospheric-inverse-radiation.v1".to_owned(),
                event: event_id,
                kind,
                resolution,
                grade,
                work,
            }],
            logical_resources: Some(logical),
            physical_resources: None,
        })
    }
}

fn resolve_prediction(
    id: AtmosphericResolutionId,
    event: EventId,
    profile: &AtmosphericProfile,
    prediction: &ReceiverRelationPrediction,
    occurrences: &[SpectralReceiverOccurrence],
    doctrine: &OpaqueThermalChordDoctrine,
    cpu: &CpuExecutor,
) -> Result<AtmosphericInverseResolution, AtmosphericInverseError> {
    doctrine.validate()?;
    let occurrence_ids = occurrences
        .iter()
        .map(|occurrence| occurrence.testimony)
        .collect::<BTreeSet<_>>();
    let predicted_ids = prediction
        .occurrences
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if occurrence_ids.len() != occurrences.len() || occurrence_ids != predicted_ids {
        return Err(AtmosphericInverseError::IncompatiblePredictionPopulation);
    }
    if let Some(occurrence) = occurrences.iter().find(|occurrence| {
        occurrence.contacts.iter().any(|contact| {
            contact.source.is_empty()
                || contact.address_doctrine.is_empty()
                || contact
                    .brightness_temperature_kelvin
                    .keys()
                    .copied()
                    .collect::<BTreeSet<_>>()
                    != contact
                        .data_quality_flags
                        .keys()
                        .copied()
                        .collect::<BTreeSet<_>>()
        })
    }) {
        return Err(AtmosphericInverseError::MalformedSpectralOccurrence(
            occurrence.testimony,
        ));
    }
    let layers = profile.complete_layers(doctrine)?;
    let inputs = occurrences.to_vec();
    let (resolved, receipt) = cpu
        .execute_indexed(&inputs, |_, occurrence| {
            resolve_occurrence(profile, &layers, doctrine, occurrence)
        })
        .map_err(map_cpu_error)?;
    let mut work = AtmosphericInverseWork {
        occurrences: usize_to_u64(occurrences.len())?,
        profile_layers: usize_to_u64(layers.len())?,
        thermal_layer_comparisons: usize_to_u64(
            occurrences
                .len()
                .checked_mul(layers.len())
                .ok_or(AtmosphericInverseError::CarrierOverflow)?,
        )?,
        ..AtmosphericInverseWork::default()
    };
    accumulate_cpu(&mut work, &receipt)?;

    let mut vertical_fibers = Vec::new();
    let mut fibers_by_testimony = BTreeMap::<ReceiverTestimonyId, Vec<u64>>::new();
    let mut contact_selections = Vec::with_capacity(resolved.len());
    let mut obstructions = Vec::new();
    for occurrence in resolved {
        work.selected_spectral_contacts = work
            .selected_spectral_contacts
            .checked_add(usize_to_u64(occurrence.selected_contacts)?)
            .ok_or(AtmosphericInverseError::CarrierOverflow)?;
        contact_selections.push(AtmosphericContactSelection {
            testimony: occurrence.testimony,
            source_identity: occurrence.source_identity,
            selected_scans: occurrence.selected_scans,
            minimum_departure_seconds: occurrence.minimum_departure_seconds,
        });
        if let Some(kind) = occurrence.obstruction {
            obstructions.push(AtmosphericObstruction {
                kind,
                testimony: Some(occurrence.testimony),
                relation_members: None,
            });
        }
        for fiber in occurrence.fibers {
            let ordinal = usize_to_u64(vertical_fibers.len())?;
            fibers_by_testimony
                .entry(fiber.testimony)
                .or_default()
                .push(ordinal);
            vertical_fibers.push(fiber);
        }
    }
    work.vertical_fibers = usize_to_u64(vertical_fibers.len())?;

    let mut lifted_relations = Vec::new();
    for relation in prediction
        .candidate_relations
        .iter()
        .filter(|relation| relation.state == ReceiverRelationState::ForcedTogether)
    {
        let left = fibers_by_testimony
            .get(&relation.members[0])
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let right = fibers_by_testimony
            .get(&relation.members[1])
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        if left.is_empty() || right.is_empty() {
            obstructions.push(AtmosphericObstruction {
                kind: AtmosphericObstructionKind::RelationEndpointHasNoVerticalFiber,
                testimony: None,
                relation_members: Some(relation.members),
            });
            continue;
        }
        for left_fiber in left {
            for right_fiber in right {
                let left_support = vertical_fibers[u64_to_usize(*left_fiber)?]
                    .support
                    .enclosure();
                let right_support = vertical_fibers[u64_to_usize(*right_fiber)?]
                    .support
                    .enclosure();
                lifted_relations.push(AtmosphericLiftedRelation {
                    source_relation_members: relation.members,
                    source_difference: relation.difference.clone(),
                    left_fiber: *left_fiber,
                    right_fiber: *right_fiber,
                    vertical_departure_metre: ExactInterval::new(
                        &right_support.lower - &left_support.upper,
                        &right_support.upper - &left_support.lower,
                    )?,
                });
            }
        }
    }
    work.lifted_relations = usize_to_u64(lifted_relations.len())?;

    let mut lifted_by_testimony = BTreeMap::<ReceiverTestimonyId, Vec<u64>>::new();
    for (ordinal, relation) in lifted_relations.iter().enumerate() {
        let ordinal = usize_to_u64(ordinal)?;
        for testimony in relation.source_relation_members {
            lifted_by_testimony
                .entry(testimony)
                .or_default()
                .push(ordinal);
        }
    }
    let bodies = prediction
        .forced_components
        .iter()
        .enumerate()
        .map(|(component, members)| {
            let member_set = members.iter().copied().collect::<BTreeSet<_>>();
            let vertical = members
                .iter()
                .flat_map(|member| {
                    fibers_by_testimony
                        .get(member)
                        .into_iter()
                        .flatten()
                        .copied()
                })
                .collect::<BTreeSet<_>>();
            let relations = members
                .iter()
                .flat_map(|member| {
                    lifted_by_testimony
                        .get(member)
                        .into_iter()
                        .flatten()
                        .copied()
                })
                .filter(|relation| {
                    let relation = &lifted_relations[u64_to_usize(*relation)
                        .expect("lifted relation ordinal was generated locally")];
                    relation
                        .source_relation_members
                        .iter()
                        .all(|member| member_set.contains(member))
                })
                .collect::<BTreeSet<_>>();
            Ok(AtmosphericReceiverBody {
                source_component: usize_to_u64(component)?,
                members: members.clone(),
                vertical_fibers: vertical.into_iter().collect(),
                lifted_relations: relations.into_iter().collect(),
            })
        })
        .collect::<Result<Vec<_>, AtmosphericInverseError>>()?;

    Ok(AtmosphericInverseResolution {
        schema: RESOLUTION_SCHEMA.to_owned(),
        id,
        caused_by: event,
        profile: profile.id,
        prediction: prediction.id,
        prediction_event: prediction.caused_by,
        source_prediction: Arc::new(prediction.clone()),
        doctrine: doctrine.clone(),
        occurrences: prediction.occurrences.clone(),
        spectral_occurrences: occurrences.to_vec(),
        contact_selections,
        vertical_fibers,
        lifted_relations,
        bodies,
        obstructions,
        work,
    })
}

struct ResolvedOccurrence {
    testimony: ReceiverTestimonyId,
    source_identity: u64,
    selected_contacts: usize,
    selected_scans: Vec<SpectralScanId>,
    minimum_departure_seconds: Option<Rat>,
    fibers: Vec<AtmosphericVerticalFiber>,
    obstruction: Option<AtmosphericObstructionKind>,
}

fn resolve_occurrence(
    profile: &AtmosphericProfile,
    layers: &[AtmosphericLayer],
    doctrine: &OpaqueThermalChordDoctrine,
    occurrence: &SpectralReceiverOccurrence,
) -> Result<ResolvedOccurrence, AtmosphericInverseError> {
    let good = occurrence
        .contacts
        .iter()
        .filter_map(|contact| {
            if contact
                .data_quality_flags
                .get(&doctrine.thermal_band)
                .copied()
                != Some(0)
            {
                return None;
            }
            let brightness = contact
                .brightness_temperature_kelvin
                .get(&doctrine.thermal_band)?;
            Some((
                contact,
                brightness,
                interval_distance(&occurrence.clock, &contact.clock),
            ))
        })
        .collect::<Vec<_>>();
    let Some(minimum_departure) = good
        .iter()
        .map(|(_, _, departure)| departure)
        .min()
        .cloned()
    else {
        return Ok(ResolvedOccurrence {
            testimony: occurrence.testimony,
            source_identity: occurrence.source_identity,
            selected_contacts: 0,
            selected_scans: Vec::new(),
            minimum_departure_seconds: None,
            fibers: Vec::new(),
            obstruction: Some(AtmosphericObstructionKind::MissingGoodThermalContact),
        });
    };
    let selected = good
        .into_iter()
        .filter(|(_, _, departure)| departure == &minimum_departure)
        .collect::<Vec<_>>();
    let mut fibers = Vec::new();
    for (contact, brightness, departure) in &selected {
        for layer in layers {
            let Some(support) = thermal_chord_intersection(layer, brightness) else {
                continue;
            };
            fibers.push(AtmosphericVerticalFiber {
                testimony: occurrence.testimony,
                source_identity: occurrence.source_identity,
                scan: contact.scan,
                spectral_receiver: contact.receiver,
                profile: profile.id,
                layer: layer.id,
                support,
                brightness_temperature_kelvin: (*brightness).clone(),
                scan_departure_seconds: (*departure).clone(),
                temporality: if departure.is_zero() {
                    SpectralContactTemporality::Concurrent
                } else {
                    SpectralContactTemporality::Carried
                },
                pressure_pascal: layer.pressure_pascal.clone(),
                layer_temperature_kelvin: layer.temperature_kelvin.clone(),
                hydrostatic: layer.hydrostatic.clone(),
            });
        }
    }
    fibers.sort_by(|left, right| {
        (
            left.scan,
            left.layer,
            left.support.enclosure().lower,
            left.support.enclosure().upper,
        )
            .cmp(&(
                right.scan,
                right.layer,
                right.support.enclosure().lower,
                right.support.enclosure().upper,
            ))
    });
    fibers.dedup();
    let obstruction = fibers
        .is_empty()
        .then_some(AtmosphericObstructionKind::ThermalProfileHasNoIntersection);
    Ok(ResolvedOccurrence {
        testimony: occurrence.testimony,
        source_identity: occurrence.source_identity,
        selected_contacts: selected.len(),
        selected_scans: selected
            .iter()
            .map(|(contact, _, _)| contact.scan)
            .collect(),
        minimum_departure_seconds: Some(minimum_departure),
        fibers,
        obstruction,
    })
}

fn thermal_chord_intersection(
    layer: &AtmosphericLayer,
    brightness: &Rat,
) -> Option<VerticalFiberSupport> {
    if brightness < &layer.temperature_kelvin.lower || brightness > &layer.temperature_kelvin.upper
    {
        return None;
    }
    let lower_temperature = &layer.lower_temperature_kelvin;
    let upper_temperature = &layer.upper_temperature_kelvin;
    if lower_temperature == upper_temperature {
        return (brightness == lower_temperature)
            .then(|| VerticalFiberSupport::Layer(layer.vertical_coordinate.clone()));
    }
    let fraction = (brightness - lower_temperature) / (upper_temperature - lower_temperature);
    let altitude = &layer.vertical_coordinate.lower
        + fraction * (&layer.vertical_coordinate.upper - &layer.vertical_coordinate.lower);
    Some(VerticalFiberSupport::Point(altitude))
}

fn grade_altitude_return(
    id: AtmosphericGradeId,
    event: EventId,
    resolution: &AtmosphericInverseResolution,
    receiver: ReceiverId,
    source: &str,
    landmarks: &[AltitudeReceiverLandmark],
) -> Result<AtmosphericAltitudeGrade, AtmosphericInverseError> {
    if source.is_empty() {
        return Err(AtmosphericInverseError::EmptyAltitudeReturnSource);
    }
    let mut indexed = BTreeMap::new();
    for landmark in landmarks {
        if landmark.receiver != receiver {
            return Err(AtmosphericInverseError::MixedAltitudeReturnReceivers);
        }
        if indexed.insert(landmark.testimony, landmark).is_some() {
            return Err(AtmosphericInverseError::RepeatedAltitudeLandmark(
                landmark.testimony,
            ));
        }
    }
    let predicted = resolution
        .occurrences
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if let Some(testimony) = indexed
        .keys()
        .find(|testimony| !predicted.contains(testimony))
    {
        return Err(AtmosphericInverseError::UnknownAltitudeLandmark(*testimony));
    }
    let fibers = resolution.vertical_fibers.iter().fold(
        BTreeMap::<ReceiverTestimonyId, Vec<ExactInterval>>::new(),
        |mut indexed, fiber| {
            indexed
                .entry(fiber.testimony)
                .or_default()
                .push(fiber.support.enclosure());
            indexed
        },
    );
    let mut counts = AtmosphericAltitudeGradeCounts {
        returned_occurrences: usize_to_u64(landmarks.len())?,
        predicted_occurrences_without_return: usize_to_u64(
            predicted.len().saturating_sub(indexed.len()),
        )?,
        ..AtmosphericAltitudeGradeCounts::default()
    };
    let mut obstructions = Vec::new();
    for landmark in landmarks {
        let candidates = fibers.get(&landmark.testimony).cloned().unwrap_or_default();
        let compatible = candidates
            .iter()
            .filter(|candidate| intervals_intersect(candidate, &landmark.vertical_coordinate_metre))
            .count();
        match compatible {
            0 => {
                counts.returned_without_compatible_fiber += 1;
                obstructions.push(AtmosphericAltitudeObstruction {
                    testimony: landmark.testimony,
                    returned: landmark.vertical_coordinate_metre.clone(),
                    predicted: candidates,
                });
            }
            1 => {
                counts.returned_with_compatible_fiber += 1;
                counts.returned_with_unique_fiber += 1;
            }
            _ => {
                counts.returned_with_compatible_fiber += 1;
                counts.returned_with_ambiguous_fibers += 1;
            }
        }
    }
    Ok(AtmosphericAltitudeGrade {
        schema: GRADE_SCHEMA.to_owned(),
        id,
        caused_by: event,
        resolution: resolution.id,
        receiver,
        source: source.to_owned(),
        counts,
        obstructions,
    })
}

fn validate_standing(standing: &AtmosphericInverseStanding) -> Result<(), AtmosphericInverseError> {
    if standing.schema != STANDING_SCHEMA
        || standing
            .profiles
            .iter()
            .any(|(id, profile)| id != &profile.id || profile.validate().is_err())
        || standing.resolutions.iter().any(|(id, resolution)| {
            let occurrence_ids = resolution
                .occurrences
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            let spectral_ids = resolution
                .spectral_occurrences
                .iter()
                .map(|occurrence| occurrence.testimony)
                .collect::<BTreeSet<_>>();
            let selection_ids = resolution
                .contact_selections
                .iter()
                .map(|selection| selection.testimony)
                .collect::<BTreeSet<_>>();
            id != &resolution.id
                || resolution.schema != RESOLUTION_SCHEMA
                || !standing.profiles.contains_key(&resolution.profile)
                || resolution.source_prediction.id != resolution.prediction
                || resolution.source_prediction.caused_by != resolution.prediction_event
                || resolution.source_prediction.occurrences != resolution.occurrences
                || occurrence_ids.len() != resolution.occurrences.len()
                || spectral_ids.len() != resolution.spectral_occurrences.len()
                || selection_ids.len() != resolution.contact_selections.len()
                || occurrence_ids != spectral_ids
                || occurrence_ids != selection_ids
        })
        || standing.grades.iter().any(|(id, grade)| {
            id != &grade.id
                || grade.schema != GRADE_SCHEMA
                || !standing.resolutions.contains_key(&grade.resolution)
        })
    {
        return Err(AtmosphericInverseError::MalformedStanding);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn hydrostatic_chord(
    lower_pressure: &Rat,
    upper_pressure: &Rat,
    lower_height: &Rat,
    upper_height: &Rat,
    lower_temperature: &Rat,
    upper_temperature: &Rat,
    gas_constant: &Rat,
    logarithm_terms: u32,
    vertical_coordinate: AtmosphericVerticalCoordinate,
) -> Result<HydrostaticChordReceipt, AtmosphericInverseError> {
    if lower_pressure <= upper_pressure
        || lower_height >= upper_height
        || !lower_temperature.is_positive()
        || !upper_temperature.is_positive()
    {
        return Err(AtmosphericInverseError::MalformedHydrostaticLayer);
    }
    let pressure_log_ratio =
        exact_positive_log_ratio(lower_pressure, upper_pressure, logarithm_terms)?;
    let two = Rat::from_integer(2.into());
    let inverse_temperature_chord = (upper_height - lower_height)
        * (Rat::one() / lower_temperature + Rat::one() / upper_temperature)
        / two;
    if !inverse_temperature_chord.is_positive() {
        return Err(AtmosphericInverseError::MalformedHydrostaticLayer);
    }
    let acceleration_over_gas_constant =
        divide_positive_interval(&pressure_log_ratio, &inverse_temperature_chord)?;
    let effective_acceleration_metre_per_second_squared = ExactInterval::new(
        &acceleration_over_gas_constant.lower * gas_constant,
        &acceleration_over_gas_constant.upper * gas_constant,
    )?;
    Ok(HydrostaticChordReceipt {
        schema: "holonic-engine.hydrostatic-chord-receipt.v1".to_owned(),
        vertical_coordinate,
        pressure_log_ratio,
        inverse_temperature_chord,
        acceleration_over_gas_constant,
        effective_acceleration_metre_per_second_squared,
        specific_gas_constant: gas_constant.clone(),
        independent_gravity_testimony: vertical_coordinate
            == AtmosphericVerticalCoordinate::IndependentGeometricHeight,
    })
}

/// Exact rational enclosure of `ln(numerator / denominator)`.
///
/// The implementation uses
/// `ln(x)=2*sum(z^(2k+1)/(2k+1))`, `z=(x-1)/(x+1)`, and retains the positive
/// geometric tail bound.  This is an enclosure, not a floating approximation.
pub fn exact_positive_log_ratio(
    numerator: &Rat,
    denominator: &Rat,
    terms: u32,
) -> Result<ExactInterval, AtmosphericInverseError> {
    if !numerator.is_positive() || !denominator.is_positive() {
        return Err(AtmosphericInverseError::NonpositiveLogarithmArgument);
    }
    if terms == 0 {
        return Err(AtmosphericInverseError::ZeroLogarithmTerms);
    }
    if numerator == denominator {
        return Ok(ExactInterval::point(Rat::zero()));
    }
    if numerator < denominator {
        let forward = exact_positive_log_ratio(denominator, numerator, terms)?;
        return Ok(ExactInterval::new(-forward.upper, -forward.lower)?);
    }
    let z = (numerator - denominator) / (numerator + denominator);
    let z_squared = &z * &z;
    let mut power = z.clone();
    let mut sum = Rat::zero();
    for term in 0..terms {
        let denominator = Rat::from_integer(BigInt::from(2_u64 * u64::from(term) + 1));
        sum += &power / denominator;
        power *= &z_squared;
    }
    sum *= Rat::from_integer(2.into());
    let first_omitted_degree = 2_u64
        .checked_mul(u64::from(terms))
        .and_then(|value| value.checked_add(1))
        .ok_or(AtmosphericInverseError::CarrierOverflow)?;
    let remainder = Rat::from_integer(2.into()) * power
        / Rat::from_integer(BigInt::from(first_omitted_degree))
        / (Rat::one() - z_squared);
    Ok(ExactInterval::new(sum.clone(), sum + remainder)?)
}

fn interval_distance(point: &Rat, interval: &ExactInterval) -> Rat {
    if point < &interval.lower {
        &interval.lower - point
    } else if point > &interval.upper {
        point - &interval.upper
    } else {
        Rat::zero()
    }
}

fn intervals_intersect(left: &ExactInterval, right: &ExactInterval) -> bool {
    left.lower <= right.upper && right.lower <= left.upper
}

fn divide_positive_interval(
    interval: &ExactInterval,
    divisor: &Rat,
) -> Result<ExactInterval, AtmosphericInverseError> {
    if !divisor.is_positive() {
        return Err(AtmosphericInverseError::NonpositiveIntervalDivisor);
    }
    Ok(ExactInterval::new(
        &interval.lower / divisor,
        &interval.upper / divisor,
    )?)
}

fn hull(left: &Rat, right: &Rat) -> ExactInterval {
    if left <= right {
        ExactInterval {
            lower: left.clone(),
            upper: right.clone(),
        }
    } else {
        ExactInterval {
            lower: right.clone(),
            upper: left.clone(),
        }
    }
}

fn logical_receipt(laws: &[&str]) -> Result<LogicalResourceReceipt, AtmosphericInverseError> {
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
    work: &mut AtmosphericInverseWork,
    receipt: &CpuExecutionReceipt,
) -> Result<(), AtmosphericInverseError> {
    work.cpu_tasks = receipt
        .tasks
        .to_u64()
        .ok_or(AtmosphericInverseError::CarrierOverflow)?;
    work.cpu_workers_used = receipt
        .workers_used
        .to_u64()
        .ok_or(AtmosphericInverseError::CarrierOverflow)?;
    work.cpu_antichains = u64::from(!receipt.tasks.is_zero());
    work.cpu_joins = receipt
        .joins
        .to_u64()
        .ok_or(AtmosphericInverseError::CarrierOverflow)?;
    Ok(())
}

fn map_cpu_error(error: CpuExecutionError<AtmosphericInverseError>) -> AtmosphericInverseError {
    match error {
        CpuExecutionError::Operation(error) => error,
        CpuExecutionError::WorkerPanicked => AtmosphericInverseError::PhysicalWorkerPanicked,
    }
}

fn usize_to_u64(value: usize) -> Result<u64, AtmosphericInverseError> {
    u64::try_from(value).map_err(|_| AtmosphericInverseError::CarrierOverflow)
}

fn u64_to_usize(value: u64) -> Result<usize, AtmosphericInverseError> {
    usize::try_from(value).map_err(|_| AtmosphericInverseError::CarrierOverflow)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum AtmosphericInverseError {
    #[error("atmospheric profile {0:?} is malformed")]
    MalformedProfile(AtmosphericProfileId),
    #[error("atmospheric profile {0:?} has already entered standing")]
    RepeatedProfile(AtmosphericProfileId),
    #[error("atmospheric profile {0:?} is absent")]
    MissingProfile(AtmosphericProfileId),
    #[error("atmospheric resolution {0:?} is absent")]
    MissingResolution(AtmosphericResolutionId),
    #[error("atmospheric inverse event {0:?} has already entered standing")]
    RepeatedEvent(EventId),
    #[error("the atmospheric inverse standing is malformed")]
    MalformedStanding,
    #[error("the generated prediction and spectral receiver population differ")]
    IncompatiblePredictionPopulation,
    #[error("spectral occurrence {0:?} is malformed")]
    MalformedSpectralOccurrence(ReceiverTestimonyId),
    #[error("a hydrostatic layer is malformed")]
    MalformedHydrostaticLayer,
    #[error("the inherited specific gas constant must be positive")]
    NonpositiveGasConstant,
    #[error("the exact logarithm requires at least one retained term")]
    ZeroLogarithmTerms,
    #[error("the exact logarithm requires positive arguments")]
    NonpositiveLogarithmArgument,
    #[error("an interval divisor must be positive")]
    NonpositiveIntervalDivisor,
    #[error("an altitude return source must be named")]
    EmptyAltitudeReturnSource,
    #[error("an altitude return mixed receiver identities")]
    MixedAltitudeReturnReceivers,
    #[error("altitude testimony {0:?} was repeated")]
    RepeatedAltitudeLandmark(ReceiverTestimonyId),
    #[error("altitude testimony {0:?} was not part of the prior prediction")]
    UnknownAltitudeLandmark(ReceiverTestimonyId),
    #[error("an atmospheric inverse carrier overflowed")]
    CarrierOverflow,
    #[error("an atmospheric inverse CPU worker panicked")]
    PhysicalWorkerPanicked,
    #[error(transparent)]
    ExactValue(#[from] ExactValueError),
    #[error(transparent)]
    Diagram(#[from] crate::DiagramError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ExactDifferenceVector, PredictedReceiverRelation, ReceiverCoordinateFamilyId,
        ReceiverRelationPrediction,
    };

    fn integer(value: i64) -> Rat {
        Rat::from_integer(value.into())
    }

    fn profile(vertical_coordinate: AtmosphericVerticalCoordinate) -> AtmosphericProfile {
        AtmosphericProfile::new(
            AtmosphericProfileId(1),
            ReceiverId(70),
            "independent sounding",
            1,
            ExactInterval::point(integer(100)),
            integer(-31),
            integer(-64),
            vertical_coordinate,
            vec![
                AtmosphericProfileLevel {
                    pressure_pascal: Some(integer(90_000)),
                    vertical_coordinate_metre: Some(integer(1_000)),
                    temperature_kelvin: Some(integer(280)),
                    relative_humidity_tenths_percent: None,
                    dewpoint_depression_kelvin: None,
                    wind_direction_degree: Some(integer(270)),
                    wind_speed_metre_per_second: Some(integer(10)),
                },
                AtmosphericProfileLevel {
                    pressure_pascal: Some(integer(80_000)),
                    vertical_coordinate_metre: Some(integer(2_000)),
                    temperature_kelvin: Some(integer(260)),
                    relative_humidity_tenths_percent: None,
                    dewpoint_depression_kelvin: None,
                    wind_direction_degree: Some(integer(280)),
                    wind_speed_metre_per_second: Some(integer(20)),
                },
                AtmosphericProfileLevel {
                    pressure_pascal: Some(integer(70_000)),
                    vertical_coordinate_metre: Some(integer(3_000)),
                    temperature_kelvin: Some(integer(270)),
                    relative_humidity_tenths_percent: None,
                    dewpoint_depression_kelvin: None,
                    wind_direction_degree: Some(integer(290)),
                    wind_speed_metre_per_second: Some(integer(30)),
                },
            ],
        )
        .unwrap()
    }

    fn doctrine() -> OpaqueThermalChordDoctrine {
        OpaqueThermalChordDoctrine {
            thermal_band: SpectralBandId(13),
            specific_gas_constant: Rat::new(28_705.into(), 100.into()),
            logarithm_terms: 12,
        }
    }

    fn prediction() -> Arc<ReceiverRelationPrediction> {
        Arc::new(ReceiverRelationPrediction {
            schema: "holonic-engine.receiver-relation-prediction.v1".to_owned(),
            id: ReceiverPredictionId(9),
            caused_by: EventId(20),
            family: ReceiverCoordinateFamilyId(1),
            algorithm: crate::ReturnedAlgorithmId(2),
            chronology: 2,
            source: "generated before return".to_owned(),
            aperture: Vec::new(),
            occurrences: vec![ReceiverTestimonyId(1), ReceiverTestimonyId(2)],
            candidate_relations: vec![PredictedReceiverRelation {
                members: [ReceiverTestimonyId(1), ReceiverTestimonyId(2)],
                difference: ExactDifferenceVector(vec![integer(1)]),
                state: ReceiverRelationState::ForcedTogether,
            }],
            forced_components: vec![vec![ReceiverTestimonyId(1), ReceiverTestimonyId(2)]],
            relation_before: crate::LearnedPartitionRelation {
                schema: "holonic-engine.learned-partition-relation.v1".to_owned(),
                family: ReceiverCoordinateFamilyId(1),
                algorithm: crate::ReturnedAlgorithmId(2),
                positive_maxima: Vec::new(),
                negative_minima: Vec::new(),
                testimony_events: BTreeSet::new(),
                returned_cells: 0,
            },
        })
    }

    fn occurrence(id: u64, temperature: i64) -> SpectralReceiverOccurrence {
        SpectralReceiverOccurrence {
            testimony: ReceiverTestimonyId(id),
            source_identity: id,
            latitude_degree: integer(-31),
            longitude_degree: integer(-64),
            clock: integer(50),
            radiant_energy: integer(1),
            contacts: vec![SpectralReceiverContact {
                scan: SpectralScanId(1),
                receiver: ReceiverId(71),
                source: "native infrared scan".to_owned(),
                clock: ExactInterval::new(integer(40), integer(60)).unwrap(),
                row: 1,
                column: 2,
                address_status: SpectralAddressStatus::SourceDeclaredExact,
                address_doctrine: "test source address".to_owned(),
                data_quality_flags: BTreeMap::from([(SpectralBandId(13), 0)]),
                brightness_temperature_kelvin: BTreeMap::from([(
                    SpectralBandId(13),
                    integer(temperature),
                )]),
            }],
        }
    }

    #[test]
    fn logarithm_enclosure_contains_a_tighter_enclosure() {
        let coarse = exact_positive_log_ratio(&integer(2), &integer(1), 4).unwrap();
        let fine = exact_positive_log_ratio(&integer(2), &integer(1), 16).unwrap();
        assert!(coarse.lower <= fine.lower);
        assert!(coarse.upper >= fine.upper);
        assert!(fine.lower.is_positive());
    }

    #[test]
    fn temperature_recurrence_returns_plural_altitude_fibers() {
        let law = AtmosphericInverseLaw::serial();
        let mut standing = AtmosphericInverseStanding::default();
        standing = law
            .enact(
                &standing,
                &AtmosphericInverseEvent::ReceiveProfile {
                    event: EventId(1),
                    profile: Box::new(profile(AtmosphericVerticalCoordinate::GeopotentialHeight)),
                },
            )
            .unwrap()
            .standing_after;
        let successor = law
            .enact(
                &standing,
                &AtmosphericInverseEvent::ResolvePrediction {
                    event: EventId(2),
                    profile: AtmosphericProfileId(1),
                    prediction: prediction(),
                    occurrences: vec![occurrence(1, 265), occurrence(2, 265)],
                    doctrine: doctrine(),
                },
            )
            .unwrap();
        let resolution = successor.radiation[0].resolution.as_ref().unwrap();
        assert_eq!(resolution.vertical_fibers.len(), 4);
        assert_eq!(resolution.lifted_relations.len(), 4);
        assert!(
            resolution
                .vertical_fibers
                .iter()
                .all(|fiber| !fiber.hydrostatic.independent_gravity_testimony)
        );
    }

    #[test]
    fn altitude_return_grades_before_it_can_replace_plural_fibers() {
        let law = AtmosphericInverseLaw::serial();
        let mut standing = AtmosphericInverseStanding::default();
        standing = law
            .enact(
                &standing,
                &AtmosphericInverseEvent::ReceiveProfile {
                    event: EventId(1),
                    profile: Box::new(profile(
                        AtmosphericVerticalCoordinate::IndependentGeometricHeight,
                    )),
                },
            )
            .unwrap()
            .standing_after;
        standing = law
            .enact(
                &standing,
                &AtmosphericInverseEvent::ResolvePrediction {
                    event: EventId(2),
                    profile: AtmosphericProfileId(1),
                    prediction: prediction(),
                    occurrences: vec![occurrence(1, 265), occurrence(2, 265)],
                    doctrine: doctrine(),
                },
            )
            .unwrap()
            .standing_after;
        let successor = law
            .enact(
                &standing,
                &AtmosphericInverseEvent::GradeAltitudeReturn {
                    event: EventId(3),
                    resolution: AtmosphericResolutionId(1),
                    receiver: ReceiverId(72),
                    source: "independent altitude receiver".to_owned(),
                    landmarks: vec![AltitudeReceiverLandmark {
                        testimony: ReceiverTestimonyId(1),
                        receiver: ReceiverId(72),
                        source_identity: 1,
                        vertical_coordinate_metre: ExactInterval::point(integer(1_750)),
                    }],
                },
            )
            .unwrap();
        let grade = successor.radiation[0].grade.as_ref().unwrap();
        assert_eq!(grade.counts.returned_with_unique_fiber, 1);
        assert_eq!(grade.counts.predicted_occurrences_without_return, 1);
        assert_eq!(
            successor.standing_after.resolutions[&AtmosphericResolutionId(1)]
                .vertical_fibers
                .len(),
            4
        );
    }
}
