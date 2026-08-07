//! Plural live-current membrane for the production coupled-informant law.
//!
//! The exact world retains every GLM optical relation, ABI spectral section, atmospheric vertical
//! fiber, returned partition, and rational phase branch. This adapter does not serialize that
//! standing into Soma or invent one common sample chart. It transports the exact structural
//! receipts of each typed successor through eight persistent receiver organs whose declared hands
//! preserve the source law:
//!
//! ```text
//! optical  ─┐
//! spectral ─┼─> prediction
//! vertical ─┤
//! chronology┘
//! prediction ─┐
//! return     ──┴─> grade ─> conditioned morphology
//! ```
//!
//! Each organ face is a declared ordered quotient of exact identifiers and population counts.
//! The full rational ecology remains borrowed typed source material throughout the transaction;
//! the quotient is receiver testimony about its change, never a replacement standing.

use std::fmt;

use body::num::Cog;
use holonic_engine::{
    CoupledInformantEvent, CoupledInformantGrade, CoupledInformantLaw, CoupledInformantPrediction,
    CoupledInformantRadiationKind, CoupledInformantStanding, EventSuccessor, ReturnedCellCoverage,
};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryRadiation, CurrentLineage, LiveCurrentError, LiveCurrentExecutor,
    LiveCurrentMachine,
};

use crate::current_world::{
    present_native_event_with, NativeEventCurrent, NativeEventRelation, NativePathChart,
    NativeRelationOrgan, NativeRelationOrganImage, NATIVE_RELATION_ORGAN_WORDS,
};
use crate::exact_world::ExactCurrentAdapter;

pub const COUPLED_INFORMANT_CURRENT_CHANNELS: usize = 8;
pub const COUPLED_INFORMANT_CURRENT_IMAGE_WORDS: usize =
    COUPLED_INFORMANT_CURRENT_CHANNELS * NATIVE_RELATION_ORGAN_WORDS;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum CoupledInformantCurrentChannel {
    Optical = 0,
    Spectral = 1,
    Vertical = 2,
    Chronology = 3,
    Prediction = 4,
    Returned = 5,
    Grade = 6,
    Morphology = 7,
}

impl CoupledInformantCurrentChannel {
    pub const ALL: [Self; COUPLED_INFORMANT_CURRENT_CHANNELS] = [
        Self::Optical,
        Self::Spectral,
        Self::Vertical,
        Self::Chronology,
        Self::Prediction,
        Self::Returned,
        Self::Grade,
        Self::Morphology,
    ];

    const fn action(self) -> i64 {
        0x4355_5200 + self as i64 + 1
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CoupledInformantCurrentAdapterImage {
    organs: [NativeRelationOrganImage; COUPLED_INFORMANT_CURRENT_CHANNELS],
}

impl CoupledInformantCurrentAdapterImage {
    pub const fn organs(self) -> [NativeRelationOrganImage; COUPLED_INFORMANT_CURRENT_CHANNELS] {
        self.organs
    }

    pub fn encode_native_words(self) -> [u32; COUPLED_INFORMANT_CURRENT_IMAGE_WORDS] {
        let mut words = [0u32; COUPLED_INFORMANT_CURRENT_IMAGE_WORDS];
        for (channel, organ) in self.organs.into_iter().enumerate() {
            let begin = channel * NATIVE_RELATION_ORGAN_WORDS;
            let end = begin + NATIVE_RELATION_ORGAN_WORDS;
            words[begin..end].copy_from_slice(&organ.encode_native_words());
        }
        words
    }

    pub fn from_native_words(
        words: &[u32],
        machine: &LiveCurrentMachine,
    ) -> Result<Self, CoupledInformantCurrentError> {
        if words.len() != COUPLED_INFORMANT_CURRENT_IMAGE_WORDS {
            return Err(CoupledInformantCurrentError::InvalidAdapterRest);
        }
        let empty = NativeRelationOrgan::new().checkpoint();
        let mut organs = [empty; COUPLED_INFORMANT_CURRENT_CHANNELS];
        for (channel, organ) in organs.iter_mut().enumerate() {
            let begin = channel * NATIVE_RELATION_ORGAN_WORDS;
            let end = begin + NATIVE_RELATION_ORGAN_WORDS;
            *organ = NativeRelationOrganImage::from_native_words(&words[begin..end], machine)?;
        }
        Ok(Self { organs })
    }
}

pub struct CoupledInformantCurrentAdapter {
    organs: [NativeRelationOrgan; COUPLED_INFORMANT_CURRENT_CHANNELS],
}

impl Default for CoupledInformantCurrentAdapter {
    fn default() -> Self {
        Self::new()
    }
}

impl CoupledInformantCurrentAdapter {
    pub fn new() -> Self {
        Self {
            organs: std::array::from_fn(|_| NativeRelationOrgan::new()),
        }
    }

    pub fn checkpoint(&self) -> CoupledInformantCurrentAdapterImage {
        CoupledInformantCurrentAdapterImage {
            organs: std::array::from_fn(|channel| self.organs[channel].checkpoint()),
        }
    }

    pub fn recover(
        image: CoupledInformantCurrentAdapterImage,
        machine: &LiveCurrentMachine,
    ) -> Result<Self, CoupledInformantCurrentError> {
        let organs = image.organs;
        Ok(Self {
            organs: [
                NativeRelationOrgan::recover(organs[0], machine)?,
                NativeRelationOrgan::recover(organs[1], machine)?,
                NativeRelationOrgan::recover(organs[2], machine)?,
                NativeRelationOrgan::recover(organs[3], machine)?,
                NativeRelationOrgan::recover(organs[4], machine)?,
                NativeRelationOrgan::recover(organs[5], machine)?,
                NativeRelationOrgan::recover(organs[6], machine)?,
                NativeRelationOrgan::recover(organs[7], machine)?,
            ],
        })
    }

    pub fn lineage(&self, channel: CoupledInformantCurrentChannel) -> Option<CurrentLineage> {
        self.organs[channel as usize].lineage()
    }

    fn present_generation(
        &mut self,
        event: &CoupledInformantEvent,
        prediction: &CoupledInformantPrediction,
        work: &holonic_engine::CoupledInformantWork,
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ContemporaryRadiation, CoupledInformantCurrentError> {
        let CoupledInformantEvent::Generate {
            event,
            chronology,
            source_grade_precondition,
            resolution,
        } = event
        else {
            return Err(CoupledInformantCurrentError::RadiationEventMismatch);
        };

        let optical = exact_face(&[
            event.0,
            resolution.source_prediction.id.0,
            usize_to_u64(resolution.source_prediction.occurrences.len())?,
            usize_to_u64(resolution.source_prediction.candidate_relations.len())?,
            work.optical_horizon_relations,
        ])?;
        let total_contacts =
            resolution
                .spectral_occurrences
                .iter()
                .try_fold(0_u64, |total, occurrence| {
                    total
                        .checked_add(usize_to_u64(occurrence.contacts.len())?)
                        .ok_or(CoupledInformantCurrentError::CarrierOverflow)
                })?;
        let selected_contacts =
            resolution
                .contact_selections
                .iter()
                .try_fold(0_u64, |total, selection| {
                    total
                        .checked_add(usize_to_u64(selection.selected_scans.len())?)
                        .ok_or(CoupledInformantCurrentError::CarrierOverflow)
                })?;
        let spectral = exact_face(&[
            resolution.id.0,
            usize_to_u64(resolution.spectral_occurrences.len())?,
            total_contacts,
            selected_contacts,
            work.spectral_local_star_relations,
            work.shared_horizon_relations,
            work.phase_branches,
            work.missing_section_relations,
        ])?;
        let vertical = exact_face(&[
            resolution.profile.0,
            usize_to_u64(resolution.vertical_fibers.len())?,
            usize_to_u64(resolution.lifted_relations.len())?,
            usize_to_u64(resolution.bodies.len())?,
            usize_to_u64(resolution.obstructions.len())?,
        ])?;
        let chronology = exact_face(&[
            event.0,
            *chronology,
            u64::from(source_grade_precondition.is_some()),
            source_grade_precondition.map_or(0, |grade| grade.0),
        ])?;
        let prediction_face = exact_face(&[
            prediction.id.0,
            prediction.source_prediction.0,
            prediction.atmospheric_resolution.0,
            prediction.chronology,
            usize_to_u64(prediction.relations.len())?,
            work.source_relations,
            work.optical_horizon_relations,
            work.spectral_local_star_relations,
            work.shared_horizon_relations,
            work.phase_branches,
            work.missing_section_relations,
        ])?;

        let optical_chart = channel_chart(CoupledInformantCurrentChannel::Optical, &optical)?;
        let spectral_chart = channel_chart(CoupledInformantCurrentChannel::Spectral, &spectral)?;
        let vertical_chart = channel_chart(CoupledInformantCurrentChannel::Vertical, &vertical)?;
        let chronology_chart =
            channel_chart(CoupledInformantCurrentChannel::Chronology, &chronology)?;
        let prediction_chart =
            channel_chart(CoupledInformantCurrentChannel::Prediction, &prediction_face)?;
        let [optical_organ, spectral_organ, vertical_organ, chronology_organ, prediction_organ, _, _, _] =
            &mut self.organs;
        let mut currents = [
            NativeEventCurrent::continuing_complex(
                optical_organ,
                optical_chart.complex(),
                channel_action(CoupledInformantCurrentChannel::Optical)?,
            ),
            NativeEventCurrent::continuing_complex(
                spectral_organ,
                spectral_chart.complex(),
                channel_action(CoupledInformantCurrentChannel::Spectral)?,
            ),
            NativeEventCurrent::continuing_complex(
                vertical_organ,
                vertical_chart.complex(),
                channel_action(CoupledInformantCurrentChannel::Vertical)?,
            ),
            NativeEventCurrent::continuing_complex(
                chronology_organ,
                chronology_chart.complex(),
                channel_action(CoupledInformantCurrentChannel::Chronology)?,
            ),
            NativeEventCurrent::continuing_complex(
                prediction_organ,
                prediction_chart.complex(),
                channel_action(CoupledInformantCurrentChannel::Prediction)?,
            ),
        ];
        present_native_event_with(
            machine,
            executor,
            &mut currents,
            &[
                NativeEventRelation::new(0, 4),
                NativeEventRelation::new(1, 4),
                NativeEventRelation::new(2, 4),
                NativeEventRelation::new(3, 4),
            ],
        )
        .map_err(Into::into)
    }

    fn present_grade(
        &mut self,
        event: &CoupledInformantEvent,
        standing_before: &CoupledInformantStanding,
        grade: &CoupledInformantGrade,
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ContemporaryRadiation, CoupledInformantCurrentError> {
        let CoupledInformantEvent::GradeReturnedPartition {
            event,
            prediction,
            returned,
        } = event
        else {
            return Err(CoupledInformantCurrentError::RadiationEventMismatch);
        };
        let prediction_body = standing_before.predictions.get(prediction).ok_or(
            CoupledInformantCurrentError::MissingPrediction(prediction.0),
        )?;
        let prediction_face = exact_face(&[
            event.0,
            prediction_body.id.0,
            prediction_body.chronology,
            usize_to_u64(prediction_body.relations.len())?,
        ])?;
        let returned_members = returned.cells.iter().try_fold(0_u64, |total, cell| {
            total
                .checked_add(usize_to_u64(cell.members.len())?)
                .ok_or(CoupledInformantCurrentError::CarrierOverflow)
        })?;
        let returned_face = exact_face(&[
            returned.algorithm.0,
            match returned.coverage {
                ReturnedCellCoverage::CompleteExclusive => 1,
                ReturnedCellCoverage::PartialOverlapping => 2,
            },
            usize_to_u64(returned.cells.len())?,
            returned_members,
        ])?;
        let counts = grade.counts;
        let grade_face = exact_face(&[
            grade.id.0,
            grade.prediction.0,
            counts.returned_together_relations,
            counts.returned_apart_relations,
            counts.forced_together_correct,
            counts.forced_apart_correct,
            counts.returned_together_open,
            counts.returned_apart_open,
            counts.returned_together_forced_apart,
            counts.returned_apart_forced_together,
            counts.conflicted_relations,
            counts.missing_section_relations,
            usize_to_u64(grade.obstructions.len())?,
        ])?;

        let prediction_chart =
            channel_chart(CoupledInformantCurrentChannel::Prediction, &prediction_face)?;
        let returned_chart =
            channel_chart(CoupledInformantCurrentChannel::Returned, &returned_face)?;
        let grade_chart = channel_chart(CoupledInformantCurrentChannel::Grade, &grade_face)?;
        let [_, _, _, _, prediction_organ, returned_organ, grade_organ, _] = &mut self.organs;
        let mut currents = [
            NativeEventCurrent::continuing_complex(
                prediction_organ,
                prediction_chart.complex(),
                channel_action(CoupledInformantCurrentChannel::Prediction)?,
            ),
            NativeEventCurrent::continuing_complex(
                returned_organ,
                returned_chart.complex(),
                channel_action(CoupledInformantCurrentChannel::Returned)?,
            ),
            NativeEventCurrent::continuing_complex(
                grade_organ,
                grade_chart.complex(),
                channel_action(CoupledInformantCurrentChannel::Grade)?,
            ),
        ];
        present_native_event_with(
            machine,
            executor,
            &mut currents,
            &[
                NativeEventRelation::new(0, 2),
                NativeEventRelation::new(1, 2),
            ],
        )
        .map_err(Into::into)
    }

    fn present_admission(
        &mut self,
        event: &CoupledInformantEvent,
        standing_before: &CoupledInformantStanding,
        standing_after: &CoupledInformantStanding,
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ContemporaryRadiation, CoupledInformantCurrentError> {
        let CoupledInformantEvent::AdmitGradedReturn { event, grade } = event else {
            return Err(CoupledInformantCurrentError::RadiationEventMismatch);
        };
        let grade_body = standing_before
            .grades
            .get(grade)
            .ok_or(CoupledInformantCurrentError::MissingGrade(grade.0))?;
        let grade_face = exact_face(&[
            event.0,
            grade_body.id.0,
            grade_body.prediction.0,
            grade_body.counts.returned_together_relations,
            grade_body.counts.returned_apart_relations,
            usize_to_u64(grade_body.obstructions.len())?,
        ])?;
        let before = &standing_before.morphology;
        let after = &standing_after.morphology;
        let morphology_face = exact_face(&[
            event.0,
            usize_to_u64(before.positive_maxima.len())?,
            usize_to_u64(after.positive_maxima.len())?,
            usize_to_u64(before.negative_witnesses.len())?,
            usize_to_u64(after.negative_witnesses.len())?,
            usize_to_u64(before.negative_minima.len())?,
            usize_to_u64(after.negative_minima.len())?,
            before.returned_together_branches,
            after.returned_together_branches,
            before.returned_apart_branches,
            after.returned_apart_branches,
            usize_to_u64(after.admitted_events.len())?,
        ])?;

        let grade_chart = channel_chart(CoupledInformantCurrentChannel::Grade, &grade_face)?;
        let morphology_chart =
            channel_chart(CoupledInformantCurrentChannel::Morphology, &morphology_face)?;
        let [_, _, _, _, _, _, grade_organ, morphology_organ] = &mut self.organs;
        let mut currents = [
            NativeEventCurrent::continuing_complex(
                grade_organ,
                grade_chart.complex(),
                channel_action(CoupledInformantCurrentChannel::Grade)?,
            ),
            NativeEventCurrent::continuing_complex(
                morphology_organ,
                morphology_chart.complex(),
                channel_action(CoupledInformantCurrentChannel::Morphology)?,
            ),
        ];
        present_native_event_with(
            machine,
            executor,
            &mut currents,
            &[NativeEventRelation::new(0, 1)],
        )
        .map_err(Into::into)
    }
}

impl ExactCurrentAdapter<CoupledInformantLaw> for CoupledInformantCurrentAdapter {
    type Error = CoupledInformantCurrentError;

    fn found(&mut self, _machine: &mut LiveCurrentMachine) -> Result<(), Self::Error> {
        // A channel cannot be founded before its first actual typed section exists. The current
        // mouth binds each still-absent organ to that first face inside `present_successor`.
        Ok(())
    }

    fn present_successor(
        &mut self,
        event: &CoupledInformantEvent,
        standing_before: &CoupledInformantStanding,
        successor: &EventSuccessor<
            CoupledInformantStanding,
            holonic_engine::CoupledInformantRadiation,
        >,
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ContemporaryRadiation, Self::Error> {
        let [radiation] = successor.radiation.as_slice() else {
            return Err(CoupledInformantCurrentError::RadiationExtent);
        };
        match radiation.kind {
            CoupledInformantRadiationKind::PredictionGenerated => self.present_generation(
                event,
                radiation
                    .prediction
                    .as_deref()
                    .ok_or(CoupledInformantCurrentError::MissingRadiatedPrediction)?,
                &radiation.work,
                machine,
                executor,
            ),
            CoupledInformantRadiationKind::ReturnGraded => self.present_grade(
                event,
                standing_before,
                radiation
                    .grade
                    .as_deref()
                    .ok_or(CoupledInformantCurrentError::MissingRadiatedGrade)?,
                machine,
                executor,
            ),
            CoupledInformantRadiationKind::GradedReturnAdmitted => self.present_admission(
                event,
                standing_before,
                &successor.standing_after,
                machine,
                executor,
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoupledInformantCurrentError {
    Live(LiveCurrentError),
    InvalidChannelGeometry(CoupledInformantCurrentChannel, LiveCurrentError),
    RadiationExtent,
    RadiationEventMismatch,
    MissingRadiatedPrediction,
    MissingRadiatedGrade,
    MissingPrediction(u64),
    MissingGrade(u64),
    CarrierOverflow,
    InvalidAdapterRest,
    NoncanonicalRelation,
    NoncanonicalAction,
}

impl fmt::Display for CoupledInformantCurrentError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Live(error) => write!(formatter, "{error:?}"),
            Self::InvalidChannelGeometry(channel, error) => {
                write!(
                    formatter,
                    "the {channel:?} receiver face is invalid: {error:?}"
                )
            }
            Self::RadiationExtent => formatter
                .write_str("the coupled-informant successor has the wrong radiation extent"),
            Self::RadiationEventMismatch => {
                formatter.write_str("coupled-informant event and radiation species disagree")
            }
            Self::MissingRadiatedPrediction => {
                formatter.write_str("prediction radiation omitted its typed prediction")
            }
            Self::MissingRadiatedGrade => {
                formatter.write_str("grade radiation omitted its typed grade")
            }
            Self::MissingPrediction(prediction) => {
                write!(
                    formatter,
                    "prediction {prediction} is absent before grading"
                )
            }
            Self::MissingGrade(grade) => {
                write!(formatter, "grade {grade} is absent before admission")
            }
            Self::CarrierOverflow => {
                formatter.write_str("a coupled-informant current receipt overflowed")
            }
            Self::InvalidAdapterRest => {
                formatter.write_str("the coupled-informant adapter rest wire is invalid")
            }
            Self::NoncanonicalRelation => {
                formatter.write_str("a coupled-informant current relation is not canonical")
            }
            Self::NoncanonicalAction => {
                formatter.write_str("a coupled-informant current action is not canonical")
            }
        }
    }
}

impl std::error::Error for CoupledInformantCurrentError {}

impl From<LiveCurrentError> for CoupledInformantCurrentError {
    fn from(error: LiveCurrentError) -> Self {
        Self::Live(error)
    }
}

fn relation_atom(value: i64) -> Result<RelationAtom, CoupledInformantCurrentError> {
    RelationAtom::new(Cog::lit(value)).ok_or(CoupledInformantCurrentError::NoncanonicalRelation)
}

fn channel_action(
    channel: CoupledInformantCurrentChannel,
) -> Result<ActionCurrent, CoupledInformantCurrentError> {
    ActionCurrent::new(Cog::lit(channel.action()))
        .ok_or(CoupledInformantCurrentError::NoncanonicalAction)
}

fn channel_chart(
    channel: CoupledInformantCurrentChannel,
    face: &[RelationAtom],
) -> Result<NativePathChart, CoupledInformantCurrentError> {
    NativePathChart::new(face)
        .map_err(|error| CoupledInformantCurrentError::InvalidChannelGeometry(channel, error))
}

/// Exact `u64` receiver face. Every field has a distinct ordered slot followed by its low and high
/// words; neither the Cog grain nor an absolute magnitude is asked to approximate a wide count.
fn exact_face(values: &[u64]) -> Result<Vec<RelationAtom>, CoupledInformantCurrentError> {
    let extent = values
        .len()
        .checked_mul(3)
        .and_then(|extent| extent.checked_add(1))
        .ok_or(CoupledInformantCurrentError::CarrierOverflow)?;
    let mut face = Vec::new();
    face.try_reserve_exact(extent)
        .map_err(|_| CoupledInformantCurrentError::CarrierOverflow)?;
    face.push(relation_atom(0x5245_4c41)?);
    for (slot, value) in values.iter().copied().enumerate() {
        let slot =
            u32::try_from(slot).map_err(|_| CoupledInformantCurrentError::CarrierOverflow)?;
        face.push(relation_atom(i64::from(0x1000_0000_u32 | slot))?);
        face.push(relation_atom(i64::from(value as u32))?);
        face.push(relation_atom(i64::from((value >> 32) as u32))?);
    }
    Ok(face)
}

fn usize_to_u64(value: usize) -> Result<u64, CoupledInformantCurrentError> {
    u64::try_from(value).map_err(|_| CoupledInformantCurrentError::CarrierOverflow)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};
    use std::sync::Arc;

    use holonic_engine::{
        AtmosphericContactSelection, AtmosphericInverseResolution, AtmosphericInverseWork,
        AtmosphericLayerId, AtmosphericProfileId, AtmosphericReceiverBody, AtmosphericResolutionId,
        AtmosphericVerticalCoordinate, AtmosphericVerticalFiber, CausalWorld,
        CoupledInformantEvent, CoupledInformantLaw, CoupledInformantStanding,
        ExactDifferenceVector, ExactInterval, HydrostaticChordReceipt, LearnedPartitionRelation,
        OpaqueThermalChordDoctrine, PredictedReceiverRelation, ReceiverCoordinateFamilyId,
        ReceiverPredictionId, ReceiverRelationPrediction, ReceiverRelationState,
        ReceiverTestimonyId, ReturnedAlgorithmId, ReturnedCellCoverage, ReturnedCellId,
        ReturnedReceiverCell, ReturnedReceiverPartition, SpectralAddressStatus, SpectralBandId,
        SpectralContactTemporality, SpectralReceiverContact, SpectralReceiverOccurrence,
        SpectralScanId, VerticalFiberSupport, COUPLED_SPECTRAL_BANDS,
    };
    use num_bigint::BigInt;
    use relational_geometry::{Rat, ReceiverId};
    use soma_membrane::{
        CurrentExecutionRequest, DirectedExecutionRequest, ExecutedContemporaryEvent,
        HostLiveCurrentExecutor, LiveCurrentError, LiveCurrentExecutor, LiveCurrentMachine,
        LiveCurrentRestImage, RegionalExecutionRequest, SparseStandingSurface,
    };

    use super::*;
    use crate::exact_world::ExactWorldOrgan;

    fn rat(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }

    fn contact(temperature_offset: i64) -> SpectralReceiverContact {
        let mut quality = BTreeMap::new();
        let mut temperatures = BTreeMap::new();
        for (offset, band) in COUPLED_SPECTRAL_BANDS.into_iter().enumerate() {
            quality.insert(band, 0);
            temperatures.insert(
                band,
                rat(270 + temperature_offset + i64::try_from(offset).unwrap()),
            );
        }
        SpectralReceiverContact {
            scan: SpectralScanId(11),
            receiver: ReceiverId(19),
            source: "synthetic exact ABI section".to_owned(),
            clock: ExactInterval::new(rat(0), rat(10)).unwrap(),
            row: 7,
            column: 13,
            address_status: SpectralAddressStatus::SourceDeclaredExact,
            address_doctrine: "test exact address".to_owned(),
            data_quality_flags: quality,
            brightness_temperature_kelvin: temperatures,
        }
    }

    fn hydrostatic(height: i64) -> HydrostaticChordReceipt {
        HydrostaticChordReceipt {
            schema: "test-hydrostatic".to_owned(),
            vertical_coordinate: AtmosphericVerticalCoordinate::IndependentGeometricHeight,
            pressure_log_ratio: ExactInterval::point(rat(1)),
            inverse_temperature_chord: rat(height),
            acceleration_over_gas_constant: ExactInterval::point(rat(1)),
            effective_acceleration_metre_per_second_squared: ExactInterval::point(rat(10)),
            specific_gas_constant: rat(287),
            independent_gravity_testimony: true,
        }
    }

    fn resolution() -> Arc<AtmosphericInverseResolution> {
        let family = ReceiverCoordinateFamilyId(71);
        let algorithm = ReturnedAlgorithmId(73);
        let left = ReceiverTestimonyId(1);
        let right = ReceiverTestimonyId(2);
        let difference = ExactDifferenceVector(vec![rat(1), rat(2), rat(3), rat(4)]);
        let prediction = Arc::new(ReceiverRelationPrediction {
            schema: "test-receiver-prediction".to_owned(),
            id: ReceiverPredictionId(17),
            caused_by: holonic_engine::EventId(19),
            family,
            algorithm,
            chronology: 1,
            source: "synthetic optical horizon".to_owned(),
            aperture: Vec::new(),
            occurrences: vec![left, right],
            candidate_relations: vec![PredictedReceiverRelation {
                members: [left, right],
                difference: difference.clone(),
                state: ReceiverRelationState::Open,
            }],
            forced_components: Vec::new(),
            relation_before: LearnedPartitionRelation {
                schema: "test-learned-relation".to_owned(),
                family,
                algorithm,
                positive_maxima: Vec::new(),
                negative_minima: Vec::new(),
                testimony_events: BTreeSet::new(),
                returned_cells: 0,
            },
        });
        let occurrences = vec![
            SpectralReceiverOccurrence {
                testimony: left,
                source_identity: 101,
                latitude_degree: rat(0),
                longitude_degree: rat(0),
                clock: rat(0),
                radiant_energy: rat(0),
                contacts: vec![contact(0)],
            },
            SpectralReceiverOccurrence {
                testimony: right,
                source_identity: 102,
                latitude_degree: rat(1),
                longitude_degree: rat(2),
                clock: rat(3),
                radiant_energy: rat(4),
                contacts: vec![contact(1)],
            },
        ];
        let profile = AtmosphericProfileId(23);
        let vertical_fibers = vec![
            AtmosphericVerticalFiber {
                testimony: left,
                source_identity: 101,
                scan: SpectralScanId(11),
                spectral_receiver: ReceiverId(19),
                profile,
                layer: AtmosphericLayerId {
                    profile,
                    lower_level: 0,
                },
                support: VerticalFiberSupport::Point(rat(100)),
                brightness_temperature_kelvin: rat(270),
                scan_departure_seconds: rat(0),
                temporality: SpectralContactTemporality::Concurrent,
                pressure_pascal: ExactInterval::point(rat(90_000)),
                layer_temperature_kelvin: ExactInterval::point(rat(270)),
                hydrostatic: hydrostatic(100),
            },
            AtmosphericVerticalFiber {
                testimony: right,
                source_identity: 102,
                scan: SpectralScanId(11),
                spectral_receiver: ReceiverId(19),
                profile,
                layer: AtmosphericLayerId {
                    profile,
                    lower_level: 1,
                },
                support: VerticalFiberSupport::Point(rat(200)),
                brightness_temperature_kelvin: rat(271),
                scan_departure_seconds: rat(1),
                temporality: SpectralContactTemporality::Concurrent,
                pressure_pascal: ExactInterval::point(rat(80_000)),
                layer_temperature_kelvin: ExactInterval::point(rat(271)),
                hydrostatic: hydrostatic(200),
            },
        ];
        Arc::new(AtmosphericInverseResolution {
            schema: "test-atmospheric-resolution".to_owned(),
            id: AtmosphericResolutionId(29),
            caused_by: holonic_engine::EventId(31),
            profile,
            prediction: prediction.id,
            prediction_event: prediction.caused_by,
            source_prediction: prediction,
            doctrine: OpaqueThermalChordDoctrine {
                thermal_band: SpectralBandId(13),
                specific_gas_constant: rat(287),
                logarithm_terms: 8,
            },
            occurrences: vec![left, right],
            spectral_occurrences: occurrences,
            contact_selections: vec![
                AtmosphericContactSelection {
                    testimony: left,
                    source_identity: 101,
                    selected_scans: vec![SpectralScanId(11)],
                    minimum_departure_seconds: Some(rat(0)),
                },
                AtmosphericContactSelection {
                    testimony: right,
                    source_identity: 102,
                    selected_scans: vec![SpectralScanId(11)],
                    minimum_departure_seconds: Some(rat(1)),
                },
            ],
            vertical_fibers,
            lifted_relations: Vec::new(),
            bodies: vec![AtmosphericReceiverBody {
                source_component: 0,
                members: vec![left, right],
                vertical_fibers: vec![0, 1],
                lifted_relations: Vec::new(),
            }],
            obstructions: Vec::new(),
            work: AtmosphericInverseWork::default(),
        })
    }

    fn returned() -> ReturnedReceiverPartition {
        ReturnedReceiverPartition {
            algorithm: ReturnedAlgorithmId(73),
            coverage: ReturnedCellCoverage::CompleteExclusive,
            cells: vec![ReturnedReceiverCell {
                id: ReturnedCellId(1),
                members: [ReceiverTestimonyId(1), ReceiverTestimonyId(2)]
                    .into_iter()
                    .collect(),
            }],
        }
    }

    struct RefusingExecutor;

    impl LiveCurrentExecutor for RefusingExecutor {
        fn enact(
            &mut self,
            _physical_revision: u64,
            _standing: &SparseStandingSurface,
            _currents: &[CurrentExecutionRequest<'_>],
            _relations: &[DirectedExecutionRequest],
            _regional: &[RegionalExecutionRequest<'_>],
        ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
            Err(LiveCurrentError::ResourceReservation)
        }
    }

    #[test]
    fn real_coupled_law_crosses_plural_organs_with_direct_parity_and_exact_remount() {
        let resolution = resolution();
        let generate = CoupledInformantEvent::Generate {
            event: holonic_engine::EventId(1),
            chronology: 1,
            source_grade_precondition: None,
            resolution: Arc::clone(&resolution),
        };
        let mut direct = CausalWorld::new(
            CoupledInformantLaw::serial(),
            CoupledInformantStanding::default(),
        );
        let mut organ = ExactWorldOrgan::new(
            CausalWorld::new(
                CoupledInformantLaw::serial(),
                CoupledInformantStanding::default(),
            ),
            CoupledInformantCurrentAdapter::new(),
        );
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
        organ.found(&mut machine).unwrap();
        let mut refusing = RefusingExecutor;
        let refusal = organ.receive_into(&generate, &mut machine, &mut refusing);
        assert!(matches!(
            refusal,
            Err(holonic_engine::ThroughTransitionError::Cross(
                CoupledInformantCurrentError::Live(LiveCurrentError::ResourceReservation)
            ))
        ));
        assert_eq!(organ.world().next_ordinal(), 1);
        assert_eq!(
            organ.world().standing(),
            &CoupledInformantStanding::default()
        );
        assert_eq!(
            [
                CoupledInformantCurrentChannel::Optical,
                CoupledInformantCurrentChannel::Spectral,
                CoupledInformantCurrentChannel::Vertical,
                CoupledInformantCurrentChannel::Chronology,
                CoupledInformantCurrentChannel::Prediction,
            ]
            .iter()
            .filter(|channel| organ.adapter().lineage(**channel).is_some())
            .count(),
            5
        );
        assert!(organ
            .adapter()
            .lineage(CoupledInformantCurrentChannel::Returned)
            .is_none());

        let mut host = HostLiveCurrentExecutor;
        let direct_generation = direct.receive(&generate).unwrap();
        let (generation, generation_current) = organ
            .receive_into(&generate, &mut machine, &mut host)
            .unwrap();
        assert_eq!(generation, direct_generation);
        assert_eq!(generation_current.currents().len(), 5);
        assert_eq!(generation_current.relations().len(), 4);

        let prediction = generation.radiation[0].prediction.as_ref().unwrap().id;
        let grade = CoupledInformantEvent::GradeReturnedPartition {
            event: holonic_engine::EventId(2),
            prediction,
            returned: returned(),
        };
        let direct_grade = direct.receive(&grade).unwrap();
        let (grade_receipt, grade_current) =
            organ.receive_into(&grade, &mut machine, &mut host).unwrap();
        assert_eq!(grade_receipt, direct_grade);
        assert_eq!(grade_current.currents().len(), 3);
        assert_eq!(grade_current.relations().len(), 2);

        let grade_id = grade_receipt.radiation[0].grade.as_ref().unwrap().id;
        let admit = CoupledInformantEvent::AdmitGradedReturn {
            event: holonic_engine::EventId(3),
            grade: grade_id,
        };
        let direct_admit = direct.receive(&admit).unwrap();
        let (admit_receipt, admit_current) =
            organ.receive_into(&admit, &mut machine, &mut host).unwrap();
        assert_eq!(admit_receipt, direct_admit);
        assert_eq!(admit_current.currents().len(), 2);
        assert_eq!(admit_current.relations().len(), 1);
        assert_eq!(organ.world().standing(), direct.standing());
        assert!(CoupledInformantCurrentChannel::ALL
            .iter()
            .all(|channel| organ.adapter().lineage(*channel).is_some()));

        let typed_native = ron::ser::to_string(organ.world().standing()).unwrap();
        let typed_remount: CoupledInformantStanding = ron::de::from_str(&typed_native).unwrap();
        let next_ordinal = organ.world().next_ordinal();
        let machine_image = machine.rest_image().unwrap();
        let machine_native = machine_image.encode_native_bytes().unwrap();
        let remounted_image = LiveCurrentRestImage::from_native_bytes(&machine_native).unwrap();
        let mut remounted_machine = LiveCurrentMachine::from_rest_image(remounted_image).unwrap();
        let adapter_words = organ.adapter().checkpoint().encode_native_words();
        let adapter_image = CoupledInformantCurrentAdapterImage::from_native_words(
            &adapter_words,
            &remounted_machine,
        )
        .unwrap();
        let adapter =
            CoupledInformantCurrentAdapter::recover(adapter_image, &remounted_machine).unwrap();
        let mut remounted = ExactWorldOrgan::new(
            CausalWorld::from_rest(CoupledInformantLaw::serial(), typed_remount, next_ordinal)
                .unwrap(),
            adapter,
        );
        assert_eq!(
            remounted_machine.rest_image().unwrap(),
            machine.rest_image().unwrap()
        );
        assert_eq!(
            remounted.adapter().checkpoint(),
            organ.adapter().checkpoint()
        );

        let recur = CoupledInformantEvent::Generate {
            event: holonic_engine::EventId(4),
            chronology: 2,
            source_grade_precondition: None,
            resolution,
        };
        let direct_recur = direct.receive(&recur).unwrap();
        let (original_recur, original_current) =
            organ.receive_into(&recur, &mut machine, &mut host).unwrap();
        let mut remounted_host = HostLiveCurrentExecutor;
        let (remounted_recur, remounted_current) = remounted
            .receive_into(&recur, &mut remounted_machine, &mut remounted_host)
            .unwrap();
        assert_eq!(original_recur, direct_recur);
        assert_eq!(remounted_recur, direct_recur);
        assert_eq!(remounted_current, original_current);
        assert_eq!(remounted.world().standing(), organ.world().standing());
        assert_eq!(
            remounted_machine.rest_image().unwrap(),
            machine.rest_image().unwrap()
        );
    }

    #[test]
    #[ignore = "requires the RTX CUDA device and committed lineage_event PTX entry"]
    fn plural_coupled_generation_crosses_the_exact_cuda_mouth() {
        let mut organ = ExactWorldOrgan::new(
            CausalWorld::new(
                CoupledInformantLaw::serial(),
                CoupledInformantStanding::default(),
            ),
            CoupledInformantCurrentAdapter::new(),
        );
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
        let mut cuda = crate::live_current_cuda::CudaLiveCurrentExecutor::new(0).unwrap();
        let (_, current) = organ
            .receive_into(
                &CoupledInformantEvent::Generate {
                    event: holonic_engine::EventId(1),
                    chronology: 1,
                    source_grade_precondition: None,
                    resolution: resolution(),
                },
                &mut machine,
                &mut cuda,
            )
            .unwrap();
        assert_eq!(current.currents().len(), 5);
        assert_eq!(current.relations().len(), 4);
    }
}
