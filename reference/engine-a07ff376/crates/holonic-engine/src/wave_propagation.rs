//! Exact receiver-local wave transport learned from returned sections.
//!
//! This module supplies one reusable causal propagation species.  A declared
//! interaction relates a source receiver to a target receiver.  Returned
//! source/target section pairs restrict an exact finite causal kernel fiber.
//! Obstructed testimony founds a new local mode instead of averaging or
//! rewriting an earlier mode.  A later source section is propagated through
//! every contemporary compatible mode before its target return exists; that
//! return is graded as a structured residual before it may condition standing.
//!
//! The finite causal kernel is not asserted to be the universal wave equation.
//! It is a translation-covariant local interaction doctrine whose exact
//! coefficient fiber, plural modes, causal horizon, source lineage, open
//! predictions, and return obstructions remain inspectable.  Audio, image
//! scan-lines, physical sensor histories, and symbolic current may use the
//! same law only when their world membrane declares the corresponding
//! receiver charts and interaction.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    AffineAdmissionWork, CpuExecutionError, CpuExecutionReceipt, CpuExecutor, EventId,
    EventSuccessor, ExactAffinePrediction, ExactAffineVersionFiber, ExactEventLaw,
    InverseTransportError, LogicalResourceReceipt,
};

const SPEC_SCHEMA: &str = "holonic-engine.wave-propagation-spec.v1";
const SECTION_SCHEMA: &str = "holonic-engine.exact-wave-section.v1";
const STANDING_SCHEMA: &str = "holonic-engine.wave-propagation-standing.v1";
const MODE_SCHEMA: &str = "holonic-engine.wave-transport-mode.v1";
const CONDITION_SCHEMA: &str = "holonic-engine.wave-conditioning-receipt.v1";
const GENERATION_SCHEMA: &str = "holonic-engine.wave-generation-receipt.v1";
const RETURN_SCHEMA: &str = "holonic-engine.wave-return-receipt.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct WaveReceiverId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct WaveInteractionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct WaveModeId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct WavePredictionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct WaveLineageId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveReceiverSpec {
    pub id: WaveReceiverId,
    pub name: String,
    /// Coordinates carried by one receiver-local sample.
    pub channels: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveInteractionSpec {
    pub id: WaveInteractionId,
    pub name: String,
    pub source: WaveReceiverId,
    pub target: WaveReceiverId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WavePropagationSpec {
    pub schema: String,
    receivers: BTreeMap<WaveReceiverId, WaveReceiverSpec>,
    interactions: BTreeMap<WaveInteractionId, WaveInteractionSpec>,
}

impl WavePropagationSpec {
    pub fn new(
        receivers: impl IntoIterator<Item = WaveReceiverSpec>,
        interactions: impl IntoIterator<Item = WaveInteractionSpec>,
    ) -> Result<Self, WavePropagationError> {
        let mut indexed_receivers = BTreeMap::new();
        for receiver in receivers {
            if receiver.channels == 0 || receiver.name.is_empty() {
                return Err(WavePropagationError::MalformedSpec);
            }
            if indexed_receivers.insert(receiver.id, receiver).is_some() {
                return Err(WavePropagationError::DuplicateReceiver);
            }
        }
        if indexed_receivers.is_empty() {
            return Err(WavePropagationError::MalformedSpec);
        }
        let mut indexed_interactions = BTreeMap::new();
        for interaction in interactions {
            if interaction.name.is_empty()
                || !indexed_receivers.contains_key(&interaction.source)
                || !indexed_receivers.contains_key(&interaction.target)
            {
                return Err(WavePropagationError::MalformedSpec);
            }
            if indexed_interactions
                .insert(interaction.id, interaction)
                .is_some()
            {
                return Err(WavePropagationError::DuplicateInteraction);
            }
        }
        if indexed_interactions.is_empty() {
            return Err(WavePropagationError::MalformedSpec);
        }
        Ok(Self {
            schema: SPEC_SCHEMA.to_owned(),
            receivers: indexed_receivers,
            interactions: indexed_interactions,
        })
    }

    pub fn receivers(&self) -> &BTreeMap<WaveReceiverId, WaveReceiverSpec> {
        &self.receivers
    }

    pub fn interactions(&self) -> &BTreeMap<WaveInteractionId, WaveInteractionSpec> {
        &self.interactions
    }

    fn validate(&self) -> Result<(), WavePropagationError> {
        if self.schema != SPEC_SCHEMA {
            return Err(WavePropagationError::MalformedSpec);
        }
        let reconstructed = Self::new(
            self.receivers.values().cloned(),
            self.interactions.values().cloned(),
        )?;
        if reconstructed.receivers != self.receivers
            || reconstructed.interactions != self.interactions
        {
            return Err(WavePropagationError::MalformedSpec);
        }
        Ok(())
    }
}

/// One complete section in a receiver-local affine chronology.
///
/// Sensor samples remain testimony.  `origin + ordinal * step` names the
/// receiver chart; it is not promoted into an absolute time axis.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactWaveSection {
    pub schema: String,
    pub receiver: WaveReceiverId,
    pub lineage: WaveLineageId,
    pub origin: Rat,
    pub step: Rat,
    /// Sample-major receiver coordinates.
    pub samples: Vec<Vec<Rat>>,
}

impl ExactWaveSection {
    pub fn new(
        receiver: WaveReceiverId,
        lineage: WaveLineageId,
        origin: Rat,
        step: Rat,
        samples: Vec<Vec<Rat>>,
    ) -> Result<Self, WavePropagationError> {
        if !step.is_positive() || samples.is_empty() {
            return Err(WavePropagationError::MalformedSection);
        }
        let channels = samples[0].len();
        if channels == 0 || samples.iter().any(|sample| sample.len() != channels) {
            return Err(WavePropagationError::MalformedSection);
        }
        Ok(Self {
            schema: SECTION_SCHEMA.to_owned(),
            receiver,
            lineage,
            origin,
            step,
            samples,
        })
    }

    pub fn sample_count(&self) -> usize {
        self.samples.len()
    }

    pub fn channel_count(&self) -> usize {
        self.samples[0].len()
    }

    fn validate(&self, receiver: &WaveReceiverSpec) -> Result<(), WavePropagationError> {
        if self.schema != SECTION_SCHEMA
            || self.receiver != receiver.id
            || !self.step.is_positive()
            || self.samples.is_empty()
            || self.channel_count()
                != usize::try_from(receiver.channels)
                    .map_err(|_| WavePropagationError::CarrierOverflow)?
            || self
                .samples
                .iter()
                .any(|sample| sample.len() != self.channel_count())
        {
            return Err(WavePropagationError::MalformedSection);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveKernelCoordinate {
    pub delay: u32,
    pub source_channel: u32,
    pub target_channel: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCausalKernelFiber {
    pub support: u32,
    pub source_channels: u32,
    pub target_channels: u32,
    pub coordinates: Vec<WaveKernelCoordinate>,
    fiber: ExactAffineVersionFiber,
}

impl ExactCausalKernelFiber {
    fn new(
        support: usize,
        source_channels: usize,
        target_channels: usize,
    ) -> Result<Self, WavePropagationError> {
        if support == 0 || source_channels == 0 || target_channels == 0 {
            return Err(WavePropagationError::MalformedKernelFiber);
        }
        let variable_count = support
            .checked_mul(source_channels)
            .and_then(|count| count.checked_mul(target_channels))
            .ok_or(WavePropagationError::CarrierOverflow)?;
        let mut coordinates = Vec::with_capacity(variable_count);
        for target_channel in 0..target_channels {
            for delay in 0..support {
                for source_channel in 0..source_channels {
                    coordinates.push(WaveKernelCoordinate {
                        delay: u32::try_from(delay)
                            .map_err(|_| WavePropagationError::CarrierOverflow)?,
                        source_channel: u32::try_from(source_channel)
                            .map_err(|_| WavePropagationError::CarrierOverflow)?,
                        target_channel: u32::try_from(target_channel)
                            .map_err(|_| WavePropagationError::CarrierOverflow)?,
                    });
                }
            }
        }
        Ok(Self {
            support: u32::try_from(support).map_err(|_| WavePropagationError::CarrierOverflow)?,
            source_channels: u32::try_from(source_channels)
                .map_err(|_| WavePropagationError::CarrierOverflow)?,
            target_channels: u32::try_from(target_channels)
                .map_err(|_| WavePropagationError::CarrierOverflow)?,
            coordinates,
            fiber: ExactAffineVersionFiber::new(variable_count)?,
        })
    }

    pub fn rank(&self) -> usize {
        self.fiber.rank()
    }

    pub fn affine_dimension(&self) -> usize {
        self.fiber.affine_dimension()
    }

    pub fn is_resolved(&self) -> bool {
        self.affine_dimension() == 0
    }

    pub fn unique_kernel(&self) -> Result<Option<Vec<Rat>>, WavePropagationError> {
        Ok(self.fiber.unique_solution()?)
    }

    fn validate(&self) -> Result<(), WavePropagationError> {
        let reconstructed = Self::new(
            usize::try_from(self.support).map_err(|_| WavePropagationError::CarrierOverflow)?,
            usize::try_from(self.source_channels)
                .map_err(|_| WavePropagationError::CarrierOverflow)?,
            usize::try_from(self.target_channels)
                .map_err(|_| WavePropagationError::CarrierOverflow)?,
        )?;
        if self.coordinates != reconstructed.coordinates
            || self.fiber.variable_count() != self.coordinates.len()
        {
            return Err(WavePropagationError::MalformedKernelFiber);
        }
        self.fiber.validate()?;
        Ok(())
    }

    fn coefficient_form(
        &self,
        source: &ExactWaveSection,
        output_ordinal: usize,
        target_channel: usize,
    ) -> Result<Vec<Rat>, WavePropagationError> {
        let source_channels = usize::try_from(self.source_channels)
            .map_err(|_| WavePropagationError::CarrierOverflow)?;
        let target_channels = usize::try_from(self.target_channels)
            .map_err(|_| WavePropagationError::CarrierOverflow)?;
        let support =
            usize::try_from(self.support).map_err(|_| WavePropagationError::CarrierOverflow)?;
        if source.channel_count() != source_channels || target_channel >= target_channels {
            return Err(WavePropagationError::KernelDimension);
        }
        let mut coefficients = vec![Rat::zero(); self.coordinates.len()];
        for delay in 0..support {
            let Some(source_ordinal) = output_ordinal.checked_sub(delay) else {
                continue;
            };
            if source_ordinal >= source.sample_count() {
                continue;
            }
            for source_channel in 0..source_channels {
                let coordinate =
                    ((target_channel * support + delay) * source_channels) + source_channel;
                coefficients[coordinate] = source.samples[source_ordinal][source_channel].clone();
            }
        }
        Ok(coefficients)
    }

    fn admit_pair(
        &mut self,
        source: &ExactWaveSection,
        target: &ExactWaveSection,
    ) -> Result<WaveKernelAdmissionWork, WavePropagationError> {
        let expected_target = source
            .sample_count()
            .checked_add(
                usize::try_from(self.support).map_err(|_| WavePropagationError::CarrierOverflow)?,
            )
            .and_then(|extent| extent.checked_sub(1))
            .ok_or(WavePropagationError::CarrierOverflow)?;
        if target.sample_count() != expected_target
            || source.channel_count()
                != usize::try_from(self.source_channels)
                    .map_err(|_| WavePropagationError::CarrierOverflow)?
            || target.channel_count()
                != usize::try_from(self.target_channels)
                    .map_err(|_| WavePropagationError::CarrierOverflow)?
        {
            return Err(WavePropagationError::KernelDimension);
        }
        let rank_before = self.rank();
        let mut equations = 0_u64;
        let mut eliminations = 0_u64;
        for output_ordinal in 0..target.sample_count() {
            for target_channel in 0..target.channel_count() {
                let coefficients = self.coefficient_form(source, output_ordinal, target_channel)?;
                let AffineAdmissionWork {
                    exact_row_eliminations,
                    ..
                } = self.fiber.admit(
                    coefficients,
                    target.samples[output_ordinal][target_channel].clone(),
                )?;
                equations = equations
                    .checked_add(1)
                    .ok_or(WavePropagationError::CarrierOverflow)?;
                eliminations = eliminations
                    .checked_add(exact_row_eliminations)
                    .ok_or(WavePropagationError::CarrierOverflow)?;
            }
        }
        self.validate()?;
        Ok(WaveKernelAdmissionWork {
            equations,
            exact_row_eliminations: eliminations,
            rank_before,
            rank_after: self.rank(),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveKernelAdmissionWork {
    pub equations: u64,
    pub exact_row_eliminations: u64,
    pub rank_before: usize,
    pub rank_after: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveTransportMode {
    pub schema: String,
    pub id: WaveModeId,
    pub interaction: WaveInteractionId,
    pub caused_by_event: EventId,
    pub kernel: ExactCausalKernelFiber,
    pub testimony_events: BTreeSet<EventId>,
    pub source_lineages: BTreeSet<WaveLineageId>,
    pub target_lineages: BTreeSet<WaveLineageId>,
}

impl WaveTransportMode {
    fn validate(&self, interaction: WaveInteractionId) -> Result<(), WavePropagationError> {
        if self.schema != MODE_SCHEMA
            || self.interaction != interaction
            || !self.testimony_events.contains(&self.caused_by_event)
        {
            return Err(WavePropagationError::MalformedStanding);
        }
        self.kernel.validate()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WaveModeObstructionKind {
    CausalSupportChanged { established: u32, returned: u32 },
    ReturnedSectionContradictsKernel,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveModeObstruction {
    pub event: EventId,
    pub interaction: WaveInteractionId,
    pub mode: WaveModeId,
    pub source_lineage: WaveLineageId,
    pub target_lineage: WaveLineageId,
    pub kind: WaveModeObstructionKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveModeConditioning {
    pub mode: WaveModeId,
    pub founded: bool,
    pub support: u32,
    pub source_channels: u32,
    pub target_channels: u32,
    pub work: WaveKernelAdmissionWork,
    pub resolved: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveConditioningReceipt {
    pub schema: String,
    pub event: EventId,
    pub interaction: WaveInteractionId,
    pub source_lineage: WaveLineageId,
    pub target_lineage: WaveLineageId,
    pub conditioned_modes: Vec<WaveModeConditioning>,
    pub obstructions: Vec<WaveModeObstruction>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WaveCoordinatePrediction {
    /// A coordinate already fixed by the contemporary response fiber.
    ///
    /// Retaining an all-zero affine residual here would make a resolved
    /// propagation occupy `output extent × kernel extent`.
    Determined(Rat),
    /// A genuinely open affine coordinate, including its unresolved support.
    Open(ExactAffinePrediction),
}

impl WaveCoordinatePrediction {
    pub fn is_determined(&self) -> bool {
        matches!(self, Self::Determined(_))
    }

    pub fn determined_value(&self) -> Option<&Rat> {
        match self {
            Self::Determined(value) => Some(value),
            Self::Open(_) => None,
        }
    }

    pub fn open_fiber(&self) -> Option<&ExactAffinePrediction> {
        match self {
            Self::Determined(_) => None,
            Self::Open(fiber) => Some(fiber),
        }
    }

    fn from_affine(prediction: ExactAffinePrediction) -> Self {
        match prediction.determined_value().cloned() {
            Some(value) => Self::Determined(value),
            None => Self::Open(prediction),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveModePrediction {
    pub mode: WaveModeId,
    pub target: WaveReceiverId,
    pub origin: Rat,
    pub step: Rat,
    pub samples: Vec<Vec<WaveCoordinatePrediction>>,
    pub determined: bool,
}

impl WaveModePrediction {
    pub fn determined_section(
        &self,
        lineage: WaveLineageId,
    ) -> Result<Option<ExactWaveSection>, WavePropagationError> {
        if !self.determined {
            return Ok(None);
        }
        let samples = self
            .samples
            .iter()
            .map(|sample| {
                sample
                    .iter()
                    .map(|coordinate| {
                        coordinate
                            .determined_value()
                            .cloned()
                            .ok_or(WavePropagationError::MalformedStanding)
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Some(ExactWaveSection::new(
            self.target,
            lineage,
            self.origin.clone(),
            self.step.clone(),
            samples,
        )?))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveGenerationReceipt {
    pub schema: String,
    pub event: EventId,
    pub prediction: WavePredictionId,
    pub interaction: WaveInteractionId,
    pub source_lineage: WaveLineageId,
    pub mode_predictions: Vec<WaveModePrediction>,
    pub open_interaction: bool,
    pub execution: CpuExecutionReceipt,
}

/// Logical generation testimony retained in standing.
///
/// Physical worker counts belong only to the emitted receipt; retaining them
/// here would make the world depend on its executor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveGenerationRecord {
    pub schema: String,
    pub event: EventId,
    pub prediction: WavePredictionId,
    pub interaction: WaveInteractionId,
    pub source_lineage: WaveLineageId,
    pub mode_predictions: Vec<WaveModePrediction>,
    pub open_interaction: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveResidualComponent {
    pub first_sample: usize,
    pub last_sample: usize,
    pub residuals: Vec<Vec<Rat>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveModeReturnGrade {
    pub mode: WaveModeId,
    pub unresolved_prediction: bool,
    pub chart_departure: bool,
    pub extent_departure: bool,
    pub exact: bool,
    pub residual_components: Vec<WaveResidualComponent>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveReturnReceipt {
    pub schema: String,
    pub event: EventId,
    pub prediction: WavePredictionId,
    pub returned_lineage: WaveLineageId,
    pub grades: Vec<WaveModeReturnGrade>,
    /// When requested, this receipt is computed before `conditioning`.
    pub conditioning: Option<WaveConditioningReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WavePropagationRadiation {
    Conditioned(WaveConditioningReceipt),
    Generated(WaveGenerationReceipt),
    Returned(WaveReturnReceipt),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveConditioningEvent {
    pub event: EventId,
    pub interaction: WaveInteractionId,
    pub source: ExactWaveSection,
    pub target_return: ExactWaveSection,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveGenerationEvent {
    pub event: EventId,
    pub interaction: WaveInteractionId,
    pub source: ExactWaveSection,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WavePredictionReturnEvent {
    pub event: EventId,
    pub prediction: WavePredictionId,
    pub target_return: ExactWaveSection,
    pub condition_after_grade: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WavePropagationEvent {
    Condition(WaveConditioningEvent),
    Generate(WaveGenerationEvent),
    Return(WavePredictionReturnEvent),
}

impl WavePropagationEvent {
    fn event(&self) -> EventId {
        match self {
            Self::Condition(event) => event.event,
            Self::Generate(event) => event.event,
            Self::Return(event) => event.event,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WavePropagationHistoryEntry {
    Conditioned(WaveConditioningReceipt),
    Generated(WaveGenerationRecord),
    Returned(WaveReturnReceipt),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PendingWavePrediction {
    pub generation: WaveGenerationRecord,
    pub source: ExactWaveSection,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveInteractionStanding {
    pub interaction: WaveInteractionId,
    pub modes: Vec<WaveTransportMode>,
    pub obstructions: Vec<WaveModeObstruction>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WavePropagationStanding {
    pub schema: String,
    pub interactions: BTreeMap<WaveInteractionId, WaveInteractionStanding>,
    pub pending: BTreeMap<WavePredictionId, PendingWavePrediction>,
    pub history: Vec<WavePropagationHistoryEntry>,
    used_events: BTreeSet<EventId>,
    next_mode: u64,
    next_prediction: u64,
}

impl WavePropagationStanding {
    pub fn new(spec: &WavePropagationSpec) -> Self {
        Self {
            schema: STANDING_SCHEMA.to_owned(),
            interactions: spec
                .interactions
                .keys()
                .copied()
                .map(|interaction| {
                    (
                        interaction,
                        WaveInteractionStanding {
                            interaction,
                            modes: Vec::new(),
                            obstructions: Vec::new(),
                        },
                    )
                })
                .collect(),
            pending: BTreeMap::new(),
            history: Vec::new(),
            used_events: BTreeSet::new(),
            next_mode: 1,
            next_prediction: 1,
        }
    }

    pub fn modes(&self, interaction: WaveInteractionId) -> Option<&[WaveTransportMode]> {
        self.interactions
            .get(&interaction)
            .map(|standing| standing.modes.as_slice())
    }

    pub fn history(&self) -> &[WavePropagationHistoryEntry] {
        &self.history
    }
}

#[derive(Clone, Debug)]
pub struct ExactWavePropagationLaw {
    spec: WavePropagationSpec,
    executor: CpuExecutor,
}

impl ExactWavePropagationLaw {
    pub fn new(
        spec: WavePropagationSpec,
        executor: CpuExecutor,
    ) -> Result<Self, WavePropagationError> {
        spec.validate()?;
        Ok(Self { spec, executor })
    }

    pub fn spec(&self) -> &WavePropagationSpec {
        &self.spec
    }

    pub fn initial_standing(&self) -> WavePropagationStanding {
        WavePropagationStanding::new(&self.spec)
    }

    fn validate_standing(
        &self,
        standing: &WavePropagationStanding,
    ) -> Result<(), WavePropagationError> {
        if standing.schema != STANDING_SCHEMA
            || standing
                .interactions
                .keys()
                .copied()
                .collect::<BTreeSet<_>>()
                != self
                    .spec
                    .interactions
                    .keys()
                    .copied()
                    .collect::<BTreeSet<_>>()
        {
            return Err(WavePropagationError::MalformedStanding);
        }
        let mut modes = BTreeSet::new();
        for (interaction, body) in &standing.interactions {
            if body.interaction != *interaction {
                return Err(WavePropagationError::MalformedStanding);
            }
            for mode in &body.modes {
                mode.validate(*interaction)?;
                if !modes.insert(mode.id) {
                    return Err(WavePropagationError::MalformedStanding);
                }
            }
        }
        for (prediction, pending) in &standing.pending {
            if pending.generation.prediction != *prediction
                || !self
                    .spec
                    .interactions
                    .contains_key(&pending.generation.interaction)
            {
                return Err(WavePropagationError::MalformedStanding);
            }
        }
        Ok(())
    }

    fn validate_pair(
        &self,
        interaction: WaveInteractionId,
        source: &ExactWaveSection,
        target: &ExactWaveSection,
    ) -> Result<&WaveInteractionSpec, WavePropagationError> {
        let interaction = self
            .spec
            .interactions
            .get(&interaction)
            .ok_or(WavePropagationError::UnknownInteraction)?;
        let source_receiver = &self.spec.receivers[&interaction.source];
        let target_receiver = &self.spec.receivers[&interaction.target];
        source.validate(source_receiver)?;
        target.validate(target_receiver)?;
        if source.origin != target.origin || source.step != target.step {
            return Err(WavePropagationError::ReceiverChartMismatch);
        }
        if target.sample_count() < source.sample_count() {
            return Err(WavePropagationError::NoncausalReturnedExtent);
        }
        Ok(interaction)
    }

    fn condition(
        &self,
        standing: &mut WavePropagationStanding,
        event: &WaveConditioningEvent,
    ) -> Result<WaveConditioningReceipt, WavePropagationError> {
        let interaction =
            self.validate_pair(event.interaction, &event.source, &event.target_return)?;
        let returned_support = event
            .target_return
            .sample_count()
            .checked_sub(event.source.sample_count())
            .and_then(|difference| difference.checked_add(1))
            .ok_or(WavePropagationError::CarrierOverflow)?;
        let source_channels = event.source.channel_count();
        let target_channels = event.target_return.channel_count();

        let body = standing
            .interactions
            .get_mut(&interaction.id)
            .ok_or(WavePropagationError::UnknownInteraction)?;
        let mut conditioned_modes = Vec::new();
        let mut obstructions = Vec::new();

        for mode in &mut body.modes {
            if usize::try_from(mode.kernel.support)
                .map_err(|_| WavePropagationError::CarrierOverflow)?
                != returned_support
            {
                obstructions.push(WaveModeObstruction {
                    event: event.event,
                    interaction: interaction.id,
                    mode: mode.id,
                    source_lineage: event.source.lineage,
                    target_lineage: event.target_return.lineage,
                    kind: WaveModeObstructionKind::CausalSupportChanged {
                        established: mode.kernel.support,
                        returned: u32::try_from(returned_support)
                            .map_err(|_| WavePropagationError::CarrierOverflow)?,
                    },
                });
                continue;
            }
            let mut candidate = mode.kernel.clone();
            match candidate.admit_pair(&event.source, &event.target_return) {
                Ok(work) => {
                    mode.kernel = candidate;
                    mode.testimony_events.insert(event.event);
                    mode.source_lineages.insert(event.source.lineage);
                    mode.target_lineages.insert(event.target_return.lineage);
                    conditioned_modes.push(WaveModeConditioning {
                        mode: mode.id,
                        founded: false,
                        support: mode.kernel.support,
                        source_channels: mode.kernel.source_channels,
                        target_channels: mode.kernel.target_channels,
                        work,
                        resolved: mode.kernel.is_resolved(),
                    });
                }
                Err(WavePropagationError::AffineFiber(
                    InverseTransportError::AffineFiberObstructed,
                )) => {
                    obstructions.push(WaveModeObstruction {
                        event: event.event,
                        interaction: interaction.id,
                        mode: mode.id,
                        source_lineage: event.source.lineage,
                        target_lineage: event.target_return.lineage,
                        kind: WaveModeObstructionKind::ReturnedSectionContradictsKernel,
                    });
                }
                Err(error) => return Err(error),
            }
        }

        if conditioned_modes.is_empty() {
            let mut kernel =
                ExactCausalKernelFiber::new(returned_support, source_channels, target_channels)?;
            let work = kernel.admit_pair(&event.source, &event.target_return)?;
            let id = WaveModeId(standing.next_mode);
            standing.next_mode = standing
                .next_mode
                .checked_add(1)
                .ok_or(WavePropagationError::CarrierOverflow)?;
            let mode = WaveTransportMode {
                schema: MODE_SCHEMA.to_owned(),
                id,
                interaction: interaction.id,
                caused_by_event: event.event,
                kernel,
                testimony_events: BTreeSet::from([event.event]),
                source_lineages: BTreeSet::from([event.source.lineage]),
                target_lineages: BTreeSet::from([event.target_return.lineage]),
            };
            conditioned_modes.push(WaveModeConditioning {
                mode: id,
                founded: true,
                support: mode.kernel.support,
                source_channels: mode.kernel.source_channels,
                target_channels: mode.kernel.target_channels,
                work,
                resolved: mode.kernel.is_resolved(),
            });
            body.modes.push(mode);
            body.modes.sort_by_key(|mode| mode.id);
        }

        body.obstructions.extend(obstructions.iter().cloned());
        Ok(WaveConditioningReceipt {
            schema: CONDITION_SCHEMA.to_owned(),
            event: event.event,
            interaction: interaction.id,
            source_lineage: event.source.lineage,
            target_lineage: event.target_return.lineage,
            conditioned_modes,
            obstructions,
        })
    }

    fn generate(
        &self,
        standing: &mut WavePropagationStanding,
        event: &WaveGenerationEvent,
    ) -> Result<WaveGenerationReceipt, WavePropagationError> {
        let interaction = self
            .spec
            .interactions
            .get(&event.interaction)
            .ok_or(WavePropagationError::UnknownInteraction)?;
        event
            .source
            .validate(&self.spec.receivers[&interaction.source])?;
        let modes = standing
            .interactions
            .get(&event.interaction)
            .ok_or(WavePropagationError::UnknownInteraction)?
            .modes
            .clone();

        let target = interaction.target;
        let target_channels = usize::try_from(self.spec.receivers[&target].channels)
            .map_err(|_| WavePropagationError::CarrierOverflow)?;
        let mode_inputs = modes
            .iter()
            .map(|mode| {
                let output_samples = event
                    .source
                    .sample_count()
                    .checked_add(
                        usize::try_from(mode.kernel.support)
                            .map_err(|_| WavePropagationError::CarrierOverflow)?,
                    )
                    .and_then(|extent| extent.checked_sub(1))
                    .ok_or(WavePropagationError::CarrierOverflow)?;
                Ok::<_, WavePropagationError>((mode.clone(), output_samples))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let (mode_predictions, execution) = self
            .executor
            .execute_indexed(&mode_inputs, |_index, (mode, output_samples)| {
                let coordinates = (0..*output_samples)
                    .flat_map(|output_ordinal| {
                        (0..target_channels)
                            .map(move |target_channel| (output_ordinal, target_channel))
                    })
                    .collect::<Vec<_>>();
                let predictions = coordinates
                    .iter()
                    .map(|(output_ordinal, target_channel)| {
                        let coefficients = mode.kernel.coefficient_form(
                            &event.source,
                            *output_ordinal,
                            *target_channel,
                        )?;
                        Ok::<_, WavePropagationError>(
                            mode.kernel.fiber.predict(&coefficients, Rat::zero())?,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let predictions = predictions
                    .into_iter()
                    .map(WaveCoordinatePrediction::from_affine)
                    .collect::<Vec<_>>();
                let determined = predictions
                    .iter()
                    .all(WaveCoordinatePrediction::is_determined);
                let mut samples = Vec::with_capacity(*output_samples);
                for chunk in predictions.chunks(target_channels) {
                    samples.push(chunk.to_vec());
                }
                Ok(WaveModePrediction {
                    mode: mode.id,
                    target,
                    origin: event.source.origin.clone(),
                    step: event.source.step.clone(),
                    samples,
                    determined,
                })
            })
            .map_err(map_cpu_error)?;

        let prediction = WavePredictionId(standing.next_prediction);
        standing.next_prediction = standing
            .next_prediction
            .checked_add(1)
            .ok_or(WavePropagationError::CarrierOverflow)?;
        let receipt = WaveGenerationReceipt {
            schema: GENERATION_SCHEMA.to_owned(),
            event: event.event,
            prediction,
            interaction: event.interaction,
            source_lineage: event.source.lineage,
            open_interaction: mode_predictions.is_empty(),
            mode_predictions,
            execution,
        };
        let record = WaveGenerationRecord {
            schema: receipt.schema.clone(),
            event: receipt.event,
            prediction: receipt.prediction,
            interaction: receipt.interaction,
            source_lineage: receipt.source_lineage,
            mode_predictions: receipt.mode_predictions.clone(),
            open_interaction: receipt.open_interaction,
        };
        standing.pending.insert(
            prediction,
            PendingWavePrediction {
                generation: record,
                source: event.source.clone(),
            },
        );
        Ok(receipt)
    }

    fn grade_return(
        &self,
        standing: &mut WavePropagationStanding,
        event: &WavePredictionReturnEvent,
    ) -> Result<WaveReturnReceipt, WavePropagationError> {
        let pending = standing
            .pending
            .remove(&event.prediction)
            .ok_or(WavePropagationError::UnknownPrediction)?;
        let interaction = self
            .spec
            .interactions
            .get(&pending.generation.interaction)
            .ok_or(WavePropagationError::UnknownInteraction)?;
        event
            .target_return
            .validate(&self.spec.receivers[&interaction.target])?;

        let mut grades = Vec::new();
        for prediction in &pending.generation.mode_predictions {
            let chart_departure = prediction.origin != event.target_return.origin
                || prediction.step != event.target_return.step;
            let extent_departure = prediction.samples.len() != event.target_return.sample_count();
            let unresolved_prediction = !prediction.determined;
            let residual_components =
                if chart_departure || extent_departure || unresolved_prediction {
                    Vec::new()
                } else {
                    residual_components(prediction, &event.target_return)?
                };
            grades.push(WaveModeReturnGrade {
                mode: prediction.mode,
                unresolved_prediction,
                chart_departure,
                extent_departure,
                exact: !unresolved_prediction
                    && !chart_departure
                    && !extent_departure
                    && residual_components.is_empty(),
                residual_components,
            });
        }

        // The complete grade above is fixed before the returned target may
        // restrict or grow the contemporary interaction modes.
        let conditioning = if event.condition_after_grade {
            Some(self.condition(
                standing,
                &WaveConditioningEvent {
                    event: event.event,
                    interaction: pending.generation.interaction,
                    source: pending.source,
                    target_return: event.target_return.clone(),
                },
            )?)
        } else {
            None
        };
        Ok(WaveReturnReceipt {
            schema: RETURN_SCHEMA.to_owned(),
            event: event.event,
            prediction: event.prediction,
            returned_lineage: event.target_return.lineage,
            grades,
            conditioning,
        })
    }

    fn logical_resources(radiation: &WavePropagationRadiation) -> LogicalResourceReceipt {
        let (work, span, width, law) = match radiation {
            WavePropagationRadiation::Conditioned(receipt) => {
                let work = receipt
                    .conditioned_modes
                    .iter()
                    .map(|mode| mode.work.equations)
                    .sum::<u64>();
                (
                    work,
                    u64::from(!receipt.conditioned_modes.is_empty()),
                    receipt.conditioned_modes.len() as u64,
                    "wave-condition",
                )
            }
            WavePropagationRadiation::Generated(receipt) => {
                let span = receipt
                    .mode_predictions
                    .iter()
                    .map(|prediction| prediction.samples.len())
                    .max()
                    .unwrap_or(0);
                let work = receipt
                    .mode_predictions
                    .iter()
                    .map(|prediction| prediction.samples.iter().map(Vec::len).sum::<usize>())
                    .sum::<usize>();
                let width = receipt
                    .mode_predictions
                    .iter()
                    .map(|prediction| prediction.samples.first().map_or(0, Vec::len))
                    .sum::<usize>();
                (work as u64, span as u64, width as u64, "wave-generate")
            }
            WavePropagationRadiation::Returned(receipt) => {
                let work = receipt
                    .grades
                    .iter()
                    .map(|grade| {
                        grade
                            .residual_components
                            .iter()
                            .map(|component| component.residuals.len())
                            .sum::<usize>()
                    })
                    .sum::<usize>();
                (
                    work as u64,
                    u64::from(!receipt.grades.is_empty()),
                    receipt.grades.len() as u64,
                    "wave-return",
                )
            }
        };
        LogicalResourceReceipt {
            schema: "holonic-engine.logical-resource-receipt.v1".to_owned(),
            work: BigUint::from(work),
            causal_span: BigUint::from(span),
            exposed_parallel_width: BigUint::from(width),
            events_by_law: BTreeMap::from([(law.to_owned(), BigUint::from(1_u8))]),
        }
    }
}

impl ExactEventLaw for ExactWavePropagationLaw {
    type Standing = WavePropagationStanding;
    type Event = WavePropagationEvent;
    type Radiation = WavePropagationRadiation;
    type Error = WavePropagationError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        self.validate_standing(standing_before)?;
        if standing_before.used_events.contains(&event.event()) {
            return Err(WavePropagationError::RepeatedEvent);
        }
        let mut standing_after = standing_before.clone();
        standing_after.used_events.insert(event.event());
        let radiation = match event {
            WavePropagationEvent::Condition(event) => {
                let receipt = self.condition(&mut standing_after, event)?;
                WavePropagationRadiation::Conditioned(receipt)
            }
            WavePropagationEvent::Generate(event) => {
                let receipt = self.generate(&mut standing_after, event)?;
                WavePropagationRadiation::Generated(receipt)
            }
            WavePropagationEvent::Return(event) => {
                let receipt = self.grade_return(&mut standing_after, event)?;
                WavePropagationRadiation::Returned(receipt)
            }
        };
        match &radiation {
            WavePropagationRadiation::Conditioned(receipt) => standing_after
                .history
                .push(WavePropagationHistoryEntry::Conditioned(receipt.clone())),
            WavePropagationRadiation::Generated(receipt) => {
                standing_after
                    .history
                    .push(WavePropagationHistoryEntry::Generated(
                        WaveGenerationRecord {
                            schema: receipt.schema.clone(),
                            event: receipt.event,
                            prediction: receipt.prediction,
                            interaction: receipt.interaction,
                            source_lineage: receipt.source_lineage,
                            mode_predictions: receipt.mode_predictions.clone(),
                            open_interaction: receipt.open_interaction,
                        },
                    ))
            }
            WavePropagationRadiation::Returned(receipt) => standing_after
                .history
                .push(WavePropagationHistoryEntry::Returned(receipt.clone())),
        }
        self.validate_standing(&standing_after)?;
        let logical_resources = Self::logical_resources(&radiation);
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![radiation],
            logical_resources: Some(logical_resources),
            physical_resources: None,
        })
    }
}

fn residual_components(
    prediction: &WaveModePrediction,
    returned: &ExactWaveSection,
) -> Result<Vec<WaveResidualComponent>, WavePropagationError> {
    let mut residuals = Vec::with_capacity(returned.sample_count());
    for (predicted, received) in prediction.samples.iter().zip(&returned.samples) {
        if predicted.len() != received.len() {
            return Err(WavePropagationError::MalformedStanding);
        }
        residuals.push(
            predicted
                .iter()
                .zip(received)
                .map(|(predicted, received)| {
                    let predicted = predicted
                        .determined_value()
                        .ok_or(WavePropagationError::MalformedStanding)?;
                    Ok(received - predicted)
                })
                .collect::<Result<Vec<_>, WavePropagationError>>()?,
        );
    }
    let mut components = Vec::new();
    let mut start = None;
    for (ordinal, residual) in residuals.iter().enumerate() {
        let departed = residual.iter().any(|value| !value.is_zero());
        match (start, departed) {
            (None, true) => start = Some(ordinal),
            (Some(first), false) => {
                components.push(WaveResidualComponent {
                    first_sample: first,
                    last_sample: ordinal - 1,
                    residuals: residuals[first..ordinal].to_vec(),
                });
                start = None;
            }
            _ => {}
        }
    }
    if let Some(first) = start {
        components.push(WaveResidualComponent {
            first_sample: first,
            last_sample: residuals.len() - 1,
            residuals: residuals[first..].to_vec(),
        });
    }
    Ok(components)
}

fn map_cpu_error(error: CpuExecutionError<WavePropagationError>) -> WavePropagationError {
    match error {
        CpuExecutionError::Operation(error) => error,
        CpuExecutionError::WorkerPanicked => WavePropagationError::WorkerPanicked,
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum WavePropagationError {
    #[error("the wave propagation specification is malformed")]
    MalformedSpec,
    #[error("a receiver was declared twice")]
    DuplicateReceiver,
    #[error("an interaction was declared twice")]
    DuplicateInteraction,
    #[error("an event occurrence was supplied twice")]
    RepeatedEvent,
    #[error("the exact wave section is malformed")]
    MalformedSection,
    #[error("the wave propagation standing is malformed")]
    MalformedStanding,
    #[error("the exact causal kernel fiber is malformed")]
    MalformedKernelFiber,
    #[error("the interaction is absent")]
    UnknownInteraction,
    #[error("the prediction is absent or has already returned")]
    UnknownPrediction,
    #[error("source and target sections do not share one receiver-local chart")]
    ReceiverChartMismatch,
    #[error("a causal return cannot be shorter than its source section")]
    NoncausalReturnedExtent,
    #[error("the causal kernel and receiver section dimensions disagree")]
    KernelDimension,
    #[error("one exact physical worker panicked")]
    WorkerPanicked,
    #[error("a finite carrier extent overflowed")]
    CarrierOverflow,
    #[error(transparent)]
    AffineFiber(#[from] InverseTransportError),
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use num_bigint::BigInt;

    use super::*;
    use crate::CausalWorld;

    fn rat(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }

    fn mono(receiver: WaveReceiverId, lineage: u64, values: &[i64]) -> ExactWaveSection {
        ExactWaveSection::new(
            receiver,
            WaveLineageId(lineage),
            Rat::zero(),
            rat(1),
            values.iter().map(|value| vec![rat(*value)]).collect(),
        )
        .unwrap()
    }

    fn convolve(source: &[i64], kernel: &[i64]) -> Vec<i64> {
        let mut output = vec![0_i64; source.len() + kernel.len() - 1];
        for (source_ordinal, source) in source.iter().enumerate() {
            for (delay, kernel) in kernel.iter().enumerate() {
                output[source_ordinal + delay] += source * kernel;
            }
        }
        output
    }

    fn law(executor: CpuExecutor) -> ExactWavePropagationLaw {
        ExactWavePropagationLaw::new(
            WavePropagationSpec::new(
                [
                    WaveReceiverSpec {
                        id: WaveReceiverId(1),
                        name: "source".to_owned(),
                        channels: 1,
                    },
                    WaveReceiverSpec {
                        id: WaveReceiverId(2),
                        name: "target".to_owned(),
                        channels: 1,
                    },
                ],
                [WaveInteractionSpec {
                    id: WaveInteractionId(1),
                    name: "causal response".to_owned(),
                    source: WaveReceiverId(1),
                    target: WaveReceiverId(2),
                }],
            )
            .unwrap(),
            executor,
        )
        .unwrap()
    }

    #[test]
    fn returned_pair_resolves_a_kernel_and_generates_before_return() {
        let law = law(CpuExecutor::serial());
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        let source = [1, 2, 3];
        let target = convolve(&source, &[2, -1]);
        world
            .receive(&WavePropagationEvent::Condition(WaveConditioningEvent {
                event: EventId(1),
                interaction: WaveInteractionId(1),
                source: mono(WaveReceiverId(1), 1, &source),
                target_return: mono(WaveReceiverId(2), 2, &target),
            }))
            .unwrap();
        let mode = &world.standing().modes(WaveInteractionId(1)).unwrap()[0];
        assert_eq!(
            mode.kernel.unique_kernel().unwrap(),
            Some(vec![rat(2), rat(-1)])
        );

        let held = [3, 1];
        let generation = world
            .receive(&WavePropagationEvent::Generate(WaveGenerationEvent {
                event: EventId(2),
                interaction: WaveInteractionId(1),
                source: mono(WaveReceiverId(1), 3, &held),
            }))
            .unwrap();
        let WavePropagationRadiation::Generated(generation) = &generation.radiation[0] else {
            panic!("generation receipt");
        };
        let predicted = generation.mode_predictions[0]
            .determined_section(WaveLineageId(4))
            .unwrap()
            .unwrap();
        assert_eq!(
            predicted.samples,
            convolve(&held, &[2, -1])
                .into_iter()
                .map(|value| vec![rat(value)])
                .collect::<Vec<_>>()
        );

        let returned = world
            .receive(&WavePropagationEvent::Return(WavePredictionReturnEvent {
                event: EventId(3),
                prediction: generation.prediction,
                target_return: predicted,
                condition_after_grade: false,
            }))
            .unwrap();
        let WavePropagationRadiation::Returned(returned) = &returned.radiation[0] else {
            panic!("return receipt");
        };
        assert!(returned.grades[0].exact);
        assert!(returned.grades[0].residual_components.is_empty());
    }

    #[test]
    fn an_incompatible_return_founds_a_plural_mode() {
        let law = law(CpuExecutor::serial());
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        let source = [1, 2, 3];
        for (event, kernel) in [(1, vec![2, -1]), (2, vec![1, 3])] {
            world
                .receive(&WavePropagationEvent::Condition(WaveConditioningEvent {
                    event: EventId(event),
                    interaction: WaveInteractionId(1),
                    source: mono(WaveReceiverId(1), event, &source),
                    target_return: mono(WaveReceiverId(2), event + 10, &convolve(&source, &kernel)),
                }))
                .unwrap();
        }
        let modes = world.standing().modes(WaveInteractionId(1)).unwrap();
        assert_eq!(modes.len(), 2);

        let held = [2, 1];
        let generated = world
            .receive(&WavePropagationEvent::Generate(WaveGenerationEvent {
                event: EventId(3),
                interaction: WaveInteractionId(1),
                source: mono(WaveReceiverId(1), 30, &held),
            }))
            .unwrap();
        let WavePropagationRadiation::Generated(generated) = &generated.radiation[0] else {
            panic!("generation receipt");
        };
        assert_eq!(generated.mode_predictions.len(), 2);
        let returned = mono(WaveReceiverId(2), 31, &convolve(&held, &[1, 3]));
        let grade = world
            .receive(&WavePropagationEvent::Return(WavePredictionReturnEvent {
                event: EventId(4),
                prediction: generated.prediction,
                target_return: returned,
                condition_after_grade: false,
            }))
            .unwrap();
        let WavePropagationRadiation::Returned(grade) = &grade.radiation[0] else {
            panic!("return receipt");
        };
        assert_eq!(grade.grades.iter().filter(|grade| grade.exact).count(), 1);
        assert_eq!(
            grade
                .grades
                .iter()
                .filter(|grade| !grade.residual_components.is_empty())
                .count(),
            1
        );
    }

    #[test]
    fn unresolved_kernel_emits_an_open_prediction() {
        let law = law(CpuExecutor::serial());
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        world
            .receive(&WavePropagationEvent::Condition(WaveConditioningEvent {
                event: EventId(1),
                interaction: WaveInteractionId(1),
                source: mono(WaveReceiverId(1), 1, &[0, 0]),
                target_return: mono(WaveReceiverId(2), 2, &[0, 0, 0]),
            }))
            .unwrap();
        let generated = world
            .receive(&WavePropagationEvent::Generate(WaveGenerationEvent {
                event: EventId(2),
                interaction: WaveInteractionId(1),
                source: mono(WaveReceiverId(1), 3, &[1, 2]),
            }))
            .unwrap();
        let WavePropagationRadiation::Generated(generated) = &generated.radiation[0] else {
            panic!("generation receipt");
        };
        assert!(!generated.mode_predictions[0].determined);
        assert!(
            generated.mode_predictions[0]
                .samples
                .iter()
                .flatten()
                .any(|coordinate| coordinate.open_fiber().is_some())
        );
    }

    #[test]
    fn serial_and_multicore_generation_are_identical() {
        fn run(executor: CpuExecutor) -> WavePropagationStanding {
            let law = law(executor);
            let mut world = CausalWorld::new(law.clone(), law.initial_standing());
            let source = [1, 2, 3];
            for (event, kernel) in [(1, vec![2, -1]), (2, vec![1, 3])] {
                world
                    .receive(&WavePropagationEvent::Condition(WaveConditioningEvent {
                        event: EventId(event),
                        interaction: WaveInteractionId(1),
                        source: mono(WaveReceiverId(1), event, &source),
                        target_return: mono(
                            WaveReceiverId(2),
                            event + 10,
                            &convolve(&source, &kernel),
                        ),
                    }))
                    .unwrap();
            }
            world
                .receive(&WavePropagationEvent::Generate(WaveGenerationEvent {
                    event: EventId(3),
                    interaction: WaveInteractionId(1),
                    source: mono(WaveReceiverId(1), 30, &[4, 1, -2]),
                }))
                .unwrap();
            world.standing().clone()
        }
        let serial = run(CpuExecutor::serial());
        let parallel = run(CpuExecutor::multicore(NonZeroUsize::new(4).unwrap()));
        assert_eq!(serial, parallel);
    }

    #[test]
    fn exact_standing_rests_and_remounts() {
        let law = law(CpuExecutor::serial());
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        let source = [1, 2, 3];
        world
            .receive(&WavePropagationEvent::Condition(WaveConditioningEvent {
                event: EventId(1),
                interaction: WaveInteractionId(1),
                source: mono(WaveReceiverId(1), 1, &source),
                target_return: mono(WaveReceiverId(2), 2, &convolve(&source, &[2, -1])),
            }))
            .unwrap();
        let encoded = ron::to_string(world.standing()).unwrap();
        let remounted: WavePropagationStanding = ron::from_str(&encoded).unwrap();
        assert_eq!(&remounted, world.standing());
        law.validate_standing(&remounted).unwrap();
    }

    #[test]
    fn refused_chart_change_is_atomic() {
        let law = law(CpuExecutor::serial());
        let standing = law.initial_standing();
        let mut target = mono(WaveReceiverId(2), 2, &[1, 2, 3]);
        target.step = rat(2);
        assert_eq!(
            law.enact(
                &standing,
                &WavePropagationEvent::Condition(WaveConditioningEvent {
                    event: EventId(1),
                    interaction: WaveInteractionId(1),
                    source: mono(WaveReceiverId(1), 1, &[1, 2]),
                    target_return: target,
                }),
            )
            .unwrap_err(),
            WavePropagationError::ReceiverChartMismatch
        );
        assert!(standing.history.is_empty());
    }
}
