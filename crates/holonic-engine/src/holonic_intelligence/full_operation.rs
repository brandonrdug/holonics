//! One mathematical operation advances the complete resident operator ecology.
//!
//! This owner begins at the first operation of the full HNA1 graph.  It consumes ordinary row
//! addresses at the occurrence port, gathers those coefficient rows without leaving the device,
//! enacts the graph's laws, and returns its emission, trace, and move-owned successor ecology
//! together.  No exterior verdict, stored activation, candidate, or commit intervenes.
//!
//! Under the contract of 2026-08-18 the cycle runs as segments (`operative_segment.rs`): each
//! segment is one passage bound whole, launched once, and read once through its census; the
//! successor projection is a midpoint seal fused into the graph; no section crosses to the host
//! but the terminal face at the declared receiver.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;
use thiserror::Error;

use crate::resident_section::{
    Positions, ResidentGrain, ResidentRefusal, ResidentSection, TransferCensus,
};

use super::{
    NativeCarrierOrdinal, NativeFullOperatorEcology, NativeMorphologyDeposit,
    NativeOperationPrimitive, NativeOperatorNode, NativeOperatorResidence,
    NativeOperatorResidenceError, NativeReturnAperture, NativeTensorOrdinal,
    operative_backward::{NativeAdjointReturnTrace, ReturnDeed},
    operative_passage_return::{PassageCultivation, NativePassageReturn},
    operative_intervention::DissectionStanding,
    operative_return::{OverlayAtom, ReturnMaterial, continuation_next_occurrences, enact_return},
    operative_scalars::projected_scale,
    operative_segment::{SegmentSite, SegmentWithdrawal, enact_segment, segments},
    operative_terminal::{TiledCarrier, stitch_intervals},
};

pub const NATIVE_FULL_OPERATION_STEP_SCHEMA: &str = "holonic-engine.native-full-operation-step.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeFullOperationOccurrence {
    pub ordinal: u64,
    pub row_addresses: Vec<u32>,
}

/// An emission: the terminal face carries its intervals, read once at the declared receiver; an
/// intermediate operation's emission names its carrier and carries no words, because no section
/// crosses to the host between two operations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFullOperationEmission {
    pub generation: u64,
    pub operation: u32,
    pub carrier: NativeCarrierOrdinal,
    pub rows: usize,
    pub width: usize,
    pub grain: u32,
    pub intervals: Vec<(i64, i64)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFullOperationTrace {
    pub schema: String,
    pub predecessor_generation: u64,
    pub successor_generation: u64,
    pub occurrence: u64,
    pub row_addresses: Vec<u32>,
    pub operation: NativeOperatorNode,
    pub successor_projection: NativeSuccessorProjection,
    pub morphology_transition: NativeMorphologyTransition,
    /// The total rank of the factorized overlay the ecology carries at this operation.
    pub morphology_overlay_rank: usize,
    /// The a-priori octave bound the operation was admitted under.
    pub admitted_octaves: u32,
    /// The measured octave bound of the successor carrier, from the segment's census.
    pub successor_bound_octaves: u32,
    pub resident_coefficient_octets: u64,
    pub census_before: TransferCensus,
    pub census_after: TransferCensus,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeMorphologyTransition {
    Unchanged,
    Changed {
        operation: u32,
        deposit: NativeMorphologyDeposit,
        adjoint: NativeAdjointReturnTrace,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeSuccessorProjection {
    Exact,
    Midpoint {
        nonpoint_coordinates: usize,
        widest_interval: u64,
    },
}

pub(super) struct ContemporaryCarrier<'chart> {
    pub(super) section: ResidentSection<'chart>,
    pub(super) bound_octaves: u32,
}

/// One operation's step inside a run: what the trace records of it.
pub(super) struct RunStep {
    pub(super) operation: NativeOperatorNode,
    pub(super) admitted_octaves: u32,
    pub(super) bound_octaves: u32,
    pub(super) projection: NativeSuccessorProjection,
    pub(super) census_before: TransferCensus,
    pub(super) census_after: TransferCensus,
}

/// The move-owned contemporary ecology.  The coefficient morphology is one borrowed resident
/// standing; every produced carrier and the chronology belong to this successor line alone.
pub struct NativeFullOperatorSession<'residence, 'chart> {
    pub(super) ecology: &'residence NativeFullOperatorEcology,
    pub(super) residence: &'residence mut NativeOperatorResidence<'chart>,
    pub(super) carriers: BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    pub(super) operation_at: usize,
    pub(super) generation: u64,
    pub(super) chronology: Vec<u64>,
    pub(super) grain: ResidentGrain,
    pub(super) positions: Option<Positions<'chart>>,
    row_population: Option<usize>,
    pub(super) cycle_complete: bool,
    /// Carriers produced in one layer (or the prologue) and consumed in another: retained through
    /// the cycle as the checkpoints the return replays each layer from.
    pub(super) cross_layer: BTreeSet<NativeCarrierOrdinal>,
    pub(super) checkpoints: BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    /// The complete emitted face of the last cycle, retained by the successor until the next
    /// occurrence enters.
    pub(super) terminal_carrier: Option<TiledCarrier<'chart>>,
    /// The reacted carrier of the tied boundary (`tanh`) and the carrier presented to the tied
    /// contraction, retained for the return.
    pub(super) terminal_reacted: Option<TiledCarrier<'chart>>,
    /// The tied contraction's own output at the receiver row, read to the host under dissection.
    pub(super) terminal_contracted: Option<Vec<(i64, i64)>>,
    pub(super) terminal_presented: Option<ContemporaryCarrier<'chart>>,
    /// The row addresses of the last cycle: the line the emitted face continued.
    pub(super) previous_context: Option<Vec<u32>>,
    /// The factorized overlay atoms deposited on each cross-section, keyed by its coefficient
    /// population, in deposit order.
    pub(super) overlay: BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'chart>>>,
    /// The declared return apertures; `None` enacts no return.
    pub(super) aperture: Option<NativeReturnAperture>,
    pub(super) passage_cultivation: Option<PassageCultivation<'chart>>,
    /// The dissection standing: the excitation's supports and face, when founded for dissection.
    pub(super) dissection: Option<DissectionStanding>,
    /// Whether the terminal's successor projection is fused; a receiver that declares the
    /// propagated remainder reads the face's enclosures instead.
    pub(super) terminal_seal: bool,
}

pub struct NativeFullOperationStep<'residence, 'chart> {
    pub emission: NativeFullOperationEmission,
    pub trace: NativeFullOperationTrace,
    pub successor: NativeFullOperatorSession<'residence, 'chart>,
}

pub struct NativeFullTerminalBranch<'residence, 'chart> {
    pub emissions: Vec<NativeFullOperationEmission>,
    pub traces: Vec<NativeFullOperationTrace>,
    pub successor: NativeFullOperatorSession<'residence, 'chart>,
}

pub struct NativeFullCycle<'residence, 'chart> {
    pub final_emission: NativeFullOperationEmission,
    pub traces: Vec<NativeFullOperationTrace>,
    pub passage_returns: Vec<NativePassageReturn>,
    pub successor: NativeFullOperatorSession<'residence, 'chart>,
}

impl<'residence, 'chart> NativeFullOperatorSession<'residence, 'chart> {
    pub fn found(
        ecology: &'residence NativeFullOperatorEcology,
        residence: &'residence mut NativeOperatorResidence<'chart>,
    ) -> Result<Self, NativeFullOperationError> {
        Self::found_with(ecology, residence, None)
    }

    /// Found the ecology with the declared return apertures: a continuing occurrence then meets
    /// the retained emission and deposits on the tied cross-section.
    pub fn found_with_return(
        ecology: &'residence NativeFullOperatorEcology,
        residence: &'residence mut NativeOperatorResidence<'chart>,
        aperture: NativeReturnAperture,
    ) -> Result<Self, NativeFullOperationError> {
        Self::found_with(ecology, residence, Some(aperture))
    }

    fn found_with(
        ecology: &'residence NativeFullOperatorEcology,
        residence: &'residence mut NativeOperatorResidence<'chart>,
        aperture: Option<NativeReturnAperture>,
    ) -> Result<Self, NativeFullOperationError> {
        ecology.validate()?;
        let mut producer: BTreeMap<NativeCarrierOrdinal, Option<u16>> = BTreeMap::new();
        for operation in &ecology.operations {
            producer.insert(operation.output, operation.layer);
        }
        let mut cross_layer = BTreeSet::new();
        for operation in &ecology.operations {
            for input in &operation.inputs {
                if producer.get(input).copied().flatten() != operation.layer
                    || producer.get(input).is_some_and(|layer| layer.is_none())
                {
                    cross_layer.insert(*input);
                }
            }
        }
        let mut grain = 0u32;
        for operation in &ecology.operations {
            if let NativeOperationPrimitive::Lookup { scale } = &operation.primitive {
                let coefficient = *operation
                    .coefficients
                    .first()
                    .ok_or(NativeFullOperationError::Operation)?;
                let scale = projected_scale(scale)?;
                let frame = residence.population_frame(coefficient)?.exponent;
                let exact = frame
                    .checked_add(scale.exponent)
                    .ok_or(NativeFullOperationError::Grain)?;
                grain =
                    grain.max(u32::try_from(-exact).map_err(|_| NativeFullOperationError::Grain)?);
            }
        }
        Ok(Self {
            ecology,
            residence,
            carriers: BTreeMap::new(),
            operation_at: 0,
            generation: 0,
            chronology: Vec::new(),
            grain: ResidentGrain(grain),
            positions: None,
            row_population: None,
            cycle_complete: false,
            cross_layer,
            checkpoints: BTreeMap::new(),
            terminal_carrier: None,
            terminal_reacted: None,
            terminal_contracted: None,
            terminal_presented: None,
            previous_context: None,
            overlay: BTreeMap::new(),
            aperture,
            passage_cultivation: None,
            dissection: None,
            terminal_seal: true,
        })
    }

    /// Declare that the receiver reads the terminal face unsealed: the emission's intervals are
    /// then the enclosures the terminal reactions propagate to every coordinate of the face, the
    /// apparatus's remainder at the receiver.  The selected face is read from midpoints as before.
    pub fn with_terminal_remainder(mut self) -> Self {
        self.terminal_seal = false;
        self
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn operation_at(&self) -> usize {
        self.operation_at
    }

    pub fn chronology(&self) -> &[u64] {
        &self.chronology
    }

    pub fn carrier_population(&self) -> usize {
        self.carriers.len() + usize::from(self.terminal_carrier.is_some())
    }

    pub fn cycle_complete(&self) -> bool {
        self.cycle_complete
    }

    pub fn accepts_occurrence(&self, occurrence: &NativeFullOperationOccurrence) -> bool {
        if occurrence.ordinal != self.generation {
            return false;
        }
        let at = if self.cycle_complete {
            0
        } else {
            self.operation_at
        };
        self.ecology.operations.get(at).is_some_and(|operation| {
            matches!(operation.primitive, NativeOperationPrimitive::Lookup { .. })
                == !occurrence.row_addresses.is_empty()
        })
    }

    /// The total rank of the factorized overlay the ecology carries.
    pub fn morphology_overlay_rank(&self) -> usize {
        self.overlay.values().flatten().map(OverlayAtom::rank).sum()
    }

    pub fn return_aperture(&self) -> Option<NativeReturnAperture> {
        self.aperture
    }

    /// The surface's transfer census now: what has crossed between host and device since the
    /// surface was mounted, including the terminal face's egress.
    pub fn census(&self) -> TransferCensus {
        self.residence.surface().census()
    }

    /// The return: if `entering` continues the last cycle's line, the retained emitted face meets
    /// the address that followed each of its rows and the deposit joins the overlay. Any other
    /// occurrence has no comparison and changes no morphology.
    fn return_on_continuation(
        &mut self,
        entering: &[u32],
    ) -> Result<NativeMorphologyTransition, NativeFullOperationError> {
        let Some(aperture) = self.aperture else {
            return Ok(NativeMorphologyTransition::Unchanged);
        };
        let (Some(previous), Some(emission), Some(reacted), Some(presented)) = (
            self.previous_context.as_deref(),
            self.terminal_carrier.as_ref(),
            self.terminal_reacted.as_ref(),
            self.terminal_presented.as_ref(),
        ) else {
            return Ok(NativeMorphologyTransition::Unchanged);
        };
        let Some(next) = continuation_next_occurrences(previous, entering) else {
            return Ok(NativeMorphologyTransition::Unchanged);
        };
        let tied = self
            .ecology
            .operations
            .len()
            .checked_sub(5)
            .and_then(|at| self.ecology.operations.get(at))
            .and_then(|operation| operation.coefficients.first().copied())
            .ok_or(NativeFullOperationError::Operation)?;
        let surface = self.residence.surface();
        let (atom, mut deposit, differential) = enact_return(
            surface,
            ReturnMaterial {
                emission: &emission.sections,
                reacted: &reacted.sections,
                presented: &presented.section,
                presented_octaves: presented.bound_octaves,
                rows: emission.rows,
                width: emission.width,
                grain: emission.grain,
            },
            &next,
            aperture,
        )?;
        deposit.population = tied.0;
        // The receiver has consumed these terminal sections; the return now owns its
        // differential and staged atom. Their old device storage is not part of the pullback.
        self.terminal_carrier = None;
        self.terminal_reacted = None;
        self.terminal_presented = None;
        self.terminal_contracted = None;
        let (adjoint, mut deposits) = self.adjoint_return(differential, ReturnDeed::Cultivate(aperture))?;
        deposits.entry(tied).or_default().push(atom);
        for (population, atoms) in deposits {
            self.overlay.entry(population).or_default().extend(atoms);
        }
        Ok(NativeMorphologyTransition::Changed {
            operation: 0,
            deposit,
            adjoint,
        })
    }

    /// Clear the previous cycle's standing when a new occurrence enters at operation zero.
    fn enter_cycle(&mut self, entering: &[u32]) -> Result<NativeMorphologyTransition, NativeFullOperationError> {
        let transition = self.return_on_continuation(entering)?;
        self.carriers.clear();
        self.checkpoints.clear();
        self.positions = None;
        self.row_population = None;
        self.terminal_carrier = None;
        self.terminal_reacted = None;
        self.terminal_contracted = None;
        self.terminal_presented = None;
        self.cycle_complete = false;
        if let Some(standing) = self.dissection.as_mut() {
            standing.clear();
        }
        Ok(transition)
    }

    /// Enact the operations `[from, to)` of the graph by segments on the contemporary carriers,
    /// each segment one passage.  With `retain_all` every produced carrier stays (the return's
    /// replay); otherwise a carrier no later operation reads is released, into the checkpoints
    /// when it crosses layers and `checkpoint` holds.  A counterfactual run (`checkpoint`
    /// false) leaves the session's checkpoints as the cycle left them.  `withdrawals` intervene
    /// on named operations' outputs.
    pub(super) fn enact_run(
        &mut self,
        from: usize,
        to: usize,
        row_addresses: &[u32],
        withdrawals: &BTreeMap<u32, SegmentWithdrawal<'_, 'chart>>,
        retain_all: bool,
        checkpoint: bool,
    ) -> Result<Vec<RunStep>, NativeFullOperationError> {
        let mut steps = Vec::with_capacity(to.saturating_sub(from));
        if from >= to {
            return Ok(steps);
        }
        if !row_addresses.is_empty() {
            self.ensure_row_population(row_addresses.len())?;
        }
        let operations: Vec<NativeOperatorNode> = self.ecology.operations[from..to].to_vec();
        for (start, end) in segments(&operations) {
            let mut cursor = start;
            while cursor < end {
            let run = &operations[cursor..end];
            let (outcomes, reading) = {
                let site = SegmentSite {
                    residence: self.residence,
                    ecology: self.ecology,
                    carriers: &self.carriers,
                    checkpoints: &self.checkpoints,
                    positions: self.positions.as_ref(),
                    overlay: &self.overlay,
                    grain: self.grain,
                    row_addresses,
                    withdrawals,
                    tile_window: None,
                    seal: true,
                };
                enact_segment(&site, run)?
            };
            if outcomes.is_empty() {
                return Err(NativeFullOperationError::Operation);
            }
            cursor += outcomes.len();
            for (outcome, operation) in outcomes.into_iter().zip(run) {
                let bound_octaves = outcome.carrier.bound_octaves;
                self.carriers.insert(outcome.output, outcome.carrier);
                self.return_joined_passage(operation.ordinal)?;
                steps.push(RunStep {
                    operation: operation.clone(),
                    admitted_octaves: outcome.admitted_octaves,
                    bound_octaves,
                    projection: outcome.projection,
                    census_before: reading.census_before.clone(),
                    census_after: reading.census_after.clone(),
                });
                if retain_all {
                    continue;
                }
                let absolute = self
                    .ecology
                    .operations
                    .iter()
                    .position(|candidate| candidate.ordinal == operation.ordinal)
                    .ok_or(NativeFullOperationError::Operation)?;
                let mut consumed = operation.inputs.clone();
                if let Some(cultivation) = &self.passage_cultivation {
                    consumed.extend(cultivation.released_sources_at(operation.ordinal));
                }
                for input in &consumed {
                    if *input != operation.output
                        && !self.passage_cultivation.as_ref().is_some_and(|c| c.retains_source_after(*input, operation.ordinal))
                        && !self.ecology.operations[absolute + 1..]
                            .iter()
                            .any(|later| later.inputs.contains(input))
                    {
                        if let Some(carrier) = self.carriers.remove(input) {
                            if checkpoint && self.cross_layer.contains(input) {
                                self.checkpoints.insert(*input, carrier);
                            }
                        }
                    }
                }
            }
            }
        }
        Ok(steps)
    }

    fn trace_of(
        &self,
        step: &RunStep,
        occurrence: &NativeFullOperationOccurrence,
        morphology_transition: NativeMorphologyTransition,
        successor_generation: u64,
    ) -> NativeFullOperationTrace {
        NativeFullOperationTrace {
            schema: NATIVE_FULL_OPERATION_STEP_SCHEMA.to_owned(),
            predecessor_generation: successor_generation - 1,
            successor_generation,
            occurrence: occurrence.ordinal,
            row_addresses: occurrence.row_addresses.clone(),
            operation: step.operation.clone(),
            successor_projection: step.projection.clone(),
            morphology_transition,
            morphology_overlay_rank: self.morphology_overlay_rank(),
            admitted_octaves: step.admitted_octaves,
            successor_bound_octaves: step.bound_octaves,
            resident_coefficient_octets: self.residence.receipt().raw_coefficient_octets,
            census_before: step.census_before.clone(),
            census_after: step.census_after.clone(),
        }
    }

    /// Enact the graph's current mathematical operation as a one-operation segment.  The
    /// emission names the successor carrier and carries no words: an intermediate section does
    /// not cross to the host.  The cycle owner (`advance_cycle`) runs whole segments.
    pub fn advance(
        mut self,
        occurrence: NativeFullOperationOccurrence,
    ) -> Result<NativeFullOperationStep<'residence, 'chart>, NativeFullOperationError> {
        if self.passage_cultivation.is_some() {
            return Err(NativeFullOperationError::Contact("this chart advances complete cycles, not exposed primitive steps"));
        }
        if occurrence.ordinal != self.generation {
            return Err(NativeFullOperationError::Occurrence);
        }
        let mut morphology_transition = NativeMorphologyTransition::Unchanged;
        if self.cycle_complete {
            if self.operation_at != 0 || occurrence.row_addresses.is_empty() {
                return Err(NativeFullOperationError::Occurrence);
            }
            morphology_transition = self.enter_cycle(&occurrence.row_addresses)?;
        }
        let at = self.operation_at;
        let operation = self
            .ecology
            .operations
            .get(at)
            .cloned()
            .ok_or(NativeFullOperationError::Operation)?;
        if matches!(operation.primitive, NativeOperationPrimitive::Lookup { .. }) {
            self.previous_context = Some(occurrence.row_addresses.clone());
        }
        let steps = self.enact_run(at, at + 1, &occurrence.row_addresses, &BTreeMap::new(), false, true)?;
        let step = steps.into_iter().next().ok_or(NativeFullOperationError::Operation)?;
        let successor_generation = self
            .generation
            .checked_add(1)
            .ok_or(NativeFullOperationError::Generation)?;
        self.chronology.push(self.generation);
        self.operation_at += 1;
        if self.operation_at == self.ecology.operations.len() {
            self.operation_at = 0;
            self.cycle_complete = true;
        }
        self.generation = successor_generation;
        let carrier = self
            .carriers
            .get(&operation.output)
            .ok_or(NativeFullOperationError::Carrier)?;
        let emission = NativeFullOperationEmission {
            generation: successor_generation,
            operation: operation.ordinal,
            carrier: operation.output,
            rows: carrier.section.rows(),
            width: carrier.section.width(),
            grain: carrier.section.grain().0,
            intervals: Vec::new(),
        };
        let trace = self.trace_of(&step, &occurrence, morphology_transition, successor_generation);
        Ok(NativeFullOperationStep {
            emission,
            trace,
            successor: self,
        })
    }

    /// Complete one whole operator recurrence from ordinary addressed occurrences, by segments,
    /// through the tiled terminal boundary.  The ecology's operation word decides which nodes
    /// consume the row population; an application cannot inspect or schedule internal primitive
    /// species.
    pub fn advance_cycle(
        mut self,
        row_addresses: &[u32],
    ) -> Result<NativeFullCycle<'residence, 'chart>, NativeFullOperationError> {
        if row_addresses.is_empty() || (self.operation_at != 0 && !self.cycle_complete) {
            return Err(NativeFullOperationError::Occurrence);
        }
        let mut morphology_transition = NativeMorphologyTransition::Unchanged;
        if self.cycle_complete {
            morphology_transition = self.enter_cycle(row_addresses)?;
        }
        let terminal_start = self.ecology.operations.len().saturating_sub(5);
        self.previous_context = Some(row_addresses.to_vec());
        let occurrence = NativeFullOperationOccurrence {
            ordinal: self.generation,
            row_addresses: row_addresses.to_vec(),
        };
        let steps = self.enact_run(0, terminal_start, row_addresses, &BTreeMap::new(), false, true)?;
        let mut traces = Vec::with_capacity(self.ecology.operations.len());
        for step in &steps {
            let successor_generation = self
                .generation
                .checked_add(1)
                .ok_or(NativeFullOperationError::Generation)?;
            let transition = std::mem::replace(&mut morphology_transition, NativeMorphologyTransition::Unchanged);
            traces.push(self.trace_of(step, &occurrence, transition, successor_generation));
            self.chronology.push(self.generation);
            self.generation = successor_generation;
            self.operation_at += 1;
        }
        let ordinal = self.generation;
        let mut terminal = self.advance_terminal(NativeFullOperationOccurrence {
            ordinal,
            row_addresses: Vec::new(),
        })?;
        traces.append(&mut terminal.traces);
        let final_emission = terminal
            .emissions
            .pop()
            .ok_or(NativeFullOperationError::Operation)?;
        Ok(NativeFullCycle {
            final_emission,
            traces,
            passage_returns: terminal.successor.publish_passage_returns(),
            successor: terminal.successor,
        })
    }

    pub(super) fn ensure_row_population(&mut self, rows: usize) -> Result<(), NativeFullOperationError> {
        match self.row_population {
            Some(held) if held == rows => Ok(()),
            Some(_) => Err(NativeFullOperationError::Occurrence),
            None => {
                let positions = (0..rows)
                    .map(|position| {
                        u32::try_from(position).map_err(|_| NativeFullOperationError::Operation)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                self.positions = Some(self.residence.surface().mount_positions(&positions)?);
                self.row_population = Some(rows);
                Ok(())
            }
        }
    }

    /// The terminal receiver's copy: the one place a carrier crosses to the serial chart.
    pub fn carrier_intervals(
        &self,
        carrier: NativeCarrierOrdinal,
    ) -> Result<Vec<(i64, i64)>, NativeFullOperationError> {
        if let Some(held) = self.carriers.get(&carrier) {
            let intervals = self.residence.surface().read_out(&held.section)?;
            if intervals.is_empty() || held.bound_octaves == 0 {
                return Err(NativeFullOperationError::Carrier);
            }
            return Ok(intervals);
        }
        let held = self
            .terminal_carrier
            .as_ref()
            .filter(|held| held.carrier == carrier)
            .ok_or(NativeFullOperationError::Carrier)?;
        let tiles = held
            .sections
            .iter()
            .map(|section| self.residence.surface().read_out(section))
            .collect::<Result<Vec<_>, _>>()?;
        stitch_intervals(held.rows, &tiles)
    }
}

#[derive(Debug, Error)]
pub enum NativeFullOperationError {
    #[error("native contact: {0}")]
    Contact(&'static str),
    #[error("operator ecology: {0}")]
    Ecology(#[from] super::NativeFullOperatorError),
    #[error("operator residence: {0}")]
    Residence(#[from] NativeOperatorResidenceError),
    #[error("resident apparatus: {0}")]
    Resident(#[from] ResidentRefusal),
    #[error("the occurrence does not join the contemporary ecology")]
    Occurrence,
    #[error("the current operation disagrees with the complete ecology")]
    Operation,
    #[error("operation {operation} is not yet enacted by the full-session owner")]
    PrimitiveOpen { operation: u32 },
    #[error("the lookup's exact common grain is outside the resident carrier")]
    Grain,
    #[error("resident operation {operation} returned obstruction flags {flags:#x}")]
    ResidentObstruction { operation: u32, flags: u32 },
    #[error("the ecology generation overflowed")]
    Generation,
    #[error("the requested contemporary carrier is absent")]
    Carrier,
    #[error("the declared successor projection did not return a point carrier")]
    Projection,
    #[error("the local morphology current is malformed or does not enter this operation")]
    Morphology,
    #[error("the return through the body refused: {0}")]
    Adjoint(String),
}

/// A contemporary carrier: produced in this cycle or replay, or retained as a checkpoint.
pub(super) fn carrier_of<'a, 'chart>(
    carriers: &'a BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    checkpoints: &'a BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    ordinal: &NativeCarrierOrdinal,
) -> Option<&'a ContemporaryCarrier<'chart>> {
    carriers.get(ordinal).or_else(|| checkpoints.get(ordinal))
}
