//! One mathematical operation advances the complete resident operator ecology.
//!
//! This owner begins at the first operation of the full HNA1 graph.  It consumes ordinary row
//! addresses at the occurrence port, gathers those coefficient rows without leaving the device,
//! enacts the graph's lookup law, and returns its emission, exact trace, and move-owned successor
//! ecology together.  No exterior verdict, stored activation, candidate, or commit intervenes.

use std::collections::{BTreeMap, BTreeSet};

use relational_geometry::Rat;
use serde::Serialize;
use thiserror::Error;

use crate::{
    resident_section::{
        Dyadic, Positions, ResidentGrain, ResidentRefusal, ResidentSection,
        SeriesAperture, TransferCensus,
    },
};

use super::{
    NativeCarrierAxis, NativeCarrierOrdinal, NativeCausalReach, NativeFullOperatorEcology,
    NativeMorphologyDeposit, NativeOperationPrimitive, NativeOperatorNode,
    NativeOperatorResidence, NativeOperatorResidenceError, NativeReturnAperture,
    NativeScaleConstraint, NativeTensorOrdinal,
    operative_backward::{NativeAdjointReturnTrace, ReturnDeed},
    operative_intervention::DissectionStanding,
    operative_scalars::{binary64_projection, operation_bound, projected_scale, scale_enclosure},
    operative_terminal::{TiledCarrier, stitch_intervals},
    operative_return::{
        OverlayAtom, ReturnMaterial, contract_tile_with_overlay, continuation_next_occurrences,
        enact_return,
    },
};

pub const NATIVE_FULL_OPERATION_STEP_SCHEMA: &str = "holonic-engine.native-full-operation-step.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeFullOperationOccurrence {
    pub ordinal: u64,
    pub row_addresses: Vec<u32>,
}

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

pub(super) struct OperationOutcome<'chart> {
    pub(super) section: ResidentSection<'chart>,
    pub(super) bound_octaves: u32,
    pub(super) rows: usize,
    pub(super) width: usize,
    pub(super) grain: ResidentGrain,
    pub(super) intervals: Vec<(i64, i64)>,
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
    /// The tied contraction's own output, retained for dissection: the excitation's first-order
    /// contribution at the vocabulary sites reads it.
    pub(super) terminal_contracted: Option<Vec<(i64, i64)>>,
    pub(super) terminal_presented: Option<ContemporaryCarrier<'chart>>,
    /// The row addresses of the last cycle: the line the emitted face continued.
    pub(super) previous_context: Option<Vec<u32>>,
    /// The factorized overlay atoms deposited on each cross-section, keyed by its coefficient
    /// population, in deposit order.
    pub(super) overlay: BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'chart>>>,
    /// The declared return apertures; `None` enacts no return.
    pub(super) aperture: Option<NativeReturnAperture>,
    /// The dissection standing: the excitation's supports and face, when founded for dissection.
    pub(super) dissection: Option<DissectionStanding>,
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
            dissection: None,
        })
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
        self.overlay.entry(tied).or_default().push(atom);
        let adjoint = self.adjoint_return(differential, ReturnDeed::Cultivate(aperture))?;
        Ok(NativeMorphologyTransition::Changed {
            operation: 0,
            deposit,
            adjoint,
        })
    }

    /// Enact one operation of the graph on the contemporary carriers, without advancing the
    /// chronology: the forward law, used by `advance` and by the return's replay alike.
    pub(super) fn enact_operation(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        let outcome = match &operation.primitive {
            NativeOperationPrimitive::Lookup { scale } => {
                self.execute_lookup(operation, occurrence, scale)?
            }
            NativeOperationPrimitive::Reshape => self.execute_reshape(operation, occurrence)?,
            NativeOperationPrimitive::Select { axis, at } => {
                self.execute_select(operation, occurrence, *axis, *at)?
            }
            NativeOperationPrimitive::Contract => self.execute_contract(operation, occurrence)?,
            NativeOperationPrimitive::RmsRebase {
                group,
                epsilon,
                has_gain,
            } => self.execute_rms(operation, occurrence, *group, epsilon, *has_gain)?,
            NativeOperationPrimitive::GeluTanh => self.execute_gelu(operation, occurrence)?,
            NativeOperationPrimitive::Tanh => self.execute_tanh(operation, occurrence)?,
            NativeOperationPrimitive::Hadamard => {
                self.execute_binary(operation, occurrence, false)?
            }
            NativeOperationPrimitive::Add => self.execute_binary(operation, occurrence, true)?,
            NativeOperationPrimitive::Scale { by }
                if !matches!(by, NativeScaleConstraint::Coefficient) =>
            {
                self.execute_scale(operation, occurrence, by)?
            }
            NativeOperationPrimitive::Scale {
                by: NativeScaleConstraint::Coefficient,
            } => self.execute_coefficient_scale(operation, occurrence)?,
            NativeOperationPrimitive::RotaryChronology {
                theta,
                head_width,
                rotated_width,
            } => self.execute_chronology(
                operation,
                occurrence,
                *theta,
                *head_width,
                *rotated_width,
            )?,
            NativeOperationPrimitive::CausalContact {
                heads,
                kv_heads,
                head_width,
                reach,
                series_terms,
            } => self.execute_contact(
                operation,
                occurrence,
                *heads,
                *kv_heads,
                *head_width,
                reach,
                *series_terms,
            )?,
            NativeOperationPrimitive::Emit => self.execute_reshape(operation, occurrence)?,
            _ => {
                return Err(NativeFullOperationError::PrimitiveOpen {
                    operation: operation.ordinal,
                });
            }
        };
        Ok(outcome)
    }

    /// Enact the graph's current mathematical operation.  HNA2 begins with the complete graph's
    /// actual lookup operation; later primitive species are added to this same match in graph order,
    /// never selected by an application driver.
    pub fn advance(
        mut self,
        occurrence: NativeFullOperationOccurrence,
    ) -> Result<NativeFullOperationStep<'residence, 'chart>, NativeFullOperationError> {
        if occurrence.ordinal != self.generation {
            return Err(NativeFullOperationError::Occurrence);
        }
        let mut morphology_transition = NativeMorphologyTransition::Unchanged;
        if self.cycle_complete {
            if self.operation_at != 0 || occurrence.row_addresses.is_empty() {
                return Err(NativeFullOperationError::Occurrence);
            }
            morphology_transition = self.return_on_continuation(&occurrence.row_addresses)?;
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
        }
        let operation = self
            .ecology
            .operations
            .get(self.operation_at)
            .cloned()
            .ok_or(NativeFullOperationError::Operation)?;
        if matches!(operation.primitive, NativeOperationPrimitive::Lookup { .. }) {
            self.previous_context = Some(occurrence.row_addresses.clone());
        }
        let outcome = self.enact_operation(&operation, &occurrence)?;
        let (outcome, successor_projection) = self.project_successor(operation.ordinal, outcome)?;
        let morphology_overlay_rank = self.morphology_overlay_rank();
        let successor_generation = self
            .generation
            .checked_add(1)
            .ok_or(NativeFullOperationError::Generation)?;
        self.chronology.push(self.generation);
        self.carriers.insert(
            operation.output,
            ContemporaryCarrier {
                section: outcome.section,
                bound_octaves: outcome.bound_octaves,
            },
        );
        self.operation_at += 1;
        for input in &operation.inputs {
            if *input != operation.output
                && !self.ecology.operations[self.operation_at..]
                    .iter()
                    .any(|later| later.inputs.contains(input))
            {
                if let Some(carrier) = self.carriers.remove(input) {
                    if self.cross_layer.contains(input) {
                        self.checkpoints.insert(*input, carrier);
                    }
                }
            }
        }
        if self.operation_at == self.ecology.operations.len() {
            self.operation_at = 0;
            self.cycle_complete = true;
        }
        self.generation = successor_generation;
        let resident_coefficient_octets = self.residence.receipt().raw_coefficient_octets;
        Ok(NativeFullOperationStep {
            emission: NativeFullOperationEmission {
                generation: successor_generation,
                operation: operation.ordinal,
                carrier: operation.output,
                rows: outcome.rows,
                width: outcome.width,
                grain: outcome.grain.0,
                intervals: outcome.intervals,
            },
            trace: NativeFullOperationTrace {
                schema: NATIVE_FULL_OPERATION_STEP_SCHEMA.to_owned(),
                predecessor_generation: successor_generation - 1,
                successor_generation,
                occurrence: occurrence.ordinal,
                row_addresses: occurrence.row_addresses,
                operation,
                successor_projection,
                morphology_transition,
                morphology_overlay_rank,
                successor_bound_octaves: outcome.bound_octaves,
                resident_coefficient_octets,
                census_before: outcome.census_before,
                census_after: outcome.census_after,
            },
            successor: self,
        })
    }

    /// Complete one whole operator recurrence from ordinary addressed occurrences. The ecology's
    /// operation word decides which nodes consume the row population; an application cannot inspect
    /// or schedule internal primitive species.
    pub fn advance_cycle(
        mut self,
        row_addresses: &[u32],
    ) -> Result<NativeFullCycle<'residence, 'chart>, NativeFullOperationError> {
        if row_addresses.is_empty() || (self.operation_at != 0 && !self.cycle_complete) {
            return Err(NativeFullOperationError::Occurrence);
        }
        let terminal_start = self.ecology.operations.len().saturating_sub(5);
        let mut traces = Vec::with_capacity(self.ecology.operations.len());
        while self.operation_at < terminal_start {
            let current = self
                .ecology
                .operations
                .get(if self.cycle_complete {
                    0
                } else {
                    self.operation_at
                })
                .ok_or(NativeFullOperationError::Operation)?;
            let rows = if matches!(current.primitive, NativeOperationPrimitive::Lookup { .. }) {
                row_addresses.to_vec()
            } else {
                Vec::new()
            };
            let ordinal = self.generation;
            let step = self.advance(NativeFullOperationOccurrence {
                ordinal,
                row_addresses: rows,
            })?;
            traces.push(step.trace);
            self = step.successor;
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
            successor: terminal.successor,
        })
    }

    pub(super) fn project_successor(
        &self,
        operation: u32,
        outcome: OperationOutcome<'chart>,
    ) -> Result<(OperationOutcome<'chart>, NativeSuccessorProjection), NativeFullOperationError>
    {
        let nonpoint_coordinates = outcome
            .intervals
            .iter()
            .filter(|(lower, upper)| lower != upper)
            .count();
        if nonpoint_coordinates == 0 {
            return Ok((outcome, NativeSuccessorProjection::Exact));
        }
        let widest_interval = outcome
            .intervals
            .iter()
            .map(|(lower, upper)| lower.abs_diff(*upper))
            .max()
            .unwrap_or(0);
        let surface = self.residence.surface();
        let shape =
            surface.shape_collapse_control(outcome.rows, outcome.width, outcome.bound_octaves)?;
        let successor = surface.fresh_section(outcome.rows, outcome.width, outcome.grain)?;
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_collapse_control(&lane, &outcome.section, &successor)?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation, &reading)?;
        let intervals = surface.read_out(&successor)?;
        if intervals.iter().any(|(lower, upper)| lower != upper) {
            return Err(NativeFullOperationError::Projection);
        }
        let census_after = surface.census();
        Ok((
            OperationOutcome {
                section: successor,
                bound_octaves,
                rows: outcome.rows,
                width: outcome.width,
                grain: outcome.grain,
                intervals,
                census_before: outcome.census_before,
                census_after,
            },
            NativeSuccessorProjection::Midpoint {
                nonpoint_coordinates,
                widest_interval,
            },
        ))
    }

    fn execute_lookup(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
        scale: &NativeScaleConstraint,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        if occurrence.row_addresses.is_empty()
            || !operation.inputs.is_empty()
            || operation.coefficients.len() != 1
        {
            return Err(NativeFullOperationError::Occurrence);
        }
        let coefficient = operation.coefficients[0];
        let population = self
            .ecology
            .coefficient_populations
            .get(coefficient.0 as usize)
            .ok_or(NativeFullOperationError::Operation)?;
        let [_, width] = population.shape.as_slice() else {
            return Err(NativeFullOperationError::Operation);
        };
        let output = self.output(operation)?;
        if output.axes
            != [
                NativeCarrierAxis::Occurrence,
                NativeCarrierAxis::Fixed(*width),
            ]
        {
            return Err(NativeFullOperationError::Operation);
        }
        let scale = projected_scale(scale)?;
        self.ensure_row_population(occurrence.row_addresses.len())?;
        let selection = self
            .residence
            .gather_rows(coefficient, &occurrence.row_addresses)?;
        if selection.width != *width || selection.rows != occurrence.row_addresses.len() {
            return Err(NativeFullOperationError::Operation);
        }
        let exact_frame = selection
            .frame
            .exponent
            .checked_add(scale.exponent)
            .ok_or(NativeFullOperationError::Grain)?;
        if exact_frame + (self.grain.0 as i32) < 0 {
            return Err(NativeFullOperationError::Grain);
        }
        let grain = self.grain;
        let surface = self.residence.surface();
        let shape = surface.shape_enter_resident_bfloat16(
            selection.rows,
            selection.width,
            scale,
            grain,
            selection.frame.exponent,
            selection.entry_octaves,
        )?;
        let successor = surface.fresh_section(selection.rows, selection.width, grain)?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_enter_resident_bfloat16(
            &lane,
            selection.address,
            selection.rows,
            selection.width,
            scale,
            &successor,
        )?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        Ok(OperationOutcome {
            section: successor,
            bound_octaves,
            rows: selection.rows,
            width: selection.width,
            grain,
            intervals,
            census_before,
            census_after,
        })
    }

    fn execute_reshape(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        require_internal_occurrence(operation, occurrence, 1, 0)?;
        self.output(operation)?;
        let input = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let surface = self.residence.surface();
        let shape = surface.shape_carry(
            input.section.rows(),
            input.section.width(),
            input.bound_octaves,
        )?;
        let successor = surface.fresh_section(
            input.section.rows(),
            input.section.width(),
            input.section.grain(),
        )?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_carry(&lane, &input.section, &successor)?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        Ok(OperationOutcome {
            rows: successor.rows(),
            width: successor.width(),
            grain: successor.grain(),
            section: successor,
            bound_octaves,
            intervals,
            census_before,
            census_after,
        })
    }

    fn execute_contract(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        if !occurrence.row_addresses.is_empty()
            || operation.inputs.len() != 1
            || operation.coefficients.len() != 1
        {
            return Err(NativeFullOperationError::Operation);
        }
        self.output(operation)?;
        let input = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let coefficient = operation.coefficients[0];
        let population = self
            .ecology
            .coefficient_populations
            .get(coefficient.0 as usize)
            .ok_or(NativeFullOperationError::Operation)?;
        let [rows, dim] = population.shape.as_slice() else {
            return Err(NativeFullOperationError::Operation);
        };
        if input.section.width() != *dim {
            return Err(NativeFullOperationError::Operation);
        }
        let surface = self.residence.surface();
        let atoms = self.overlay.get(&coefficient).map(Vec::as_slice).unwrap_or(&[]);
        let tile = self.residence.align_tile(coefficient, 0, *rows)?;
        let census_before = surface.census();
        let (successor, reading) = contract_tile_with_overlay(
            surface,
            &input.section,
            input.bound_octaves,
            &tile.mounted.readout,
            atoms,
            0,
            *rows,
        )?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        drop(tile);
        Ok(OperationOutcome {
            rows: successor.rows(),
            width: successor.width(),
            grain: successor.grain(),
            section: successor,
            bound_octaves,
            intervals,
            census_before,
            census_after,
        })
    }

    fn execute_rms(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
        group: usize,
        epsilon: &Rat,
        has_gain: bool,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        require_internal_occurrence(operation, occurrence, 1, usize::from(has_gain))?;
        self.output(operation)?;
        let input = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let surface = self.residence.surface();
        let gain = if has_gain {
            Some(self.residence.align_tile(operation.coefficients[0], 0, 1)?)
        } else {
            None
        };
        let gain_readout = gain.as_ref().map(|tile| &tile.mounted.readout);
        let shape = surface.shape_rms_rebase(
            input.section.rows(),
            input.section.width(),
            group,
            input.bound_octaves,
            gain_readout,
        )?;
        let successor = surface.fresh_section(
            input.section.rows(),
            input.section.width(),
            input.section.grain(),
        )?;
        let eps = binary64_projection(epsilon)?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_rms_rebase(
            &lane,
            &input.section,
            group,
            gain_readout,
            eps,
            &shape,
            &successor,
        )?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        drop(gain);
        Ok(OperationOutcome {
            rows: successor.rows(),
            width: successor.width(),
            grain: successor.grain(),
            section: successor,
            bound_octaves,
            intervals,
            census_before,
            census_after,
        })
    }

    fn execute_tanh(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        require_internal_occurrence(operation, occurrence, 1, 0)?;
        self.output(operation)?;
        let input = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let surface = self.residence.surface();
        let terms = SeriesAperture(14);
        let shape = surface.shape_tanh(
            input.section.rows(),
            input.section.width(),
            input.bound_octaves,
            input.section.grain(),
            terms,
        )?;
        let successor = surface.fresh_section(
            input.section.rows(),
            input.section.width(),
            input.section.grain(),
        )?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_tanh(&lane, &input.section, terms, &successor)?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        Ok(OperationOutcome {
            rows: successor.rows(),
            width: successor.width(),
            grain: successor.grain(),
            section: successor,
            bound_octaves,
            intervals,
            census_before,
            census_after,
        })
    }

    fn execute_gelu(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        require_internal_occurrence(operation, occurrence, 1, 0)?;
        self.output(operation)?;
        let input = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let surface = self.residence.surface();
        let c1 = Dyadic::of_binary64_bits(0x3fe9_8845_33d4_3651)?;
        let c2 = Dyadic::of_binary64_bits(0x3fa6_e4e2_6d48_01f7)?;
        let terms = SeriesAperture(14);
        let shape = surface.shape_gelu_tanh(
            input.section.rows(),
            input.section.width(),
            input.bound_octaves,
            input.section.grain(),
            c1,
            c2,
            terms,
        )?;
        let successor = surface.fresh_section(
            input.section.rows(),
            input.section.width(),
            input.section.grain(),
        )?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_gelu_tanh(&lane, &input.section, c1, c2, terms, &successor)?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        Ok(OperationOutcome {
            rows: successor.rows(),
            width: successor.width(),
            grain: successor.grain(),
            section: successor,
            bound_octaves,
            intervals,
            census_before,
            census_after,
        })
    }

    fn execute_binary(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
        additive: bool,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        require_internal_occurrence(operation, occurrence, 2, 0)?;
        self.output(operation)?;
        let left = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let right = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[1])
            .ok_or(NativeFullOperationError::Carrier)?;
        if left.section.rows() != right.section.rows()
            || left.section.width() != right.section.width()
            || left.section.grain() != right.section.grain()
        {
            return Err(NativeFullOperationError::Operation);
        }
        let surface = self.residence.surface();
        let shape = if additive {
            surface.shape_re_entry(
                left.section.rows(),
                left.section.width(),
                left.bound_octaves,
                right.bound_octaves,
            )?
        } else {
            surface.shape_hadamard(
                left.section.rows(),
                left.section.width(),
                left.bound_octaves,
                right.bound_octaves,
            )?
        };
        let successor = surface.fresh_section(
            left.section.rows(),
            left.section.width(),
            left.section.grain(),
        )?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        if additive {
            surface.record_re_entry(&lane, &left.section, &right.section, &successor)?;
        } else {
            surface.record_hadamard(&lane, &left.section, &right.section, &successor)?;
        }
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        Ok(OperationOutcome {
            rows: successor.rows(),
            width: successor.width(),
            grain: successor.grain(),
            section: successor,
            bound_octaves,
            intervals,
            census_before,
            census_after,
        })
    }

    fn execute_scale(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
        constraint: &NativeScaleConstraint,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        require_internal_occurrence(operation, occurrence, 1, 0)?;
        self.output(operation)?;
        let input = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let by = scale_enclosure(constraint)?;
        let surface = self.residence.surface();
        let shape = surface.shape_scale(
            input.section.rows(),
            input.section.width(),
            input.bound_octaves,
            by,
        )?;
        let successor = surface.fresh_section(
            input.section.rows(),
            input.section.width(),
            input.section.grain(),
        )?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_scale(&lane, &input.section, by, &successor)?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        Ok(OperationOutcome {
            rows: successor.rows(),
            width: successor.width(),
            grain: successor.grain(),
            section: successor,
            bound_octaves,
            intervals,
            census_before,
            census_after,
        })
    }

    fn execute_coefficient_scale(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        require_internal_occurrence(operation, occurrence, 1, 1)?;
        self.output(operation)?;
        let input = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let surface = self.residence.surface();
        let coefficient = self.residence.align_tile(operation.coefficients[0], 0, 1)?;
        let shape = surface.shape_scale_by_aligned(
            input.section.rows(),
            input.section.width(),
            input.bound_octaves,
            &coefficient.mounted.readout,
        )?;
        let successor = surface.fresh_section(
            input.section.rows(),
            input.section.width(),
            input.section.grain(),
        )?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_scale_by_aligned(
            &lane,
            &input.section,
            &coefficient.mounted.readout,
            &successor,
        )?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        drop(coefficient);
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        Ok(OperationOutcome {
            rows: successor.rows(),
            width: successor.width(),
            grain: successor.grain(),
            section: successor,
            bound_octaves,
            intervals,
            census_before,
            census_after,
        })
    }

    fn execute_select(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
        axis: usize,
        at: usize,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        require_internal_occurrence(operation, occurrence, 1, 0)?;
        if axis != 1 {
            return Err(NativeFullOperationError::Operation);
        }
        let output = self.output(operation)?;
        let span = match output.axes.last() {
            Some(NativeCarrierAxis::Fixed(span)) => *span,
            _ => return Err(NativeFullOperationError::Operation),
        };
        let input = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let from = at
            .checked_mul(span)
            .ok_or(NativeFullOperationError::Operation)?;
        let surface = self.residence.surface();
        let shape = surface.shape_select_columns(
            input.section.rows(),
            input.section.width(),
            from,
            span,
            input.bound_octaves,
        )?;
        let successor = surface.fresh_section(input.section.rows(), span, input.section.grain())?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_select_columns(&lane, &input.section, from, span, &successor)?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        Ok(OperationOutcome {
            rows: successor.rows(),
            width: successor.width(),
            grain: successor.grain(),
            section: successor,
            bound_octaves,
            intervals,
            census_before,
            census_after,
        })
    }

    fn execute_contact(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        reach: &NativeCausalReach,
        series_terms: u32,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        require_internal_occurrence(operation, occurrence, 3, 0)?;
        self.output(operation)?;
        let q = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let k = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[1])
            .ok_or(NativeFullOperationError::Carrier)?;
        let v = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[2])
            .ok_or(NativeFullOperationError::Carrier)?;
        if q.section.rows() != k.section.rows()
            || q.section.rows() != v.section.rows()
            || q.section.grain() != k.section.grain()
            || q.section.grain() != v.section.grain()
        {
            return Err(NativeFullOperationError::Operation);
        }
        let window = match reach {
            NativeCausalReach::Window(window) if *window > 0 => *window,
            NativeCausalReach::Complete => q.section.rows(),
            _ => return Err(NativeFullOperationError::Operation),
        };
        let terms = SeriesAperture(series_terms);
        let surface = self.residence.surface();
        let shape = surface.shape_contact(
            q.section.rows(),
            q.section.width(),
            k.section.width(),
            v.section.width(),
            heads,
            kv_heads,
            head_width,
            window,
            terms,
            q.section.grain(),
            q.bound_octaves,
            k.bound_octaves,
            v.bound_octaves,
        )?;
        let successor =
            surface.fresh_section(q.section.rows(), heads * head_width, q.section.grain())?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_contact(
            &lane, &q.section, &k.section, &v.section, heads, kv_heads, head_width, window, terms,
            None, &shape, &successor,
        )?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        Ok(OperationOutcome {
            rows: successor.rows(),
            width: successor.width(),
            grain: successor.grain(),
            section: successor,
            bound_octaves,
            intervals,
            census_before,
            census_after,
        })
    }

    fn execute_chronology(
        &mut self,
        operation: &NativeOperatorNode,
        occurrence: &NativeFullOperationOccurrence,
        theta: u64,
        head_width: usize,
        rotated_width: usize,
    ) -> Result<OperationOutcome<'chart>, NativeFullOperationError> {
        require_internal_occurrence(operation, occurrence, 1, 0)?;
        self.output(operation)?;
        let input = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        if input.section.width() % head_width != 0 {
            return Err(NativeFullOperationError::Operation);
        }
        let heads = input.section.width() / head_width;
        let positions = self
            .positions
            .as_ref()
            .ok_or(NativeFullOperationError::Occurrence)?;
        let bands = self
            .residence
            .chronology(theta, head_width, rotated_width)?;
        let surface = self.residence.surface();
        let shape = surface.shape_chronology(
            input.section.rows(),
            input.section.width(),
            heads,
            head_width,
            input.bound_octaves,
            bands,
            positions,
            u32::try_from(input.section.rows().saturating_sub(1))
                .map_err(|_| NativeFullOperationError::Operation)?,
        )?;
        let successor = surface.fresh_section(
            input.section.rows(),
            input.section.width(),
            input.section.grain(),
        )?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_chronology(
            &lane,
            &input.section,
            heads,
            head_width,
            bands,
            positions,
            &successor,
        )?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation.ordinal, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let census_after = surface.census();
        Ok(OperationOutcome {
            rows: successor.rows(),
            width: successor.width(),
            grain: successor.grain(),
            section: successor,
            bound_octaves,
            intervals,
            census_before,
            census_after,
        })
    }

    fn ensure_row_population(&mut self, rows: usize) -> Result<(), NativeFullOperationError> {
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

    fn output(
        &self,
        operation: &NativeOperatorNode,
    ) -> Result<&super::NativeCarrierChart, NativeFullOperationError> {
        self.ecology
            .carriers
            .get(operation.output.0 as usize)
            .ok_or(NativeFullOperationError::Operation)
    }

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

fn require_internal_occurrence(
    operation: &NativeOperatorNode,
    occurrence: &NativeFullOperationOccurrence,
    inputs: usize,
    coefficients: usize,
) -> Result<(), NativeFullOperationError> {
    if !occurrence.row_addresses.is_empty()
        || operation.inputs.len() != inputs
        || operation.coefficients.len() != coefficients
    {
        Err(NativeFullOperationError::Operation)
    } else {
        Ok(())
    }
}
