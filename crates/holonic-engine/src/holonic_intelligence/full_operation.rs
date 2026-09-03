//! One mathematical operation advances the complete resident operator ecology.
//!
//! This owner begins at the first operation of the full HNA1 graph.  It consumes ordinary row
//! addresses at the occurrence port, gathers those coefficient rows without leaving the device,
//! enacts the graph's lookup law, and returns its emission, exact trace, and move-owned successor
//! ecology together.  No exterior verdict, stored activation, candidate, or commit intervenes.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::Serialize;
use thiserror::Error;

use crate::{
    exact_value::ieee754::{BinaryFloatSpecies, decode_bfloat16_bits, round_into},
    exact_value::{AlgebraicRoot, ExactInterval},
    resident_section::{
        Dyadic, DyadicEnclosure, Positions, ResidentGrain, ResidentRefusal, ResidentSection,
        SeriesAperture, TransferCensus,
    },
};

use super::{
    NativeCarrierAxis, NativeCarrierOrdinal, NativeCausalReach, NativeFullOperatorEcology,
    NativeOperationPrimitive, NativeOperatorNode, NativeOperatorResidence,
    NativeOperatorResidenceError, NativeScaleConstraint,
};

pub const NATIVE_FULL_OPERATION_STEP_SCHEMA: &str = "holonic-engine.native-full-operation-step.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeFullOperationOccurrence {
    pub ordinal: u64,
    pub row_addresses: Vec<u32>,
    pub morphology_current: Option<NativeLocalMorphologyCurrent>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct NativeLocalMorphologyCurrent {
    pub significand: i64,
    pub exponent: i32,
}

impl NativeLocalMorphologyCurrent {
    pub const IDENTITY: Self = Self {
        significand: 1,
        exponent: 0,
    };

    fn validate(self) -> Result<(), NativeFullOperationError> {
        if self.significand <= 0 {
            Err(NativeFullOperationError::Morphology)
        } else {
            Ok(())
        }
    }

    fn compose(self, current: Self) -> Result<Self, NativeFullOperationError> {
        self.validate()?;
        current.validate()?;
        Ok(Self {
            significand: self
                .significand
                .checked_mul(current.significand)
                .ok_or(NativeFullOperationError::Morphology)?,
            exponent: self
                .exponent
                .checked_add(current.exponent)
                .ok_or(NativeFullOperationError::Morphology)?,
        })
    }

    fn enclosure(self) -> Result<DyadicEnclosure, NativeFullOperationError> {
        self.validate()?;
        let value = if self.exponent >= 0 {
            Rat::from_integer(BigInt::from(self.significand) << self.exponent as usize)
        } else {
            Rat::new(
                BigInt::from(self.significand),
                BigInt::from(1) << (-self.exponent) as usize,
            )
        };
        finest_enclosure(&ExactInterval::point(value))
    }
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
    pub morphology_factor: NativeLocalMorphologyCurrent,
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
        before: NativeLocalMorphologyCurrent,
        after: NativeLocalMorphologyCurrent,
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

struct ContemporaryCarrier<'chart> {
    section: ResidentSection<'chart>,
    bound_octaves: u32,
}

struct OperationOutcome<'chart> {
    section: ResidentSection<'chart>,
    bound_octaves: u32,
    rows: usize,
    width: usize,
    grain: ResidentGrain,
    intervals: Vec<(i64, i64)>,
    census_before: TransferCensus,
    census_after: TransferCensus,
}

struct TiledCarrier<'chart> {
    sections: Vec<ResidentSection<'chart>>,
    bounds: Vec<u32>,
    rows: usize,
    width: usize,
    grain: ResidentGrain,
    carrier: NativeCarrierOrdinal,
}

struct TiledOperationOutcome<'chart> {
    carrier: TiledCarrier<'chart>,
    intervals: Vec<(i64, i64)>,
    projection: NativeSuccessorProjection,
    census_before: TransferCensus,
    census_after: TransferCensus,
}

#[derive(Clone, Copy)]
enum TiledUnary {
    Scale(DyadicEnclosure),
    Tanh(SeriesAperture),
    Carry,
}

/// The move-owned contemporary ecology.  The coefficient morphology is one borrowed resident
/// standing; every produced carrier and the chronology belong to this successor line alone.
pub struct NativeFullOperatorSession<'residence, 'chart> {
    ecology: &'residence NativeFullOperatorEcology,
    residence: &'residence mut NativeOperatorResidence<'chart>,
    carriers: BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    operation_at: usize,
    generation: u64,
    chronology: Vec<u64>,
    grain: ResidentGrain,
    positions: Option<Positions<'chart>>,
    row_population: Option<usize>,
    cycle_complete: bool,
    terminal_carrier: Option<TiledCarrier<'chart>>,
    morphology: NativeLocalMorphologyCurrent,
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
        ecology.validate()?;
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
            terminal_carrier: None,
            morphology: NativeLocalMorphologyCurrent::IDENTITY,
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
            let row_shape = matches!(operation.primitive, NativeOperationPrimitive::Lookup { .. })
                == !occurrence.row_addresses.is_empty();
            let morphology_shape = occurrence.morphology_current.is_none()
                || matches!(
                    operation.primitive,
                    NativeOperationPrimitive::Scale {
                        by: NativeScaleConstraint::Coefficient
                    }
                );
            row_shape && morphology_shape
        })
    }

    pub fn morphology_factor(&self) -> NativeLocalMorphologyCurrent {
        self.morphology
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
        if self.cycle_complete {
            if self.operation_at != 0 || occurrence.row_addresses.is_empty() {
                return Err(NativeFullOperationError::Occurrence);
            }
            self.carriers.clear();
            self.positions = None;
            self.row_population = None;
            self.terminal_carrier = None;
            self.cycle_complete = false;
        }
        let operation = self
            .ecology
            .operations
            .get(self.operation_at)
            .cloned()
            .ok_or(NativeFullOperationError::Operation)?;
        if occurrence.morphology_current.is_some()
            && !matches!(
                operation.primitive,
                NativeOperationPrimitive::Scale {
                    by: NativeScaleConstraint::Coefficient
                }
            )
        {
            return Err(NativeFullOperationError::Morphology);
        }
        let morphology_before = self.morphology;
        let outcome = match &operation.primitive {
            NativeOperationPrimitive::Lookup { scale } => {
                self.execute_lookup(&operation, &occurrence, scale)?
            }
            NativeOperationPrimitive::Reshape => self.execute_reshape(&operation, &occurrence)?,
            NativeOperationPrimitive::Select { axis, at } => {
                self.execute_select(&operation, &occurrence, *axis, *at)?
            }
            NativeOperationPrimitive::Contract => self.execute_contract(&operation, &occurrence)?,
            NativeOperationPrimitive::RmsRebase {
                group,
                epsilon,
                has_gain,
            } => self.execute_rms(&operation, &occurrence, *group, epsilon, *has_gain)?,
            NativeOperationPrimitive::GeluTanh => self.execute_gelu(&operation, &occurrence)?,
            NativeOperationPrimitive::Tanh => self.execute_tanh(&operation, &occurrence)?,
            NativeOperationPrimitive::Hadamard => {
                self.execute_binary(&operation, &occurrence, false)?
            }
            NativeOperationPrimitive::Add => self.execute_binary(&operation, &occurrence, true)?,
            NativeOperationPrimitive::Scale { by }
                if !matches!(by, NativeScaleConstraint::Coefficient) =>
            {
                self.execute_scale(&operation, &occurrence, by)?
            }
            NativeOperationPrimitive::Scale {
                by: NativeScaleConstraint::Coefficient,
            } => self.execute_coefficient_scale(&operation, &occurrence)?,
            NativeOperationPrimitive::RotaryChronology {
                theta,
                head_width,
                rotated_width,
            } => self.execute_chronology(
                &operation,
                &occurrence,
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
                &operation,
                &occurrence,
                *heads,
                *kv_heads,
                *head_width,
                reach,
                *series_terms,
            )?,
            NativeOperationPrimitive::Emit => self.execute_reshape(&operation, &occurrence)?,
            _ => {
                return Err(NativeFullOperationError::PrimitiveOpen {
                    operation: operation.ordinal,
                });
            }
        };
        let (outcome, first_projection) = self.project_successor(operation.ordinal, outcome)?;
        if let Some(current) = occurrence.morphology_current {
            let input = operation
                .inputs
                .first()
                .and_then(|input| self.carriers.get(input))
                .ok_or(NativeFullOperationError::Morphology)?;
            let presented = self.residence.surface().read_out(&input.section)?;
            if alignment(&presented, &outcome.intervals)? <= BigInt::from(0) {
                return Err(NativeFullOperationError::Morphology);
            }
            self.morphology = self.morphology.compose(current)?;
        }
        let (outcome, morphology_projection) = self.apply_morphology(operation.ordinal, outcome)?;
        let successor_projection = combine_projections(&[first_projection, morphology_projection]);
        let morphology_after = self.morphology;
        let morphology_transition = if morphology_before == morphology_after {
            NativeMorphologyTransition::Unchanged
        } else {
            NativeMorphologyTransition::Changed {
                operation: operation.ordinal,
                before: morphology_before,
                after: morphology_after,
            }
        };
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
                self.carriers.remove(input);
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
                morphology_factor: morphology_after,
                successor_bound_octaves: outcome.bound_octaves,
                resident_coefficient_octets,
                census_before: outcome.census_before,
                census_after: outcome.census_after,
            },
            successor: self,
        })
    }

    /// Complete the mutually-exclusive tiled boundary as the final five operations of the graph.
    /// The engine owns their order; the application receives the five emissions and exact joining
    /// traces but cannot insert a score loop or replace a successor.
    pub fn advance_terminal(
        mut self,
        occurrence: NativeFullOperationOccurrence,
    ) -> Result<NativeFullTerminalBranch<'residence, 'chart>, NativeFullOperationError> {
        let start = self.ecology.operations.len().saturating_sub(5);
        if self.operation_at != start
            || occurrence.ordinal != self.generation
            || !occurrence.row_addresses.is_empty()
            || occurrence.morphology_current.is_some()
        {
            return Err(NativeFullOperationError::Occurrence);
        }
        let operations = self.ecology.operations[start..].to_vec();
        if operations.len() != 5
            || !matches!(operations[0].primitive, NativeOperationPrimitive::Contract)
            || !matches!(
                operations[1].primitive,
                NativeOperationPrimitive::Scale { .. }
            )
            || !matches!(operations[2].primitive, NativeOperationPrimitive::Tanh)
            || !matches!(
                operations[3].primitive,
                NativeOperationPrimitive::Scale { .. }
            )
            || !matches!(operations[4].primitive, NativeOperationPrimitive::Emit)
            || operations
                .windows(2)
                .any(|pair| pair[1].inputs.as_slice() != [pair[0].output])
        {
            return Err(NativeFullOperationError::Operation);
        }
        let mut emissions = Vec::with_capacity(5);
        let mut traces = Vec::with_capacity(5);
        let first = self.execute_tiled_boundary(&operations[0])?;
        let mut carrier =
            self.record_tiled_outcome(operations[0].clone(), first, &mut emissions, &mut traces)?;
        let first_scale = match &operations[1].primitive {
            NativeOperationPrimitive::Scale { by } => scale_enclosure(by)?,
            _ => return Err(NativeFullOperationError::Operation),
        };
        let scaled =
            self.execute_tiled_unary(&operations[1], carrier, TiledUnary::Scale(first_scale))?;
        carrier =
            self.record_tiled_outcome(operations[1].clone(), scaled, &mut emissions, &mut traces)?;
        let reacted = self.execute_tiled_unary(
            &operations[2],
            carrier,
            TiledUnary::Tanh(SeriesAperture(14)),
        )?;
        carrier =
            self.record_tiled_outcome(operations[2].clone(), reacted, &mut emissions, &mut traces)?;
        let second_scale = match &operations[3].primitive {
            NativeOperationPrimitive::Scale { by } => scale_enclosure(by)?,
            _ => return Err(NativeFullOperationError::Operation),
        };
        let scaled =
            self.execute_tiled_unary(&operations[3], carrier, TiledUnary::Scale(second_scale))?;
        carrier =
            self.record_tiled_outcome(operations[3].clone(), scaled, &mut emissions, &mut traces)?;
        let emitted = self.execute_tiled_unary(&operations[4], carrier, TiledUnary::Carry)?;
        carrier =
            self.record_tiled_outcome(operations[4].clone(), emitted, &mut emissions, &mut traces)?;
        self.carriers.clear();
        self.operation_at = 0;
        self.cycle_complete = true;
        self.terminal_carrier = Some(carrier);
        Ok(NativeFullTerminalBranch {
            emissions,
            traces,
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
                morphology_current: None,
            })?;
            traces.push(step.trace);
            self = step.successor;
        }
        let ordinal = self.generation;
        let mut terminal = self.advance_terminal(NativeFullOperationOccurrence {
            ordinal,
            row_addresses: Vec::new(),
            morphology_current: None,
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

    fn execute_tiled_boundary(
        &mut self,
        operation: &NativeOperatorNode,
    ) -> Result<TiledOperationOutcome<'chart>, NativeFullOperationError> {
        if operation.inputs.len() != 1 || operation.coefficients.len() != 1 {
            return Err(NativeFullOperationError::Operation);
        }
        let input = self
            .carriers
            .get(&operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let coefficient = operation.coefficients[0];
        let population = self
            .ecology
            .coefficient_populations
            .get(coefficient.0 as usize)
            .ok_or(NativeFullOperationError::Operation)?;
        let [total_width, dim] = population.shape.as_slice() else {
            return Err(NativeFullOperationError::Operation);
        };
        if input.section.width() != *dim {
            return Err(NativeFullOperationError::Operation);
        }
        let capacity = self.residence.aligned_row_capacity(coefficient)?;
        if capacity == 0 {
            return Err(NativeFullOperationError::Operation);
        }
        let surface = self.residence.surface();
        let census_before = surface.census();
        let mut sections = Vec::new();
        let mut bounds = Vec::new();
        let mut tile_intervals = Vec::new();
        let mut projections = Vec::new();
        let mut first_row = 0usize;
        while first_row < *total_width {
            let rows = (*total_width - first_row).min(capacity);
            let tile = self.residence.align_tile(coefficient, first_row, rows)?;
            let shape = surface.shape_contract(
                input.section.rows(),
                input.section.width(),
                input.bound_octaves,
                &tile.mounted.readout,
            )?;
            let successor =
                surface.fresh_section(input.section.rows(), rows, input.section.grain())?;
            let tile_before = surface.census();
            let mut builder = surface.begin_passage(&[vec![]])?;
            let lane = builder.open(0, &[])?;
            surface.record_contract(&lane, &input.section, &tile.mounted.readout, &successor)?;
            builder.close(0, &successor, shape.needed)?;
            let reading = builder.finish()?.launch()?;
            let bound_octaves = operation_bound(operation.ordinal, &reading)?;
            let intervals = surface.read_out(&successor)?;
            let tile_after = surface.census();
            drop(tile);
            let outcome = OperationOutcome {
                section: successor,
                bound_octaves,
                rows: input.section.rows(),
                width: rows,
                grain: input.section.grain(),
                intervals,
                census_before: tile_before,
                census_after: tile_after,
            };
            let (outcome, projection) = self.project_successor(operation.ordinal, outcome)?;
            let (outcome, morphology_projection) =
                self.apply_morphology(operation.ordinal, outcome)?;
            sections.push(outcome.section);
            bounds.push(outcome.bound_octaves);
            tile_intervals.push(outcome.intervals);
            projections.push(combine_projections(&[projection, morphology_projection]));
            first_row += rows;
        }
        let intervals = stitch_intervals(input.section.rows(), &tile_intervals)?;
        Ok(TiledOperationOutcome {
            carrier: TiledCarrier {
                sections,
                bounds,
                rows: input.section.rows(),
                width: *total_width,
                grain: input.section.grain(),
                carrier: operation.output,
            },
            intervals,
            projection: combine_projections(&projections),
            census_before,
            census_after: surface.census(),
        })
    }

    fn execute_tiled_unary(
        &self,
        operation: &NativeOperatorNode,
        input: TiledCarrier<'chart>,
        primitive: TiledUnary,
    ) -> Result<TiledOperationOutcome<'chart>, NativeFullOperationError> {
        if operation.inputs.as_slice() != [input.carrier] || !operation.coefficients.is_empty() {
            return Err(NativeFullOperationError::Operation);
        }
        let surface = self.residence.surface();
        let census_before = surface.census();
        let mut sections = Vec::with_capacity(input.sections.len());
        let mut bounds = Vec::with_capacity(input.bounds.len());
        let mut tile_intervals = Vec::with_capacity(input.sections.len());
        let mut projections = Vec::with_capacity(input.sections.len());
        for (section, bound) in input.sections.into_iter().zip(input.bounds) {
            let shape = match primitive {
                TiledUnary::Scale(by) => {
                    surface.shape_scale(section.rows(), section.width(), bound, by)?
                }
                TiledUnary::Tanh(terms) => surface.shape_tanh(
                    section.rows(),
                    section.width(),
                    bound,
                    section.grain(),
                    terms,
                )?,
                TiledUnary::Carry => surface.shape_carry(section.rows(), section.width(), bound)?,
            };
            let successor =
                surface.fresh_section(section.rows(), section.width(), section.grain())?;
            let tile_before = surface.census();
            let mut builder = surface.begin_passage(&[vec![]])?;
            let lane = builder.open(0, &[])?;
            match primitive {
                TiledUnary::Scale(by) => surface.record_scale(&lane, &section, by, &successor)?,
                TiledUnary::Tanh(terms) => {
                    surface.record_tanh(&lane, &section, terms, &successor)?
                }
                TiledUnary::Carry => surface.record_carry(&lane, &section, &successor)?,
            }
            builder.close(0, &successor, shape.needed)?;
            let reading = builder.finish()?.launch()?;
            let bound_octaves = operation_bound(operation.ordinal, &reading)?;
            let intervals = surface.read_out(&successor)?;
            let tile_after = surface.census();
            let outcome = OperationOutcome {
                section: successor,
                bound_octaves,
                rows: section.rows(),
                width: section.width(),
                grain: section.grain(),
                intervals,
                census_before: tile_before,
                census_after: tile_after,
            };
            let (outcome, projection) = self.project_successor(operation.ordinal, outcome)?;
            let (outcome, morphology_projection) =
                self.apply_morphology(operation.ordinal, outcome)?;
            sections.push(outcome.section);
            bounds.push(outcome.bound_octaves);
            tile_intervals.push(outcome.intervals);
            projections.push(combine_projections(&[projection, morphology_projection]));
        }
        let intervals = stitch_intervals(input.rows, &tile_intervals)?;
        Ok(TiledOperationOutcome {
            carrier: TiledCarrier {
                sections,
                bounds,
                rows: input.rows,
                width: input.width,
                grain: input.grain,
                carrier: operation.output,
            },
            intervals,
            projection: combine_projections(&projections),
            census_before,
            census_after: surface.census(),
        })
    }

    fn record_tiled_outcome(
        &mut self,
        operation: NativeOperatorNode,
        outcome: TiledOperationOutcome<'chart>,
        emissions: &mut Vec<NativeFullOperationEmission>,
        traces: &mut Vec<NativeFullOperationTrace>,
    ) -> Result<TiledCarrier<'chart>, NativeFullOperationError> {
        let predecessor_generation = self.generation;
        let successor_generation = predecessor_generation
            .checked_add(1)
            .ok_or(NativeFullOperationError::Generation)?;
        let bound = outcome.carrier.bounds.iter().copied().max().unwrap_or(1);
        emissions.push(NativeFullOperationEmission {
            generation: successor_generation,
            operation: operation.ordinal,
            carrier: operation.output,
            rows: outcome.carrier.rows,
            width: outcome.carrier.width,
            grain: outcome.carrier.grain.0,
            intervals: outcome.intervals,
        });
        traces.push(NativeFullOperationTrace {
            schema: NATIVE_FULL_OPERATION_STEP_SCHEMA.to_owned(),
            predecessor_generation,
            successor_generation,
            occurrence: predecessor_generation,
            row_addresses: Vec::new(),
            operation,
            successor_projection: outcome.projection,
            morphology_transition: NativeMorphologyTransition::Unchanged,
            morphology_factor: self.morphology,
            successor_bound_octaves: bound,
            resident_coefficient_octets: self.residence.receipt().raw_coefficient_octets,
            census_before: outcome.census_before,
            census_after: outcome.census_after,
        });
        self.chronology.push(predecessor_generation);
        self.generation = successor_generation;
        self.operation_at += 1;
        Ok(outcome.carrier)
    }

    fn apply_morphology(
        &self,
        operation: u32,
        outcome: OperationOutcome<'chart>,
    ) -> Result<(OperationOutcome<'chart>, NativeSuccessorProjection), NativeFullOperationError>
    {
        if self.morphology == NativeLocalMorphologyCurrent::IDENTITY {
            return Ok((outcome, NativeSuccessorProjection::Exact));
        }
        let surface = self.residence.surface();
        let by = self.morphology.enclosure()?;
        let shape = surface.shape_scale(outcome.rows, outcome.width, outcome.bound_octaves, by)?;
        let successor = surface.fresh_section(outcome.rows, outcome.width, outcome.grain)?;
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_scale(&lane, &outcome.section, by, &successor)?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation, &reading)?;
        let intervals = surface.read_out(&successor)?;
        let scaled = OperationOutcome {
            section: successor,
            bound_octaves,
            rows: outcome.rows,
            width: outcome.width,
            grain: outcome.grain,
            intervals,
            census_before: outcome.census_before,
            census_after: surface.census(),
        };
        self.project_successor(operation, scaled)
    }

    fn project_successor(
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
        let input = self
            .carriers
            .get(&operation.inputs[0])
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
        let input = self
            .carriers
            .get(&operation.inputs[0])
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
        let tile = self.residence.align_tile(coefficient, 0, *rows)?;
        let shape = surface.shape_contract(
            input.section.rows(),
            input.section.width(),
            input.bound_octaves,
            &tile.mounted.readout,
        )?;
        let successor = surface.fresh_section(
            input.section.rows(),
            tile.mounted.readout.rows(),
            input.section.grain(),
        )?;
        let census_before = surface.census();
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_contract(&lane, &input.section, &tile.mounted.readout, &successor)?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
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
        let input = self
            .carriers
            .get(&operation.inputs[0])
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
        let input = self
            .carriers
            .get(&operation.inputs[0])
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
        let input = self
            .carriers
            .get(&operation.inputs[0])
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
        let left = self
            .carriers
            .get(&operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let right = self
            .carriers
            .get(&operation.inputs[1])
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
        let input = self
            .carriers
            .get(&operation.inputs[0])
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
        let input = self
            .carriers
            .get(&operation.inputs[0])
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
        let input = self
            .carriers
            .get(&operation.inputs[0])
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
        let q = self
            .carriers
            .get(&operation.inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let k = self
            .carriers
            .get(&operation.inputs[1])
            .ok_or(NativeFullOperationError::Carrier)?;
        let v = self
            .carriers
            .get(&operation.inputs[2])
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
        let input = self
            .carriers
            .get(&operation.inputs[0])
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

fn stitch_intervals(
    rows: usize,
    tiles: &[Vec<(i64, i64)>],
) -> Result<Vec<(i64, i64)>, NativeFullOperationError> {
    if rows == 0
        || tiles.is_empty()
        || tiles
            .iter()
            .any(|tile| tile.is_empty() || tile.len() % rows != 0)
    {
        return Err(NativeFullOperationError::Operation);
    }
    let width = tiles.iter().map(|tile| tile.len() / rows).sum::<usize>();
    let mut stitched = Vec::with_capacity(rows * width);
    for row in 0..rows {
        for tile in tiles {
            let tile_width = tile.len() / rows;
            stitched.extend_from_slice(&tile[row * tile_width..(row + 1) * tile_width]);
        }
    }
    Ok(stitched)
}

fn alignment(
    presented: &[(i64, i64)],
    reacted: &[(i64, i64)],
) -> Result<BigInt, NativeFullOperationError> {
    if presented.is_empty() || presented.len() != reacted.len() {
        return Err(NativeFullOperationError::Morphology);
    }
    Ok(presented
        .iter()
        .zip(reacted)
        .fold(BigInt::from(0), |sum, ((pl, ph), (rl, rh))| {
            let presented_center_twice = BigInt::from(*pl) + BigInt::from(*ph);
            let reacted_center_twice = BigInt::from(*rl) + BigInt::from(*rh);
            sum + presented_center_twice * reacted_center_twice
        }))
}

fn combine_projections(projections: &[NativeSuccessorProjection]) -> NativeSuccessorProjection {
    let mut nonpoint_coordinates = 0usize;
    let mut widest_interval = 0u64;
    for projection in projections {
        if let NativeSuccessorProjection::Midpoint {
            nonpoint_coordinates: count,
            widest_interval: widest,
        } = projection
        {
            nonpoint_coordinates += count;
            widest_interval = widest_interval.max(*widest);
        }
    }
    if nonpoint_coordinates == 0 {
        NativeSuccessorProjection::Exact
    } else {
        NativeSuccessorProjection::Midpoint {
            nonpoint_coordinates,
            widest_interval,
        }
    }
}

fn binary64_projection(value: &Rat) -> Result<Dyadic, NativeFullOperationError> {
    let (datum, _) = round_into(value, BinaryFloatSpecies::Binary64)
        .map_err(|_| NativeFullOperationError::Operation)?;
    let magnitude =
        i64::try_from(&datum.significand).map_err(|_| NativeFullOperationError::Operation)?;
    Ok(Dyadic {
        significand: if datum.negative {
            -magnitude
        } else {
            magnitude
        },
        exponent: datum.ulp_exponent,
    })
}

fn scale_enclosure(
    constraint: &NativeScaleConstraint,
) -> Result<DyadicEnclosure, NativeFullOperationError> {
    let interval = match constraint {
        NativeScaleConstraint::ReciprocalSquareRootOf(value) if *value > 0 => {
            AlgebraicRoot::nth_root(&Rat::from_integer(BigInt::from(*value)), 2, 64)
                .map_err(|_| NativeFullOperationError::Operation)?
                .enclosure()
                .reciprocal()
                .map_err(|_| NativeFullOperationError::Operation)?
        }
        NativeScaleConstraint::Rational {
            numerator,
            denominator,
        } if *denominator > 0 => ExactInterval::point(Rat::new(
            BigInt::from(*numerator),
            BigInt::from(*denominator),
        )),
        _ => return Err(NativeFullOperationError::Operation),
    };
    finest_enclosure(&interval)
}

fn finest_enclosure(interval: &ExactInterval) -> Result<DyadicEnclosure, NativeFullOperationError> {
    for grain in (0..=60).rev() {
        if let Ok(enclosure) = DyadicEnclosure::of_interval(&interval, grain) {
            return Ok(enclosure);
        }
    }
    Err(NativeFullOperationError::Operation)
}

fn projected_scale(constraint: &NativeScaleConstraint) -> Result<Dyadic, NativeFullOperationError> {
    let NativeScaleConstraint::Bfloat16NearestSquareRootOf(value) = constraint else {
        return Err(NativeFullOperationError::Operation);
    };
    nearest_bfloat16_square_root(*value)
}

fn nearest_bfloat16_square_root(value: u32) -> Result<Dyadic, NativeFullOperationError> {
    if value == 0 {
        return Ok(Dyadic {
            significand: 0,
            exponent: 0,
        });
    }
    let target = Rat::from_integer(BigInt::from(value));
    let mut low_word = 0u16;
    let mut high_word = 0x7f7fu16;
    while low_word + 1 < high_word {
        let middle = low_word + (high_word - low_word) / 2;
        let middle_value = decode_bfloat16_bits(middle)
            .map_err(|_| NativeFullOperationError::Operation)?
            .value();
        if &middle_value * &middle_value <= target {
            low_word = middle;
        } else {
            high_word = middle;
        }
    }
    let low = decode_bfloat16_bits(low_word)
        .map_err(|_| NativeFullOperationError::Operation)?
        .value();
    let high = decode_bfloat16_bits(high_word)
        .map_err(|_| NativeFullOperationError::Operation)?
        .value();
    let midpoint = (&low + &high) / Rat::from_integer(BigInt::from(2));
    let word = if &midpoint * &midpoint < target {
        high_word
    } else if &midpoint * &midpoint > target || low_word & 1 == 0 {
        low_word
    } else {
        high_word
    };
    Dyadic::of_bfloat16_bits(word).map_err(NativeFullOperationError::Resident)
}

fn operation_bound(
    operation: u32,
    reading: &crate::resident_section::PassageReading,
) -> Result<u32, NativeFullOperationError> {
    exact_bound(reading)
        .map_err(|flags| NativeFullOperationError::ResidentObstruction { operation, flags })
}

fn exact_bound(reading: &crate::resident_section::PassageReading) -> Result<u32, u32> {
    if !reading.obstruction.is_empty() {
        return Err(reading.obstruction.joined_flags());
    }
    Ok(reading
        .slots
        .last()
        .map(|slot| slot.max_octave.max(1))
        .unwrap_or(1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_morphology_requires_positive_exact_conductance_and_composes() {
        let two = NativeLocalMorphologyCurrent {
            significand: 2,
            exponent: 0,
        };
        assert_eq!(
            NativeLocalMorphologyCurrent::IDENTITY
                .compose(two)
                .expect("positive current"),
            two
        );
        assert!(
            NativeLocalMorphologyCurrent {
                significand: 0,
                exponent: 0
            }
            .validate()
            .is_err()
        );
    }

    #[test]
    fn presented_reacted_alignment_is_exact_and_can_refuse() {
        assert!(alignment(&[(1, 1), (2, 2)], &[(3, 3), (4, 4)]).unwrap() > BigInt::from(0));
        assert!(alignment(&[(1, 1)], &[(-1, -1)]).unwrap() < BigInt::from(0));
    }

    #[test]
    fn tiled_faces_stitch_in_row_major_order() {
        let left = vec![(1, 1), (2, 2), (5, 5), (6, 6)];
        let right = vec![(3, 3), (4, 4), (7, 7), (8, 8)];
        assert_eq!(
            stitch_intervals(2, &[left, right]).unwrap(),
            vec![
                (1, 1),
                (2, 2),
                (3, 3),
                (4, 4),
                (5, 5),
                (6, 6),
                (7, 7),
                (8, 8),
            ]
        );
    }
}
