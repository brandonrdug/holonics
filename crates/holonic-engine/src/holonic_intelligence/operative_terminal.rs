//! The tiled terminal boundary of the recurrent operator: the tied contraction over the
//! sixteen vocabulary tiles, the soft-cap reactions, and the emission.  The engine owns their
//! order; an application receives the emissions and exact traces and cannot insert a score loop
//! or replace a successor.  The boundary is one owner so the ordinary cycle and a counterfactual
//! forward under an intervention enact the same tiles.

use crate::resident_section::{DyadicEnclosure, ResidentGrain, ResidentSection, SeriesAperture, TransferCensus};

use super::{
    NATIVE_FULL_OPERATION_STEP_SCHEMA, NativeCarrierOrdinal, NativeFullOperationEmission,
    NativeFullOperationError, NativeFullOperationOccurrence, NativeFullOperationTrace,
    NativeFullOperatorSession, NativeFullTerminalBranch, NativeMorphologyTransition,
    NativeOperationPrimitive, NativeOperatorNode, NativeSuccessorProjection,
    full_operation::{OperationOutcome, carrier_of},
    operative_return::contract_tile_with_overlay,
    operative_scalars::{operation_bound, scale_enclosure},
};

pub(super) struct TiledCarrier<'chart> {
    pub(super) sections: Vec<ResidentSection<'chart>>,
    pub(super) bounds: Vec<u32>,
    pub(super) rows: usize,
    pub(super) width: usize,
    pub(super) grain: ResidentGrain,
    pub(super) carrier: NativeCarrierOrdinal,
}

pub(super) struct TiledOperationOutcome<'chart> {
    pub(super) carrier: TiledCarrier<'chart>,
    pub(super) intervals: Vec<(i64, i64)>,
    pub(super) projection: NativeSuccessorProjection,
    pub(super) census_before: TransferCensus,
    pub(super) census_after: TransferCensus,
}

#[derive(Clone, Copy)]
pub(super) enum TiledUnary {
    Scale(DyadicEnclosure),
    Tanh(SeriesAperture),
    Carry,
}

impl<'residence, 'chart> NativeFullOperatorSession<'residence, 'chart> {
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
        let contracted =
            self.record_tiled_outcome(operations[0].clone(), first, &mut emissions, &mut traces)?;
        let first_scale = match &operations[1].primitive {
            NativeOperationPrimitive::Scale { by } => scale_enclosure(by)?,
            _ => return Err(NativeFullOperationError::Operation),
        };
        let scaled =
            self.execute_tiled_unary(&operations[1], &contracted, TiledUnary::Scale(first_scale))?;
        if self.dissection.is_some() {
            // The last row alone, read to the host: the excitation's contribution at the
            // vocabulary sites reads it, and the tiles need not stay resident.
            self.terminal_contracted = Some(self.tiled_last_row(&contracted)?);
        }
        drop(contracted);
        let scaled_carrier =
            self.record_tiled_outcome(operations[1].clone(), scaled, &mut emissions, &mut traces)?;
        let reacted = self.execute_tiled_unary(
            &operations[2],
            &scaled_carrier,
            TiledUnary::Tanh(SeriesAperture(14)),
        )?;
        drop(scaled_carrier);
        let reacted_carrier =
            self.record_tiled_outcome(operations[2].clone(), reacted, &mut emissions, &mut traces)?;
        let second_scale = match &operations[3].primitive {
            NativeOperationPrimitive::Scale { by } => scale_enclosure(by)?,
            _ => return Err(NativeFullOperationError::Operation),
        };
        let scaled_back = self.execute_tiled_unary(
            &operations[3],
            &reacted_carrier,
            TiledUnary::Scale(second_scale),
        )?;
        let scaled_back_carrier = self.record_tiled_outcome(
            operations[3].clone(),
            scaled_back,
            &mut emissions,
            &mut traces,
        )?;
        let emitted =
            self.execute_tiled_unary(&operations[4], &scaled_back_carrier, TiledUnary::Carry)?;
        drop(scaled_back_carrier);
        let emitted_carrier =
            self.record_tiled_outcome(operations[4].clone(), emitted, &mut emissions, &mut traces)?;
        // The carrier presented to the tied contraction and the reacted carrier stay with the
        // successor when a return is declared: they are what the next occurrence meets.
        let presented = self.carriers.remove(&operations[0].inputs[0]);
        self.carriers.clear();
        self.operation_at = 0;
        self.cycle_complete = true;
        self.terminal_carrier = Some(emitted_carrier);
        if self.aperture.is_some() || self.dissection.is_some() {
            self.terminal_reacted = Some(reacted_carrier);
            self.terminal_presented = presented;
        } else {
            self.terminal_reacted = None;
            self.terminal_presented = None;
            self.checkpoints.clear();
        }
        Ok(NativeFullTerminalBranch {
            emissions,
            traces,
            successor: self,
        })
    }

    pub(super) fn execute_tiled_boundary(
        &mut self,
        operation: &NativeOperatorNode,
    ) -> Result<TiledOperationOutcome<'chart>, NativeFullOperationError> {
        if operation.inputs.len() != 1 || operation.coefficients.len() != 1 {
            return Err(NativeFullOperationError::Operation);
        }
        let input = carrier_of(&self.carriers, &self.checkpoints, &operation.inputs[0])
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
            let atoms = self.overlay.get(&coefficient).map(Vec::as_slice).unwrap_or(&[]);
            let tile = self.residence.align_tile(coefficient, first_row, rows)?;
            let tile_before = surface.census();
            let (joined, reading) = contract_tile_with_overlay(
                surface,
                &input.section,
                input.bound_octaves,
                &tile.mounted.readout,
                atoms,
                first_row,
                rows,
            )?;
            let bound_octaves = operation_bound(operation.ordinal, &reading)?;
            let intervals = surface.read_out(&joined)?;
            let tile_after = surface.census();
            drop(tile);
            let outcome = OperationOutcome {
                section: joined,
                bound_octaves,
                rows: input.section.rows(),
                width: rows,
                grain: input.section.grain(),
                intervals,
                census_before: tile_before,
                census_after: tile_after,
            };
            let (outcome, projection) = self.project_successor(operation.ordinal, outcome)?;
            sections.push(outcome.section);
            bounds.push(outcome.bound_octaves);
            tile_intervals.push(outcome.intervals);
            projections.push(projection);
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

    pub(super) fn execute_tiled_unary(
        &self,
        operation: &NativeOperatorNode,
        input: &TiledCarrier<'chart>,
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
        for (section, bound) in input.sections.iter().zip(input.bounds.iter().copied()) {
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
                TiledUnary::Scale(by) => surface.record_scale(&lane, section, by, &successor)?,
                TiledUnary::Tanh(terms) => {
                    surface.record_tanh(&lane, section, terms, &successor)?
                }
                TiledUnary::Carry => surface.record_carry(&lane, section, &successor)?,
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
            sections.push(outcome.section);
            bounds.push(outcome.bound_octaves);
            tile_intervals.push(outcome.intervals);
            projections.push(projection);
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
            morphology_overlay_rank: self.morphology_overlay_rank(),
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
}

pub(super) fn stitch_intervals(
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

#[cfg(test)]
mod tests {
    use super::*;

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
