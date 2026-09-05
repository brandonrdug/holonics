//! The tiled terminal boundary of the recurrent operator: the tied contraction over the
//! vocabulary tiles, the soft-cap reactions, and the emission.  The engine owns their order; an
//! application receives the emissions and traces and cannot insert a score loop or replace a
//! successor.  Each tile is one segment, one passage: the contraction, its seal, the two scales,
//! the reaction and its seal, and the carry, bound whole and launched once; the emitted tiles are
//! read out once, as the terminal face at the declared receiver.

use std::collections::BTreeMap;

use crate::resident_section::{ResidentGrain, ResidentSection, TransferCensus};

use super::{
    NATIVE_FULL_OPERATION_STEP_SCHEMA, NativeCarrierOrdinal, NativeFullOperationEmission,
    NativeFullOperationError, NativeFullOperationOccurrence, NativeFullOperationTrace,
    NativeFullOperatorSession, NativeFullTerminalBranch, NativeMorphologyTransition,
    NativeOperationPrimitive, NativeOperatorNode, NativeSuccessorProjection,
    full_operation::carrier_of,
    operative_segment::{SegmentSite, SegmentWithdrawal, enact_segment},
};

pub(super) struct TiledCarrier<'chart> {
    pub(super) sections: Vec<ResidentSection<'chart>>,
    pub(super) bounds: Vec<u32>,
    pub(super) rows: usize,
    pub(super) width: usize,
    pub(super) grain: ResidentGrain,
    pub(super) carrier: NativeCarrierOrdinal,
}

/// The five terminal operations enacted tile by tile: every tile's sections per operation, the
/// projections and bounds per operation joined over the tiles, and the census of the run.
pub(super) struct TerminalRun<'chart> {
    /// One tiled carrier per retained operation; an operation not retained is released tile by
    /// tile as soon as its consumer in the same passage has read it.
    pub(super) carriers: Vec<Option<TiledCarrier<'chart>>>,
    pub(super) projections: Vec<NativeSuccessorProjection>,
    pub(super) admitted: Vec<u32>,
    /// The measured bound of each operation's carrier, joined over the tiles.
    pub(super) bounds: Vec<u32>,
    pub(super) rows: usize,
    pub(super) width: usize,
    pub(super) grain: ResidentGrain,
    pub(super) census_before: TransferCensus,
    pub(super) census_after: TransferCensus,
}

impl<'residence, 'chart> NativeFullOperatorSession<'residence, 'chart> {
    /// The terminal boundary's five operations, in the engine's order.
    pub(super) fn terminal_operations(&self) -> Result<Vec<NativeOperatorNode>, NativeFullOperationError> {
        let start = self.ecology.operations.len().saturating_sub(5);
        let operations = self.ecology.operations[start..].to_vec();
        if operations.len() != 5
            || !matches!(operations[0].primitive, NativeOperationPrimitive::Contract)
            || !matches!(operations[1].primitive, NativeOperationPrimitive::Scale { .. })
            || !matches!(operations[2].primitive, NativeOperationPrimitive::Tanh)
            || !matches!(operations[3].primitive, NativeOperationPrimitive::Scale { .. })
            || !matches!(operations[4].primitive, NativeOperationPrimitive::Emit)
            || operations
                .windows(2)
                .any(|pair| pair[1].inputs.as_slice() != [pair[0].output])
        {
            return Err(NativeFullOperationError::Operation);
        }
        Ok(operations)
    }

    /// Enact the terminal boundary tile by tile on the contemporary carriers, each tile one
    /// passage.  `tied_withdrawal` intervenes on the tied contraction's output at the sites the
    /// mask names, offset by each tile's first row.
    pub(super) fn enact_terminal(
        &self,
        operations: &[NativeOperatorNode],
        tied_withdrawal: Option<&SegmentWithdrawal<'_, 'chart>>,
        retain: [bool; 5],
    ) -> Result<TerminalRun<'chart>, NativeFullOperationError> {
        let input = carrier_of(&self.carriers, &self.checkpoints, &operations[0].inputs[0])
            .ok_or(NativeFullOperationError::Carrier)?;
        let coefficient = operations[0].coefficients[0];
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
        let rows = input.section.rows();
        let grain = input.section.grain();
        let mut per_operation: Vec<Vec<ResidentSection<'chart>>> = (0..5).map(|_| Vec::new()).collect();
        let mut per_bounds: Vec<Vec<u32>> = (0..5).map(|_| Vec::new()).collect();
        let mut projections: Vec<(usize, u64)> = vec![(0, 0); 5];
        let mut admitted = vec![0u32; 5];
        let mut census_before = None;
        let mut census_after = self.residence.surface().census();
        let mut first_row = 0usize;
        while first_row < *total_width {
            let tile_rows = (*total_width - first_row).min(capacity);
            let withdrawals: BTreeMap<u32, SegmentWithdrawal<'_, 'chart>> = match tied_withdrawal {
                Some(withdrawal) => BTreeMap::from([(
                    operations[0].ordinal,
                    SegmentWithdrawal {
                        mask: withdrawal.mask,
                        offset: withdrawal.offset + first_row,
                    },
                )]),
                None => BTreeMap::new(),
            };
            // A tile is one passage: the five operations bound whole.  Should a later tile
            // operation's obligation exceed the a-priori bounds, the tile continues in a second
            // passage on the measured bounds; the tile's sections stay resident between them.
            let mut tile_carriers: BTreeMap<_, _> = BTreeMap::new();
            let mut outcomes = Vec::with_capacity(5);
            let mut cursor = 0usize;
            while cursor < operations.len() {
                let (produced, reading) = {
                    let carriers = if cursor == 0 { &self.carriers } else { &tile_carriers };
                    let site = SegmentSite {
                        residence: self.residence,
                        ecology: self.ecology,
                        carriers,
                        checkpoints: &self.checkpoints,
                        positions: self.positions.as_ref(),
                        overlay: &self.overlay,
                        grain: self.grain,
                        row_addresses: &[],
                        withdrawals: &withdrawals,
                        tile_window: Some((first_row, tile_rows)),
                        seal: self.terminal_seal,
                    };
                    enact_segment(&site, &operations[cursor..])?
                };
                if produced.is_empty() {
                    return Err(NativeFullOperationError::Operation);
                }
                if census_before.is_none() {
                    census_before = Some(reading.census_before.clone());
                }
                census_after = reading.census_after.clone();
                cursor += produced.len();
                for outcome in produced {
                    outcomes.push((outcome.output, outcome.admitted_octaves, outcome.projection));
                    tile_carriers.insert(outcome.output, outcome.carrier);
                }
            }
            for (at, (output, admitted_octaves, projection)) in outcomes.into_iter().enumerate() {
                if let NativeSuccessorProjection::Midpoint {
                    nonpoint_coordinates,
                    widest_interval,
                } = projection
                {
                    projections[at].0 += nonpoint_coordinates;
                    projections[at].1 = projections[at].1.max(widest_interval);
                }
                admitted[at] = admitted[at].max(admitted_octaves);
                let carrier = tile_carriers
                    .remove(&output)
                    .ok_or(NativeFullOperationError::Carrier)?;
                per_bounds[at].push(carrier.bound_octaves);
                if retain[at] {
                    per_operation[at].push(carrier.section);
                }
            }
            first_row += tile_rows;
        }
        let bounds: Vec<u32> = per_bounds.iter().map(|b| b.iter().copied().max().unwrap_or(1)).collect();
        let carriers = per_operation
            .into_iter()
            .zip(per_bounds)
            .zip(operations)
            .zip(retain)
            .map(|(((sections, bounds), operation), retained)| {
                retained.then_some(TiledCarrier {
                    sections,
                    bounds,
                    rows,
                    width: *total_width,
                    grain,
                    carrier: operation.output,
                })
            })
            .collect();
        Ok(TerminalRun {
            carriers,
            bounds,
            rows,
            width: *total_width,
            grain,
            projections: projections
                .into_iter()
                .map(|(nonpoint_coordinates, widest_interval)| {
                    if nonpoint_coordinates == 0 {
                        NativeSuccessorProjection::Exact
                    } else {
                        NativeSuccessorProjection::Midpoint {
                            nonpoint_coordinates,
                            widest_interval,
                        }
                    }
                })
                .collect(),
            admitted,
            census_before: census_before.unwrap_or_else(|| census_after.clone()),
            census_after,
        })
    }

    /// Complete the mutually-exclusive tiled boundary as the final five operations of the graph.
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
        let operations = self.terminal_operations()?;
        let dissecting = self.dissection.is_some();
        let returning = self.aperture.is_some() || dissecting;
        let mut run = loop {
            match self.enact_terminal(&operations, None, [dissecting, false, returning, false, true]) {
                Ok(run) => break run,
                Err(error) if super::full_operation::allocation_refusal(&error)
                    && self.forward_reuse.as_mut().is_some_and(|reuse| reuse.relieve_pressure()) => {},
                Err(error) => return Err(error),
            }
        };
        let mut emissions = Vec::with_capacity(5);
        let mut traces = Vec::with_capacity(5);
        let emitted_intervals = {
            let emitted = run
                .carriers
                .last()
                .and_then(Option::as_ref)
                .ok_or(NativeFullOperationError::Operation)?;
            let tiles = emitted
                .sections
                .iter()
                .map(|section| self.residence.surface().read_out(section))
                .collect::<Result<Vec<_>, _>>()?;
            stitch_intervals(emitted.rows, &tiles)?
        };
        for (at, operation) in operations.iter().enumerate() {
            let predecessor_generation = self.generation;
            let successor_generation = predecessor_generation
                .checked_add(1)
                .ok_or(NativeFullOperationError::Generation)?;
            let (rows, width, grain, bound) = match &run.carriers[at] {
                Some(carrier) => (
                    carrier.rows,
                    carrier.width,
                    carrier.grain.0,
                    carrier.bounds.iter().copied().max().unwrap_or(1),
                ),
                None => (run.rows, run.width, run.grain.0, run.bounds[at]),
            };
            emissions.push(NativeFullOperationEmission {
                generation: successor_generation,
                operation: operation.ordinal,
                carrier: operation.output,
                rows,
                width,
                grain,
                intervals: if at == 4 { emitted_intervals.clone() } else { Vec::new() },
            });
            traces.push(NativeFullOperationTrace {
                schema: NATIVE_FULL_OPERATION_STEP_SCHEMA.to_owned(),
                predecessor_generation,
                successor_generation,
                occurrence: predecessor_generation,
                row_addresses: Vec::new(),
                operation: operation.clone(),
                successor_projection: run.projections[at].clone(),
                morphology_transition: NativeMorphologyTransition::Unchanged,
                morphology_overlay_rank: self.morphology_overlay_rank(),
                admitted_octaves: run.admitted[at],
                successor_bound_octaves: bound,
                numerical_origin: None,
                resident_coefficient_octets: self.residence.receipt().raw_coefficient_octets,
                census_before: run.census_before.clone(),
                census_after: run.census_after.clone(),
            });
            self.chronology.push(predecessor_generation);
            self.generation = successor_generation;
            self.operation_at += 1;
        }
        // The carrier presented to the tied contraction, the reacted carrier, and the tied
        // contraction's own row stay with the successor when a return or a dissection is
        // declared: they are what the next occurrence meets.
        let presented = self.carriers.remove(&operations[0].inputs[0]);
        if let Some(reuse) = &mut self.forward_reuse {
            for (output, carrier) in std::mem::take(&mut self.carriers) { reuse.retain(output, carrier); }
        } else { self.carriers.clear(); }
        self.operation_at = 0;
        self.cycle_complete = true;
        let emitted = run
            .carriers
            .pop()
            .flatten()
            .ok_or(NativeFullOperationError::Operation)?;
        let _scaled_back = run.carriers.pop();
        let reacted = run.carriers.pop().flatten();
        let _scaled = run.carriers.pop();
        let contracted = run.carriers.pop().flatten();
        self.terminal_carrier = Some(emitted);
        if returning {
            self.terminal_reacted = Some(reacted.ok_or(NativeFullOperationError::Operation)?);
            self.terminal_presented = presented;
        } else {
            self.terminal_reacted = None;
            self.terminal_presented = None;
            if let Some(reuse) = &mut self.forward_reuse {
                if let Some(presented) = presented { reuse.retain(operations[0].inputs[0], presented); }
                for (output, carrier) in std::mem::take(&mut self.checkpoints) { reuse.retain(output, carrier); }
            } else { self.checkpoints.clear(); }
        }
        if dissecting {
            let contracted = contracted.ok_or(NativeFullOperationError::Operation)?;
            self.terminal_contracted = Some(self.tiled_last_row(&contracted)?);
        }
        Ok(NativeFullTerminalBranch {
            emissions,
            traces,
            successor: self,
        })
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tiled_faces_stitch_in_row_major_order() {
        let left = vec![(1, 1), (2, 2), (5, 5), (6, 6)];
        let right = vec![(3, 3), (4, 4), (7, 7), (8, 8)];
        assert_eq!(
            stitch_intervals(2, &[left, right]).unwrap(),
            vec![(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)]
        );
    }
}
