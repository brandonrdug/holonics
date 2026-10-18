//! One joined receiving direction, with two independent normal-law metrics.
//!
//! Carry receipt indices use joined NORMALIZED INTERNAL coordinates: map entries
//! are row-major in the concatenation, and Gram entries occupy diagonal blocks
//! of the full square. They are not residuals expressed in physical operand units.
//! The owner retains the operand scales needed to interpret each block's reading.
use super::receiving_material::ReceivingMaterial;
use super::*;

/// Certificate inputs for the physical joined direction. There is no joined law.
pub(super) struct JoinedReceivingDirection {
    pub(super) unit: IntegralMatrix,
    pub(super) alignment: Rat,
    pub(super) moves: Rat,
    pub(super) covector: Rat,
    pub(super) unit_norms: (Rat, Rat),
}

pub(super) struct PreparedReceivingBlocks {
    owner: ReceivingMaterial,
    samples: Vec<Sample>,
    blocks: [Option<PreparedStep>; 2],
    direction: JoinedReceivingDirection,
}

/// Execute against one block's local receipt indices, then merge them disjointly.
/// Staging affects subsequent rounding, so remapping is arithmetic, not decoration.
fn block_stroke<T>(
    at: &mut BudgetedCarry,
    rows: usize,
    width: usize,
    block: usize,
    work: impl FnOnce(&mut BudgetedCarry) -> Result<T, HnnError>,
) -> Result<T, HnnError> {
    let full = width.checked_mul(2).ok_or(HnnError::CountOverflow)?;
    let offset = block.checked_mul(width).ok_or(HnnError::CountOverflow)?;
    if width == 0 || block >= 2 {
        return Err(HnnError::CountOverflow);
    }
    full.checked_mul(full).ok_or(HnnError::CountOverflow)?;
    rows.checked_mul(full).ok_or(HnnError::CountOverflow)?;
    let local_index = |carrier: Carrier, index: usize| -> Option<usize> {
        let (r, c) = (index / full, index % full);
        if c < offset || c >= offset + width {
            return None;
        }
        match carrier {
            Carrier::Map if r < rows => Some(r * width + c - offset),
            Carrier::Gram if r >= offset && r < offset + width => {
                Some((r - offset) * width + c - offset)
            }
            _ => None,
        }
    };
    let mut local = BudgetedCarry::new(at.lattice, at.clock);
    for (&(carrier, index), staged) in &at.staged {
        if let Some(index) = local_index(carrier, index) {
            local.staged.insert((carrier, index), staged.clone());
        }
    }
    let result = work(&mut local)?;
    let mut remapped = Vec::with_capacity(local.staged.len());
    for ((carrier, index), staged) in local.staged {
        let (r, c) = (index / width, index % width);
        let joined = match carrier {
            Carrier::Map if r < rows => r * full + offset + c,
            Carrier::Gram if r < width => (offset + r) * full + offset + c,
            _ => {
                return Err(HnnError::Unadmitted {
                    reason: "a receiving block stages only its own map and Gram",
                });
            }
        };
        remapped.push(((carrier, joined), staged));
    }
    at.staged
        .retain(|&(carrier, index), _| local_index(carrier, index).is_none());
    at.staged.extend(remapped);
    at.moved |= local.moved;
    at.backtracks.extend(local.backtracks);
    Ok(result)
}

fn joined_integral(rows: &[Vec<Rat>]) -> IntegralMatrix {
    let m = rows.len();
    let n = rows.first().map_or(0, Vec::len);
    let terms: Vec<(Rat, Chart, Chart)> = rows
        .iter()
        .enumerate()
        .map(|(i, row)| {
            let mut basis = vec![Rat::zero(); m];
            basis[i] = Rat::one();
            (Rat::one(), integral(&basis), integral(row))
        })
        .collect();
    outer_integral(
        m,
        n,
        &terms.iter().map(|(w, l, r)| (w, l, r)).collect::<Vec<_>>(),
    )
}

impl PreparedReceivingBlocks {
    /// Prepare both metrics on the same physical comparison, without publishing.
    /// On failure neither the owner nor the caller's receipt is changed.
    pub(super) fn prepare(
        material: &ReceivingMaterial,
        samples: &[Sample],
        rule: &ChartRule,
        at: &mut BudgetedCarry,
    ) -> Result<Option<Self>, HnnError> {
        material.validate()?;
        let mut owner = material.clone();
        if owner.blocks().is_none() {
            return Err(HnnError::Unadmitted {
                reason: "joined preparation requires arrival-context material",
            });
        }
        for sample in samples {
            if sample.weight.is_negative()
                || sample.feature.len() != owner.map().columns()
                || sample.covector.len() != owner.map().rows()
            {
                return Err(HnnError::Unadmitted {
                    reason: "joined receiving samples have their physical shape and nonnegative weight",
                });
            }
            if !sample.weight.is_zero() {
                owner.found_operand_charts(&sample.feature)?;
            }
        }
        // Zero-weight operands cannot found a block or contribute phase evidence.
        let active: Vec<Sample> = samples
            .iter()
            .filter(|s| !s.weight.is_zero())
            .cloned()
            .collect();
        let samples = active.as_slice();
        let metric = receiving_metric_samples(samples);
        let metric_samples = metric.as_deref().unwrap_or(samples);
        let (rows, width) = (owner.map().rows(), owner.blocks().unwrap()[0].width());
        let mut staged = at.clone();
        let mut blocks: [Option<PreparedStep>; 2] = [None, None];
        let mut directions = Vec::with_capacity(2);
        for index in 0..2 {
            let block = &owner.blocks().unwrap()[index];
            if block.chart().is_some() {
                let raw = owner.block_samples(index, samples)?;
                let metric = owner.block_samples(index, metric_samples)?;
                blocks[index] = block_stroke(&mut staged, rows, width, index, |local| {
                    block
                        .law()
                        .prepare_receiving_window(&raw, &metric, rule, local)
                })?;
            }
            directions.push(match &blocks[index] {
                Some(prepared) => block.prepared_physical_direction(prepared)?,
                None => ExactRatMatrix::zero(rows, width)?,
            });
        }
        if blocks.iter().all(Option::is_none) {
            return Ok(None);
        }
        let joined: Vec<Vec<Rat>> = directions[0]
            .to_rows()
            .into_iter()
            .zip(directions[1].to_rows())
            .map(|(mut left, right)| {
                left.extend(right);
                left
            })
            .collect();
        let unit = joined_integral(&joined);
        // Full physical Df is evaluated once. In particular curvature includes
        // source/context cross terms; summing block curvatures is not equivalent.
        let (moves, oscillation, raw_alignment) =
            receiving_fisher_face(samples, &joined).ok_or(HnnError::Unadmitted {
                reason: "a joined receiving certificate requires the full comparison's face masses",
            })?;
        let alignment = if raw_alignment.is_negative() {
            raw_alignment
        } else {
            match odometer_alignment_defect(samples, &joined) {
                Some(defect) if raw_alignment > defect => raw_alignment - defect,
                _ => Rat::zero(),
            }
        };
        let direction = JoinedReceivingDirection {
            unit_norms: unit.schur_norms(),
            unit,
            alignment,
            moves,
            covector: oscillation.max(Rat::one()),
        };
        *at = staged;
        Ok(Some(Self {
            owner,
            samples: samples.to_vec(),
            blocks,
            direction,
        }))
    }

    pub(super) fn direction(&self) -> &JoinedReceivingDirection {
        &self.direction
    }

    /// Exact pass-2 updates in each block's own carry coordinates, before rounding.
    pub(super) fn step_entries(&self, eta: &Rat) -> Vec<Rat> {
        self.blocks
            .iter()
            .flatten()
            .flat_map(|prepared| prepared.unit.scaled_rows(eta).into_iter().flatten())
            .collect()
    }

    /// One jointly certified eta is applied to both blocks. The shared full phase
    /// is absorbed at the producing map once, before replacing either successor.
    pub(super) fn stepped(
        mut self,
        eta: &Rat,
        at: &mut BudgetedCarry,
    ) -> Result<(ReceivingMaterial, Vec<ChartReading>), HnnError> {
        if eta.is_negative() {
            return Err(HnnError::Unadmitted {
                reason: "a joined receiving step is nonnegative",
            });
        }
        self.owner.absorb_full_phase(&self.samples)?;
        let rows = self.owner.map().rows();
        let owner_blocks = self.owner.blocks().unwrap();
        let width = owner_blocks[0].width();
        let mut laws = [owner_blocks[0].law().clone(), owner_blocks[1].law().clone()];
        let mut staged = at.clone();
        let mut readings = Vec::new();
        for (index, prepared) in self.blocks.into_iter().enumerate() {
            if let Some(prepared) = prepared {
                let (law, mut reading) = block_stroke(&mut staged, rows, width, index, |local| {
                    prepared.stepped(eta, local)
                })?;
                reading.receiving_block = Some(ReceivingBlockReading {
                    index,
                    operand_scale: owner_blocks[index]
                        .chart()
                        .expect("a prepared block is founded")
                        .scale()
                        .clone(),
                });
                laws[index] = law;
                readings.push(reading);
            }
        }
        let material = self.owner.with_block_laws(laws)?;
        *at = staged;
        Ok((material, readings))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::integer;

    #[test]
    fn block_stroke_keeps_rounded_receipts_disjoint() {
        let mut at = BudgetedCarry::new(Lattice::new(12), 1);
        for block in 0..2 {
            block_stroke(&mut at, 2, 2, block, |local| {
                assert!(local.staged.is_empty());
                local.staged.insert(
                    (Carrier::Map, 1),
                    (integer((block + 1) as i64), BigInt::from(block + 2)),
                );
                local.staged.insert(
                    (Carrier::Gram, 3),
                    (integer((block + 3) as i64), BigInt::from(block + 4)),
                );
                local.moved = true;
                Ok(())
            })
            .unwrap();
        }
        assert_eq!(at.staged.len(), 4);
        assert_eq!(at.staged[&(Carrier::Map, 1)].0, integer(1));
        assert_eq!(at.staged[&(Carrier::Map, 3)].0, integer(2));
        assert_eq!(at.staged[&(Carrier::Gram, 5)].0, integer(3));
        assert_eq!(at.staged[&(Carrier::Gram, 15)].0, integer(4));
        for block in 0..2 {
            block_stroke(&mut at, 2, 2, block, |local| {
                assert_eq!(local.staged.len(), 2);
                assert_eq!(
                    local.staged[&(Carrier::Map, 1)].0,
                    integer((block + 1) as i64)
                );
                Ok(())
            })
            .unwrap();
        }
        assert!(at.moved());
        assert_eq!(at.stepped(), 4);
    }

    #[test]
    fn joined_preparation_leaves_zero_context_pristine() {
        let law = NormalLaw::with_receiving_prior(ExactRatMatrix::zero(4, 4).unwrap(), 1);
        let owner = ReceivingMaterial::arrival_context(law, 2, 2).unwrap();
        let half = Rat::new(1.into(), 2.into());
        let sample = Sample {
            feature: vec![integer(2), integer(0), integer(0), integer(0)],
            covector: vec![half.clone(), integer(0), -half.clone(), integer(0)],
            weight: integer(1),
            masses: Some(vec![half.clone(), half]),
        };
        let rule = ChartRule::new(Lattice::new(20), 16);
        let mut at = BudgetedCarry::new(Lattice::new(20), 1);
        let prepared = PreparedReceivingBlocks::prepare(&owner, &[sample], &rule, &mut at)
            .unwrap()
            .unwrap();
        let rows = prepared.direction().unit.to_rows();
        assert!(rows.iter().all(|row| row[2..].iter().all(Zero::is_zero)));
        let (after, readings) = prepared
            .stepped(&Rat::new(1.into(), 2.into()), &mut at)
            .unwrap();
        assert_eq!(readings.len(), 1);
        assert_eq!(after.blocks().unwrap()[1], owner.blocks().unwrap()[1]);
        assert!(
            after.blocks().unwrap()[0]
                .law()
                .phase_statistics()
                .is_none()
        );
        after.validate().unwrap();
    }
}
