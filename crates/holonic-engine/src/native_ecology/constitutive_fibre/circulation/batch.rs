//! Ordered ingress through the existing circulation kernel. Scheduling edges carry failure
//! dependency, not an invented semantic returned-source contact. Unlinked ingress never deposits
//! a relation row, so the complete receiver basis is unchanged throughout this batch.
use super::*;
use crate::resident_section::ObstructionLineage;

pub struct NativeUnlinkedBatchReturn {
    pub steps: Vec<NativeCurrentStep>,
    /// Batch-local index. The preceding prefix committed; this index and its suffix did not.
    pub refused_at: Option<usize>,
    pub obstruction: ObstructionLineage,
}

impl<'chart> NativeConstitutiveEcology<'chart> {
    pub fn advance_unlinked_batch(
        &mut self,
        currents: &[NativePhaseCurrent],
    ) -> Result<NativeUnlinkedBatchReturn, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() || !self.pending_batch.is_empty() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let count = currents.len();
        let start = self.history.len();
        start
            .checked_add(count)
            .ok_or(ConstitutiveFibreError::Shape)?;
        self.relation
            .occurrences
            .checked_add(count as u64)
            .ok_or(ConstitutiveFibreError::Shape)?;
        self.history
            .try_reserve(count)
            .map_err(|_| ConstitutiveFibreError::Shape)?;
        let mut steps = Vec::new();
        steps
            .try_reserve(count)
            .map_err(|_| ConstitutiveFibreError::Shape)?;
        if count == 0 {
            return Ok(NativeUnlinkedBatchReturn {
                steps,
                refused_at: None,
                obstruction: ObstructionLineage::default(),
            });
        }
        let surface = self.relation.surface;
        let mut inputs = Vec::with_capacity(count);
        let mut outputs = Vec::with_capacity(count);
        for (index, current) in currents.iter().enumerate() {
            inputs.push(
                surface.mount_section_rest(
                    &ResidentSectionRest::found(
                        1,
                        3,
                        ResidentGrain(0),
                        64,
                        current.words().into_iter().map(|v| (v, v)).collect(),
                    )
                    .map_err(|_| ConstitutiveFibreError::Shape)?,
                )?,
            );
            outputs.push(HeldEmission {
                section: surface.fresh_section(
                    1,
                    6 * self.material.len() + 13,
                    ResidentGrain(0),
                )?,
                lineage: NativeCurrentLineage {
                    occurrence: start + index,
                    frame: self.frame.view.ordinal,
                    predecessor_state: (start + index).checked_sub(1),
                    received_from: None,
                    incoming: *current,
                },
                returned: false,
                frame: Rc::clone(&self.frame),
                material: Rc::clone(&self.material),
            });
        }
        let dependencies: Vec<Vec<usize>> = (0..count)
            .map(|i| i.checked_sub(1).into_iter().collect())
            .collect();
        let mut passage = surface.begin_passage_serialized(&dependencies)?;
        for index in 0..count {
            {
                let lane = passage.open(index, &dependencies[index])?;
                surface.record_constitutive_circulation(
                    &lane,
                    &self.seed,
                    &mut self.memory,
                    &mut self.relation.basis,
                    &inputs[index],
                    None,
                    &self.frame.native,
                    None,
                    &outputs[index].section,
                )?;
            }
            passage.close(index, &outputs[index].section, 64)?;
        }
        let passage = passage.finish()?;
        self.pending_batch = outputs;
        self.relation.usable = false;
        let reading = passage.launch()?;
        let refused_at = reading.obstruction.refusals.first().map(|r| r.index);
        let committed = refused_at.unwrap_or(count);
        // Every suffix occurrence must have carried the preceding refusal. A malformed receipt
        // leaves the staged batch with the faulted owner; never guess what committed.
        if reading.slots.len() != count
            || reading
                .obstruction
                .refusals
                .iter()
                .map(|r| r.index)
                .ne(committed..count)
        {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        for held in self.pending_batch.iter().take(committed) {
            let words = surface.read_out(&held.section)?;
            let source_width = self.relation.source_width;
            let width = source_width + 2;
            let current_at = source_width + 1;
            if words.len() != 6 * self.material.len() + 13
                || words.iter().any(|(a, b)| a != b)
                || words[source_width].0 <= 0
                || words[current_at + width + 2].0 != -1
            {
                return Err(ConstitutiveFibreError::Uncertain);
            }
            let rank = usize::try_from(words[current_at + width + 3].0)
                .map_err(|_| ConstitutiveFibreError::Uncertain)?;
            if rank > width {
                return Err(ConstitutiveFibreError::Uncertain);
            }
            let denominator = words[source_width].0;
            let source_currents = (0..self.material.len())
                .map(|i| {
                    ExactComplexWaveCurrent::new(
                        Rat::new(words[2 * i].0.into(), denominator.into()),
                        Rat::new(words[2 * i + 1].0.into(), denominator.into()),
                    )
                })
                .collect();
            steps.push(NativeCurrentStep {
                source: NativeEmissionHandle {
                    owner: Rc::clone(&self.owner),
                    occurrence: held.lineage.occurrence,
                },
                lineage: held.lineage.clone(),
                frame: Rc::clone(&held.frame.view),
                source_currents,
                receiver: self.relation.decode_reading(&words, current_at, None)?,
                received_difference: None,
                formed_pivot: None,
                successor_rank: rank,
            });
        }
        // Publish the GPU-produced successor and its exact carriers together after decoding.
        self.history.extend(self.pending_batch.drain(..committed));
        self.pending_batch.clear();
        self.relation.occurrences += committed as u64;
        self.relation.usable = true;
        Ok(NativeUnlinkedBatchReturn {
            steps,
            refused_at,
            obstruction: reading.obstruction,
        })
    }
}
