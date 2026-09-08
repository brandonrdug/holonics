//! Productive real-ray contextual section from two actual source-null field passages.
use super::*;

impl<'c> NativeConstitutiveField<'c> {
    /// Derive the local relation alpha*(c1-c0) -> alpha*(y1-y0), with reference (c0,y0),
    /// from two actual returns. Both source faces must coincide and be nonzero; the native
    /// complete-current contrast must exclude zero with its original error intact.
    /// This creates immutable native material and issues no new field source capability.
    pub fn derive_contextual_contrast(
        &mut self,
        receiving: [usize; 2],
    ) -> Result<ResidentContextualSection<'c>, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if receiving[0] >= receiving[1] {
            return Err(ConstitutiveFibreError::Shape);
        }
        let source = receiving.map(|at| self.history.get(at).and_then(|h| h.lineage.received_from));
        let [Some(s0), Some(s1)] = source else {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        };
        let context = [
            receiving[0]
                .checked_sub(1)
                .ok_or(ConstitutiveFibreError::ForeignOccurrence)?,
            receiving[1] - 1,
        ];
        let n = self.nodes();
        let y = 2 * n;
        let j = y + 2;
        let grain = self.transport_grain()?;
        let feature = match self.material_transport_source() {
            Some(NativeMaterialTransportSource::HomogeneousMoment) => 28 * n + 12,
            Some(NativeMaterialTransportSource::CompleteCurrent) => 38 * n + 12,
            Some(NativeMaterialTransportSource::Contextual | NativeMaterialTransportSource::BilinearContextual) => {
                material_transport::contextual::offsets(n)[3]
            }
            _ => return Err(ConstitutiveFibreError::Shape),
        };
        for at in [receiving[0], receiving[1], s0, s1, context[0], context[1]] {
            self.mount_history_source(at)?;
        }
        let surface = self.relation.surface;
        let mut inputs = Vec::new();
        for &at in &receiving {
            let h = &self.history[at];
            inputs.push(if let Some(i) = &h.resident()?.incoming {
                Rc::clone(i)
            } else {
                let words = h
                    .lineage
                    .incoming
                    .exterior()
                    .ok_or(ConstitutiveFibreError::Uncertain)?
                    .iter()
                    .flat_map(|p| p.words())
                    .map(|v| (v, v))
                    .collect();
                Rc::new(
                    surface.mount_section_rest(
                        &ResidentSectionRest::found(n, 3, ResidentGrain(0), 64, words)
                            .map_err(|_| ConstitutiveFibreError::Shape)?,
                    )?,
                )
            });
        }
        let contexts = [
            Rc::clone(
                self.history[context[0]]
                    .resident()?
                    .transport
                    .as_ref()
                    .ok_or(ConstitutiveFibreError::Uncertain)?,
            ),
            Rc::clone(
                self.history[context[1]]
                    .resident()?
                    .transport
                    .as_ref()
                    .ok_or(ConstitutiveFibreError::Uncertain)?,
            ),
        ];
        let mut pointers = Vec::new();
        for (index, s) in [s0, s1].into_iter().enumerate() {
            for ptr in [
                self.history[receiving[index]]
                    .resident()?
                    .section
                    .lo_device_ptr(),
                self.history[s].resident()?.section.lo_device_ptr(),
                inputs[index].lo_device_ptr(),
                self.history[receiving[index]].frame.native.lo_device_ptr(),
                self.history[s].frame.native.lo_device_ptr(),
                contexts[index].lo_device_ptr() + 8 * feature as u64,
            ] {
                let word = ptr as i64;
                pointers.push((word, word));
            }
        }
        let table = surface.mount_section_rest(
            &ResidentSectionRest::found(2, 6, ResidentGrain(0), 64, pointers)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let basis = surface.fresh_section(j, j, ResidentGrain(0))?;
        let joint = surface.fresh_section(1, j * j + j + 5, ResidentGrain(0))?;
        let fixed = surface.fresh_section(1, 4 * n + 1, ResidentGrain(0))?;
        let base = surface.fresh_section(1, y + 1, ResidentGrain(0))?;
        let proof = surface.fresh_section(1, 18, ResidentGrain(0))?;
        let endpoint = surface.fresh_section(1, y + 1, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_field_context_section(
                &lane, &table, n, grain, &basis, &joint, &fixed, &base, &endpoint, &proof,
            )?;
        }
        passage.close(0, &joint, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "field contextual contrast not established: {:?}",
                receipt.obstruction
            )));
        }
        let origin = ContextualSectionOrigin::FieldContrast {
            receiving,
            source: [s0, s1],
            context,
            field_occurrences: self.history.len(),
            ambient_context_complex: 3 * n
                + self.history[..=context[1]]
                    .iter()
                    .filter(|h| h.lineage.received_from.is_some())
                    .count(),
            fractional_bits: grain,
        };
        Ok(ResidentContextualSection::from_field(
            surface,
            self.history.len() as u64,
            y,
            basis,
            joint,
            fixed,
            base,
            endpoint,
            proof,
            contexts,
            origin,
        ))
    }
}

#[cfg(test)]
mod tests;
