//! Linear row transport and complete bilinear variation of the existing enclosure carrier.
mod concatenate;
#[cfg(test)]
mod tests;

use super::*;
use crate::ExactWavePhaseTransport;
use crate::resident_section::EnclosureComposition;
use crate::resident_section::SLOT_WORDS;
use num_integer::Integer;
use num_traits::ToPrimitive;

impl<'c> ResidentNormalEnclosureSection<'c> {
    fn composition_output(
        &self,
        rows: usize,
        width: usize,
    ) -> Result<ResidentSection<'c>, ConstitutiveFibreError> {
        if rows == 0
            || rows > u32::MAX as usize
            || width == 0
            || width % 2 != 0
            || width >= u32::MAX as usize
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let stride = width
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        self.surface
            .fresh_section(rows, stride, ResidentGrain(0))
            .map_err(Into::into)
    }
    fn enact_composition(
        &self,
        op: EnclosureComposition<'_, 'c>,
        outputs: &[&ResidentSection<'c>],
    ) -> Result<(), ConstitutiveFibreError> {
        let operation = match &op {
            EnclosureComposition::Gather { .. } => "phased gather",
            EnclosureComposition::GatherAdjoint { .. } => "phased scatter adjoint",
            EnclosureComposition::Concatenate { .. } => "row concatenation",
            EnclosureComposition::Refine { .. } => "held refinement",
            EnclosureComposition::Features { .. } => "bilinear features",
            EnclosureComposition::FeaturesAdjoint { .. } => "bilinear input adjoints",
            EnclosureComposition::NormalAdjoint { .. } => "normal material adjoint",
        };
        let flags =
            self.surface
                .fresh_section(outputs[0].rows(), SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface
                .record_enclosure_composition(&lane, op, outputs, &flags)?;
        }
        pass.close(0, outputs[0], 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "enclosure composition ({operation}): {:?}",
                result.obstruction
            )));
        }
        Ok(())
    }
    fn phase_map(
        &self,
        addresses: &[usize],
        phases: &[ExactWavePhaseTransport],
        extent: usize,
    ) -> Result<ResidentSection<'c>, ConstitutiveFibreError> {
        if addresses.is_empty()
            || addresses.len() != phases.len()
            || addresses.iter().any(|a| *a >= extent)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut values = Vec::with_capacity(
            addresses
                .len()
                .checked_mul(4)
                .ok_or(ConstitutiveFibreError::Shape)?,
        );
        for (&address, phase) in addresses.iter().zip(phases) {
            if &phase.cosine * &phase.cosine + &phase.sine * &phase.sine != Rat::one() {
                return Err(ConstitutiveFibreError::Shape);
            }
            let den = phase.cosine.denom().lcm(phase.sine.denom());
            if den <= num_bigint::BigInt::from(0) {
                return Err(ConstitutiveFibreError::Shape);
            }
            let c = phase.cosine.numer() * (&den / phase.cosine.denom());
            let s = phase.sine.numer() * (&den / phase.sine.denom());
            let tuple = [
                i64::try_from(address).map_err(|_| ConstitutiveFibreError::Shape)?,
                c.to_i64().ok_or(ConstitutiveFibreError::Uncertain)?,
                s.to_i64().ok_or(ConstitutiveFibreError::Uncertain)?,
                den.to_i64().ok_or(ConstitutiveFibreError::Uncertain)?,
            ];
            values.extend(tuple.into_iter().map(|x| (x, x)));
        }
        let rest = ResidentSectionRest::found(addresses.len(), 4, ResidentGrain(0), 64, values)
            .map_err(|_| ConstitutiveFibreError::Shape)?;
        self.surface.mount_section_rest(&rest).map_err(Into::into)
    }
    fn phase_adjoint_map(
        &self,
        addresses: &[usize],
        phases: &[ExactWavePhaseTransport],
        extent: usize,
    ) -> Result<(ResidentSection<'c>, ResidentSection<'c>), ConstitutiveFibreError> {
        if addresses.len() != self.rows
            || phases.len() != addresses.len()
            || addresses.is_empty()
            || addresses.iter().any(|a| *a >= extent)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut grouped = vec![Vec::<[(i64, i64); 4]>::new(); extent];
        for (input, (&address, phase)) in addresses.iter().zip(phases).enumerate() {
            if &phase.cosine * &phase.cosine + &phase.sine * &phase.sine != Rat::one() {
                return Err(ConstitutiveFibreError::Shape);
            }
            let den = phase.cosine.denom().lcm(phase.sine.denom());
            if den <= num_bigint::BigInt::from(0) {
                return Err(ConstitutiveFibreError::Shape);
            }
            let c = phase.cosine.numer() * (&den / phase.cosine.denom());
            let s = phase.sine.numer() * (&den / phase.sine.denom());
            grouped[address].push([
                (
                    i64::try_from(input).map_err(|_| ConstitutiveFibreError::Shape)?,
                    i64::try_from(input).map_err(|_| ConstitutiveFibreError::Shape)?,
                ),
                (
                    c.to_i64().ok_or(ConstitutiveFibreError::Uncertain)?,
                    c.to_i64().ok_or(ConstitutiveFibreError::Uncertain)?,
                ),
                (
                    s.to_i64().ok_or(ConstitutiveFibreError::Uncertain)?,
                    s.to_i64().ok_or(ConstitutiveFibreError::Uncertain)?,
                ),
                (
                    den.to_i64().ok_or(ConstitutiveFibreError::Uncertain)?,
                    den.to_i64().ok_or(ConstitutiveFibreError::Uncertain)?,
                ),
            ]);
        }
        let mut offsets = Vec::with_capacity(extent + 1);
        offsets.push((0, 0));
        let mut total = 0usize;
        let mut entries = Vec::with_capacity(addresses.len() * 4);
        for group in grouped {
            total = total
                .checked_add(group.len())
                .ok_or(ConstitutiveFibreError::Shape)?;
            offsets.push((
                i64::try_from(total).map_err(|_| ConstitutiveFibreError::Shape)?,
                i64::try_from(total).map_err(|_| ConstitutiveFibreError::Shape)?,
            ));
            entries.extend(group.into_iter().flatten());
        }
        let offsets = self.surface.mount_section_rest(
            &ResidentSectionRest::found(extent + 1, 1, ResidentGrain(0), 64, offsets)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let entries = self.surface.mount_section_rest(
            &ResidentSectionRest::found(addresses.len(), 4, ResidentGrain(0), 64, entries)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        Ok((offsets, entries))
    }
    /// Gather the stated source rows and apply the existing exact unit phase on every channel.
    /// Optional enlargement appends exact zero coordinates, preserving the original radius.
    pub fn gather_phase_rows(
        &self,
        addresses: &[usize],
        phases: &[ExactWavePhaseTransport],
        components: usize,
    ) -> Result<Self, ConstitutiveFibreError> {
        let map = self.phase_map(addresses, phases, self.rows)?;
        let out = self.composition_output(addresses.len(), components)?;
        let enacted = self.enact_composition(
            EnclosureComposition::Gather {
                input: &self.section,
                map: &map,
                components: self.width,
                output_components: components,
            },
            &[&out],
        );
        if let Err(error) = enacted {
            // A failed packet is diagnostic evidence, never a successor. Inspect only at this
            // rejected boundary and report locations/counts rather than source coordinates.
            let wire = self.surface.detach_section(&self.section, 64)?;
            let mismatches: Vec<_> = wire
                .intervals
                .iter()
                .enumerate()
                .filter_map(|(i, (lo, hi))| (lo != hi).then_some(i))
                .collect();
            let negative_radii = wire
                .intervals
                .chunks_exact(self.section.width())
                .filter(|row| row[2 * self.width + 1].0 < 0)
                .count();
            let map_wire = self.surface.detach_section(&map, 64)?;
            let malformed_maps = map_wire
                .intervals
                .chunks_exact(4)
                .filter(|row| {
                    row.iter().any(|(lo, hi)| lo != hi)
                        || row[0].0 < 0
                        || row[0].0 as usize >= self.rows
                        || row[3].0 <= 0
                })
                .count();
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "{error}; gather input rows={} components={} unsealed_words={} first_unsealed={:?} negative_radii={negative_radii} malformed_maps={malformed_maps}",
                self.rows,
                self.width,
                mismatches.len(),
                mismatches.first(),
            )));
        }
        Self::from_resident(self.surface, out, addresses.len(), components, self.grain)
    }
    /// The actual transpose of phased gather, including every repeated source address.
    /// Each output row owns its exact sum and its refusal, with no unordered float accumulation.
    pub fn scatter_phase_adjoint(
        &self,
        addresses: &[usize],
        phases: &[ExactWavePhaseTransport],
        output_rows: usize,
    ) -> Result<Self, ConstitutiveFibreError> {
        if addresses.len() != self.rows {
            return Err(ConstitutiveFibreError::Shape);
        }
        let (offsets, entries) = self.phase_adjoint_map(addresses, phases, output_rows)?;
        let out = self.composition_output(output_rows, self.width)?;
        self.enact_composition(
            EnclosureComposition::GatherAdjoint {
                input: &self.section,
                offsets: &offsets,
                entries: &entries,
                components: self.width,
            },
            &[&out],
        )?;
        Self::from_resident(self.surface, out, output_rows, self.width, self.grain)
    }
    pub fn held_refinement(
        &self,
        seed: &Self,
        held: &[bool],
        step_bits: u32,
    ) -> Result<Self, ConstitutiveFibreError> {
        if self.rows != seed.rows
            || self.width != seed.width
            || self.grain != seed.grain
            || !std::ptr::eq(self.surface, seed.surface)
            || Some(held.len()) != self.rows.checked_mul(self.width / 2)
            || step_bits > 120
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mask = self.surface.mount_section_rest(
            &ResidentSectionRest::found(
                self.rows,
                self.width / 2,
                ResidentGrain(0),
                64,
                held.iter()
                    .map(|x| {
                        let x = i64::from(*x);
                        (x, x)
                    })
                    .collect(),
            )
            .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let out = self.composition_output(self.rows, self.width)?;
        self.enact_composition(
            EnclosureComposition::Refine {
                generated: &self.section,
                seed: &seed.section,
                mask: &mask,
                components: self.width,
                step_bits,
            },
            &[&out],
        )?;
        Self::from_resident(self.surface, out, self.rows, self.width, self.grain)
    }
    /// Phi(s,c)=s ⊕ c ⊕ (c tensor s), including both input radii and their mixed term.
    pub fn bilinear_enclosed_features(
        &self,
        condition: &Self,
    ) -> Result<Self, ConstitutiveFibreError> {
        if self.rows != condition.rows
            || self.grain != condition.grain
            || !std::ptr::eq(self.surface, condition.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let f = self
            .width
            .checked_mul(condition.width / 2)
            .and_then(|n| n.checked_add(self.width)?.checked_add(condition.width))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let out = self.composition_output(self.rows, f)?;
        self.enact_composition(
            EnclosureComposition::Features {
                source: &self.section,
                condition: &condition.section,
                d: self.width,
                k: condition.width,
                grain: self.grain.0,
            },
            &[&out],
        )?;
        Self::from_resident(self.surface, out, self.rows, f, self.grain)
    }
    /// Real adjoint of that same Phi through the supplied producing source and condition balls.
    pub fn bilinear_enclosed_pullback(
        &self,
        condition: &Self,
        covector: &Self,
    ) -> Result<(Self, Self), ConstitutiveFibreError> {
        if self.rows != condition.rows
            || self.rows != covector.rows
            || self.grain != condition.grain
            || self.grain != covector.grain
            || !std::ptr::eq(self.surface, condition.surface)
            || !std::ptr::eq(self.surface, covector.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let a = self.composition_output(self.rows, self.width)?;
        let b = self.composition_output(self.rows, condition.width)?;
        self.enact_composition(
            EnclosureComposition::FeaturesAdjoint {
                source: &self.section,
                condition: &condition.section,
                covector: &covector.section,
                d: self.width,
                k: condition.width,
                grain: self.grain.0,
            },
            &[&a, &b],
        )?;
        Ok((
            Self::from_resident(self.surface, a, self.rows, self.width, self.grain)?,
            Self::from_resident(self.surface, b, self.rows, condition.width, self.grain)?,
        ))
    }
}
impl<'c> ResidentNormalMaterialView<'c> {
    /// Adjoint of the stored executed coefficient map, held fixed at this material cut.
    pub fn pull_back_enclosed_section(
        &self,
        covector: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        if self.grain != covector.grain
            || !std::ptr::eq(self.surface, covector.surface)
            || covector.width != 2 * self.targets
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let sources = self
            .source_chart
            .complex_sources()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let width = sources
            .checked_mul(2)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let out = covector.composition_output(covector.rows, width)?;
        covector.enact_composition(
            EnclosureComposition::NormalAdjoint {
                state: &self.state,
                covector: &covector.section,
                sources,
                targets: self.targets,
                grain: self.grain.0,
            },
            &[&out],
        )?;
        ResidentNormalEnclosureSection::from_resident(
            self.surface,
            out,
            covector.rows,
            width,
            self.grain,
        )
    }
}
impl<'c> ResidentNormalMaterial<'c> {
    pub fn pull_back_enclosed_section(
        &self,
        covector: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        self.retained_view().pull_back_enclosed_section(covector)
    }
}
