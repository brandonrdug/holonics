//! Positive pair material from a fixed template and its current amplitude vector.
//!
//! The source-only field has no occurrence decoder to replay. Current parameters, current
//! q/b and independently owned live comparisons are sufficient; completed updates add no journal.
use super::*;
use crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureSection;
use crate::resident_section::SLOT_WORDS;

pub struct NativeDeclaredAmplitudeCommit<'c> {
    material: NativeFieldGlobalMaterialCommit<'c>,
    gradient: ResidentNormalEnclosureSection<'c>,
    reference: ResidentNormalEnclosureSection<'c>,
    accepted_steps: ResidentSection<'c>,
    amplitudes: Rc<ResidentSection<'c>>,
    surface: &'c ResidentSurface<'c>,
    group_width: usize,
    grain: u32,
}
impl<'c> NativeDeclaredAmplitudeCommit<'c> {
    /// Cotangent at the old producing word, contracted with the contemporary relative basis.
    pub fn gradient(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.gradient
    }
    /// Reference to the unrounded parameter proposal; the installed amplitudes are exact points.
    pub fn proposal_reference(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.reference
    }
    pub fn inspect_amplitudes(&self) -> Result<Vec<holonics::geometry::Rat>, Error> {
        amplitude_points(self.surface, &self.amplitudes, self.grain)
    }
    pub fn inspect_step_bits(&self) -> Result<Vec<u32>, Error> {
        let rest = self.surface.detach_section(&self.accepted_steps, 64)?;
        wides(&rest.intervals)?
            .into_iter()
            .map(|x| u32::try_from(x).map_err(|_| Error::Shape))
            .collect()
    }
    pub fn group_width(&self) -> usize {
        self.group_width
    }
}
fn amplitude_points<'c>(
    surface: &'c ResidentSurface<'c>,
    section: &ResidentSection<'c>,
    grain: u32,
) -> Result<Vec<holonics::geometry::Rat>, Error> {
    let rest = surface.detach_section(section, 64)?;
    let words = wides(&rest.intervals)?;
    words
        .chunks_exact(3)
        .map(|r| {
            if r[0] <= 0 || r[1] != 0 || r[2] != 0 {
                return Err(Error::Shape);
            }
            Ok(holonics::geometry::Rat::new(
                r[0].into(),
                num_bigint::BigInt::from(1) << grain,
            ))
        })
        .collect()
}
impl<'c> NativeFieldCurrentSource<'c> {
    /// Cold parameter reading, without realizing a dense D matrix or any update history.
    pub fn inspect_declared_amplitudes(
        &self,
    ) -> Result<Option<Vec<holonics::geometry::Rat>>, Error> {
        self._producing
            .factor_program
            .as_ref()
            .and_then(|p| p.amplitude_family.as_ref())
            .map(|a| amplitude_points(self.surface, &a.amplitudes, self.grain))
            .transpose()
    }
}
impl<'c> NativeConstitutiveField<'c> {
    /// Stage a positive relative step against the current pair basis from complete old q/b
    /// pullbacks, then reconstruct the sparse factor from its fixed template. Only the current
    /// parameter vector survives publication. The source-only restriction makes the absence
    /// of an occurrence/update archive an explicit property of this operation.
    pub fn prepare_declared_contact_amplitude_return<'a>(
        &mut self,
        pullbacks: &[&NativeFieldActionPullback<'a, 'c>],
        group_width: usize,
        step_bits: u32,
    ) -> Result<NativeDeclaredAmplitudeCommit<'c>, Error> {
        if !self.relation.usable
            || self.pending.is_some()
            || !self.relation.source_only()
            || !self.history.is_empty()
            || pullbacks.is_empty()
            || step_bits > 120
            || group_width == 0
        {
            return Err(Error::Uncertain);
        }
        let current = self.read_current_source()?;
        let old = &current._producing;
        let program = old.factor_program.as_ref().ok_or(Error::Shape)?;
        let count = program.rows;
        let d = program.boundary_components;
        if program.rank != 0
            || count == 0
            || count % group_width != 0
            || current.declared_origins.len() != count
            || d != current.boundary_components()
            || d > u32::MAX as usize / 2
            || count > u32::MAX as usize / 4
            || program.nonzeros > u32::MAX as usize
        {
            return Err(Error::Shape);
        }
        let groups = count / group_width;
        let surface = self.relation.surface;
        let grain = current.grain;
        if !(1..=120).contains(&grain) {
            return Err(Error::Shape);
        }
        let family = match &program.amplitude_family {
            Some(family) if family.group_width == group_width => Rc::clone(family),
            Some(_) => return Err(Error::Shape),
            None => {
                let point = [1i128 << grain, 0, 0];
                let mut values = Vec::new();
                values
                    .try_reserve_exact(groups.checked_mul(6).ok_or(Error::Shape)?)
                    .map_err(|_| Error::Shape)?;
                for _ in 0..groups {
                    for value in point {
                        for w in [value as i64, (value >> 64) as i64] {
                            values.push((w, w));
                        }
                    }
                }
                Rc::new(DeclaredAmplitudeFamily {
                    group_width,
                    template_values: Rc::clone(&program.values),
                    template_transpose_values: Rc::clone(&program.transpose_values),
                    template_bounds: Rc::clone(&old.bounds),
                    amplitudes: Rc::new(
                        surface.mount_section_rest(
                            &ResidentSectionRest::found(groups, 6, ResidentGrain(0), 64, values)
                                .map_err(|_| Error::Shape)?,
                        )?,
                    ),
                })
            }
        };
        // The producing covector stays old; its receiving parameter basis is CURRENT.
        // This is g_now=(rho_now/rho_old)g_old on the exact shared-template family,
        // with the native coefficient family error paid by the contraction enclosure.
        let mut total: Option<ResidentNormalEnclosureSection<'c>> = None;
        for pullback in pullbacks {
            let gradient = current.declared_factor_scale_gradient(pullback, group_width)?;
            total = Some(match total {
                None => ResidentNormalEnclosureSection::concatenate_rows(&[gradient.gradient()])?,
                Some(previous) => previous.sum_same_shape(gradient.gradient())?,
            });
        }
        let gradient = total.ok_or(Error::Shape)?;
        let amplitudes = Rc::new(surface.fresh_section(groups, 6, ResidentGrain(0))?);
        let steps = surface.fresh_section(groups, 2, ResidentGrain(0))?;
        let reference = surface.fresh_section(groups, 6, ResidentGrain(0))?;
        let flags = surface.fresh_section(groups, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut pass = surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            surface.record_contact_amplitude_proposal(
                &lane,
                gradient.resident_section(),
                &family.amplitudes,
                groups,
                step_bits,
                grain,
                &amplitudes,
                &steps,
                Some(&reference),
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, groups)?;
        }
        pass.close(0, &amplitudes, 64)?;
        let receipt = pass.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "positive contact proposal: {:?}",
                receipt.obstruction
            )));
        }
        let values = Rc::new(surface.fresh_section(1, program.values.width(), ResidentGrain(0))?);
        let transpose_values = Rc::new(surface.fresh_section(
            1,
            program.transpose_values.width(),
            ResidentGrain(0),
        )?);
        let csr_rounding = surface.fresh_section(count, 2, ResidentGrain(0))?;
        let transpose_rounding = surface.fresh_section(d / 2, 2, ResidentGrain(0))?;
        let csr_flags = surface.fresh_section(count, SLOT_WORDS / 2, ResidentGrain(0))?;
        let transpose_flags = surface.fresh_section(d / 2, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut pass = surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            for (transpose, output, rounding, flags, rows) in [
                (false, &*values, &csr_rounding, &csr_flags, count),
                (
                    true,
                    &*transpose_values,
                    &transpose_rounding,
                    &transpose_flags,
                    d / 2,
                ),
            ] {
                surface.record_contact_amplitude_rebuild(
                    &lane,
                    &program.row_offsets,
                    &program.columns,
                    &family.template_values,
                    &program.transpose_offsets,
                    &program.transpose_rows,
                    &family.template_transpose_values,
                    &amplitudes,
                    count,
                    d / 2,
                    program.nonzeros,
                    group_width,
                    grain,
                    transpose,
                    output,
                    rounding,
                    flags,
                )?;
                surface.collect_phase_status(&lane, flags, rows)?;
            }
        }
        pass.close(0, &values, 64)?;
        let receipt = pass.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "pair template reconstruction: {:?}",
                receipt.obstruction
            )));
        }
        let bounds = Rc::new(surface.fresh_section(1, 4, ResidentGrain(0))?);
        let mut pass = surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            surface.record_contact_amplitude_bounds(
                &lane,
                &amplitudes,
                &csr_rounding,
                &family.template_bounds,
                &old.bounds,
                groups,
                count,
                grain,
                &bounds,
            )?;
        }
        pass.close(0, &bounds, 64)?;
        let receipt = pass.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "pair template bound: {:?}",
                receipt.obstruction
            )));
        }
        let successor = Rc::new(OperativeFactorProgram {
            amplitude_family: Some(Rc::new(DeclaredAmplitudeFamily {
                group_width,
                template_values: Rc::clone(&family.template_values),
                template_transpose_values: Rc::clone(&family.template_transpose_values),
                template_bounds: Rc::clone(&family.template_bounds),
                amplitudes: Rc::clone(&amplitudes),
            })),
            row_offsets: Rc::clone(&program.row_offsets),
            columns: Rc::clone(&program.columns),
            values,
            transpose_offsets: Rc::clone(&program.transpose_offsets),
            transpose_rows: Rc::clone(&program.transpose_rows),
            transpose_values,
            left: Rc::clone(&program.left),
            right: Rc::clone(&program.right),
            defects: Rc::clone(&program.defects),
            rows: count,
            boundary_components: d,
            rank: 0,
            nonzeros: program.nonzeros,
        });
        let sections = Rc::new(OperativeSections {
            map: Rc::clone(&old.map),
            b: Rc::clone(&old.b),
            bounds,
            covariance: std::cell::OnceCell::new(),
            aggregate: surface.fresh_section(1, 2 * d, ResidentGrain(0))?,
            moment_bounds: surface.fresh_section(1, 8, ResidentGrain(0))?,
            factor_program: Some(successor),
        });
        sections.refresh_factor_aggregate(surface, grain)?;
        let material = NativeFieldGlobalMaterialCommit {
            owner: Rc::clone(&self.owner),
            cut: self.history.len(),
            births: current.births.clone(),
            producing: Rc::clone(old),
            sections,
            origin: Rc::new(()),
            returns: Vec::new(),
            program: None,
            grain,
        };
        Ok(NativeDeclaredAmplitudeCommit {
            material,
            gradient,
            reference: ResidentNormalEnclosureSection::from_resident(
                surface,
                reference,
                groups,
                2,
                ResidentGrain(grain),
            )?,
            accepted_steps: steps,
            amplitudes,
            surface,
            group_width,
            grain,
        })
    }
    pub fn commit_declared_contact_amplitude_return(
        &mut self,
        prepared: NativeDeclaredAmplitudeCommit<'c>,
    ) -> Result<(), Error> {
        self.commit_global_action_material_return(prepared.material)
    }
}

#[cfg(test)]
mod tests;
