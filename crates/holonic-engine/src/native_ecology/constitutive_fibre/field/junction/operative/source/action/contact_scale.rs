//! Source-qualified cotangent for fixed rectangular contact-factor amplitudes.
use super::*;
use crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureSection;
use crate::resident_section::SLOT_WORDS;

/// The receiving covector contracted with a declared pure-CSR basis. The basis and
/// producing field are retained separately: later material need not be the producing material.
/// This is a derivative, not a positive proposal or a material publication.
pub struct NativeDeclaredFactorScaleGradient<'c> {
    basis: NativeFieldCurrentSource<'c>,
    producing: NativeFieldCurrentSource<'c>,
    group_width: usize,
    gradient: ResidentNormalEnclosureSection<'c>,
}
impl<'c> NativeDeclaredFactorScaleGradient<'c> {
    pub fn basis(&self) -> &NativeFieldCurrentSource<'c> {
        &self.basis
    }
    pub fn producing(&self) -> &NativeFieldCurrentSource<'c> {
        &self.producing
    }
    pub fn group_width(&self) -> usize {
        self.group_width
    }
    pub fn gradient(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.gradient
    }
}

impl<'c> NativeFieldCurrentSource<'c> {
    /// For `D(rho)=sum_a rho_a B_a`, return `Re <G_D,B_a>` for each contiguous
    /// group of basis contact columns. `D` is the rectangular global coupling, not
    /// the contact form `D D*` or `B* B`. The complete q/b pullback supplies both
    /// rank-one terms of `G_D`; no interior return is discarded.
    pub fn declared_factor_scale_gradient(
        &self,
        pullback: &NativeFieldActionPullback<'_, 'c>,
        group_width: usize,
    ) -> Result<NativeDeclaredFactorScaleGradient<'c>, Error> {
        let count = self.births.len();
        let d = self.boundary_components();
        let program = self
            ._producing
            .factor_program
            .as_ref()
            .ok_or(Error::Shape)?;
        if group_width == 0
            || count == 0
            || count % group_width != 0
            || program.rank != 0
            || program.rows != count
            || program.boundary_components != d
            || self.declared_origins.len() != count
            || d > u32::MAX as usize / 2
            || count > u32::MAX as usize / 4
            || program.nonzeros > u32::MAX as usize
            || !self.same_owner(pullback.source())
            || self.births != pullback.source.births
            || self.declared_origins != pullback.source.declared_origins
            || self.grain != pullback.source.grain
            || d != pullback.layout.boundary_components
        {
            return Err(Error::Shape);
        }
        let groups = count / group_width;
        groups
            .checked_mul(6)
            .and_then(|n| n.checked_mul(16))
            .ok_or(Error::Shape)?;
        let output = self.surface.fresh_section(groups, 6, ResidentGrain(0))?;
        let flags = self
            .surface
            .fresh_section(groups, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_contact_scale_gradient(
                &lane,
                &program.row_offsets,
                &program.columns,
                &program.values,
                &self._producing.bounds,
                &pullback.ports,
                &pullback.currents,
                &pullback.delta_bounds,
                d,
                count,
                program.nonzeros,
                group_width,
                self.grain,
                &output,
                &flags,
            )?;
            self.surface.collect_phase_status(&lane, &flags, groups)?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "declared contact-factor gradient: {:?}",
                receipt.obstruction
            )));
        }
        let gradient = ResidentNormalEnclosureSection::from_resident(
            self.surface,
            output,
            groups,
            2,
            ResidentGrain(self.grain),
        )?;
        Ok(NativeDeclaredFactorScaleGradient {
            basis: self.retained_clone(),
            producing: pullback.source.retained_clone(),
            group_width,
            gradient,
        })
    }
}

#[cfg(test)]
pub(super) mod tests;
