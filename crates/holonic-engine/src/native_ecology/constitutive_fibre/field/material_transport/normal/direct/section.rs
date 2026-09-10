use super::*;
use std::rc::Rc;

/// The two complete response fields share actual immutable producing operator cuts. Input
/// sections remain borrowed comparison operands, never a population retained by the model.
pub struct ResidentNormalSectionReturn<'a, 'c> {
    surface: &'c ResidentSurface<'c>,
    prior: Rc<ResidentSection<'c>>,
    successor: Rc<ResidentSection<'c>>,
    source: ResidentConstitutiveSection<'a, 'c>,
    observed: ResidentConstitutiveSection<'a, 'c>,
    before: ResidentSection<'c>,
    after: ResidentSection<'c>,
    roots: usize,
    targets: usize,
    grain: ResidentGrain,
    pub predecessor_observations: u64,
    pub successor_observations: u64,
}
impl<'a, 'c> ResidentNormalSectionReturn<'a, 'c> {
    pub fn source(&self) -> ResidentConstitutiveSection<'a, 'c> {
        self.source
    }
    pub fn observed(&self) -> ResidentConstitutiveSection<'a, 'c> {
        self.observed
    }
    pub fn rows(&self) -> usize {
        self.source.rows()
    }
    fn view<'r>(
        &'r self,
        section: &'r ResidentSection<'c>,
        row: usize,
    ) -> Result<ResidentNormalEnclosureView<'r, 'c>, ConstitutiveFibreError> {
        if row >= self.rows() {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(ResidentNormalEnclosureView {
            surface: self.surface,
            section,
            offset: row * section.width(),
            width: 2 * self.targets,
            grain: self.grain,
        })
    }
    pub fn before(
        &self,
        row: usize,
    ) -> Result<ResidentNormalEnclosureView<'_, 'c>, ConstitutiveFibreError> {
        self.view(&self.before, row)
    }
    pub fn forward(
        &self,
        row: usize,
    ) -> Result<ResidentNormalEnclosureView<'_, 'c>, ConstitutiveFibreError> {
        self.view(&self.after, row)
    }
    pub fn inspect_before_operator(
        &self,
    ) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
        decode_state(
            &self.surface.detach_section(&self.prior, i64::BITS)?,
            self.roots,
            self.targets,
            self.grain.0,
        )
    }
    pub fn inspect_after_operator(
        &self,
    ) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
        decode_state(
            &self.surface.detach_section(&self.successor, i64::BITS)?,
            self.roots,
            self.targets,
            self.grain.0,
        )
    }
    /// Read the entire field once at the explicitly requested exterior receiver.
    pub fn inspect_forward(&self) -> Result<Vec<NativeFieldCurrentBall>, ConstitutiveFibreError> {
        let words = self.surface.read_out(&self.after)?;
        let scale = BigInt::one() << self.grain.0;
        words
            .chunks_exact(self.after.width())
            .map(|row| {
                let v = wides(row)?;
                let width = 2 * self.targets;
                if v[width] < 0 {
                    return Err(ConstitutiveFibreError::Uncertain);
                }
                Ok(NativeFieldCurrentBall {
                    center: v[..width]
                        .chunks_exact(2)
                        .map(|v| {
                            ExactComplexWaveCurrent::new(
                                Rat::new(v[0].into(), scale.clone()),
                                Rat::new(v[1].into(), scale.clone()),
                            )
                        })
                        .collect(),
                    radius: Rat::new(v[width].into(), scale.clone()),
                })
            })
            .collect()
    }
}
impl<'c> ResidentNormalMaterial<'c> {
    /// Integrate all supplied point observations into the same normal geometry, then fit once.
    /// The row population is a measured section aperture. It is not a native clock or new
    /// coefficient population. Any failure precedes publication of the complete successor.
    pub fn receive_section<'a>(
        &mut self,
        source: ResidentConstitutiveSection<'a, 'c>,
        observed: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<ResidentNormalSectionReturn<'a, 'c>, ConstitutiveFibreError> {
        let returned = self.prepare_section(source, observed)?;
        self.publish_section(&returned);
        Ok(returned)
    }
    pub(super) fn publish_section(&mut self, returned: &ResidentNormalSectionReturn<'_, 'c>) {
        self.state = Rc::clone(&returned.successor);
        self.observations = returned.successor_observations;
    }
    pub(super) fn prepare_section<'a>(
        &self,
        source: ResidentConstitutiveSection<'a, 'c>,
        observed: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<ResidentNormalSectionReturn<'a, 'c>, ConstitutiveFibreError> {
        let layout =
            NormalLayout::new(self.roots, self.targets).ok_or(ConstitutiveFibreError::Shape)?;
        if source.rows() != observed.rows()
            || source.components() != layout.source_components
            || observed.components() != layout.target_components
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let count = self
            .observations
            .checked_add(source.rows() as u64)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let fresh = |width| self.surface.fresh_section(1, width, ResidentGrain(0));
        let next = fresh(layout.state_words)?;
        let before = self.surface.fresh_section(
            source.rows(),
            2 * (layout.target_components + 1),
            ResidentGrain(0),
        )?;
        let after = self
            .surface
            .fresh_section(source.rows(), before.width(), ResidentGrain(0))?;
        let work = fresh(layout.workspace_words)?;
        let input = fresh((layout.source_components + 1) * 4 + 3 * self.targets)?;
        let report = fresh(layout.report_words)?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_normal_material_section(
                &lane,
                &self.state,
                source,
                observed,
                self.roots,
                self.targets,
                self.grain.0,
                &next,
                &before,
                &after,
                &work,
                &input,
                &report,
            )?;
        }
        passage.close(0, &after, i64::BITS)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal section: {:?}",
                returned.obstruction
            )));
        }
        let predecessor_observations = self.observations;
        let successor = Rc::new(next);
        let prior = Rc::clone(&self.state);
        Ok(ResidentNormalSectionReturn {
            surface: self.surface,
            prior,
            successor,
            source,
            observed,
            before,
            after,
            roots: self.roots,
            targets: self.targets,
            grain: self.grain,
            predecessor_observations,
            successor_observations: count,
        })
    }
}

#[cfg(test)]
mod tests;
