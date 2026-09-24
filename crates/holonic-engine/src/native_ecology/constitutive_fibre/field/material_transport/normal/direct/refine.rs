use super::*;

impl<'c> ResidentNormalMaterial<'c> {
    /// Refine the numerical realization to a finer grain. The exact moments (the constitution's
    /// storage and source) are unchanged; only the applied coefficients' realization error
    /// shrinks. Returns the predecessor constitution: a shared cut of the section it replaced
    /// (its `inspect()` is the before-reading; `self.inspect()` the after-reading).
    pub fn refine_realization(
        &mut self,
        grain: ResidentGrain,
    ) -> Result<ResidentNormalMaterial<'c>, ConstitutiveFibreError> {
        if grain.0 <= self.grain.0 || grain.0 > 120 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let layout = self.source_chart.layout(self.targets)?;
        let next = self
            .surface
            .fresh_section(1, layout.state_words, ResidentGrain(0))?;
        let work = self
            .surface
            .fresh_section(1, layout.workspace_words, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_normal_refine(
                &lane,
                &self.state,
                self.source_complex(),
                self.targets,
                self.grain.0,
                grain.0,
                &next,
                &work,
            )?;
        }
        passage.close(0, &next, 64)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal realization refinement: {:?}",
                returned.obstruction
            )));
        }
        let predecessor = self.clone();
        self.state = Rc::new(next);
        self.grain = grain;
        Ok(predecessor)
    }
}
