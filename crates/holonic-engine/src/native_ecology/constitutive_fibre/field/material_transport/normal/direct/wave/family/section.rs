//! Conditional source sections used to evaluate an entire dependent return generator.
use super::*;
impl<'c> NormalWaveFamily<'c> {
    pub(in super::super) fn parameter_section(
        &self,
        parameters: &ResidentSection<'c>,
        anchor: &ResidentSection<'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        let s = self.origin.fibre().surface;
        let t = self.relation.target_width();
        let returned = ResidentConstitutiveReturn::allocate(
            s,
            1,
            t,
            self.relation.occurrence(),
            ConstitutiveSourceChart::Linear,
        )?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_coupled_family_section(
                &lane,
                self.relation.report(),
                self.relation.source_width(),
                t,
                parameters,
                anchor,
                returned.report(),
            )?;
        }
        passage.close(0, returned.report(), 64)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "dependent source section: {:?}",
                result.obstruction
            )));
        }
        Ok(returned)
    }
    /// The image and final map come from the actual retained word; source restriction has not
    /// changed its clock. The caller retains the parameter assignment and complete original domain.
    pub(in super::super) fn parameter_image(
        &self,
        relation: ResidentConstitutiveReturn<'c>,
        last: Rc<ResidentWaveRelation<'c>>,
        coverage: ResidentSection<'c>,
        passages: u64,
    ) -> Self {
        Self {
            origin: Rc::clone(&self.origin),
            relation,
            last_relation: Some(last),
            affine_coverage: Some(coverage),
            passages,
        }
    }
}
