use super::*;
impl<'c> ResidentNormalMaterial<'c> {
    /// Stage one conditional observation on the bilinear feature chart.  The supplied resident
    /// current ports may be views into larger packets; the feature passage consumes their
    /// offsets and denominators directly and the normal preparation owns the `u u*`/`eta u*`
    /// update.  No part of `self` is published until the complete CUDA passage succeeds.
    pub fn stage_bilinear_observation<'a>(
        &self,
        source: ResidentConstitutiveCurrent<'a, 'c>,
        condition: ResidentConstitutiveCurrent<'a, 'c>,
        observed: ResidentConstitutiveCurrent<'a, 'c>,
    ) -> Result<Self, ConstitutiveFibreError> {
        if source.width == 0
            || condition.width == 0
            || source.width % 2 != 0
            || condition.width % 2 != 0
            || observed.width
                != self
                    .targets
                    .checked_mul(2)
                    .ok_or(ConstitutiveFibreError::Shape)?
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let source_complex = source.width / 2;
        let condition_complex = condition.width / 2;
        let features = source_complex
            .checked_mul(condition_complex)
            .and_then(|n| n.checked_add(source_complex))
            .and_then(|n| n.checked_add(condition_complex))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if self.source_chart
            != (NormalSourceChart::Features {
                source_complex: features,
            })
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let feature_width = features
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let feature_section = self
            .surface
            .fresh_section(1, feature_width, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_constitutive_bilinear_source(
                &lane,
                source,
                condition,
                &feature_section,
            )?;
        }
        passage.close(0, &feature_section, i64::BITS)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "conditioned feature formation: {:?}",
                result.obstruction
            )));
        }
        let feature = ResidentConstitutiveCurrent::rational(&feature_section)?;
        self.stage_source_observation(feature, observed)
    }

    pub(crate) fn stage_source_observation<'a>(
        &self,
        source: impl Into<ResidentNormalInput<'a, 'c>>,
        observed: impl Into<ResidentNormalInput<'a, 'c>>,
    ) -> Result<Self, ConstitutiveFibreError>
    where
        'c: 'a,
    {
        let (_, next) = self.prepare(source.into(), Some(observed.into()))?;
        let state = next.ok_or(ConstitutiveFibreError::Shape)?;
        Ok(Self {
            surface: self.surface,
            state: Rc::new(state),
            source_chart: self.source_chart,
            targets: self.targets,
            grain: self.grain,
            observations: self
                .observations
                .checked_add(1)
                .ok_or(ConstitutiveFibreError::Shape)?,
        })
    }

    /// Immutable executable view of stored M on the declared bilinear feature chart, or of
    /// a Wave source's M(a) with zero condition/mixed coefficients. The Wave declaration
    /// supplies this condition-independent specialization; widths alone do not choose it.
    /// The caller retains this normal material and its normal-reference bounds. Graph
    /// axis rows are construction occurrences, not additional observations of the model.
    pub fn read_applied_bilinear_relation(
        &self,
        source_complex: usize,
        condition_complex: usize,
    ) -> Result<ResidentConstitutiveFibre<'c>, ConstitutiveFibreError> {
        let sources = source_complex
            .checked_mul(condition_complex)
            .and_then(|n| n.checked_add(source_complex))
            .and_then(|n| n.checked_add(condition_complex))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let admitted = match self.source_chart {
            NormalSourceChart::Features { source_complex } => source_complex == sources,
            NormalSourceChart::Wave { roots } => roots.checked_mul(3) == Some(source_complex),
        };
        if !admitted {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut relation = ResidentConstitutiveFibre::found_bilinear_contact(
            self.surface,
            source_complex,
            condition_complex,
            self.targets,
        )?;
        let w = relation
            .source_width
            .checked_add(relation.target_width)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let work = self.surface.fresh_section(1, 2 * w, ResidentGrain(0))?;
        let mut p = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            self.surface.record_normal_applied_relation(
                &lane,
                &self.state,
                self.source_complex(),
                sources,
                self.targets,
                self.grain.0,
                &relation.basis,
                &work,
            )?;
        }
        p.close(0, &relation.basis, 64)?;
        let returned = p.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "applied normal graph: {:?}",
                returned.obstruction
            )));
        }
        relation.occurrences = relation.source_width as u64;
        Ok(relation)
    }
}
