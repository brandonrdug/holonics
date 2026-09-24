use super::*;

/// Same-row exact source/condition packets, retaining both supplied sections.
pub struct ResidentBilinearFeatures<'a, 'c> {
    source: ResidentConstitutiveSection<'a, 'c>,
    conditions: ResidentConstitutiveSection<'a, 'c>,
    features: ResidentSection<'c>,
}

impl<'a, 'c> ResidentBilinearFeatures<'a, 'c> {
    pub fn source(&self) -> ResidentConstitutiveSection<'a, 'c> {
        self.source
    }
    pub fn conditions(&self) -> ResidentConstitutiveSection<'a, 'c> {
        self.conditions
    }
    pub fn features(&self) -> ResidentConstitutiveSection<'_, 'c> {
        ResidentConstitutiveSection::rationals(&self.features)
            .expect("completed resident bilinear features")
    }
    /// Transfer the joined packet for a delayed return. Its direct source and condition
    /// blocks remain present, followed by their products; the consumer retains that chart.
    pub fn into_features(self) -> ResidentSection<'c> {
        self.features
    }

    /// Return one feature covector to BOTH operands of the same row.
    ///
    /// `φ = [s, c, c⊗s]` is holomorphic in each operand, so the real transpose of its
    /// differential multiplies by the conjugate of the other operand:
    /// `g_s = g[s] + Σ_c conj(c) g[c⊗s]` and `g_c = g[c] + Σ_s conj(s) g[c⊗s]`. Hence
    /// `⟨Dφ[δs,δc], g⟩ = ⟨δs, g_s⟩ + ⟨δc, g_c⟩` in the interleaved real chart. The
    /// retained forward operands are the linearization point and stay exact point rows;
    /// each returned enclosure carries the radius this law transported to it. The pair is
    /// `(source covector, condition covector)`; neither is a state displacement.
    pub fn pull_back(
        &self,
        covector: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<
        (
            ResidentNormalEnclosureSection<'c>,
            ResidentNormalEnclosureSection<'c>,
        ),
        ConstitutiveFibreError,
    > {
        let surface = self.features.surface();
        let rows = self.source.rows();
        let source_complex = self.source.components() / 2;
        let condition_complex = self.conditions.components() / 2;
        let width = source_complex
            .checked_mul(condition_complex)
            .and_then(|n| n.checked_add(source_complex))
            .and_then(|n| n.checked_add(condition_complex))
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if covector.rows() != rows
            || covector.components() != width
            || !std::ptr::eq(covector.resident_section().surface(), surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let words = |components: usize| {
            components
                .checked_mul(2)
                .and_then(|n| n.checked_add(1)?.checked_mul(2))
                .ok_or(ConstitutiveFibreError::Shape)
        };
        let source_out =
            surface.fresh_section(rows, words(source_complex)?, ResidentGrain(0))?;
        let condition_out =
            surface.fresh_section(rows, words(condition_complex)?, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_bilinear_source_adjoint(
                &lane,
                self.source,
                self.conditions,
                covector.resident_section(),
                &source_out,
                &condition_out,
            )?;
        }
        passage.close(0, &source_out, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "bilinear source adjoint: {:?}",
                receipt.obstruction
            )));
        }
        Ok((
            ResidentNormalEnclosureSection::from_resident(
                surface,
                source_out,
                rows,
                2 * source_complex,
                covector.grain(),
            )?,
            ResidentNormalEnclosureSection::from_resident(
                surface,
                condition_out,
                rows,
                2 * condition_complex,
                covector.grain(),
            )?,
        ))
    }
}

impl<'a, 'c> ResidentConstitutiveSection<'a, 'c> {
    /// Form exact feature packets for each same-row source/condition contact in one passage.
    pub fn bilinear_features(
        self,
        surface: &'c ResidentSurface<'c>,
        conditions: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<ResidentBilinearFeatures<'a, 'c>, ConstitutiveFibreError> {
        if self.rows() == 0
            || self.rows() != conditions.rows()
            || self.components() % 2 != 0
            || conditions.components() % 2 != 0
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let source_complex = self.components() / 2;
        let condition_complex = conditions.components() / 2;
        let width = source_complex
            .checked_mul(condition_complex)
            .and_then(|n| n.checked_add(source_complex))
            .and_then(|n| n.checked_add(condition_complex))
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let features = surface.fresh_section(
            self.rows(),
            width.checked_add(1).ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            for row in 0..self.rows() {
                surface.record_constitutive_bilinear_source_row(
                    &lane,
                    self.row(row)?,
                    conditions.row(row)?,
                    &features,
                    row,
                )?;
            }
        }
        passage.close(0, &features, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "resident bilinear feature section: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentBilinearFeatures {
            source: self,
            conditions,
            features,
        })
    }
}
