use super::*;

/// The supplied current path and its complete local comparisons. The two support endpoints
/// have no such three-site comparison; no boundary value or successor outside the source is invented.
pub struct ResidentDifferenceSection<'a, 'c> {
    original: ResidentConstitutiveSection<'a, 'c>,
    source: ResidentSection<'c>,
    observed: ResidentSection<'c>,
}
impl<'a, 'c> ResidentDifferenceSection<'a, 'c> {
    pub fn original(&self) -> ResidentConstitutiveSection<'a, 'c> {
        self.original
    }
    pub fn source(&self) -> ResidentConstitutiveSection<'_, 'c> {
        ResidentConstitutiveSection::rationals(&self.source).expect("completed difference source")
    }
    pub fn observed(&self) -> ResidentConstitutiveSection<'_, 'c> {
        ResidentConstitutiveSection::rationals(&self.observed)
            .expect("completed difference receiver")
    }
}
impl<'a, 'c> ResidentConstitutiveSection<'a, 'c> {
    pub fn differences(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<ResidentDifferenceSection<'a, 'c>, ConstitutiveFibreError> {
        let rows = self
            .rows()
            .checked_sub(2)
            .filter(|n| *n > 0)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let source_width = self
            .width
            .checked_mul(3)
            .and_then(|n| n.checked_add(1))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let source = surface.fresh_section(rows, source_width, ResidentGrain(0))?;
        let observed = surface.fresh_section(rows, self.width + 1, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_current_difference_section(&lane, self, &source, &observed)?;
        }
        passage.close(0, &source, i64::BITS)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "current difference section: {:?}",
                returned.obstruction
            )));
        }
        Ok(ResidentDifferenceSection {
            original: self,
            source,
            observed,
        })
    }
}

/// Complete ordered adjacent source pairs, with their original supplied field. This makes
/// source incidence; it neither asserts an outside endpoint nor supplies a fitting target.
pub struct ResidentSourcePairs<'a, 'c> {
    original: ResidentConstitutiveSection<'a, 'c>,
    source: ResidentSection<'c>,
}
impl<'a, 'c> ResidentSourcePairs<'a, 'c> {
    pub fn original(&self) -> ResidentConstitutiveSection<'a, 'c> {
        self.original
    }
    pub fn source(&self) -> ResidentConstitutiveSection<'_, 'c> {
        ResidentConstitutiveSection::rationals(&self.source).expect("completed source pairs")
    }
}
impl<'a, 'c> ResidentConstitutiveSection<'a, 'c> {
    pub fn source_pairs(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<ResidentSourcePairs<'a, 'c>, ConstitutiveFibreError> {
        let rows = self
            .rows()
            .checked_sub(1)
            .filter(|r| *r > 0)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let width = self
            .width
            .checked_mul(3)
            .and_then(|v| v.checked_add(1))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let source = surface.fresh_section(rows, width, ResidentGrain(0))?;
        let workspace = surface.fresh_section(rows, 2 * (width - 1), ResidentGrain(0))?;
        let mut p = surface.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            surface.record_wave_source_pairs(&lane, self, &source, &workspace)?;
        }
        p.close(0, &source, 64)?;
        let receipt = p.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "source pairs: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentSourcePairs {
            original: self,
            source,
        })
    }
}
