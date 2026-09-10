//! Read the existing local law without advancing its material chronology or depositing a row.
use super::*;
impl<'c> ResidentConstitutiveFibre<'c> {
    pub fn read_resident(
        &self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        self.read_contact(source, None)
    }
    pub fn read_bilinear(
        &self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        self.read_contact(source, Some(condition))
    }
    fn read_contact(
        &self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        condition: Option<ResidentConstitutiveCurrent<'_, 'c>>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let valid = match (self.source_chart, condition) {
            (ConstitutiveSourceChart::Linear, None) => source.width == self.source_width,
            (
                ConstitutiveSourceChart::BilinearContact {
                    source_complex,
                    condition_complex,
                },
                Some(c),
            ) => source.width == 2 * source_complex && c.width == 2 * condition_complex,
            _ => false,
        };
        if !valid {
            return Err(ConstitutiveFibreError::Shape);
        }
        let returned = self.allocate_current_return(self.occurrences)?;
        let contact = condition
            .map(|_| {
                self.surface
                    .fresh_section(1, self.source_width + 1, ResidentGrain(0))
            })
            .transpose()?;
        let lineage = if contact.is_some() {
            vec![vec![], vec![0]]
        } else {
            vec![vec![]]
        };
        let mut passage = self.surface.begin_passage(&lineage)?;
        if let (Some(condition), Some(contact)) = (condition, contact.as_ref()) {
            {
                let lane = passage.open(0, &[])?;
                self.surface
                    .record_constitutive_bilinear_source(&lane, source, condition, contact)?;
            }
            passage.close(0, contact, 64)?;
        }
        let (at, parents) = if contact.is_some() {
            (1, vec![0])
        } else {
            (0, vec![])
        };
        {
            let lane = passage.open(at, &parents)?;
            let input = contact
                .as_ref()
                .map_or(source, |c| ResidentConstitutiveCurrent {
                    section: c,
                    offset: 0,
                    width: self.source_width,
                    denominator: Some(self.source_width),
                    disposition: None,
                });
            self.surface
                .record_constitutive_query(&lane, &self.basis, input, returned.report())?;
        }
        passage.close(at, returned.report(), 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "local generator reading: {:?}",
                receipt.obstruction
            )));
        }
        Ok(returned)
    }
}
