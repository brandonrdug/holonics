use super::*;
mod difference;
pub use difference::ResidentDifferenceSection;

/// A borrowed measured section. Rows are addresses in this exterior/current chart, not
/// intrinsic Holon identities or model clock ticks. The device still validates pointness.
#[derive(Clone, Copy)]
pub struct ResidentConstitutiveSection<'a, 'c> {
    pub(crate) section: &'a ResidentSection<'c>,
    pub(crate) width: usize,
    pub(crate) rational: bool,
}
impl<'a, 'c> ResidentConstitutiveSection<'a, 'c> {
    pub fn integers(section: &'a ResidentSection<'c>) -> Result<Self, ConstitutiveFibreError> {
        Self::found(section, false)
    }
    pub fn rationals(section: &'a ResidentSection<'c>) -> Result<Self, ConstitutiveFibreError> {
        Self::found(section, true)
    }
    fn found(
        section: &'a ResidentSection<'c>,
        rational: bool,
    ) -> Result<Self, ConstitutiveFibreError> {
        let width = section
            .width()
            .checked_sub(usize::from(rational))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if section.rows() == 0 || width == 0 || section.grain().0 != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(Self {
            section,
            width,
            rational,
        })
    }
    pub fn rows(&self) -> usize {
        self.section.rows()
    }
    pub fn components(&self) -> usize {
        self.width
    }
    pub fn row(
        &self,
        row: usize,
    ) -> Result<ResidentConstitutiveCurrent<'a, 'c>, ConstitutiveFibreError> {
        if row >= self.rows() {
            return Err(ConstitutiveFibreError::Shape);
        }
        let offset = row
            .checked_mul(self.section.width())
            .ok_or(ConstitutiveFibreError::Shape)?;
        Ok(ResidentConstitutiveCurrent {
            section: self.section,
            offset,
            width: self.width,
            denominator: self.rational.then_some(offset + self.width),
            disposition: None,
        })
    }
}
