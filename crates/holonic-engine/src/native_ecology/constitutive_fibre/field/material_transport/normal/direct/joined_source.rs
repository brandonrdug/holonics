use super::*;

impl<'a, 'c> ResidentNormalEnclosureView<'a, 'c> {
    /// An outer enclosure of the paired source. This does not assert independence or erase
    /// the finer relationship retained by the producing sources. Both grains must agree.
    pub fn join(self, other: Self) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        self.pair_receiver(other, 1)
    }
    /// The oriented receiver self-other. The same immutable source cancels exactly, including
    /// its uncertainty; distinct sources retain the sum bound on their difference.
    pub fn difference(
        self,
        other: Self,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        self.pair_receiver(other, 2)
    }
    pub fn to_owned(self) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        self.pair_receiver(self, 0)
    }
    fn pair_receiver(
        self,
        other: Self,
        kind: u32,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        if self.grain != other.grain
            || !std::ptr::eq(self.surface, other.surface)
            || (kind == 2 && self.width != other.width)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let width = if kind == 1 {
            self.width
                .checked_add(other.width)
                .ok_or(ConstitutiveFibreError::Shape)?
        } else {
            self.width
        };
        let words = width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let section = self.surface.fresh_section(1, words, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface
                .record_normal_enclosure_pair(&lane, self, other, kind, &section)?;
        }
        passage.close(0, &section, 64)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "enclosure receiver: {:?}",
                result.obstruction
            )));
        }
        Ok(ResidentNormalEnclosure {
            surface: self.surface,
            section,
            width,
            grain: self.grain,
        })
    }
}
impl<'c> ResidentNormalEnclosure<'c> {
    /// Apply phi(p,c)=(c-p,c,p) to one paired source enclosure. The complete paired source
    /// stays available on self; this is its existing outward wave-source receiver.
    pub fn difference_source(&self) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        if self.width == 0 || self.width % 4 != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let roots = self.width / 4;
        let width = roots.checked_mul(6).ok_or(ConstitutiveFibreError::Shape)?;
        let section = self
            .surface
            .fresh_section(1, 2 * (width + 1), ResidentGrain(0))?;
        let mut p = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            self.surface
                .record_normal_wave_source(&lane, &self.section, roots, &section)?;
        }
        p.close(0, &section, 64)?;
        let r = p.finish()?.launch()?;
        if !r.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "paired source lift: {:?}",
                r.obstruction
            )));
        }
        Ok(ResidentNormalEnclosure {
            surface: self.surface,
            section,
            width,
            grain: self.grain,
        })
    }
}
