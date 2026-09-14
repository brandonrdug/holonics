use super::*;

impl<'a, 'c> ResidentNormalEnclosureView<'a, 'c> {
    /// The same bilinear feature chart (a,h,h tensor a), with h fixed at its
    /// producing cut. Source uncertainty and numerical rounding remain bounded.
    pub fn bilinear_features(self,condition:ResidentConstitutiveCurrent<'_, 'c>)
        ->Result<ResidentNormalEnclosure<'c>,ConstitutiveFibreError>{
        let width=self.width.checked_mul(condition.width/2)
            .and_then(|v|v.checked_add(self.width)?.checked_add(condition.width))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let words=width.checked_add(1).and_then(|v|v.checked_mul(2)).ok_or(ConstitutiveFibreError::Shape)?;
        let section=self.surface.fresh_section(1,words,ResidentGrain(0))?;
        let mut p=self.surface.begin_passage(&[vec![]])?;
        {let lane=p.open(0,&[])?;self.surface.record_normal_enclosure_features(&lane,self,condition,&section)?;}
        p.close(0,&section,64)?;
        let r=p.finish()?.launch()?;
        if !r.obstruction.is_empty(){return Err(ConstitutiveFibreError::Arithmetic(format!(
            "enclosed bilinear features: {:?}",r.obstruction)));}
        Ok(ResidentNormalEnclosure{surface:self.surface,section,width,grain:self.grain})
    }
    /// Coordinate restriction of the declared ball. Indices count real coordinates
    /// and must retain whole complex pairs; the radius bounds the joint restriction.
    pub fn restrict(self,range:std::ops::Range<usize>)->Result<ResidentNormalEnclosure<'c>,ConstitutiveFibreError>{
        let width=range.end.checked_sub(range.start).ok_or(ConstitutiveFibreError::Shape)?;
        let words=width.checked_add(1).and_then(|v|v.checked_mul(2)).ok_or(ConstitutiveFibreError::Shape)?;
        let section=self.surface.fresh_section(1,words,ResidentGrain(0))?;
        let mut p=self.surface.begin_passage(&[vec![]])?;
        {let lane=p.open(0,&[])?;self.surface.record_normal_enclosure_restrict(&lane,self,range.start,width,&section)?;}
        p.close(0,&section,64)?;
        let r=p.finish()?.launch()?;
        if !r.obstruction.is_empty(){return Err(ConstitutiveFibreError::Arithmetic(format!(
            "enclosure restriction: {:?}",r.obstruction)));}
        Ok(ResidentNormalEnclosure{surface:self.surface,section,width,grain:self.grain})
    }
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
        self.difference_source_in_chart(WaveSourceReceiver::Direct)
    }
    pub fn difference_source_in_chart(&self,receiver:WaveSourceReceiver)
        ->Result<ResidentNormalEnclosure<'c>,ConstitutiveFibreError>{
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
                .record_normal_wave_source_in_chart(&lane, &self.section, roots, self.grain,
                    u32::from(receiver==WaveSourceReceiver::UnitRealSum), &section)?;
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
