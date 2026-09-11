use super::*;
/// The source φ(p,c)=(c−p,c,p), retaining the actual comparands and generating joint.
/// Its outward ball is a receiver of that shared family, not three independent sources.
pub struct NormalWaveSource<'c> {
    previous: NormalWaveCurrent<'c>,
    current: NormalWaveCurrent<'c>,
    fibre: NormalWaveFibre<'c>,
    joint: Rc<ResidentSection<'c>>,
    source: ResidentSection<'c>,
}
impl<'c> NormalWaveSource<'c> {
    pub fn previous(&self) -> &NormalWaveCurrent<'c> {
        &self.previous
    }
    pub fn current(&self) -> &NormalWaveCurrent<'c> {
        &self.current
    }
    pub fn fibre(&self) -> &NormalWaveFibre<'c> {
        &self.fibre
    }
    pub fn joint(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.fibre.surface,
            section: &self.joint,
            offset: 0,
            width: 4 * self.fibre.roots,
            grain: self.fibre.grain,
        }
    }
    pub fn enclosure(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.fibre.surface,
            section: &self.source,
            offset: 0,
            width: 6 * self.fibre.roots,
            grain: self.fibre.grain,
        }
    }
}
impl<'c> ResidentNormalWave<'c> {
    /// Read the explicit source relation without advancing or narrowing the continuing current.
    pub fn read_source(&self) -> Result<NormalWaveSource<'c>, ConstitutiveFibreError> {
        let s = self.material.surface;
        let width = self
            .material
            .roots
            .checked_mul(12)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let source = s.fresh_section(1, width, ResidentGrain(0))?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_wave_source(&lane, &self.joint, self.material.roots, &source)?;
        }
        passage.close(0, &source, 64)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "wave source lift: {:?}",
                returned.obstruction
            )));
        }
        Ok(NormalWaveSource {
            previous: self.previous.snapshot(),
            current: self.current.snapshot(),
            fibre: self.fibre(),
            joint: Rc::clone(&self.joint),
            source,
        })
    }
}
#[cfg(test)]
mod tests;
