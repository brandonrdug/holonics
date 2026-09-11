use super::*;
/// The actual joint source and its generating fibre. Its lifetime does not depend on whether
/// a particular outward image bound fits a receiver's carrier.
pub struct NormalWaveJointSource<'c> {
    previous: NormalWaveCurrent<'c>,
    current: NormalWaveCurrent<'c>,
    fibre: NormalWaveFibre<'c>,
    joint: Rc<ResidentSection<'c>>,
}
/// The source φ(p,c)=(c−p,c,p) observed through its outward ball. The retained joint
/// precedes this receiver; failure of this bound need not stop another family operation.
pub struct NormalWaveSource<'c> {
    origin: NormalWaveJointSource<'c>,
    source: ResidentSection<'c>,
}
impl<'c> NormalWaveJointSource<'c> {
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
    pub fn read_source(&self) -> Result<NormalWaveSource<'c>, ConstitutiveFibreError> {
        let s = self.fibre.surface;
        let width = self
            .fibre
            .roots
            .checked_mul(12)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let source = s.fresh_section(1, width, ResidentGrain(0))?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_wave_source(&lane, &self.joint, self.fibre.roots, &source)?;
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
            origin: Self {
                previous: self.previous.snapshot(),
                current: self.current.snapshot(),
                fibre: self.fibre.snapshot(),
                joint: Rc::clone(&self.joint),
            },
            source,
        })
    }
}
impl<'c> NormalWaveSource<'c> {
    pub fn previous(&self) -> &NormalWaveCurrent<'c> {
        self.origin.previous()
    }
    pub fn current(&self) -> &NormalWaveCurrent<'c> {
        self.origin.current()
    }
    pub fn fibre(&self) -> &NormalWaveFibre<'c> {
        self.origin.fibre()
    }
    pub fn joint(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.origin.joint()
    }
    pub fn enclosure(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.origin.fibre.surface,
            section: &self.source,
            offset: 0,
            width: 6 * self.origin.fibre.roots,
            grain: self.origin.fibre.grain,
        }
    }
}
impl<'c> ResidentNormalWave<'c> {
    pub fn joint_source(&self) -> NormalWaveJointSource<'c> {
        NormalWaveJointSource {
            previous: self.previous.snapshot(),
            current: self.current.snapshot(),
            fibre: self.fibre(),
            joint: Rc::clone(&self.joint),
        }
    }
    pub fn read_source(&self) -> Result<NormalWaveSource<'c>, ConstitutiveFibreError> {
        self.joint_source().read_source()
    }
}
#[cfg(test)]
mod tests;
