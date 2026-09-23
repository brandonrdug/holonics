use super::*;
/// [definition] **A point on the normal wave Holon** (plan phase 9; core `HolonState`): the
/// previous and current occurrences, their joint enclosure `(p, c)` and the generating fibre
/// (constitution, seed and word) that produced it. Its lifetime does not depend on whether a
/// particular outward image bound fits a receiver's carrier. `NormalWaveStep` and
/// `NormalWaveJointSource` are this type.
pub struct NormalWaveState<'c> {
    pub(super) previous: NormalWaveCurrent<'c>,
    pub(super) current: NormalWaveCurrent<'c>,
    pub(super) fibre: NormalWaveFibre<'c>,
    pub(super) joint: Rc<ResidentSection<'c>>,
    pub(super) metadata: Rc<ResidentSection<'c>>,
}
/// Compatibility name of [`NormalWaveState`].
pub type NormalWaveJointSource<'c> = NormalWaveState<'c>;
impl<'c> NormalWaveState<'c> {
    /// Share this immutable producing source; the continuing generator is not cloned.
    pub fn snapshot(&self) -> Self {
        Self {
            previous: self.previous.snapshot(),
            current: self.current.snapshot(),
            fibre: self.fibre.snapshot(),
            joint: Rc::clone(&self.joint),
            metadata: Rc::clone(&self.metadata),
        }
    }
    pub fn inspect(&self) -> Result<NormalWaveReading, ConstitutiveFibreError> {
        let surface = self.current.surface;
        let meta = wides(&surface.read_out(&self.metadata)?)?;
        // The native metadata packet has four wide fields; this reading exposes its first
        // three numerical bounds. The fourth is the joint-current radius, also retained
        // in the joint enclosure decoded below.
        if meta.len() != 4 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let scale = BigInt::one() << self.current.grain.0;
        let joint = ResidentNormalEnclosureView {
            surface,
            section: &self.joint,
            offset: 0,
            width: 2 * self.current.width,
            grain: self.current.grain,
        }
        .inspect()?;
        Ok(NormalWaveReading {
            transport: self.fibre.transport,
            steps: self.fibre.steps,
            maximum_computed_power_norm: Rat::from_integer(meta[0].into()),
            uniform_power_equation_defect: Rat::new(meta[1].into(), scale.clone()),
            operator_word_error: Rat::new(meta[2].into(), scale),
            joint_current: joint,
        })
    }
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
    /// The lifted source `φ(p,c) = (c−p, c, p)` of this point, observed through its outward
    /// ball (`6n` real components). The retained joint precedes this receiver; failure of this
    /// bound need not stop another family operation.
    pub fn read_source(&self) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
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
        Ok(ResidentNormalEnclosure {
            surface: s,
            section: source,
            width: 6 * self.fibre.roots,
            grain: self.fibre.grain,
        })
    }
}
impl<'c> ResidentNormalWave<'c> {
    pub fn joint_source(&self) -> NormalWaveState<'c> {
        NormalWaveState {
            previous: self.previous.snapshot(),
            current: self.current.snapshot(),
            fibre: self.fibre(),
            joint: Rc::clone(&self.joint),
            metadata: Rc::clone(&self.metadata),
        }
    }
    pub fn read_source(&self) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        self.joint_source().read_source()
    }
}
#[cfg(test)]
mod tests;
