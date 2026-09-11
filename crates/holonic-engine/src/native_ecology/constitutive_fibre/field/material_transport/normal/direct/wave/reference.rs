use super::*;

/// A read-only normal-reference comparison from an actual held source. This has no current
/// occurrence of its own and cannot publish a successor. Refusal of this receiver leaves the
/// continuing applied transport untouched.
pub struct NormalWaveReference<'c> {
    source: Rc<ResidentSection<'c>>,
    fibre: NormalWaveFibre<'c>,
    next: ResidentSection<'c>,
}
#[derive(Debug, Serialize)]
pub struct NormalWaveReferenceReading {
    pub source_epoch: u64,
    pub source_transport: NormalWaveTransport,
    pub reference_next_joint: NativeFieldCurrentBall,
}
impl<'c> NormalWaveReference<'c> {
    pub fn source(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.fibre.surface,
            section: &self.source,
            offset: 0,
            width: 4 * self.fibre.roots,
            grain: self.fibre.grain,
        }
    }
    pub fn producing_fibre(&self) -> &NormalWaveFibre<'c> {
        &self.fibre
    }
    pub fn inspect(&self) -> Result<NormalWaveReferenceReading, ConstitutiveFibreError> {
        let reading = ResidentNormalEnclosureView {
            surface: self.fibre.surface,
            section: &self.next,
            offset: 0,
            width: 4 * self.fibre.roots,
            grain: self.fibre.grain,
        }
        .inspect()?;
        Ok(NormalWaveReferenceReading {
            source_epoch: self.fibre.epoch,
            source_transport: self.fibre.transport,
            reference_next_joint: reading,
        })
    }
}
impl<'c> ResidentNormalWave<'c> {
    /// Read one ideal-normal-family continuation from the complete contemporary source. This
    /// separate receiver pays the M/P comparison, without turning it into the next applied input.
    pub fn reference_next(&self) -> Result<NormalWaveReference<'c>, ConstitutiveFibreError> {
        let s = self.material.surface;
        let n = self.material.roots;
        let d = 2 * n;
        let seed = self.material.prepare_joint_seed(&self.joint, self.epoch)?;
        let fresh = |w| s.fresh_section(1, w, ResidentGrain(0));
        let power = fresh(4 * d * d)?;
        let metadata = fresh(8)?;
        let joint = fresh(2 * (2 * d + 1))?;
        let current = fresh(2 * (d + 1))?;
        let work = fresh(6 * d)?;
        let mut passage = s.begin_passage(&[vec![], vec![0]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_wave_power(
                &lane,
                &self.material.state,
                &seed.power,
                n,
                self.material.grain.0,
                &power,
            )?;
        }
        passage.close(0, &power, i64::BITS)?;
        {
            let lane = passage.open(1, &[0])?;
            s.record_normal_wave_evaluate(
                &lane,
                &self.material.state,
                &power,
                &self.joint,
                &seed.metadata,
                n,
                self.material.grain.0,
                1,
                &metadata,
                &joint,
                &current,
                &work,
                true,
            )?;
        }
        passage.close(1, &joint, i64::BITS)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal reference receiver: {:?}",
                result.obstruction
            )));
        }
        Ok(NormalWaveReference {
            source: Rc::clone(&self.joint),
            fibre: self.fibre(),
            next: joint,
        })
    }
}
