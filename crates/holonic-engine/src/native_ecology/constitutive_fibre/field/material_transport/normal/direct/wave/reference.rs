use super::*;

impl<'c> ResidentNormalWave<'c> {
    /// Read one ideal-normal-family continuation from the complete contemporary source. This
    /// separate receiver pays the M/P comparison, without turning it into the next applied input.
    pub fn reference_next<'a>(&self) -> Result<NormalWavePassage<'a, 'c>, ConstitutiveFibreError> {
        let s = self.material.surface;
        let n = self.material.roots();
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
        // A pure receiver: the predecessor and successor are the same unchanged point.
        let mut passage =
            NormalWavePassage::new(NormalPassageKind::Reference, self.fibre(), self.fibre());
        passage.source_joint = Some(Rc::clone(&self.joint));
        passage.produced_joint = Some(Rc::new(joint));
        Ok(passage)
    }
}
