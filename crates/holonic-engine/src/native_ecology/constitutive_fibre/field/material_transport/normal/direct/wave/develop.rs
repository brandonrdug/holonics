use super::*;

/// Actual section operands and producing material cuts accompany the development return.
/// The body retains the changed material and current seed, not these source sections.
pub struct NormalWaveDevelopment<'a, 'c> {
    pub comparison: ResidentNormalSectionReturn<'a, 'c>,
    pub predecessor_fibre: NormalWaveFibre<'c>,
    pub successor_fibre: NormalWaveFibre<'c>,
    pub rebased_joint_enclosure: bool,
}

struct JointSeed<'c> {
    power: ResidentSection<'c>,
    metadata: ResidentSection<'c>,
    previous: NormalWaveCurrent<'c>,
    current: NormalWaveCurrent<'c>,
}
impl<'c> ResidentNormalMaterial<'c> {
    fn prepare_joint_seed(
        &self,
        joint: &ResidentSection<'c>,
        epoch: u64,
    ) -> Result<JointSeed<'c>, ConstitutiveFibreError> {
        let s = self.surface;
        let r = 2 * self.roots;
        let fresh = |w| s.fresh_section(1, w, ResidentGrain(0));
        let previous = fresh(2 * (r + 1))?;
        let current = fresh(2 * (r + 1))?;
        let power = fresh(4 * r * r)?;
        let metadata = fresh(8)?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_wave_joint_seed(
                &lane,
                joint,
                self.roots,
                self.grain.0,
                &previous,
                &current,
                &power,
                &metadata,
            )?;
        }
        passage.close(0, &current, i64::BITS)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "joint wave seed: {:?}",
                returned.obstruction
            )));
        }
        let wrap = |section, at| NormalWaveCurrent {
            inner: Rc::new(WaveCurrent { section, at }),
            surface: s,
            width: r,
            grain: self.grain,
        };
        Ok(JointSeed {
            power,
            metadata,
            previous: wrap(previous, epoch.checked_sub(1)),
            current: wrap(current, Some(epoch)),
        })
    }
    pub(super) fn into_joint_wave(
        self,
        joint: Rc<ResidentSection<'c>>,
        epoch: u64,
    ) -> Result<ResidentNormalWave<'c>, NormalWaveSeedRefusal<'c>> {
        match self.prepare_joint_seed(&joint, epoch) {
            Ok(JointSeed {
                power,
                metadata,
                previous,
                current,
            }) => Ok(ResidentNormalWave {
                material: self,
                seed: Rc::clone(&joint),
                seed_bound: Rc::clone(&joint),
                joint,
                seed_kind: NormalWaveSeedKind::JointEnclosure,
                epoch,
                power,
                metadata: Rc::new(metadata),
                previous,
                current,
                steps: 0,
            }),
            Err(reason) => Err(NormalWaveSeedRefusal {
                material: self,
                reason,
            }),
        }
    }
}
impl<'c> ResidentNormalWave<'c> {
    /// Develop the current generator from a measured source/target section. This creates no
    /// emitted/received current and does not invent adjacency with the supplied field.
    /// Current occurrence identity and epoch remain; observation geometry changes atomically.
    pub fn develop_section<'a>(
        &mut self,
        source: ResidentConstitutiveSection<'a, 'c>,
        observed: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<NormalWaveDevelopment<'a, 'c>, ConstitutiveFibreError> {
        let comparison = self.material.prepare_section(source, observed)?;
        let staged = if self.steps > 0 {
            Some(self.material.prepare_joint_seed(&self.joint, self.epoch)?)
        } else {
            None
        };
        let predecessor_fibre = self.fibre();
        let rebased_joint_enclosure = staged.is_some();
        if let Some(JointSeed {
            power, metadata, ..
        }) = staged
        {
            // Keep the ACTUAL current occurrences. The staged marginal views are only
            // needed by a cold decoder; no new current occurs during material development.
            self.seed = Rc::clone(&self.joint);
            self.seed_bound = Rc::clone(&self.joint);
            self.seed_kind = NormalWaveSeedKind::JointEnclosure;
            self.power = power;
            self.metadata = Rc::new(metadata);
            self.steps = 0;
        }
        self.material.publish_section(&comparison);
        Ok(NormalWaveDevelopment {
            comparison,
            predecessor_fibre,
            successor_fibre: self.fibre(),
            rebased_joint_enclosure,
        })
    }
}
