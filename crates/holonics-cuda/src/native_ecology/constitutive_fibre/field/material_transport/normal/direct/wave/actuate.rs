use super::develop::JointSeed;
use super::*;

impl<'c> ResidentNormalWave<'c> {
    /// Act on held reference/current standing using the passive-contact law of each source
    /// pair and its learned joined arrival. This updates both current components under one
    /// source occurrence. It does not refit material or increment its observation count.
    pub fn actuate_section<'a>(
        &mut self,
        source: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<NormalWavePassage<'a, 'c>, ConstitutiveFibreError> {
        let n = self.material.roots();
        if source.rows() < 2 || source.components() != 2 * n {
            return Err(ConstitutiveFibreError::Shape);
        }
        let epoch = self
            .epoch
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let s = self.material.surface;
        let r = 2 * n;
        let w = 2 * r;
        let d = 3 * r;
        let fresh = |width| s.fresh_section(1, width, ResidentGrain(0));
        let joint = fresh(2 * (w + 1))?;
        let anchors = fresh(2 * (2 * (w + 1) + (r + 1)))?;
        let frame = fresh(4 * (d + 1))?;
        let work = fresh(4 * n)?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_source_actuation(
                &lane,
                &self.material.state,
                &self.joint,
                source,
                n,
                self.material.grain.0,
                &joint,
                &anchors,
                &frame,
                &work,
                self.transport.is_reference(),
            )?;
        }
        passage.close(0, &joint, i64::BITS)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "source actuation: {:?}",
                returned.obstruction
            )));
        }
        let JointSeed {
            power,
            metadata,
            mut previous,
            current,
        } = self.material.prepare_joint_seed(&joint, epoch)?;
        // Both are contemporary images of the held section under this source action.
        // The old immutable currents remain available in their producing receipts.
        Rc::get_mut(&mut previous.inner)
            .expect("unpublished source reference")
            .at = Some(epoch);
        let predecessor_fibre = self.fibre();
        let before = Rc::clone(&self.joint);
        self.joint = Rc::new(joint);
        self.seed = Rc::clone(&self.joint);
        self.seed_bound = Rc::clone(&self.joint);
        self.seed_kind = NormalWaveSeedKind::JointEnclosure;
        self.seed_epochs = [previous.at(), current.at()];
        self.power = power;
        self.metadata = Rc::new(metadata);
        self.previous = previous;
        self.current = current;
        self.epoch = epoch;
        self.steps = 0;
        let mut passage =
            NormalWavePassage::new(NormalPassageKind::Actuate, predecessor_fibre, self.fibre());
        passage.section = Some(source);
        passage.source_joint = Some(before);
        passage.produced_joint = Some(Rc::clone(&self.joint));
        Ok(passage)
    }
}
