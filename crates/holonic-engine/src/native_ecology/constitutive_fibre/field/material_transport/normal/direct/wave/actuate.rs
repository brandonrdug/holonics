use super::develop::JointSeed;
use super::*;

/// A source word of learned joined passages acting on the actual held joint current.
/// Source sections are borrowed evidence. Material is shared immutable producing standing.
pub struct NormalSourceActuation<'a, 'c> {
    source: ResidentConstitutiveSection<'a, 'c>,
    predecessor_fibre: NormalWaveFibre<'c>,
    successor_fibre: NormalWaveFibre<'c>,
    before: Rc<ResidentSection<'c>>,
    after: Rc<ResidentSection<'c>>,
}
impl<'a, 'c> NormalSourceActuation<'a, 'c> {
    pub fn predecessor_fibre(&self) -> &NormalWaveFibre<'c> {
        &self.predecessor_fibre
    }
    pub fn successor_fibre(&self) -> &NormalWaveFibre<'c> {
        &self.successor_fibre
    }

    pub fn source(&self) -> ResidentConstitutiveSection<'a, 'c> {
        self.source
    }
    fn view<'r>(&'r self, section: &'r ResidentSection<'c>) -> ResidentNormalEnclosureView<'r, 'c> {
        ResidentNormalEnclosureView {
            surface: self.successor_fibre.surface,
            section,
            offset: 0,
            width: 4 * self.successor_fibre.roots,
            grain: self.successor_fibre.grain,
        }
    }
    pub fn before(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.view(&self.before)
    }
    pub fn after(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.view(&self.after)
    }
}
impl<'c> ResidentNormalWave<'c> {
    /// Act on held reference/current standing using the passive-contact law of each source
    /// pair and its learned joined arrival. This updates both current components under one
    /// source occurrence. It does not refit material or increment its observation count.
    pub fn actuate_section<'a>(
        &mut self,
        source: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<NormalSourceActuation<'a, 'c>, ConstitutiveFibreError> {
        let n = self.material.roots;
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
        Ok(NormalSourceActuation {
            source,
            predecessor_fibre,
            successor_fibre: self.fibre(),
            before,
            after: Rc::clone(&self.joint),
        })
    }
}
