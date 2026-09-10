use super::*;

/// Both x=(c-p,c,p) and y=v-c come from the retained joint pair and actual received point.
/// The numerical moment envelopes overapproximate that shared family, not independent causes.
pub struct NormalWaveReception<'c> {
    pub previous: NormalWaveCurrent<'c>,
    pub current: NormalWaveCurrent<'c>,
    pub predecessor_fibre: NormalWaveFibre<'c>,
    pub successor_fibre: NormalWaveFibre<'c>,
    source_joint: Rc<ResidentSection<'c>>,
    report: ResidentSection<'c>,
}
#[derive(Debug, Serialize)]
pub struct NormalWaveReceptionReading {
    pub epoch: u64,
    pub source_joint: NativeFieldCurrentBall,
    pub comparison: NativeNormalMaterialReading,
}
impl<'c> NormalWaveReception<'c> {
    pub fn source_joint(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.current.surface,
            section: &self.source_joint,
            offset: 0,
            width: 2 * self.current.width,
            grain: self.current.grain,
        }
    }
    pub fn inspect(&self) -> Result<NormalWaveReceptionReading, ConstitutiveFibreError> {
        let fibre = &self.successor_fibre;
        Ok(NormalWaveReceptionReading {
            epoch: fibre.epoch,
            source_joint: self.source_joint().inspect()?,
            comparison: decode_report(
                &fibre.surface.detach_section(&self.report, i64::BITS)?,
                fibre.roots,
                fibre.roots,
                fibre.grain.0,
                true,
            )?,
        })
    }
}
impl<'c> ResidentNormalWave<'c> {
    /// Receive an actual next current in this generator's receiver chart. Publish the changed
    /// material and (c,v) together, preserving c's occurrence. Rebase to its full enclosure:
    /// this bounds the preceding family; it does not assert an exact future quotient.
    pub fn receive(
        &mut self,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<NormalWaveReception<'c>, ConstitutiveFibreError> {
        let epoch = self
            .epoch
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let count = self
            .material
            .observations
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let staged = self
            .material
            .prepare_wave_seed(self.current.view().into(), observed)?;
        let s = self.material.surface;
        let n = self.material.roots;
        let layout = NormalLayout::new(n, n).ok_or(ConstitutiveFibreError::Shape)?;
        let fresh = |w| s.fresh_section(1, w, ResidentGrain(0));
        let next = fresh(layout.state_words)?;
        let report = fresh(layout.report_words)?;
        let work = fresh(layout.workspace_words)?;
        let input = fresh(4 * (layout.source_components + 1))?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_wave_receive(
                &lane,
                &self.material.state,
                &self.joint,
                observed,
                n,
                self.material.grain.0,
                &next,
                &report,
                &work,
                &input,
            )?;
        }
        passage.close(0, &report, i64::BITS)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "wave reception: {:?}",
                returned.obstruction
            )));
        }
        let predecessor_fibre = self.fibre();
        let source_joint = Rc::clone(&self.joint);
        let StagedWaveSeed {
            seed,
            seed_bound,
            power,
            metadata,
            previous: _,
            mut current,
        } = staged;
        // This just-created occurrence has no aliases yet; the old c is moved, never remounted.
        Rc::get_mut(&mut current.inner)
            .expect("unpublished received current")
            .at = Some(epoch);
        self.previous = std::mem::replace(&mut self.current, current);
        self.material.state = Rc::new(next);
        self.material.observations = count;
        self.seed = Rc::new(seed);
        self.seed_bound = Rc::new(seed_bound);
        self.joint = Rc::clone(&self.seed_bound);
        self.power = power;
        self.metadata = Rc::new(metadata);
        self.steps = 0;
        self.epoch = epoch;
        self.seed_kind = NormalWaveSeedKind::ReceivedCurrent;
        Ok(NormalWaveReception {
            previous: self.previous.snapshot(),
            current: self.current.snapshot(),
            predecessor_fibre,
            successor_fibre: self.fibre(),
            source_joint,
            report,
        })
    }
}
