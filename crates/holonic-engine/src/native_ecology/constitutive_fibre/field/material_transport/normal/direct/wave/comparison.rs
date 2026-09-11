use super::*;

/// One active producing cut, shared immutably until its comparison is returned or released.
/// This is not another continuing wave and contains no archive of source observations.
pub(super) struct ProducingCut<'c> {
    pub(super) joint: Rc<ResidentSection<'c>>,
    pub(super) fibre: NormalWaveFibre<'c>,
}

/// A capability for one prediction of this continuing owner. Its serial address alone is not
/// authority: the private owner identity and retained producing cut must still agree.
pub struct NormalProducingHandle {
    owner: Rc<()>,
    id: u64,
}
impl NormalProducingHandle {
    pub fn id(&self) -> u64 {
        self.id
    }
}

pub struct NormalWavePrediction<'c> {
    pub step: NormalWaveStep<'c>,
    pub handle: NormalProducingHandle,
}

/// The observed point and its producing joint remain the operands of the comparison. The
/// complete contemporary current is unchanged by this material-only return. Numerical moment
/// envelopes may enlarge the shared source family; the finer generating cut remains available.
pub struct NormalWaveComparison<'a, 'c> {
    prediction_id: u64,
    source: Rc<ProducingCut<'c>>,
    observed: ResidentConstitutiveCurrent<'a, 'c>,
    report: ResidentSection<'c>,
    pub predecessor_fibre: NormalWaveFibre<'c>,
    pub successor_fibre: NormalWaveFibre<'c>,
}

#[derive(Debug, Serialize)]
pub struct NormalWaveComparisonReading {
    pub prediction_id: u64,
    pub producing_epoch: u64,
    pub producing_transport: NormalWaveTransport,
    pub successor_transport: NormalWaveTransport,
    pub source_joint: NativeFieldCurrentBall,
    pub comparison: NativeNormalMaterialReading,
}
impl<'a, 'c> NormalWaveComparison<'a, 'c> {
    pub fn observed(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.observed
    }
    pub fn producing_fibre(&self) -> &NormalWaveFibre<'c> {
        &self.source.fibre
    }
    pub fn source_joint(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        let f = &self.source.fibre;
        ResidentNormalEnclosureView {
            surface: f.surface,
            section: &self.source.joint,
            offset: 0,
            width: 4 * f.roots,
            grain: f.grain,
        }
    }
    pub fn inspect(&self) -> Result<NormalWaveComparisonReading, ConstitutiveFibreError> {
        let f = &self.source.fibre;
        Ok(NormalWaveComparisonReading {
            prediction_id: self.prediction_id,
            producing_epoch: f.epoch,
            producing_transport: f.transport,
            successor_transport: self.successor_fibre.transport,
            source_joint: self.source_joint().inspect()?,
            comparison: decode_report(
                &f.surface.detach_section(&self.report, i64::BITS)?,
                f.roots,
                f.roots,
                f.grain.0,
                true,
            )?,
        })
    }
}
impl<'c> ResidentNormalWave<'c> {
    /// Expose a prediction and retain its actual preceding joint/material cut. Ordinary
    /// `advance` remains available without opening an addressed comparison obligation.
    pub fn predict(&mut self) -> Result<NormalWavePrediction<'c>, ConstitutiveFibreError> {
        let source = Rc::new(ProducingCut {
            joint: Rc::clone(&self.joint),
            fibre: self.fibre(),
        });
        let step = self.advance()?;
        let id = self.epoch;
        self.pending.insert(id, source);
        Ok(NormalWavePrediction {
            step,
            handle: NormalProducingHandle {
                owner: Rc::clone(&self.owner),
                id,
            },
        })
    }

}
impl<'c,C> ResidentNormalWave<'c,C> {
    pub fn pending_predictions(&self) -> usize {
        self.pending.len()
    }

    /// Resolve an address already present in this owner's active comparison population,
    /// including after a validated remount. Application source association is retained outside
    /// this native address; an arbitrary message id does not produce a comparison here.
    pub fn pending_prediction(
        &self,
        id: u64,
    ) -> Result<NormalProducingHandle, ConstitutiveFibreError> {
        if !self.pending.contains_key(&id) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        Ok(NormalProducingHandle {
            owner: Rc::clone(&self.owner),
            id,
        })
    }

    fn producing_cut(
        &self,
        handle: &NormalProducingHandle,
    ) -> Result<&Rc<ProducingCut<'c>>, ConstitutiveFibreError> {
        if !Rc::ptr_eq(&self.owner, &handle.owner) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.pending
            .get(&handle.id)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)
    }

    /// Release a comparison that the caller no longer admits as a future return. Existing
    /// external handles then refuse; no coordinates or material are changed by release.
    pub fn release_prediction(
        &mut self,
        handle: &NormalProducingHandle,
    ) -> Result<(), ConstitutiveFibreError> {
        self.producing_cut(handle)?;
        self.pending.remove(&handle.id);
        Ok(())
    }

    /// Develop at a retained producing joint while preserving the actual contemporary pair.
    /// The existing correlated reception kernel forms φ=(c_s-p_s,c_s,p_s), η=v-c_s on device.
    /// Its forward reading uses producing material; the increment joins contemporary material.
    /// No enclosed centre enters a point-current port and no earlier material is restored.
    pub(super) fn receive_normal_prediction<'a>(
        &mut self,
        handle: &NormalProducingHandle,
        observed: ResidentConstitutiveCurrent<'a, 'c>,
    ) -> Result<NormalWaveComparison<'a, 'c>, ConstitutiveFibreError> {
        let source = Rc::clone(self.producing_cut(handle)?);
        let count = self
            .material
            .observations
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let staged = if self.steps > 0 {
            Some(self.material.prepare_joint_seed(&self.joint, self.epoch)?)
        } else {
            None
        };
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
            s.record_normal_wave_comparison(
                &lane,
                &self.material.state,
                &source.fibre.material,
                &source.joint,
                observed,
                n,
                self.material.grain.0,
                source.fibre.transport.is_reference(),
                self.transport.is_reference(),
                &next,
                &report,
                &work,
                &input,
            )?;
        }
        passage.close(0, &report, i64::BITS)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            let stage = s.read_out(&report).ok().and_then(|words| words.first().map(|w| w.1));
            let stage = match stage {
                Some(1) => "joint source/target moments",
                Some(2) => "producing response",
                Some(3) => "moment increment",
                Some(4) => "normal fit",
                Some(5) => "updated response",
                Some(6) => "returned difference",
                _ => "unavailable stage",
            };
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "producing wave comparison ({stage}): {:?}", returned.obstruction
            )));
        }
        // Every fallible operation precedes this publication. Retain both contemporary current
        // occurrence handles while rebasing the word onto their actual joint enclosure.
        let predecessor_fibre = self.normal_bank_fibre();
        if let Some(super::develop::JointSeed {
            power, metadata, ..
        }) = staged
        {
            self.seed = Rc::clone(&self.joint);
            self.seed_bound = Rc::clone(&self.joint);
            self.seed_kind = NormalWaveSeedKind::JointEnclosure;
            self.power = power;
            self.metadata = Rc::new(metadata);
            self.steps = 0;
            self.seed_epochs = [self.previous.at(), self.current.at()];
        }
        self.material.state = Rc::new(next);
        self.material.observations = count;
        self.pending.remove(&handle.id);
        Ok(NormalWaveComparison {
            prediction_id: handle.id,
            source,
            observed,
            report,
            predecessor_fibre,
            successor_fibre: self.normal_bank_fibre(),
        })
    }
}

impl<'c> ResidentNormalWave<'c>{
    pub fn receive_prediction<'a>(&mut self,handle:&NormalProducingHandle,observed:ResidentConstitutiveCurrent<'a,'c>)
        ->Result<NormalWaveComparison<'a,'c>,ConstitutiveFibreError>{self.receive_normal_prediction(handle,observed)}
}
