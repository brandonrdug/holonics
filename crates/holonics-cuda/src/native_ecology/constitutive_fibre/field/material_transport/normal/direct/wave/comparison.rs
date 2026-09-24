//! **One-cut pullback of a pending prediction** (plan phase 9, retention law).
//!
//! [definition] A prediction retains only its **source**: the joint `(p, c)` the predicting word
//! read. Nothing of its producing constitution is kept — no material section, operator-family
//! transport or generating fibre. When the observation `v` returns, the kernel forms
//! `φ = (c − p, c, p)` and `η = v − c` from that retained joint and reads the forward response,
//! the fit and the updated response all at the **contemporary** constitution (its material
//! and transport), so a delayed return is the return an immediate one would be at the same cut.
//! Retention is then a future-sufficient quotient (the constitution plus the pending sources),
//! not an archive of producing cuts (`Foundation/Standing.lean`; the generator path's
//! `generator_delayed_observe_is_one_cut_equal_to_an_immediate_observe`). An immediate return
//! — no intervening material or transport change — reads the same numbers as the former
//! producing-cut comparison, whose producing and contemporary material coincide.
use super::*;

impl<'c> ResidentNormalWave<'c> {
    /// Advance one word and retain its source joint as a pending prediction, addressed by the
    /// successor epoch. Ordinary `advance` opens no comparison obligation.
    pub fn predict(&mut self) -> Result<(u64, NormalWaveState<'c>), ConstitutiveFibreError> {
        let source = Rc::clone(&self.joint);
        let step = self.advance()?;
        let id = self.epoch;
        self.pending.insert(id, source);
        Ok((id, step))
    }
    /// The one-cut pullback (see the module header).
    pub fn pullback<'a>(
        &mut self,
        id: u64,
        observed: ResidentConstitutiveCurrent<'a, 'c>,
    ) -> Result<NormalWavePassage<'a, 'c>, ConstitutiveFibreError> {
        self.pull_back_pending(id, observed)
    }
}
impl<'c, C> ResidentNormalWave<'c, C> {
    pub fn pending_predictions(&self) -> usize {
        self.pending.len()
    }
    pub fn pending_prediction_ids(&self) -> impl Iterator<Item = u64> + '_ {
        self.pending.keys().copied()
    }
    /// Whether `id` is an address of this owner's pending population, including after a
    /// validated remount. An arbitrary message id does not produce a comparison here.
    pub fn has_pending_prediction(&self, id: u64) -> bool {
        self.pending.contains_key(&id)
    }
    /// Release a comparison the caller no longer admits as a future return. No coordinates or
    /// material change.
    pub fn release_prediction(&mut self, id: u64) -> Result<(), ConstitutiveFibreError> {
        self.pending
            .remove(&id)
            .map(|_| ())
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)
    }

    /// The one-cut pullback: the retained source joint read at the contemporary constitution;
    /// the increment joins that same constitution. The contemporary current is unchanged.
    pub(super) fn pull_back_pending<'a>(
        &mut self,
        id: u64,
        observed: ResidentConstitutiveCurrent<'a, 'c>,
    ) -> Result<NormalWavePassage<'a, 'c>, ConstitutiveFibreError> {
        let source = Rc::clone(
            self.pending
                .get(&id)
                .ok_or(ConstitutiveFibreError::ForeignOccurrence)?,
        );
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
        let n = self.material.roots();
        let layout = NormalLayout::new(n, n).ok_or(ConstitutiveFibreError::Shape)?;
        let fresh = |w| s.fresh_section(1, w, ResidentGrain(0));
        let next = fresh(layout.state_words)?;
        let report = fresh(layout.report_words)?;
        let work = fresh(layout.workspace_words)?;
        let input = fresh(4 * (layout.source_components + 1))?;
        let reference = self.transport.is_reference();
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            // One cut: the producing and contemporary material and transport are the same.
            s.record_normal_wave_comparison(
                &lane,
                &self.material.state,
                &self.material.state,
                &source,
                observed,
                n,
                self.material.grain.0,
                reference,
                reference,
                &next,
                &report,
                &work,
                &input,
            )?;
        }
        passage.close(0, &report, i64::BITS)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            let stage = s
                .read_out(&report)
                .ok()
                .and_then(|words| words.first().map(|w| w.1));
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
                "one-cut wave pullback ({stage}): {:?}",
                returned.obstruction
            )));
        }
        // Every fallible operation precedes this publication. Retain both contemporary current
        // occurrence handles while rebasing the word onto their actual joint enclosure.
        let predecessor_fibre = self.normal_bank_fibre();
        let rebased = staged.is_some();
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
        self.pending.remove(&id);
        let mut returned = NormalWavePassage::new(
            NormalPassageKind::Pullback,
            predecessor_fibre,
            self.normal_bank_fibre(),
        );
        returned.prediction = Some(id);
        returned.rebased_joint_enclosure = rebased;
        returned.source_joint = Some(source);
        returned.observed = Some(observed);
        returned.report = Some(report);
        Ok(returned)
    }
}
