//! Pending returns retain the actual ordered relations between their source and the current
//! family. Intermediate equality is part of this word: projecting every step to a marginal
//! and forgetting its map does not preserve the pending source/current joint.
use super::*;

/// An implicit joint relation. For consecutive factors L_i its members satisfy
/// z_0 in source(), (z_i,z_{i+1}) in L_i, and z_last in current(), with the same joining
/// z_i at both adjacent ports. Factors are actual immutable maps used by this wave.
/// This is a source-qualified expression, not a list of equal endpoint counts or hashes.
pub struct NormalCoupledContinuation<'a, 'c> {
    cut: &'a CoupledProducingCut<'c>,
    current: &'a NormalWaveFamily<'c>,
    from: u64,
    through: u64,
    word: &'a BTreeMap<u64, Vec<Rc<ResidentWaveRelation<'c>>>>,
}
impl<'a, 'c> NormalCoupledContinuation<'a, 'c> {
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        &self.cut.source
    }
    pub fn produced(&self) -> &NormalWaveFamily<'c> {
        &self.cut.produced
    }
    pub fn current(&self) -> &NormalWaveFamily<'c> {
        self.current
    }
    pub fn producing_epoch(&self) -> u64 {
        self.from
    }
    pub fn contemporary_epoch(&self) -> u64 {
        self.through
    }
    pub fn passages(&self) -> usize {
        self.word.range(self.from..=self.through).count()
    }
    /// Every internal factor of one source-field occurrence has the same public epoch. Its
    /// vector order is still causal composition and is never replaced by the final factor.
    pub fn factors(&self) -> impl Iterator<Item = (u64, &ResidentWaveRelation<'c>)> {
        self.word
            .range(self.from..=self.through)
            .flat_map(|(epoch, factors)| factors.iter().map(move |f| (*epoch, f.as_ref())))
    }
}

impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    pub fn pending_coupled_continuation<'a>(
        &'a self,
        handle: &NormalCoupledProducingHandle,
    ) -> Result<NormalCoupledContinuation<'a, 'c>, ConstitutiveFibreError> {
        let cut = self.coupled_producing_cut(handle)?;
        Ok(NormalCoupledContinuation {
            cut,
            current: self.current(),
            from: handle.id(),
            through: self.epoch(),
            word: &self.continuation.transport,
        })
    }
    /// Only still-pending source cuts need this continuation. Maps are shared once across all
    /// pending returns; release forgets the unneeded prefix without copying a live ecology.
    pub(super) fn prune_coupled_transport(&mut self) {
        if let Some(first) = self.continuation.pending.keys().next().copied() {
            self.continuation
                .transport
                .retain(|epoch, _| *epoch >= first);
        } else {
            self.continuation.transport.clear();
        }
    }
}
