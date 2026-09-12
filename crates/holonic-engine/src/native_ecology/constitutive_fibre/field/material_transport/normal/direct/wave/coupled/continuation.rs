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

/// A later constraint joined through the retained actual word. Every pair remains available;
/// source projections alone cannot stand in for this object during a following return.
pub struct NormalContinuationPullback<'a, 'c> {
    source: &'a NormalWaveFamily<'c>,
    target: &'a NormalWaveFamily<'c>,
    joins: Vec<NormalContinuationJoin<'c>>,
}
pub struct NormalContinuationJoin<'c> {
    epoch: u64,
    factor: usize,
    transport: Rc<ResidentWaveRelation<'c>>,
    source: Rc<NormalWaveFamily<'c>>,
    supported_source: NormalWaveFamily<'c>,
    supported_target: NormalWaveFamily<'c>,
    joint: ResidentConstitutiveReturn<'c>,
    constraints: ResidentSection<'c>,
}
impl<'c> NormalContinuationJoin<'c> {
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn factor(&self) -> usize {
        self.factor
    }
    pub fn transport(&self) -> &ResidentWaveRelation<'c> {
        &self.transport
    }
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        &self.source
    }
    pub fn supported_source(&self) -> &NormalWaveFamily<'c> {
        &self.supported_source
    }
    pub fn supported_target(&self) -> &NormalWaveFamily<'c> {
        &self.supported_target
    }
    pub fn joint(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.joint
    }
    pub fn constraints(&self) -> &ResidentSection<'c> {
        &self.constraints
    }
}
impl<'a, 'c> NormalContinuationPullback<'a, 'c> {
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        self.source
    }
    pub fn target(&self) -> &NormalWaveFamily<'c> {
        self.target
    }
    /// Joins in original causal order. Equal boundaries name a shared state variable.
    pub fn joins(&self) -> &[NormalContinuationJoin<'c>] {
        &self.joins
    }
    pub fn supported_source(&self) -> &NormalWaveFamily<'c> {
        &self.joins[0].supported_source
    }
    pub fn supported_target(&self) -> &NormalWaveFamily<'c> {
        &self
            .joins
            .last()
            .expect("nonempty retained word")
            .supported_target
    }
}
impl<'a, 'c> NormalCoupledContinuation<'a, 'c> {
    pub fn read_pullback<'r>(
        &'r self,
        target: &'r NormalWaveFamily<'c>,
    ) -> Result<NormalContinuationPullback<'r, 'c>, ConstitutiveFibreError> {
        // Reconstruct the admitted affine sections through the actual immutable word. These
        // are derived carriers, not copies of a continuing ecology or a numerical host replay.
        let mut at = Rc::clone(&self.cut.source);
        let mut frames = Vec::new();
        for (epoch, maps) in self.word.range(self.from..=self.through) {
            let passage = at
                .passages()
                .checked_add(1)
                .ok_or(ConstitutiveFibreError::Shape)?;
            for (factor, map) in maps.iter().enumerate() {
                let next = Rc::new(at.read_through_at(Rc::clone(map), passage)?);
                frames.push((*epoch, factor, Rc::clone(map), at));
                at = next;
            }
        }
        if frames.is_empty() || target.passages() != at.passages() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let mut joins: Vec<NormalContinuationJoin<'c>> = Vec::with_capacity(frames.len());
        for (epoch, factor, transport, source) in frames.into_iter().rev() {
            let next = joins.last().map_or(target, |j| &j.supported_source);
            let (joint, supported_source, supported_target, constraints) =
                source.read_pullback(&transport, next)?.into_sections();
            joins.push(NormalContinuationJoin {
                epoch,
                factor,
                transport,
                source,
                supported_source,
                supported_target,
                joint,
                constraints,
            });
        }
        joins.reverse();
        Ok(NormalContinuationPullback {
            source: self.source(),
            target,
            joins,
        })
    }
}
