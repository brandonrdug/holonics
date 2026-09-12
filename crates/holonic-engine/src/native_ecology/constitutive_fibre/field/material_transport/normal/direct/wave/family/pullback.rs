//! The affine join accompanied by its actual common anchor, original frames and clocks.
use super::*;
/// Scoped joined construction. Its restricted families retain their original physical clocks,
/// but are not standalone legacy wave-family rests: persist the enclosing generator and these
/// source constraints, not a marginal with an unrelated transport coverage receipt.
pub struct NormalFamilyPullback<'a, 'c> {
    source: &'a NormalWaveFamily<'c>,
    target: &'a NormalWaveFamily<'c>,
    transport: &'a ResidentWaveRelation<'c>,
    joint: ResidentConstitutiveReturn<'c>,
    supported_source: NormalWaveFamily<'c>,
    supported_target: NormalWaveFamily<'c>,
    constraints: ResidentSection<'c>,
}
impl<'a, 'c> NormalFamilyPullback<'a, 'c> {
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        self.source
    }
    pub fn target(&self) -> &NormalWaveFamily<'c> {
        self.target
    }
    pub fn transport(&self) -> &ResidentWaveRelation<'c> {
        self.transport
    }
    pub fn joint(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.joint
    }
    pub fn supported_source(&self) -> &NormalWaveFamily<'c> {
        &self.supported_source
    }
    pub fn supported_target(&self) -> &NormalWaveFamily<'c> {
        &self.supported_target
    }
    pub(in super::super) fn into_sections(
        self,
    ) -> (
        ResidentConstitutiveReturn<'c>,
        NormalWaveFamily<'c>,
        NormalWaveFamily<'c>,
        ResidentSection<'c>,
    ) {
        (
            self.joint,
            self.supported_source,
            self.supported_target,
            self.constraints,
        )
    }
    pub fn constraints(&self) -> &ResidentSection<'c> {
        &self.constraints
    }
}
impl<'c> NormalWaveFamily<'c> {
    /// Pull back a later constraint through one actual map, retaining its full joined pairs.
    /// Source and target must use the same original anchor object at adjoining passage cuts.
    /// This does not certify bounded feasibility from affine support; use the retained bound.
    pub fn read_pullback<'a>(
        &'a self,
        transport: &'a ResidentWaveRelation<'c>,
        target: &'a Self,
    ) -> Result<NormalFamilyPullback<'a, 'c>, ConstitutiveFibreError> {
        if !Rc::ptr_eq(&self.origin, &target.origin)
            || !(self.passages.checked_add(1) == Some(target.passages)
                || (self.passages == target.passages && transport.is_total_current_map()))
            || transport.roots() != self.origin.fibre().roots
        {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let result = transport.read_pullback(&self.relation, &target.relation)?;
        let (joint, left, right, constraints) = result.into_sections();
        let restrict = |original: &Self, relation| Self {
            origin: Rc::clone(&original.origin),
            relation,
            last_relation: original.last_relation.as_ref().map(Rc::clone),
            // Original transport coverage does not certify this new restriction's coverage.
            affine_coverage: None,
            passages: original.passages,
        };
        Ok(NormalFamilyPullback {
            source: self,
            target,
            transport,
            joint,
            supported_source: restrict(self, left),
            supported_target: restrict(target, right),
            constraints,
        })
    }
}
