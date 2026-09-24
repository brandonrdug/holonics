//! Source/target constraints joined through the actual fixed conditional map. This is a
//! relational pullback, not backward physical evolution and not an independent pairing.
use super::*;

pub struct ResidentWavePullback<'a, 'c> {
    relation: &'a ResidentWaveRelation<'c>,
    source: &'a ResidentConstitutiveReturn<'c>,
    target: &'a ResidentConstitutiveReturn<'c>,
    joint: ResidentConstitutiveReturn<'c>,
    supported_source: ResidentConstitutiveReturn<'c>,
    supported_target: ResidentConstitutiveReturn<'c>,
    constraints: ResidentSection<'c>,
}
impl<'a, 'c> ResidentWavePullback<'a, 'c> {
    pub fn relation(&self) -> &ResidentWaveRelation<'c> {
        self.relation
    }
    pub fn source(&self) -> &ResidentConstitutiveReturn<'c> {
        self.source
    }
    pub fn target(&self) -> &ResidentConstitutiveReturn<'c> {
        self.target
    }
    /// Complete joined pairs (source,target), with the equation residual before the pair.
    pub fn joint(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.joint
    }
    pub fn supported_source(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.supported_source
    }
    pub fn supported_target(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.supported_target
    }
    pub(crate) fn into_sections(
        self,
    ) -> (
        ResidentConstitutiveReturn<'c>,
        ResidentConstitutiveReturn<'c>,
        ResidentConstitutiveReturn<'c>,
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
impl<'c> ResidentWaveRelation<'c> {
    /// Join two affine carriers through this exact relation. Original bound/receiver owners
    /// must accompany these affine reports; nonempty affine support alone proves no ball
    /// feasibility. Marginals are offered alongside, never instead of, the complete pair.
    pub fn read_pullback<'a>(
        &'a self,
        source: &'a ResidentConstitutiveReturn<'c>,
        target: &'a ResidentConstitutiveReturn<'c>,
    ) -> Result<ResidentWavePullback<'a, 'c>, ConstitutiveFibreError> {
        let t = self.width();
        if source.target_width() != t
            || target.target_width() != t
            || !std::ptr::eq(source.surface, self.surface)
            || !std::ptr::eq(target.surface, self.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let w = t.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let k = w.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let scratch = t.checked_mul(20).ok_or(ConstitutiveFibreError::Shape)?;
        let s = self.surface;
        let graph = s.fresh_section(k, k, ResidentGrain(0))?;
        let lb = s.fresh_section(t, t, ResidentGrain(0))?;
        let rb = s.fresh_section(t, t, ResidentGrain(0))?;
        let workspace = s.fresh_section(1, scratch, ResidentGrain(0))?;
        let allocate = |target| {
            ResidentConstitutiveReturn::allocate(
                s,
                w,
                target,
                self.relation_cut,
                ConstitutiveSourceChart::Linear,
            )
        };
        let joint = allocate(w)?;
        let supported_source = allocate(t)?;
        let supported_target = allocate(t)?;
        let mut p = s.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            s.record_wave_family_pullback(
                &lane,
                &self.basis,
                source.report(),
                source.source_width(),
                target.report(),
                target.source_width(),
                t,
                &graph,
                joint.report(),
                &lb,
                &rb,
                supported_source.report(),
                supported_target.report(),
                &workspace,
            )?;
        }
        p.close(0, joint.report(), 64)?;
        let result = p.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "wave source/target pullback: {:?}",
                result.obstruction
            )));
        }
        Ok(ResidentWavePullback {
            relation: self,
            source,
            target,
            joint,
            supported_source,
            supported_target,
            constraints: graph,
        })
    }
}
