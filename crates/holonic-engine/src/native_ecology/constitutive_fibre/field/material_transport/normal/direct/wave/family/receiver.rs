use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum NormalFamilySupport {
    Supported,
    EmptyAffineRelation,
    OutsideAnchorBall,
}
#[derive(Debug, Serialize)]
pub struct NormalFamilyReceiverReading {
    pub support: NormalFamilySupport,
    /// The projection of the ball centre onto the affine anchor domain, when that domain exists.
    pub nearest_anchor: Option<Vec<Rat>>,
    /// A declared minimum-norm joint receiver at nearest_anchor, only for supported families.
    pub projected_joint: Option<Vec<Rat>>,
    pub anchor_difference: Option<Vec<Rat>>,
    /// Nonzero coordinates of directions at fixed anchor. False does not imply a constant
    /// coordinate over the full ball; those coordinates can still vary with the anchor.
    pub anchor_independent_free: Vec<bool>,
}
pub struct NormalWaveFamilyReceiver<'a, 'c> {
    source: &'a NormalWaveFamily<'c>,
    report: ResidentSection<'c>,
    vertical: ResidentSection<'c>,
}
impl<'a, 'c> NormalWaveFamilyReceiver<'a, 'c> {
    pub(crate) fn require_supported(&self)->Result<(),ConstitutiveFibreError>{
        let s=self.source.origin.fibre().surface;let out=s.fresh_section(1,1,ResidentGrain(0))?;
        let mut passage=s.begin_passage(&[vec![]])?;
        {let lane=passage.open(0,&[])?;s.record_normal_family_admit(&lane,&self.report,&out)?;}
        passage.close(0,&out,64)?;let result=passage.finish()?.launch()?;
        if !result.obstruction.is_empty(){return Err(ConstitutiveFibreError::Arithmetic(format!("conditional family admission: {:?}",result.obstruction)));}
        Ok(())
    }
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        self.source
    }
    pub fn inspect_vertical_directions(
        &self,
    ) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        Ok(self
            .source
            .origin
            .fibre()
            .surface
            .detach_section(&self.vertical, 64)?)
    }
    pub fn inspect(&self) -> Result<NormalFamilyReceiverReading, ConstitutiveFibreError> {
        let a = self.source.origin.fibre().roots * 4;
        let values = wides(&self.source.origin.fibre().surface.read_out(&self.report)?)?;
        if values.len() != 4 + 4 * a
            || values[1] <= 0
            || values[2 + a] <= 0
            || values[3 + 2 * a] <= 0
            || values[4 + 3 * a..].iter().any(|v| !(0..=1).contains(v))
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let support = match values[0] {
            0 => NormalFamilySupport::Supported,
            1 => NormalFamilySupport::EmptyAffineRelation,
            2 => NormalFamilySupport::OutsideAnchorBall,
            _ => return Err(ConstitutiveFibreError::Shape),
        };
        let vector = |at: usize, den: usize| {
            values[at..at + a]
                .iter()
                .map(|v| Rat::new((*v).into(), values[den].into()))
                .collect()
        };
        Ok(NormalFamilyReceiverReading {
            support,
            nearest_anchor: (support != NormalFamilySupport::EmptyAffineRelation)
                .then(|| vector(2, 1)),
            projected_joint: (support == NormalFamilySupport::Supported)
                .then(|| vector(3 + a, 2 + a)),
            anchor_difference: (support != NormalFamilySupport::EmptyAffineRelation)
                .then(|| vector(4 + 2 * a, 3 + 2 * a)),
            anchor_independent_free: values[4 + 3 * a..].iter().map(|v| *v != 0).collect(),
        })
    }
}
impl<'c> NormalWaveFamily<'c> {
    /// Situated receiver of the constrained family. This returns a supported projection or
    /// an explicit source-domain obstruction; it never replaces the source relation by a point.
    pub fn read_receiver(
        &self,
    ) -> Result<NormalWaveFamilyReceiver<'_, 'c>, ConstitutiveFibreError> {
        let s = self.origin.fibre().surface;
        let a = self
            .origin
            .fibre()
            .roots
            .checked_mul(4)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let w = a.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let rw = a
            .checked_mul(8)
            .and_then(|v| v.checked_add(8))
            .ok_or(ConstitutiveFibreError::Shape)?;
        w.checked_mul(w).ok_or(ConstitutiveFibreError::Shape)?;
        let joint = s.fresh_section(w, w, ResidentGrain(0))?;
        let ab = s.fresh_section(a, a, ResidentGrain(0))?;
        let vertical = s.fresh_section(a, a, ResidentGrain(0))?;
        let graph = s.fresh_section(w, w, ResidentGrain(0))?;
        let report = s.fresh_section(1, rw, ResidentGrain(0))?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_family_receiver(
                &lane,
                self.relation.report(),
                self.relation.source_width(),
                self.anchor(),
                self.origin.fibre().roots,
                &joint,
                &ab,
                &vertical,
                &graph,
                &report,
            )?;
        }
        passage.close(0, &report, 64)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "family receiver: {:?}",
                returned.obstruction
            )));
        }
        Ok(NormalWaveFamilyReceiver {
            source: self,
            report,
            vertical,
        })
    }
}
#[cfg(test)]
mod tests;
