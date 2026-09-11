use super::*;
mod receiver;
mod rest;
pub use rest::NormalWaveFamilyRest;
pub use receiver::{NormalFamilySupport,NormalFamilyReceiverReading,NormalWaveFamilyReceiver};
use crate::native_ecology::constitutive_fibre::{ResidentConstitutiveReturn, ResidentWaveRelation};

/// A constrained affine family, not a normal ball and not a point-current operand.
/// The relation targets (lambda,anchor,p,c); lambda=1 and the anchor retains the producing
/// joint ball. Conditional composition eliminates intermediate variables but keeps that bound.
pub struct NormalWaveFamily<'c> {
    origin: Rc<NormalWaveJointSource<'c>>,
    relation: ResidentConstitutiveReturn<'c>,
    last_relation: Option<Rc<ResidentWaveRelation<'c>>>,
    affine_coverage: Option<ResidentSection<'c>>,
    passages: u64,
}
impl<'c> NormalWaveFamily<'c> {
    pub fn origin(&self) -> &NormalWaveJointSource<'c> {
        &self.origin
    }
    pub fn anchor(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.origin.joint()
    }
    /// Complete affine carrier. Its members are further constrained by the retained anchor ball;
    /// this receiver alone does not certify bounded feasibility or independent marginals.
    pub fn affine_relation(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.relation
    }
    pub fn passages(&self) -> u64 {
        self.passages
    }
    pub fn last_relation(&self) -> Option<&ResidentWaveRelation<'c>> {
        self.last_relation.as_deref()
    }
    pub fn inspect_affine_coverage(
        &self,
    ) -> Result<Option<ResidentSectionRest>, ConstitutiveFibreError> {
        self.affine_coverage
            .as_ref()
            .map(|v| {
                self.origin
                    .fibre()
                    .surface
                    .detach_section(v, 64)
                    .map_err(Into::into)
            })
            .transpose()
    }
    /// Compose the complete constrained family through an admitted fixed-condition wave map.
    /// Free output directions and partial domain constraints remain represented. No bounded
    /// feasibility or ball-enclosure conversion is inferred from the affine image disposition.
    pub fn read_through(
        &self,
        law: Rc<ResidentWaveRelation<'c>>,
    ) -> Result<Self, ConstitutiveFibreError> {
        if law.roots() != self.origin.fibre().roots {
            return Err(ConstitutiveFibreError::Shape);
        }
        let passages = self
            .passages
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        self.origin.fibre().epoch.checked_add(passages).ok_or(ConstitutiveFibreError::Shape)?;
        let image = law.read_image(&self.relation)?;
        let (relation, coverage) = image.into_output();
        Ok(Self {
            origin: Rc::clone(&self.origin),
            relation,
            last_relation: Some(law),
            affine_coverage: Some(coverage),
            passages,
        })
    }
}
impl<'c> ResidentNormalWave<'c> {
    /// Lift this actual joint into an anchored affine carrier without selecting the centre.
    pub fn read_family(&self) -> Result<NormalWaveFamily<'c>, ConstitutiveFibreError> {
        let origin = self.joint_source();
        let n = self.material.roots;
        let t = n
            .checked_mul(8)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let relation = ResidentConstitutiveReturn::allocate(
            self.material.surface,
            1,
            t,
            self.epoch,
            ConstitutiveSourceChart::Linear,
        )?;
        let s = self.material.surface;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_wave_family_seed(&lane, n, relation.report())?;
        }
        passage.close(0, relation.report(), 64)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "anchored wave family: {:?}",
                result.obstruction
            )));
        }
        Ok(NormalWaveFamily {
            origin: Rc::new(origin),
            relation,
            last_relation: None,
            affine_coverage: None,
            passages: 0,
        })
    }
}
#[cfg(test)]
mod tests;
