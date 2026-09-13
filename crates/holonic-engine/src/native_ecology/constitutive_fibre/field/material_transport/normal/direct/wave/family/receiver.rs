use super::*;
use crate::native_ecology::constitutive_fibre::ResidentConstitutiveImage;

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
    /// Every frame has (lambda, anchor, p, c). The first lambda/anchor are reported above;
    /// later copies remain in projected_joint so shared-frame constraints are not discarded.
    pub state_width: usize,
    pub state_count: usize,
}
impl NormalFamilyReceiverReading {
    /// The p,c coordinates at one state in this SAME joint projection, not separately
    /// projected marginal optima. The complete affine family remains on the native receiver.
    pub fn projected_state(&self, state: usize) -> Option<&[Rat]> {
        if state >= self.state_count {
            return None;
        }
        let width = self.state_width.checked_sub(2)? / 2;
        let start = state.checked_mul(self.state_width)?;
        self.projected_joint
            .as_ref()?
            .get(start..start.checked_add(width)?)
    }
}
pub struct NormalWaveFamilyReceiver<'a, 'c> {
    source: &'a NormalWaveFamily<'c>,
    image: Option<ResidentConstitutiveImage<'a, 'c>>,
    report: ResidentSection<'c>,
    vertical: ResidentSection<'c>,
}
impl<'a, 'c> NormalWaveFamilyReceiver<'a, 'c> {
    pub(super) fn report(&self) -> &ResidentSection<'c> { &self.report }
    pub(super) fn into_report(self) -> ResidentSection<'c> {
        self.report
    }
    pub(crate) fn require_supported(&self) -> Result<(), ConstitutiveFibreError> {
        let s = self.source.origin.fibre().surface;
        let out = s.fresh_section(1, 1, ResidentGrain(0))?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_family_admit(&lane, &self.report, &out)?;
        }
        passage.close(0, &out, 64)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "conditional family admission: {:?}",
                result.obstruction
            )));
        }
        Ok(())
    }
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        self.source
    }
    pub fn image(&self) -> Option<&ResidentConstitutiveImage<'a, 'c>> {
        self.image.as_ref()
    }
    /// Full source/future joint before applying the retained original anchor bound.
    pub fn affine_relation(&self) -> &ResidentConstitutiveReturn<'c> {
        self.image
            .as_ref()
            .map_or(self.source.affine_relation(), |image| image.joint())
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
        let state_width = 2 + 2 * a;
        let t = self.affine_relation().target_width();
        let y = t.checked_sub(2 + a).ok_or(ConstitutiveFibreError::Shape)?;
        if t % state_width != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let values = wides(&self.source.origin.fibre().surface.read_out(&self.report)?)?;
        if values.len() != 4 + 2 * a + 2 * y
            || values[1] <= 0
            || values[2 + a] <= 0
            || values[3 + a + y] <= 0
            || values[4 + 2 * a + y..].iter().any(|v| !(0..=1).contains(v))
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let support = match values[0] {
            0 => NormalFamilySupport::Supported,
            1 => NormalFamilySupport::EmptyAffineRelation,
            2 => NormalFamilySupport::OutsideAnchorBall,
            _ => return Err(ConstitutiveFibreError::Shape),
        };
        let vector = |at: usize, den: usize, width: usize| {
            values[at..at + width]
                .iter()
                .map(|v| Rat::new((*v).into(), values[den].into()))
                .collect()
        };
        Ok(NormalFamilyReceiverReading {
            support,
            nearest_anchor: (support != NormalFamilySupport::EmptyAffineRelation)
                .then(|| vector(2, 1, a)),
            projected_joint: (support == NormalFamilySupport::Supported)
                .then(|| vector(3 + a, 2 + a, y)),
            anchor_difference: (support != NormalFamilySupport::EmptyAffineRelation)
                .then(|| vector(4 + a + y, 3 + a + y, a)),
            anchor_independent_free: values[4 + 2 * a + y..].iter().map(|v| *v != 0).collect(),
            state_width,
            state_count: t / state_width,
        })
    }
}
impl<'c> NormalWaveFamily<'c> {
    /// Situated receiver of the constrained family. This returns a supported projection or
    /// an explicit source-domain obstruction; it never replaces the source relation by a point.
    pub fn read_receiver(
        &self,
    ) -> Result<NormalWaveFamilyReceiver<'_, 'c>, ConstitutiveFibreError> {
        self.receiver_with_image(None)
    }
    /// Compose an actual learned word while retaining every shared future state variable
    /// and the original bounded source. The output is one anchored joint receiver.
    pub fn read_prospective(
        &self,
        word: Vec<Rc<ResidentWaveRelation<'c>>>,
    ) -> Result<NormalWaveFamilyReceiver<'_, 'c>, ConstitutiveFibreError> {
        self.check_prospective_extent(word.len())?;
        let image = self.relation.read_wave_word(word)?;
        self.receiver_with_image(Some(image))
    }
    pub(in super::super) fn check_prospective_extent(
        &self,
        steps: usize,
    ) -> Result<(), ConstitutiveFibreError> {
        if steps == 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let a = self
            .origin
            .fibre()
            .roots
            .checked_mul(4)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let t = steps
            .checked_add(1)
            .and_then(|n| n.checked_mul(self.relation.target_width()))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let y = t.checked_sub(2 + a).ok_or(ConstitutiveFibreError::Shape)?;
        let required = a
            .max(y)
            .checked_mul(5)
            .and_then(|n| n.checked_add(a.checked_mul(3)?)?.checked_add(y))
            .and_then(|n| n.checked_mul(16))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let available = self.origin.fibre().surface.declaration().max_sectiond_bytes;
        if required > available as usize {
            return Err(ConstitutiveFibreError::ScratchAperture {
                required,
                available,
            });
        }
        Ok(())
    }
    fn receiver_with_image<'a>(
        &'a self,
        image: Option<ResidentConstitutiveImage<'a, 'c>>,
    ) -> Result<NormalWaveFamilyReceiver<'a, 'c>, ConstitutiveFibreError> {
        let s = self.origin.fibre().surface;
        let a = self
            .origin
            .fibre()
            .roots
            .checked_mul(4)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let relation = image.as_ref().map_or(&self.relation, |image| image.joint());
        let t = relation.target_width();
        if t % (2 + 2 * a) != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let y = t.checked_sub(2 + a).ok_or(ConstitutiveFibreError::Shape)?;
        let w = a.checked_add(y).ok_or(ConstitutiveFibreError::Shape)?;
        let projection = a
            .max(y)
            .checked_mul(2)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let rw = w
            .checked_mul(4)
            .and_then(|v| v.checked_add(8))
            .ok_or(ConstitutiveFibreError::Shape)?;
        w.checked_mul(w).ok_or(ConstitutiveFibreError::Shape)?;
        let joint = s.fresh_section(w, w, ResidentGrain(0))?;
        let ab = s.fresh_section(a, a, ResidentGrain(0))?;
        let vertical = s.fresh_section(y, y, ResidentGrain(0))?;
        let graph = s.fresh_section(projection, projection, ResidentGrain(0))?;
        let report = s.fresh_section(1, rw, ResidentGrain(0))?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_family_receiver(
                &lane,
                relation.report(),
                relation.source_width(),
                self.anchor(),
                self.origin.fibre().roots,
                y,
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
            image,
            report,
            vertical,
        })
    }
}
#[cfg(test)]
mod tests;
