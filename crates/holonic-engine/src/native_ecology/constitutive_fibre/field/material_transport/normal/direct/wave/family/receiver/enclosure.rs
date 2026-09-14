use super::*;

impl<'a, 'c> NormalWaveFamilyReceiver<'a, 'c> {
    /// An outer Euclidean ball for the whole projected joint output. The anchor,
    /// affine source and every shared output variable remain on this receiver.
    /// Nonzero vertical freedom is unbounded and refuses this particular port.
    /// This enclosure makes no choice of a member of the original source family.
    pub fn enclosure(
        &self,
        grain: ResidentGrain,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        let fail = || ConstitutiveFibreError::Shape;
        if !(1..=120).contains(&grain.0) {
            return Err(fail());
        }
        let a = self
            .source
            .origin
            .fibre()
            .roots
            .checked_mul(4)
            .ok_or_else(fail)?;
        let y = self
            .target_width()
            .checked_sub(a.checked_add(2).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        let s = self.source.origin.fibre().surface;
        let words = y
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let section = s.fresh_section(1, words, ResidentGrain(0))?;
        // Workspace ownership spans the recorded passage AND its launch.
        let work = if self.point_word.is_none() {
            let g = a.checked_mul(2).ok_or_else(fail)?;
            let scratch = a
                .checked_mul(6)
                .and_then(|v| v.checked_add(y.checked_mul(3)?))
                .and_then(|v| v.checked_mul(2))
                .ok_or_else(fail)?;
            Some((
                s.fresh_section(g, g, ResidentGrain(0))?,
                s.fresh_section(1, scratch, ResidentGrain(0))?,
            ))
        } else {
            None
        };
        let mut p = s.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            if let Some((graph, scratch)) = &work {
                s.record_normal_family_enclosure(
                    &lane,
                    &self.report,
                    self.joint.as_ref().ok_or_else(fail)?,
                    self.anchor_basis.as_ref().ok_or_else(fail)?,
                    self.vertical.as_ref().ok_or_else(fail)?,
                    self.source.anchor(),
                    a,
                    y,
                    grain,
                    graph,
                    scratch,
                    &section,
                )?;
            } else {
                s.record_normal_family_enclosure_point(&lane, &self.report, a, y, grain, &section)?;
            }
        }
        p.close(0, &section, 64)?;
        let returned = p.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "bounded family enclosure: {:?}",
                returned.obstruction
            )));
        }
        Ok(ResidentNormalEnclosure {
            surface: s,
            section,
            width: y,
            grain,
        })
    }
}
