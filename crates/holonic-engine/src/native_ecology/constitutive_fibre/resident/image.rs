//! Serial affine current-family transport through existing local relations. The retained joint
//! input/output carrier records the joining fibre; no particular member is selected to compose.
use super::condition_image::{ConditionCoverage, read_coverage};
use super::*;

/// Actual borrowed producing relation, not equality inferred from endpoint values or cuts.
pub enum ConstitutiveImageReceiver<'a, 'c> {
    Linear(&'a ResidentConstitutiveFibre<'c>),
    ContextChange(&'a ResidentContextualSection<'c>),
    WaveConditional(&'a ResidentWaveRelation<'c>),
    WaveSourceContact(&'a ResidentWaveRelation<'c>),
    WaveObservation(&'a ResidentWaveRelation<'c>),
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct ConstitutiveImageReading {
    pub source_return_cut: u64,
    pub receiver_cut: u64,
    /// The supplied current family is the receiver's source condition. Field names in this
    /// existing coverage type retain that meaning; no source member is silently discarded.
    pub coverage: ConditionCoverage,
    pub supported_source: ConstitutiveReading,
    pub output: ConstitutiveReading,
    pub joint: ConstitutiveReading,
}

pub struct ResidentConstitutiveImage<'a, 'c> {
    source: &'a ResidentConstitutiveReturn<'c>,
    receiver: ConstitutiveImageReceiver<'a, 'c>,
    joint: ResidentConstitutiveReturn<'c>,
    domain: ResidentConstitutiveReturn<'c>,
    output: ResidentConstitutiveReturn<'c>,
    constraint: ResidentSection<'c>,
    rhs: ResidentSection<'c>,
    coverage: ResidentSection<'c>,
    safe: ResidentSection<'c>,
}
impl<'a, 'c> ResidentConstitutiveImage<'a, 'c> {
    pub fn source(&self) -> &ResidentConstitutiveReturn<'c> {
        self.source
    }
    pub fn receiver(&self) -> &ConstitutiveImageReceiver<'a, 'c> {
        &self.receiver
    }
    pub fn joint(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.joint
    }
    /// Supported output marginal. Check coverage before claiming it represents every supplied
    /// source; the joint carrier and original source remain available on this image.
    pub fn output(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.output
    }
    /// Consume this derived image into its output relation and affine-domain receipt. Callers
    /// that carry additional constraints must retain those alongside the returned family.
    pub(crate) fn into_output(self) -> (ResidentConstitutiveReturn<'c>, ResidentSection<'c>) {
        (self.output, self.coverage)
    }

    /// The point port requires full source coverage and a unique output, not a unique input.
    pub fn current(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        ResidentConstitutiveCurrent {
            section: &self.safe,
            offset: 0,
            width: self.output.target_width,
            denominator: Some(self.output.target_width),
            disposition: Some(self.output.target_width + 1),
        }
    }
    pub fn read_differential_pairs(
        &self,
        first: usize,
        pairs: usize,
    ) -> Result<ConstitutiveDifferentialReading, ConstitutiveFibreError> {
        self.output
            .read_differential_pairs_guarded(first, pairs, Some(&self.coverage))
    }
    pub fn inspect(&self) -> Result<ConstitutiveImageReading, ConstitutiveFibreError> {
        Ok(ConstitutiveImageReading {
            source_return_cut: self.source.occurrence,
            receiver_cut: self.joint.occurrence,
            coverage: read_coverage(
                self.joint.surface,
                &self.coverage,
                self.domain.target_width,
                self.joint.source_width,
            )?,
            supported_source: self.domain.inspect()?.predecessor_reading,
            output: self.output.inspect()?.predecessor_reading,
            joint: self.joint.inspect()?.predecessor_reading,
        })
    }
    pub fn inspect_constraints(
        &self,
    ) -> Result<(ResidentSectionRest, ResidentSectionRest), ConstitutiveFibreError> {
        Ok((
            self.joint.surface.detach_section(&self.constraint, 64)?,
            self.joint.surface.detach_section(&self.rhs, 64)?,
        ))
    }
    /// Restrict the original joint fibre by an actual downstream observation. This does not
    /// choose an earlier source or add a row to either learned law. Full-domain coverage is
    /// required for this unqualified return; a partial image retains its explicit obstruction.
    pub fn receive<'r>(
        &'r self,
        observed: ResidentConstitutiveCurrent<'r, 'c>,
    ) -> Result<ResidentConstitutiveRefinement<'r, 'c>, ConstitutiveFibreError> {
        let surface = self.joint.surface;
        let c = self.domain.target_width;
        let y = self.output.target_width;
        if observed.width != y {
            return Err(ConstitutiveFibreError::Shape);
        }
        let width = c
            .checked_add(y)
            .and_then(|n| n.checked_add(1))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let scratch = width.checked_mul(32).ok_or(ConstitutiveFibreError::Shape)?;
        let available = surface.declaration().max_sectiond_bytes;
        if scratch > available as usize {
            return Err(ConstitutiveFibreError::ScratchAperture {
                required: scratch,
                available,
            });
        }
        let constraint = surface.fresh_section(width, width, ResidentGrain(0))?;
        let rhs = surface.fresh_section(1, y + 2, ResidentGrain(0))?;
        let returned = ResidentConstitutiveReturn::allocate(
            surface,
            y + 1,
            c,
            self.joint.occurrence,
            ConstitutiveSourceChart::Linear,
        )?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_condition_image_receive(
                &lane,
                self.joint.report(),
                self.joint.source_width,
                c,
                y,
                &self.coverage,
                observed,
                &constraint,
                &rhs,
                returned.report(),
            )?;
        }
        passage.close(0, returned.report(), 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "joint source refinement: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentConstitutiveRefinement {
            joint: &self.joint,
            source: self.source,
            observed,
            returned,
            constraint,
            rhs,
        })
    }
}

/// An actual observation restricts the retained joint source/output relation. The borrowed
/// joint and observation retain the producing objects while the new source family is used.
pub struct ResidentConstitutiveRefinement<'a, 'c> {
    source: &'a ResidentConstitutiveReturn<'c>,
    joint: &'a ResidentConstitutiveReturn<'c>,
    observed: ResidentConstitutiveCurrent<'a, 'c>,
    returned: ResidentConstitutiveReturn<'c>,
    constraint: ResidentSection<'c>,
    rhs: ResidentSection<'c>,
}
impl<'a, 'c> ResidentConstitutiveRefinement<'a, 'c> {
    pub fn source(&self) -> &ResidentConstitutiveReturn<'c> {
        self.source
    }
    pub fn joint(&self) -> &ResidentConstitutiveReturn<'c> {
        self.joint
    }
    pub fn observed(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.observed
    }
    pub fn family(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.returned
    }
    pub fn inspect(&self) -> Result<ConstitutiveFibreReturn, ConstitutiveFibreError> {
        self.returned.inspect()
    }
    pub fn inspect_constraints(
        &self,
    ) -> Result<(ResidentSectionRest, ResidentSectionRest), ConstitutiveFibreError> {
        Ok((
            self.joint.surface.detach_section(&self.constraint, 64)?,
            self.joint.surface.detach_section(&self.rhs, 64)?,
        ))
    }
}

impl<'c> ResidentConditionPreimage<'c> {
    /// Recover the original condition port after a downstream image/observation restriction.
    /// The refinement must concern this exact source object, not an equal-looking family or
    /// another relation at the same cut. Move only its new constraints; retain no history chain.
    pub fn refined_by(
        &self,
        refinement: ResidentConstitutiveRefinement<'_, 'c>,
    ) -> Result<ResidentConditionPreimage<'c>, ConstitutiveFibreError> {
        if !std::ptr::eq(self.family(), refinement.source)
            || refinement.returned.target_width != self.inner.returned.target_width
        {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let mut returned = refinement.returned;
        // The residual-prefix coordinates belong to the downstream observation; its target
        // coordinates are the proven original condition port, not a shape-based relabeling.
        returned.source_chart = self.source_chart();
        returned.occurrence = self.relation_cut();
        Ok(ResidentConditionPreimage {
            inner: std::rc::Rc::new(super::preimage::ConditionPreimageData {
                returned,
                constraint: refinement.constraint,
                rhs: refinement.rhs,
                action_target_width: self.inner.action_target_width,
            }),
        })
    }
}

pub(super) fn image<'a, 'c>(
    surface: &'c ResidentSurface<'c>,
    basis: &ResidentSection<'c>,
    c: usize,
    y: usize,
    cut: u64,
    source: &'a ResidentConstitutiveReturn<'c>,
    receiver: ConstitutiveImageReceiver<'a, 'c>,
) -> Result<ResidentConstitutiveImage<'a, 'c>, ConstitutiveFibreError> {
    if source.target_width != c {
        return Err(ConstitutiveFibreError::Shape);
    }
    let w = c.checked_add(y).ok_or(ConstitutiveFibreError::Shape)?;
    let k = w.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
    let words = k
        .checked_mul(2)
        .and_then(|v| v.checked_add(w)?.checked_mul(2))
        .ok_or(ConstitutiveFibreError::Shape)?;
    let workspace = surface.fresh_section(1, words, ResidentGrain(0))?;
    let joint =
        ResidentConstitutiveReturn::allocate(surface, w, w, cut, ConstitutiveSourceChart::Linear)?;
    let domain =
        ResidentConstitutiveReturn::allocate(surface, w, c, cut, ConstitutiveSourceChart::Linear)?;
    let output =
        ResidentConstitutiveReturn::allocate(surface, w, y, cut, ConstitutiveSourceChart::Linear)?;
    let constraint = surface.fresh_section(k, k, ResidentGrain(0))?;
    let rhs = surface.fresh_section(1, w + 1, ResidentGrain(0))?;
    let domain_basis = surface.fresh_section(c, c, ResidentGrain(0))?;
    let output_basis = surface.fresh_section(y, y, ResidentGrain(0))?;
    let coverage = surface.fresh_section(1, 4 + c + w, ResidentGrain(0))?;
    let safe = surface.fresh_section(1, y + 2, ResidentGrain(0))?;
    let mut passage = surface.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        surface.record_fibre_image(
            &lane,
            basis,
            source.report(),
            source.source_width,
            c,
            y,
            [
                &constraint,
                &rhs,
                joint.report(),
                &domain_basis,
                &output_basis,
                domain.report(),
                output.report(),
                &coverage,
                &safe,
            ],
            &workspace,
        )?;
    }
    passage.close(0, joint.report(), 64)?;
    let receipt = passage.finish()?.launch()?;
    if !receipt.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "affine family image: {:?}",
            receipt.obstruction
        )));
    }
    Ok(ResidentConstitutiveImage {
        source,
        receiver,
        joint,
        domain,
        output,
        constraint,
        rhs,
        coverage,
        safe,
    })
}
impl<'c> ResidentConstitutiveFibre<'c> {
    /// Read the full affine image through this linear relation. Both native source and receiver
    /// remain borrowed while the image is in use; no learned morphology is cloned or modified.
    pub fn read_image<'a>(
        &'a self,
        source: &'a ResidentConstitutiveReturn<'c>,
    ) -> Result<ResidentConstitutiveImage<'a, 'c>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if self.source_chart != ConstitutiveSourceChart::Linear {
            return Err(ConstitutiveFibreError::Shape);
        }
        image(
            self.surface,
            &self.basis,
            self.source_width,
            self.target_width,
            self.occurrences,
            source,
            ConstitutiveImageReceiver::Linear(self),
        )
    }
}
impl<'c> ResidentContextualSection<'c> {
    /// Compose a family of actual condition changes through the learned source-null section.
    /// This returns changes; it does not silently add an absolute field reference.
    pub fn read_change_image<'a>(
        &'a self,
        source: &'a ResidentConstitutiveReturn<'c>,
    ) -> Result<ResidentConstitutiveImage<'a, 'c>, ConstitutiveFibreError> {
        image(
            self.surface,
            &self.basis,
            self.c,
            self.y,
            self.relation_cut,
            source,
            ConstitutiveImageReceiver::ContextChange(self),
        )
    }
}
#[cfg(test)]
mod tests;

impl<'c> ResidentWaveRelation<'c> {
    pub fn read_image<'a>(
        &'a self,
        source: &'a ResidentConstitutiveReturn<'c>,
    ) -> Result<ResidentConstitutiveImage<'a, 'c>, ConstitutiveFibreError> {
        image(
            self.surface,
            &self.basis,
            self.width(),
            self.width(),
            self.relation_cut,
            source,
            if self.observed_next().is_some() {
                ConstitutiveImageReceiver::WaveObservation(self)
            } else if self.source_contact().is_some() {
                ConstitutiveImageReceiver::WaveSourceContact(self)
            } else {
                ConstitutiveImageReceiver::WaveConditional(self)
            },
        )
    }
}
