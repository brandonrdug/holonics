//! Serial affine current-family transport through existing local relations. The retained joint
//! input/output carrier records the joining fibre; no particular member is selected to compose.
use super::condition_image::{AffineImageData, ConditionCoverage, read_coverage};
use super::*;

/// Actual borrowed producing relation, not equality inferred from endpoint values or cuts.
pub enum ConstitutiveImageReceiver<'a, 'c> {
    Linear(&'a ResidentConstitutiveFibre<'c>),
    ContextChange(&'a ResidentContextualSection<'c>),
    WaveConditional(&'a ResidentWaveRelation<'c>),
    WaveSourceContact(&'a ResidentWaveRelation<'c>),
    WaveObservation(&'a ResidentWaveRelation<'c>),
    /// The immutable factors of a joint wave word.  Keeping the actual relations here makes
    /// the receiver a producing receipt rather than an inferred list of equal-shaped maps.
    WaveWord(Vec<Rc<ResidentWaveRelation<'c>>>),
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
    pub(super) data: AffineImageData<'c>,
}
impl<'a, 'c> ResidentConstitutiveImage<'a, 'c> {
    pub fn source(&self) -> &ResidentConstitutiveReturn<'c> {
        self.source
    }
    pub fn receiver(&self) -> &ConstitutiveImageReceiver<'a, 'c> {
        &self.receiver
    }
    pub fn joint(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.data.joint
    }
    /// Supported output marginal. Check coverage before claiming it represents every supplied
    /// source; the joint carrier and original source remain available on this image.
    pub fn output(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.data.output
    }
    /// Consume this derived image into its output relation and affine-domain receipt. Callers
    /// that carry additional constraints must retain those alongside the returned family.
    pub(crate) fn into_output(self) -> (ResidentConstitutiveReturn<'c>, ResidentSection<'c>) {
        (self.data.output, self.data.coverage)
    }

    /// The point port requires full source coverage and a unique output, not a unique input.
    pub fn current(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.data.current()
    }
    pub fn read_differential_pairs(
        &self,
        first: usize,
        pairs: usize,
    ) -> Result<ConstitutiveDifferentialReading, ConstitutiveFibreError> {
        self.data
            .output
            .read_differential_pairs_guarded(first, pairs, Some(&self.data.coverage))
    }
    pub fn inspect(&self) -> Result<ConstitutiveImageReading, ConstitutiveFibreError> {
        self.data.generic_reading(self.source)
    }
    pub fn inspect_coverage(&self) -> Result<ConditionCoverage, ConstitutiveFibreError> {
        read_coverage(self.data.joint.surface, &self.data.coverage,
            self.data.domain.target_width, self.data.joint.source_width)
    }
    pub fn inspect_constraints(
        &self,
    ) -> Result<(ResidentSectionRest, ResidentSectionRest), ConstitutiveFibreError> {
        self.data.inspect_constraints()
    }
    /// Restrict the original joint fibre by an actual downstream observation. This does not
    /// choose an earlier source or add a row to either learned law. Full-domain coverage is
    /// required for this unqualified return; a partial image retains its explicit obstruction.
    pub fn receive<'r>(
        &'r self,
        observed: ResidentConstitutiveCurrent<'r, 'c>,
    ) -> Result<ResidentConstitutiveRefinement<'r, 'c>, ConstitutiveFibreError> {
        let (returned, constraint, rhs) = self.data.refine(observed)?;
        Ok(ResidentConstitutiveRefinement {
            joint: &self.data.joint,
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
            "affine family image: {}",
            receipt.obstruction
        )));
    }
    Ok(ResidentConstitutiveImage {
        source,
        receiver,
        data: AffineImageData {
            joint,
            domain,
            output,
            constraint,
            rhs,
            coverage,
            safe_current: safe,
        },
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

impl<'c> ResidentConstitutiveReturn<'c> {
    /// Compile the joint future (z1,...,zN) of one nonempty word, retaining the original
    /// source z0 and every intermediate joining variable. The public anchored-family
    /// owner supplies the wave's validated unit homogeneous source chart.
    pub(crate) fn read_wave_word(
        &self,
        word: Vec<Rc<ResidentWaveRelation<'c>>>,
    ) -> Result<ResidentConstitutiveImage<'_, 'c>, ConstitutiveFibreError> {
        let first = word.first().ok_or(ConstitutiveFibreError::Shape)?;
        let t = first.width();
        if t == 0 || self.target_width != t {
            return Err(ConstitutiveFibreError::Shape);
        }
        if word.iter().any(|map| {
            map.width() != t || !std::ptr::eq(map.surface, self.surface)
        }) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let targets = t.checked_mul(word.len()).ok_or(ConstitutiveFibreError::Shape)?;
        let total = t.checked_add(targets).ok_or(ConstitutiveFibreError::Shape)?;
        if total > u32::MAX as usize / 2 - 4 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let map = Rc::clone(first);
        if word.len() == 1 {
            return image(self.surface, &map.basis, t, t, map.relation_cut, self,
                ConstitutiveImageReceiver::WaveWord(word));
        }
        let s = self.surface;
        // The first ordinary image already owns exactly (z0,z1); consume that joint,
        // not its output marginal. Later steps append to this same variable population.
        let mut joint = map.read_image(self)?.data.joint;
        for map in word.iter().skip(1) {
            let width = joint.target_width;
            let next_width = width.checked_add(t).ok_or(ConstitutiveFibreError::Shape)?;
            let relation_width = width.checked_add(next_width).ok_or(ConstitutiveFibreError::Shape)?;
            let lifted = s.fresh_section(relation_width, relation_width, ResidentGrain(0))?;
            let workspace = s.fresh_section(1, 2*relation_width, ResidentGrain(0))?;
            let mut passage = s.begin_passage(&[vec![]])?;
            { let lane = passage.open(0, &[])?;
              s.record_wave_word_lift(&lane, &map.basis, t, width-t, &lifted, &workspace)?; }
            passage.close(0, &lifted, 64)?;
            let result = passage.finish()?.launch()?;
            if !result.obstruction.is_empty() { return Err(ConstitutiveFibreError::Arithmetic(
                format!("joint word lift: {}", result.obstruction))); }
            let next = image(s, &lifted, width, next_width, map.relation_cut, &joint,
                ConstitutiveImageReceiver::WaveConditional(map))?.into_output().0;
            joint = next;
        }
        // Homogenize with the original lambda=1 coordinate. This yields the exact
        // composite relation; the final ordinary image computes ORIGINAL-source coverage.
        let basis = s.fresh_section(total, total, ResidentGrain(0))?;
        let workspace = s.fresh_section(1, 2*total, ResidentGrain(0))?;
        let mut passage = s.begin_passage(&[vec![]])?;
        { let lane = passage.open(0, &[])?;
          s.record_wave_family_span(&lane, joint.report(), joint.source_width, total, &basis, &workspace)?; }
        passage.close(0, &basis, 64)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() { return Err(ConstitutiveFibreError::Arithmetic(
            format!("joint word span: {}", result.obstruction))); }
        let cut = word.last().expect("nonempty word").relation_cut;
        image(s, &basis, t, targets, cut, self, ConstitutiveImageReceiver::WaveWord(word))
    }
}
