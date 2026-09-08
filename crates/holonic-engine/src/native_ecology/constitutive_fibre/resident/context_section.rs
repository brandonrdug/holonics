//! Immutable source-null section of the continuing joint relation, including mixed conduct.
use super::preimage::ConditionPreimageData;
use super::*;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum ContextualSectionOrigin {
    Bilinear {
        relation_cut: u64,
        source_chart: ConstitutiveSourceChart,
    },
    /// One real coefficient multiplies the actual oriented context contrast. Its imaginary
    /// coefficient is outside this observed real-ray domain. The ambient context is retained
    /// implicitly by the two source expressions, not claimed to be one-dimensional.
    FieldContrast {
        receiving: [usize; 2],
        source: [usize; 2],
        context: [usize; 2],
        field_occurrences: usize,
        ambient_context_complex: usize,
        fractional_bits: u32,
    },
}

/// A derived local relation, not a second move-owned learner. It retains the producing cut
/// and its fixed source; later parent deposits cannot rewrite its current or inverse faces.
pub struct ResidentContextualSection<'c> {
    pub(in super::super) surface: &'c ResidentSurface<'c>,
    pub(in super::super) source_chart: ConstitutiveSourceChart,
    pub(in super::super) relation_cut: u64,
    pub(in super::super) c: usize,
    pub(in super::super) y: usize,
    pub(in super::super) basis: ResidentSection<'c>,
    pub(in super::super) joint: ResidentSection<'c>,
    pub(in super::super) fixed: ResidentSection<'c>,
    pub(in super::super) constraint: ResidentSection<'c>,
    pub(in super::super) origin: ContextualSectionOrigin,
    reference: Option<ResidentSection<'c>>,
    endpoint: Option<ResidentSection<'c>>,
    context_carriers: Option<[Rc<ResidentSection<'c>>; 2]>,
}

impl<'c> ResidentContextualSection<'c> {
    /// The mounted current chart for explicit application excitations and native composition.
    pub fn surface(&self) -> &'c ResidentSurface<'c> {
        self.surface
    }
    #[allow(clippy::too_many_arguments)]
    pub(in super::super) fn from_field(
        surface: &'c ResidentSurface<'c>,
        cut: u64,
        y: usize,
        basis: ResidentSection<'c>,
        joint: ResidentSection<'c>,
        fixed: ResidentSection<'c>,
        reference: ResidentSection<'c>,
        endpoint: ResidentSection<'c>,
        proof: ResidentSection<'c>,
        contexts: [Rc<ResidentSection<'c>>; 2],
        origin: ContextualSectionOrigin,
    ) -> Self {
        Self {
            surface,
            source_chart: ConstitutiveSourceChart::Linear,
            relation_cut: cut,
            c: 2,
            y,
            basis,
            joint,
            fixed,
            constraint: proof,
            origin,
            reference: Some(reference),
            endpoint: Some(endpoint),
            context_carriers: Some(contexts),
        }
    }
    /// Zero in the section's CHANGE coordinates. For a field contrast this denotes its
    /// actual first contextual reference, not zero physical context or an inferred cause.
    pub fn zero_change(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        ResidentConstitutiveCurrent {
            section: &self.joint,
            offset: 1,
            width: self.c,
            denominator: Some(1 + self.c + self.y),
            disposition: None,
        }
    }
    pub fn reference_return(&self) -> Option<ResidentConstitutiveCurrent<'_, 'c>> {
        self.reference
            .as_ref()
            .map(|section| ResidentConstitutiveCurrent {
                section,
                offset: 0,
                width: self.y,
                denominator: Some(self.y),
                disposition: None,
            })
    }
    /// The second actual founding return, kept as observation rather than recomputed as a prediction.
    pub fn second_observed_return(&self) -> Option<ResidentConstitutiveCurrent<'_, 'c>> {
        self.endpoint
            .as_ref()
            .map(|section| ResidentConstitutiveCurrent {
                section,
                offset: 0,
                width: self.y,
                denominator: Some(self.y),
                disposition: None,
            })
    }
    /// Cold original generating expressions. They are retained with the oriented (-1,+1)
    /// occurrence combination and numerical fibre; no exact context centre is selected.
    pub fn inspect_context_carriers(
        &self,
    ) -> Result<Option<[ResidentSectionRest; 2]>, ConstitutiveFibreError> {
        self.context_carriers
            .as_ref()
            .map(|c| {
                Ok([
                    self.surface.detach_section(&c[0], 64)?,
                    self.surface.detach_section(&c[1], 64)?,
                ])
            })
            .transpose()
    }
    /// Read y0+D(alpha) in an established field contrast chart. This uses the learned
    /// relative transport on the device; the reference is one actual prior receiving current.
    pub fn read_absolute(
        &self,
        change: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        let base = self
            .reference
            .as_ref()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let delta = self.read_change(change)?;
        let out = ResidentConstitutiveReturn::allocate(
            self.surface,
            self.c,
            self.y,
            self.relation_cut,
            self.source_chart,
        )?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_context_output_origin(
                &lane,
                &delta.report,
                base,
                self.c,
                self.y,
                &out.report,
            )?;
        }
        passage.close(0, &out.report, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "context absolute return: {:?}",
                receipt.obstruction
            )));
        }
        Ok(out)
    }
    /// Keep the full coefficient family compatible with an actual later absolute return.
    /// This does not require the retained condition current to be that inferred coefficient.
    pub fn preimage_absolute(
        &self,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentConditionPreimage<'c>, ConstitutiveFibreError> {
        if observed.width != self.y {
            return Err(ConstitutiveFibreError::Shape);
        }
        let base = self
            .reference
            .as_ref()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let delta = self
            .surface
            .fresh_section(1, self.y + 1, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface
                .record_context_return_difference(&lane, base, observed, &delta)?;
        }
        passage.close(0, &delta, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "context receiving difference: {:?}",
                receipt.obstruction
            )));
        }
        self.preimage_change(
            self.zero_change(),
            ResidentConstitutiveCurrent::rational(&delta)?,
        )
    }
    pub fn origin(&self) -> &ContextualSectionOrigin {
        &self.origin
    }
    pub fn relation_cut(&self) -> u64 {
        self.relation_cut
    }
    pub fn context_width(&self) -> usize {
        self.c
    }
    pub fn target_width(&self) -> usize {
        self.y
    }
    pub fn fixed_source(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        ResidentConstitutiveCurrent {
            section: &self.fixed,
            offset: 0,
            width: self.fixed.width() - 1,
            denominator: Some(self.fixed.width() - 1),
            disposition: None,
        }
    }
    pub fn inspect_relation(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        Ok(self.surface.detach_section(&self.basis, 64)?)
    }
    /// Cold construction evidence, distinguished by `origin`: the full residual graph for
    /// a bilinear section, or the bounded squared-norm/error receipt for a field contrast.
    pub fn inspect_constraint(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        Ok(self.surface.detach_section(&self.constraint, 64)?)
    }
    /// Read the full returned-change fibre at an actual condition change. A point consumer
    /// checks its original disposition; unsupported and vertical directions stay explicit.
    pub fn read_change(
        &self,
        change: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        if change.width != self.c {
            return Err(ConstitutiveFibreError::Shape);
        }
        let returned = ResidentConstitutiveReturn::allocate(
            self.surface,
            self.c,
            self.y,
            self.relation_cut,
            self.source_chart,
        )?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface
                .record_constitutive_query(&lane, &self.basis, change, &returned.report)?;
        }
        passage.close(0, &returned.report, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "context section reading: {:?}",
                receipt.obstruction
            )));
        }
        Ok(returned)
    }
    /// Derive the absolute family {c' | (c'-about,observed_change) in D_s}. `about` is an
    /// explicitly retained actual reference, not a particular solution chosen from a fibre.
    pub fn preimage_change(
        &self,
        about: ResidentConstitutiveCurrent<'_, 'c>,
        observed_change: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentConditionPreimage<'c>, ConstitutiveFibreError> {
        if about.width != self.c || observed_change.width != self.y {
            return Err(ConstitutiveFibreError::Shape);
        }
        let k = self
            .c
            .checked_add(self.y)
            .and_then(|v| v.checked_add(1))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let s = self.y + 1;
        let surface = self.surface;
        let translated = surface.fresh_section(1, self.joint.width(), ResidentGrain(0))?;
        let coverage = surface.fresh_section(1, 1, ResidentGrain(0))?;
        let constraint = surface.fresh_section(k, k, ResidentGrain(0))?;
        let rhs = surface.fresh_section(1, s + 1, ResidentGrain(0))?;
        let returned = ResidentConstitutiveReturn::allocate(
            surface,
            s,
            self.c,
            self.relation_cut,
            self.source_chart,
        )?;
        let mut passage = surface.begin_passage(&[vec![], vec![0]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_context_translation(
                &lane,
                &self.joint,
                about,
                self.y,
                &translated,
                &coverage,
            )?;
        }
        passage.close(0, &translated, 64)?;
        {
            let lane = passage.open(1, &[0])?;
            surface.record_condition_image_receive(
                &lane,
                &translated,
                1,
                self.c,
                self.y,
                &coverage,
                observed_change,
                &constraint,
                &rhs,
                &returned.report,
            )?;
        }
        passage.close(1, &returned.report, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "context section preimage: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentConditionPreimage {
            inner: Rc::new(ConditionPreimageData {
                returned,
                constraint,
                rhs,
                action_target_width: self.y,
            }),
        })
    }
    /// Found the existing actual-current owner in this section's context chart. The initial
    /// current is supplied explicitly; the section never chooses an inferred cause.
    pub fn retain_condition_current(
        &self,
        initial: ResidentConstitutiveCurrent<'_, 'c>,
        metric: ConditionContactMetric,
    ) -> Result<ResidentConditionCurrent<'c>, ConstitutiveFibreError> {
        ResidentConditionCurrent::found(self.surface, self.source_chart, self.c, initial, metric)
    }
}

impl<'c> ResidentConstitutiveFibre<'c> {
    /// D_s={(dc,dy) | (0,dc,s tensor dc,dy) belongs to R}. Derive it from the complete
    /// current relation, including its original vertical directions, at the actual fixed s.
    pub fn contextual_section(
        &self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentContextualSection<'c>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let ConstitutiveSourceChart::BilinearContact {
            source_complex: ns,
            condition_complex: nc,
        } = self.source_chart
        else {
            return Err(ConstitutiveFibreError::Shape);
        };
        if source.width != 2 * ns {
            return Err(ConstitutiveFibreError::Shape);
        }
        let c = 2 * nc;
        let y = self.target_width;
        let w = self.source_width + y;
        let j = c.checked_add(y).ok_or(ConstitutiveFibreError::Shape)?;
        let k = w.checked_add(j).ok_or(ConstitutiveFibreError::Shape)?;
        let shared = w
            .checked_add(k)
            .and_then(|v| v.checked_mul(16))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let available = self.surface.declaration().max_sectiond_bytes;
        if shared > available as usize {
            return Err(ConstitutiveFibreError::ScratchAperture {
                required: shared,
                available,
            });
        }
        let jw = j
            .checked_mul(j)
            .and_then(|v| v.checked_add(j)?.checked_add(5))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let surface = self.surface;
        let constraint = surface.fresh_section(k, k, ResidentGrain(0))?;
        let basis = surface.fresh_section(j, j, ResidentGrain(0))?;
        let joint = surface.fresh_section(1, jw, ResidentGrain(0))?;
        let fixed = surface.fresh_section(1, 2 * ns + 1, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_context_section(
                &lane,
                &self.basis,
                source,
                ns,
                nc,
                y,
                &constraint,
                &basis,
                &joint,
                &fixed,
            )?;
        }
        passage.close(0, &joint, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "context section: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentContextualSection {
            surface,
            source_chart: self.source_chart,
            relation_cut: self.occurrences,
            c,
            y,
            basis,
            joint,
            fixed,
            constraint,
            origin: ContextualSectionOrigin::Bilinear {
                relation_cut: self.occurrences,
                source_chart: self.source_chart,
            },
            reference: None,
            endpoint: None,
            context_carriers: None,
        })
    }
}

#[cfg(test)]
mod tests;
