//! Joint condition/output transport. The supported image never hides a condition-domain loss.
use super::preimage::ConditionPreimageData;
use super::*;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum ConditionCoverage {
    Complete,
    Partial {
        direction: Option<usize>,
        condition: Vec<Rat>,
        residual: Vec<Rat>,
    },
    NoSupportedCondition {
        condition: Vec<Rat>,
        residual: Vec<Rat>,
    },
    EmptyConditionFibre,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct ConditionImageReading {
    pub condition_width: usize,
    pub output_width: usize,
    pub coverage: ConditionCoverage,
    pub supported_conditions: ConstitutiveReading,
    pub supported_outputs: ConstitutiveReading,
    /// Condition coordinates precede output coordinates; directions keep their correlation.
    pub joint: ConstitutiveReading,
}

/// Shared native carriers for conditional and general affine images.
pub(super) struct AffineImageData<'chart> {
    pub(super) joint: ResidentConstitutiveReturn<'chart>,
    pub(super) domain: ResidentConstitutiveReturn<'chart>,
    pub(super) output: ResidentConstitutiveReturn<'chart>,
    pub(super) constraint: ResidentSection<'chart>,
    pub(super) rhs: ResidentSection<'chart>,
    pub(super) coverage: ResidentSection<'chart>,
    pub(super) safe_current: ResidentSection<'chart>,
}

impl<'chart> AffineImageData<'chart> {
    pub(super) fn current(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        let width = self.output.target_width;
        ResidentConstitutiveCurrent {
            section: &self.safe_current,
            offset: 0,
            width,
            denominator: Some(width),
            disposition: Some(width + 1),
        }
    }
    pub(super) fn inspect_constraints(
        &self,
    ) -> Result<(ResidentSectionRest, ResidentSectionRest), ConstitutiveFibreError> {
        Ok((
            self.joint.surface.detach_section(&self.constraint, 64)?,
            self.joint.surface.detach_section(&self.rhs, 64)?,
        ))
    }
    pub(super) fn condition_reading(
        &self,
    ) -> Result<ConditionImageReading, ConstitutiveFibreError> {
        let c = self.domain.target_width;
        let w = self.joint.source_width;
        Ok(ConditionImageReading {
            condition_width: c,
            output_width: self.output.target_width,
            coverage: read_coverage(self.joint.surface, &self.coverage, c, w)?,
            supported_conditions: self.domain.inspect()?.predecessor_reading,
            supported_outputs: self.output.inspect()?.predecessor_reading,
            joint: self.joint.inspect()?.predecessor_reading,
        })
    }
    pub(super) fn generic_reading(
        &self,
        source: &ResidentConstitutiveReturn<'chart>,
    ) -> Result<super::image::ConstitutiveImageReading, ConstitutiveFibreError> {
        let reading = self.condition_reading()?;
        Ok(super::image::ConstitutiveImageReading {
            source_return_cut: source.occurrence,
            receiver_cut: self.joint.occurrence,
            coverage: reading.coverage,
            supported_source: reading.supported_conditions,
            output: reading.supported_outputs,
            joint: reading.joint,
        })
    }

    pub(super) fn refine(
        &self,
        observed: ResidentConstitutiveCurrent<'_, 'chart>,
    ) -> Result<
        (
            ResidentConstitutiveReturn<'chart>,
            ResidentSection<'chart>,
            ResidentSection<'chart>,
        ),
        ConstitutiveFibreError,
    > {
        let s = self.joint.surface;
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
        let available = s.declaration().max_sectiond_bytes;
        if scratch > available as usize {
            return Err(ConstitutiveFibreError::ScratchAperture {
                required: scratch,
                available,
            });
        }
        let constraint = s.fresh_section(width, width, ResidentGrain(0))?;
        let rhs = s.fresh_section(1, y + 2, ResidentGrain(0))?;
        let returned = ResidentConstitutiveReturn::allocate(
            s,
            y + 1,
            c,
            self.joint.occurrence,
            self.joint.source_chart,
        )?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_condition_image_receive(
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
                "condition image reception: {:?}",
                receipt.obstruction
            )));
        }
        Ok((returned, constraint, rhs))
    }
}

pub(super) fn read_coverage<'c>(
    surface: &ResidentSurface<'c>,
    section: &ResidentSection<'c>,
    c: usize,
    w: usize,
) -> Result<ConditionCoverage, ConstitutiveFibreError> {
    let words = surface.read_out(section)?;
    if words.iter().any(|(lo, hi)| lo != hi) || words[2].0 <= 0 || words[3 + c].0 <= 0 {
        return Err(ConstitutiveFibreError::Uncertain);
    }
    let condition = || {
        (0..c)
            .map(|i| Rat::new(words[3 + i].0.into(), words[2].0.into()))
            .collect()
    };
    let residual = |length| {
        (0..length)
            .map(|i| Rat::new(words[4 + c + i].0.into(), words[3 + c].0.into()))
            .collect()
    };
    let coverage = match words[0].0 {
        0 => ConditionCoverage::Complete,
        1 => ConditionCoverage::Partial {
            direction: match words[1].0 {
                -1 => None,
                n if n >= 0 && (n as usize) < c => Some(n as usize),
                _ => return Err(ConstitutiveFibreError::Uncertain),
            },
            condition: condition(),
            residual: residual(c),
        },
        2 => ConditionCoverage::NoSupportedCondition {
            condition: condition(),
            residual: residual(w),
        },
        3 => ConditionCoverage::EmptyConditionFibre,
        _ => return Err(ConstitutiveFibreError::Uncertain),
    };
    Ok(coverage)
}

pub struct ResidentConditionImage<'chart> {
    condition: ResidentConditionPreimage<'chart>,
    pub(super) data: AffineImageData<'chart>,
}

impl<'chart> ResidentConditionImage<'chart> {
    pub fn original_condition(&self) -> &ResidentConditionPreimage<'chart> {
        &self.condition
    }
    pub fn relation_cut(&self) -> u64 {
        self.data.joint.occurrence
    }
    /// This point port requires both complete condition coverage and one output. Its guard is
    /// native; a constant output on a strict subset cannot masquerade as a whole-family result.
    pub fn current(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        self.data.current()
    }
    pub fn read_differential_pairs(
        &self,
        first_complex: usize,
        pairs: usize,
    ) -> Result<ConstitutiveDifferentialReading, ConstitutiveFibreError> {
        self.data.output.read_differential_pairs_guarded(
            first_complex,
            pairs,
            Some(&self.data.coverage),
        )
    }
    pub fn inspect(&self) -> Result<ConditionImageReading, ConstitutiveFibreError> {
        self.data.condition_reading()
    }
    pub fn inspect_constraints(
        &self,
    ) -> Result<(ResidentSectionRest, ResidentSectionRest), ConstitutiveFibreError> {
        self.data.inspect_constraints()
    }

    /// A later observation restricts the same joint family. Full condition-domain coverage is
    /// required for this unqualified update; a partial-domain image keeps its obstruction instead
    /// of quietly discarding the unsupported conditions. No model row or prior fibre is changed.
    pub fn receive(
        &self,
        observed: ResidentConstitutiveCurrent<'_, 'chart>,
    ) -> Result<ResidentConditionPreimage<'chart>, ConstitutiveFibreError> {
        let (mut returned, constraint, rhs) = self.data.refine(observed)?;
        returned.source_chart = self.condition.source_chart();
        returned.occurrence = self.condition.relation_cut();
        Ok(ResidentConditionPreimage {
            inner: Rc::new(ConditionPreimageData {
                returned,
                constraint,
                rhs,
                action_target_width: self.condition.inner.action_target_width,
            }),
        })
    }
}

impl<'chart> ResidentConditionPreimage<'chart> {
    /// Compile the existing linear receiver over this complete condition family. The derived
    /// image retains the original preimage data and all joint carriers; no point current is read.
    pub fn read_image(
        &self,
        receiver: &ResidentConstitutiveFibre<'chart>,
    ) -> Result<ResidentConditionImage<'chart>, ConstitutiveFibreError> {
        let image = receiver.read_image(self.family())?;
        Ok(ResidentConditionImage {
            condition: ResidentConditionPreimage {
                inner: Rc::clone(&self.inner),
            },
            data: image.data,
        })
    }
}

impl<'chart> ResidentConstitutiveFibre<'chart> {
    /// Read `{(c,y) | c in condition and (Phi(source,c),y) in R}`. The original condition remains
    /// shared immutable standing. Its supported domain, output image and full joint fibre return
    /// separately; this receiver never advances or clones the learned ecology.
    pub fn read_condition_image(
        &self,
        source: ResidentConstitutiveCurrent<'_, 'chart>,
        condition: &ResidentConditionPreimage<'chart>,
    ) -> Result<ResidentConditionImage<'chart>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let ConstitutiveSourceChart::BilinearContact {
            source_complex,
            condition_complex,
        } = self.source_chart
        else {
            return Err(ConstitutiveFibreError::Shape);
        };
        let c = 2 * condition_complex;
        let y = self.target_width;
        let w = self
            .source_width
            .checked_add(y)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if source.width != 2 * source_complex
            || condition.source_chart() != self.source_chart
            || condition.inner.action_target_width != y
            || condition.inner.returned.target_width != c
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let joint_width = c.checked_add(y).ok_or(ConstitutiveFibreError::Shape)?;
        let width = w
            .checked_add(joint_width)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let scratch = width
            .checked_mul(2)
            .and_then(|n| n.checked_add(w))
            .and_then(|n| n.checked_mul(16))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if scratch > self.surface.declaration().max_sectiond_bytes as usize {
            return Err(ConstitutiveFibreError::ScratchAperture {
                required: scratch,
                available: self.surface.declaration().max_sectiond_bytes,
            });
        }
        let s = self.surface;
        let cut = self.occurrences;
        let joint =
            ResidentConstitutiveReturn::allocate(s, w, joint_width, cut, self.source_chart)?;
        let domain = ResidentConstitutiveReturn::allocate(s, w, c, cut, self.source_chart)?;
        let output = ResidentConstitutiveReturn::allocate(s, w, y, cut, self.source_chart)?;
        let constraint = s.fresh_section(width, width, ResidentGrain(0))?;
        let rhs = s.fresh_section(1, w + 1, ResidentGrain(0))?;
        let domain_basis = s.fresh_section(c, c, ResidentGrain(0))?;
        let output_basis = s.fresh_section(y, y, ResidentGrain(0))?;
        let coverage = s.fresh_section(1, 4 + c + w, ResidentGrain(0))?;
        let safe_current = s.fresh_section(1, y + 2, ResidentGrain(0))?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_condition_image(
                &lane,
                &self.basis,
                source,
                condition.inner.returned.report(),
                condition.inner.returned.source_width,
                source_complex,
                condition_complex,
                y,
                &constraint,
                &rhs,
                joint.report(),
                &domain_basis,
                &output_basis,
                domain.report(),
                output.report(),
                &coverage,
                &safe_current,
            )?;
        }
        passage.close(0, joint.report(), 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "condition image: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentConditionImage {
            condition: ResidentConditionPreimage {
                inner: Rc::clone(&condition.inner),
            },
            data: AffineImageData {
                joint,
                domain,
                output,
                constraint,
                rhs,
                coverage,
                safe_current,
            },
        })
    }
}

#[cfg(test)]
mod tests;
