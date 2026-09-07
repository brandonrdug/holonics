//! Affine section of the existing bilinear relation at a fixed source and observed return.
//! The represented family may be partial or plural; no inverse of the whole ecology is assumed.

use super::*;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum ConditionPreimageReading {
    Compatible {
        particular: Vec<Rat>,
        directions: Vec<Vec<Rat>>,
    },
    /// No condition belongs to this fixed-source/return section of the currently represented
    /// relation. This says nothing about unadmitted extensions or different constitutive laws.
    OutsideRepresentedRelation { residual: Vec<Rat> },
}

/// Immutable derived constraints and their full condition fibre, not a copy of the learned body.
pub struct ResidentConditionPreimage<'chart> {
    pub(super) inner: Rc<ConditionPreimageData<'chart>>,
}

pub(super) struct ConditionPreimageData<'chart> {
    pub(super) returned: ResidentConstitutiveReturn<'chart>,
    pub(super) constraint: ResidentSection<'chart>,
    pub(super) rhs: ResidentSection<'chart>,
    pub(super) action_target_width: usize,
}

impl<'chart> ResidentConditionPreimage<'chart> {
    pub fn relation_cut(&self) -> u64 {
        self.inner.returned.occurrence()
    }

    pub fn source_chart(&self) -> ConstitutiveSourceChart {
        self.inner.returned.source_chart()
    }

    /// Carry a uniquely supported condition into another native operation. The consumer checks
    /// the original fibre disposition on device; a plural fibre is never silently a point.
    pub fn current(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        self.inner.returned.current()
    }

    pub fn inspect(&self) -> Result<ConditionPreimageReading, ConstitutiveFibreError> {
        Ok(match self.inner.returned.inspect()?.predecessor_reading {
            ConstitutiveReading::Unique { current } => ConditionPreimageReading::Compatible {
                particular: current,
                directions: Vec::new(),
            },
            ConstitutiveReading::Plural {
                particular,
                directions,
            } => ConditionPreimageReading::Compatible {
                particular,
                directions,
            },
            ConstitutiveReading::OutsideDomain { source_remainder } => {
                ConditionPreimageReading::OutsideRepresentedRelation {
                    residual: source_remainder,
                }
            }
        })
    }

    /// Cold evidence: the graph of the residual map from condition coordinates, and its RHS.
    /// Together these describe the derived constraints without retaining the original ecology.
    pub fn inspect_constraints(
        &self,
    ) -> Result<(ResidentSectionRest, ResidentSectionRest), ConstitutiveFibreError> {
        Ok((
            self.inner
                .returned
                .surface
                .detach_section(&self.inner.constraint, 64)?,
            self.inner
                .returned
                .surface
                .detach_section(&self.inner.rhs, 64)?,
        ))
    }

    pub fn read_differential_pairs(
        &self,
        first_complex: usize,
        pairs: usize,
    ) -> Result<ConstitutiveDifferentialReading, ConstitutiveFibreError> {
        self.inner
            .returned
            .read_differential_pairs(first_complex, pairs)
    }
}

impl<'chart> ResidentConstitutiveFibre<'chart> {
    /// Derive `{c | (Phi(source,c), observed) belongs to R}` inside this same learned relation.
    /// Fixing the source makes this an affine section in c, including when R is not a function.
    /// This explicit receiver changes no learned row, occurrence count or source capability.
    pub fn read_condition_preimage(
        &self,
        source: ResidentConstitutiveCurrent<'_, 'chart>,
        observed: ResidentConstitutiveCurrent<'_, 'chart>,
    ) -> Result<ResidentConditionPreimage<'chart>, ConstitutiveFibreError> {
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
        if source.width != 2 * source_complex || observed.width != self.target_width {
            return Err(ConstitutiveFibreError::Shape);
        }
        let residual_width = self
            .source_width
            .checked_add(self.target_width)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let conditions = condition_complex
            .checked_mul(2)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let width = residual_width
            .checked_add(conditions)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let scratch = residual_width
            .checked_add(width.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?)
            .and_then(ResidentSurface::constitutive_wide_scratch)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let available = self.surface.declaration().max_sectiond_bytes;
        if scratch > available as usize {
            return Err(ConstitutiveFibreError::ScratchAperture {
                required: scratch,
                available,
            });
        }
        let report_width = conditions
            .checked_mul(conditions)
            .and_then(|n| n.checked_add(width + 4))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let constraint = self.surface.fresh_section(width, width, ResidentGrain(0))?;
        let rhs = self
            .surface
            .fresh_section(1, residual_width + 1, ResidentGrain(0))?;
        let returned = ResidentConstitutiveReturn {
            surface: self.surface,
            report: self
                .surface
                .fresh_section(1, report_width, ResidentGrain(0))?,
            source_width: residual_width,
            target_width: conditions,
            occurrence: self.occurrences,
            source_occurrence: None,
            source_chart: self.source_chart,
        };
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_condition_preimage(
                &lane,
                &self.basis,
                source,
                observed,
                source_complex,
                condition_complex,
                self.target_width,
                &constraint,
                &rhs,
                &returned.report,
            )?;
        }
        passage.close(0, &returned.report, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "condition preimage: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentConditionPreimage {
            inner: Rc::new(ConditionPreimageData {
                returned,
                constraint,
                rhs,
                action_target_width: self.target_width,
            }),
        })
    }
}

#[cfg(test)]
mod tests;
