//! Actual generative standing meets evidence about compatible conditions. The declared metric
//! is part of the contact; an affine particular solution is never installed as an inferred cause.

use super::*;
use serde::{Deserialize, Serialize};
use std::rc::Rc;

/// Equal unit admittance for each real/imaginary coordinate in the bound local chart.
/// Orthogonal chart changes preserve this law. General recharting owes the transported metric.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConditionContactMetric {
    UnitAdmittanceRealification,
}

mod rest;
pub use rest::ResidentConditionCurrentRest;

#[derive(Debug, PartialEq, Eq, Serialize)]
pub enum ConditionContactStatus {
    Compatible,
    OutsideRepresentedRelation,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct ConditionContactReading {
    pub contact: u64,
    pub relation_cut: u64,
    pub metric: ConditionContactMetric,
    pub status: ConditionContactStatus,
    pub predecessor: Vec<Rat>,
    pub successor: Vec<Rat>,
    pub incoming_normal: Vec<Rat>,
    pub returned_normal: Vec<Rat>,
    pub difference: Vec<Rat>,
}

/// One move owner for the actual retained condition current. Immutable passage receipts may
/// share its current section; they cannot move or develop this owner. No live ecology is cloned.
pub struct ResidentConditionCurrent<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    section: Rc<ResidentSection<'chart>>,
    source_chart: ConstitutiveSourceChart,
    metric: ConditionContactMetric,
    width: usize,
    contacts: u64,
}

/// Complete local contact return, including the original compatible-condition evidence.
/// It does not recursively retain every previous current or assert the successor is the cause.
pub struct ResidentConditionContact<'chart> {
    section: Rc<ResidentSection<'chart>>,
    family: ResidentConditionPreimage<'chart>,
    metric: ConditionContactMetric,
    contact: u64,
    width: usize,
}

fn current_view<'a, 'c>(
    section: &'a ResidentSection<'c>,
    c: usize,
    at: usize,
) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent {
        section,
        offset: at,
        width: c,
        denominator: Some(5 * c),
        disposition: None,
    }
}

impl<'chart> ResidentConstitutiveFibre<'chart> {
    /// Retain an explicitly supplied actual current in this action's condition chart. This
    /// does not install an inferred parameter, add learned rows, or create a default cause.
    pub fn retain_condition_current(
        &self,
        initial: ResidentConstitutiveCurrent<'_, 'chart>,
        metric: ConditionContactMetric,
    ) -> Result<ResidentConditionCurrent<'chart>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let ConstitutiveSourceChart::BilinearContact {
            condition_complex, ..
        } = self.source_chart
        else {
            return Err(ConstitutiveFibreError::Shape);
        };
        let c = 2 * condition_complex;
        if initial.width != c {
            return Err(ConstitutiveFibreError::Shape);
        }
        let width = c
            .checked_mul(5)
            .and_then(|n| n.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let section = self.surface.fresh_section(1, width, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface
                .record_condition_contact(&lane, initial, None, &section)?;
        }
        passage.close(0, &section, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "condition current: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentConditionCurrent {
            surface: self.surface,
            section: Rc::new(section),
            source_chart: self.source_chart,
            metric,
            width: c,
            contacts: 0,
        })
    }
}

impl<'chart> ResidentConditionCurrent<'chart> {
    pub fn current(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        current_view(&self.section, self.width, self.width)
    }
    pub fn contacts(&self) -> u64 {
        self.contacts
    }
    pub fn metric(&self) -> ConditionContactMetric {
        self.metric
    }

    /// For nonempty F=a+V, return h'=P_V h+(I-P_V)a with the complete incoming/returned
    /// normal current and difference. The actual prior current fixes the undetermined part.
    /// Empty F preserves h and returns its original scoped obstruction. Native arithmetic
    /// failure also preserves h, without a rollback copy or a semantic host read.
    pub fn contact(
        &mut self,
        family: &ResidentConditionPreimage<'chart>,
    ) -> Result<ResidentConditionContact<'chart>, ConstitutiveFibreError> {
        let f = &family.inner.returned;
        if family.source_chart() != self.source_chart
            || f.target_width != self.width
            || !std::ptr::eq(self.surface, f.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let next = self
            .contacts
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let c = self.width;
        let required = c
            .checked_mul(9)
            .and_then(ResidentSurface::constitutive_wide_scratch)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let available = self.surface.declaration().max_sectiond_bytes;
        if required > available as usize {
            return Err(ConstitutiveFibreError::ScratchAperture {
                required,
                available,
            });
        }
        let graph = self.surface.fresh_section(2 * c, 2 * c, ResidentGrain(0))?;
        let section = self.surface.fresh_section(1, 5 * c + 2, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_condition_contact(
                &lane,
                self.current(),
                Some((&f.report, f.source_width, &graph)),
                &section,
            )?;
        }
        passage.close(0, &section, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "condition contact: {:?}",
                receipt.obstruction
            )));
        }
        let section = Rc::new(section);
        // Atomic publication after the complete return. Only immutable standing is shared.
        self.section = Rc::clone(&section);
        self.contacts = next;
        Ok(ResidentConditionContact {
            section,
            family: ResidentConditionPreimage {
                inner: Rc::clone(&family.inner),
            },
            metric: self.metric,
            contact: next,
            width: c,
        })
    }
}

impl<'chart> ResidentConditionContact<'chart> {
    pub fn family(&self) -> &ResidentConditionPreimage<'chart> {
        &self.family
    }
    pub fn successor(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        current_view(&self.section, self.width, self.width)
    }
    pub fn incoming_normal(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        current_view(&self.section, self.width, 2 * self.width)
    }
    pub fn returned_normal(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        current_view(&self.section, self.width, 3 * self.width)
    }
    pub fn difference(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        current_view(&self.section, self.width, 4 * self.width)
    }
    pub fn inspect(&self) -> Result<ConditionContactReading, ConstitutiveFibreError> {
        let words = self.family.inner.returned.surface.read_out(&self.section)?;
        let c = self.width;
        let den = words[5 * c].0;
        if den <= 0 || words.iter().any(|(lo, hi)| lo != hi) {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let row = |at: usize| {
            words[at..at + c]
                .iter()
                .map(|(v, _)| Rat::new((*v).into(), den.into()))
                .collect()
        };
        Ok(ConditionContactReading {
            contact: self.contact,
            relation_cut: self.family.relation_cut(),
            metric: self.metric,
            status: match words[5 * c + 1].0 {
                0 => ConditionContactStatus::Compatible,
                1 => ConditionContactStatus::OutsideRepresentedRelation,
                _ => return Err(ConstitutiveFibreError::Uncertain),
            },
            predecessor: row(0),
            successor: row(c),
            incoming_normal: row(2 * c),
            returned_normal: row(3 * c),
            difference: row(4 * c),
        })
    }
}

#[cfg(test)]
mod tests;
