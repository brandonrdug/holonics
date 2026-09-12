//! Actual generative standing meets evidence about compatible conditions. The declared metric
//! is part of the contact; an affine particular solution is never installed as an inferred cause.

use super::*;
use std::rc::Rc;

mod affine;
use affine::affine_contact_section;
pub(crate) use affine::ResidentWaveSourceGeometry;
pub(super) use affine::read_affine_contact;
pub use affine::{AffineContactReading, ResidentAffineContact};

/// Equal unit admittance for each real/imaginary coordinate in the bound local chart.
/// Orthogonal chart changes preserve this law. General recharting owes the transported metric.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
pub enum ConditionContactMetric {
    UnitAdmittanceRealification,
}

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

/// Immutable actual standing used by a producing passage. Sharing its resident section does
/// not create another move owner or retain a chain of earlier states.
pub struct ResidentConditionStanding<'chart> {
    section: Rc<ResidentSection<'chart>>,
    width: usize,
    source_chart: ConstitutiveSourceChart,
    metric: ConditionContactMetric,
    contacts: u64,
}
impl<'chart> ResidentConditionStanding<'chart> {
    pub fn current(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        current_view(&self.section, self.width, self.width)
    }
    pub fn source_chart(&self) -> ConstitutiveSourceChart {
        self.source_chart
    }
    pub fn metric(&self) -> ConditionContactMetric {
        self.metric
    }
    pub fn contacts(&self) -> u64 {
        self.contacts
    }
}

pub struct PreparedConditionContact<'chart> {
    predecessor: Rc<ResidentSection<'chart>>,
    returned: ResidentConditionContact<'chart>,
}
impl<'chart> PreparedConditionContact<'chart> {
    pub fn successor(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        self.returned.successor()
    }
    /// Continue a conditional contact along its actual returned current. This stages another
    /// contact; it neither publishes the first one nor constructs another ecology owner.
    pub(crate) fn prepare_following(
        &self, family: &ResidentConditionPreimage<'chart>,
    ) -> Result<Self, ConstitutiveFibreError> {
        let old=&self.returned;
        let f=&family.inner.returned;
        if family.source_chart()!=old.family.source_chart() || f.target_width!=old.width
            || !std::ptr::eq(f.surface,old.family.inner.returned.surface) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let contact=old.contact.checked_add(1).ok_or(ConstitutiveFibreError::Shape)?;
        let section=Rc::new(affine_contact_section(f.surface,self.successor(),f)?);
        Ok(Self {
            predecessor:Rc::clone(&old.section),
            returned:ResidentConditionContact {
                section,family:ResidentConditionPreimage {inner:Rc::clone(&family.inner)},
                metric:old.metric,contact,width:old.width,
            },
        })
    }

    pub fn family(&self) -> &ResidentConditionPreimage<'chart> {
        self.returned.family()
    }
    pub fn inspect(&self) -> Result<ConditionContactReading, ConstitutiveFibreError> {
        self.returned.inspect()
    }
}

mod rest;
pub use rest::ConditionCurrentRest;

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
        ResidentConditionCurrent::found(self.surface, self.source_chart, c, initial, metric)
    }
}

impl<'chart> ResidentConditionCurrent<'chart> {
    pub(super) fn found(
        surface: &'chart ResidentSurface<'chart>,
        source_chart: ConstitutiveSourceChart,
        c: usize,
        initial: ResidentConstitutiveCurrent<'_, 'chart>,
        metric: ConditionContactMetric,
    ) -> Result<Self, ConstitutiveFibreError> {
        if initial.width != c || c == 0 || c % 2 != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let width = c
            .checked_mul(5)
            .and_then(|n| n.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let section = surface.fresh_section(1, width, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_condition_contact(&lane, initial, None, &section)?;
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
            surface,
            section: Rc::new(section),
            source_chart,
            metric,
            width: c,
            contacts: 0,
        })
    }
}

impl<'chart> ResidentConditionCurrent<'chart> {
    pub fn standing(&self) -> ResidentConditionStanding<'chart> {
        ResidentConditionStanding {
            section: Rc::clone(&self.section),
            width: self.width,
            source_chart: self.source_chart,
            metric: self.metric,
            contacts: self.contacts,
        }
    }
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
        let prepared = self.prepare_contact(family)?;
        self.commit_contact(prepared)
    }

    /// Compute the complete native reaction into fresh material, without changing standing.
    /// The proposal retains the exact predecessor section; it cannot be committed to another
    /// current or after another contact changed this one.
    pub fn prepare_contact(
        &self,
        family: &ResidentConditionPreimage<'chart>,
    ) -> Result<PreparedConditionContact<'chart>, ConstitutiveFibreError> {
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
        let section = affine_contact_section(self.surface, self.current(), f)?;
        let section = Rc::new(section);
        Ok(PreparedConditionContact {
            predecessor: Rc::clone(&self.section),
            returned: ResidentConditionContact {
                section,
                family: ResidentConditionPreimage {
                    inner: Rc::clone(&family.inner),
                },
                metric: self.metric,
                contact: next,
                width: c,
            },
        })
    }

    pub fn commit_contact(
        &mut self,
        prepared: PreparedConditionContact<'chart>,
    ) -> Result<ResidentConditionContact<'chart>, ConstitutiveFibreError> {
        if !self.can_commit(&prepared) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        Ok(self.publish_prepared(prepared))
    }

    pub(super) fn can_commit(&self, prepared: &PreparedConditionContact<'chart>) -> bool {
        Rc::ptr_eq(&self.section, &prepared.predecessor)
            && self.contacts.checked_add(1) == Some(prepared.returned.contact)
            && self.source_chart == prepared.returned.family.source_chart()
            && self.width == prepared.returned.width
            && self.metric == prepared.returned.metric
    }

    /// The neighborhood preflights this predicate under exclusive ownership before its only
    /// other mutation (the local law deposit). That mutation cannot change this current.
    pub(super) fn publish_prepared(
        &mut self,
        prepared: PreparedConditionContact<'chart>,
    ) -> ResidentConditionContact<'chart> {
        debug_assert!(self.can_commit(&prepared));
        self.section = Rc::clone(&prepared.returned.section);
        self.contacts = prepared.returned.contact;
        prepared.returned
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
