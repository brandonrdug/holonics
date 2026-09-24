//! Actual generative standing meets evidence about compatible conditions. The declared metric
//! is part of the contact; an affine particular solution is never installed as an inferred cause.

use super::*;
use std::rc::Rc;

mod affine;
mod reaction;
pub use affine::ResidentAffineContact;
pub(crate) use affine::ResidentWaveSourceGeometry;
use affine::affine_contact_section;
pub(crate) use reaction::block;
pub use reaction::{AffineContactReading, ResidentContactReaction};

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

/// One move owner for the actual retained condition current: the successor block of its latest
/// contact reaction. Immutable passage receipts may share its reaction section; they cannot move
/// or develop this owner. A clone is the retained standing a producing passage reads.
#[derive(Clone)]
pub struct ResidentConditionCurrent<'chart> {
    reaction: ResidentContactReaction<'chart>,
    source_chart: ConstitutiveSourceChart,
    contacts: u64,
}

/// Complete local contact return, including the original compatible-condition evidence.
/// It does not recursively retain every previous current or assert the successor is the cause.
pub struct ResidentConditionContact<'chart> {
    reaction: ResidentContactReaction<'chart>,
    family: ResidentConditionPreimage<'chart>,
    contact: u64,
}

pub struct PreparedConditionContact<'chart> {
    predecessor: Rc<ResidentSection<'chart>>,
    returned: ResidentConditionContact<'chart>,
}
impl<'chart> PreparedConditionContact<'chart> {
    pub fn standing(&self) -> ResidentConditionCurrent<'chart> {
        ResidentConditionCurrent {
            reaction: self.returned.reaction.clone(),
            source_chart: self.returned.family.source_chart(),
            contacts: self.returned.contact,
        }
    }
    pub fn successor(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        self.returned.successor()
    }
    pub fn family(&self) -> &ResidentConditionPreimage<'chart> {
        self.returned.family()
    }
    pub fn inspect(&self) -> Result<AffineContactReading, ConstitutiveFibreError> {
        self.returned.inspect()
    }
}

mod rest;
pub use rest::ConditionCurrentRest;

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
            reaction: ResidentContactReaction::new(surface, Rc::new(section), c, metric),
            source_chart,
            contacts: 0,
        })
    }
    pub(super) fn from_reaction(
        reaction: ResidentContactReaction<'chart>,
        source_chart: ConstitutiveSourceChart,
        contacts: u64,
    ) -> Self {
        Self {
            reaction,
            source_chart,
            contacts,
        }
    }
    pub(super) fn reaction(&self) -> &ResidentContactReaction<'chart> {
        &self.reaction
    }

    /// The retained standing a producing passage reads: a clone sharing the reaction section.
    pub fn standing(&self) -> ResidentConditionCurrent<'chart> {
        self.clone()
    }
    /// The actual current: the successor block of the latest reaction.
    pub fn current(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        self.reaction.block(block::SUCCESSOR, false)
    }
    pub fn source_chart(&self) -> ConstitutiveSourceChart {
        self.source_chart
    }
    pub fn metric(&self) -> ConditionContactMetric {
        self.reaction.metric()
    }
    pub fn contacts(&self) -> u64 {
        self.contacts
    }

    /// Receive an explicitly supplied actual condition through the existing exact current
    /// constructor. This is an input, not an inferred cause. The standing it replaces is
    /// returned for a producing passage that still reads it.
    pub fn receive_current(
        &mut self,
        incoming: ResidentConstitutiveCurrent<'_, 'chart>,
    ) -> Result<ResidentConditionCurrent<'chart>, ConstitutiveFibreError> {
        let next = self.with_current(incoming)?;
        Ok(std::mem::replace(self, next))
    }
    /// A successor standing founded on an explicitly supplied current. `with_current_count`
    /// counts `inputs` received currents at once.
    pub(crate) fn with_current(
        &self,
        incoming: ResidentConstitutiveCurrent<'_, 'chart>,
    ) -> Result<Self, ConstitutiveFibreError> {
        self.with_current_count(incoming, 1)
    }
    pub(crate) fn with_current_count(
        &self,
        incoming: ResidentConstitutiveCurrent<'_, 'chart>,
        inputs: u64,
    ) -> Result<Self, ConstitutiveFibreError> {
        if inputs == 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let count = self
            .contacts
            .checked_add(inputs)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let mut next = Self::found(
            self.reaction.surface(),
            self.source_chart,
            self.reaction.width(),
            incoming,
            self.reaction.metric(),
        )?;
        next.contacts = count;
        Ok(next)
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
        let surface = self.reaction.surface();
        if family.source_chart() != self.source_chart
            || f.target_width != self.reaction.width()
            || !std::ptr::eq(surface, f.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let next = self
            .contacts
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let section = Rc::new(affine_contact_section(surface, self.current(), f)?);
        Ok(PreparedConditionContact {
            predecessor: Rc::clone(self.reaction.section()),
            returned: ResidentConditionContact {
                reaction: ResidentContactReaction::new(
                    surface,
                    section,
                    self.reaction.width(),
                    self.reaction.metric(),
                ),
                family: ResidentConditionPreimage {
                    inner: Rc::clone(&family.inner),
                },
                contact: next,
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
        let returned = &prepared.returned;
        self.reaction.same_section(&prepared.predecessor)
            && self.contacts.checked_add(1) == Some(returned.contact)
            && self.source_chart == returned.family.source_chart()
            && self.reaction.width() == returned.reaction.width()
            && self.reaction.metric() == returned.reaction.metric()
    }

    /// The neighborhood preflights this predicate under exclusive ownership before its only
    /// other mutation (the local law deposit). That mutation cannot change this current.
    pub(super) fn publish_prepared(
        &mut self,
        prepared: PreparedConditionContact<'chart>,
    ) -> ResidentConditionContact<'chart> {
        debug_assert!(self.can_commit(&prepared));
        self.reaction = prepared.returned.reaction.clone();
        self.contacts = prepared.returned.contact;
        prepared.returned
    }
}

impl<'chart> ResidentConditionContact<'chart> {
    pub fn family(&self) -> &ResidentConditionPreimage<'chart> {
        &self.family
    }
    /// The contact reaction this return published.
    pub fn reaction(&self) -> &ResidentContactReaction<'chart> {
        &self.reaction
    }
    pub fn successor(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        self.reaction.block(block::SUCCESSOR, false)
    }
    pub fn incoming_normal(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        self.reaction.block(block::INCOMING_NORMAL, false)
    }
    pub fn returned_normal(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        self.reaction.block(block::RETURNED_NORMAL, false)
    }
    pub fn difference(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        self.reaction.block(block::DIFFERENCE, false)
    }
    pub fn inspect(&self) -> Result<AffineContactReading, ConstitutiveFibreError> {
        self.reaction
            .inspect(self.family.relation_cut(), Some(self.contact))
    }
}

#[cfg(test)]
mod tests;
