//! Immutable accepted-deed topology beside one [`ActiveCut`](crate::ActiveCut).
//!
//! Source events act once.  Their successful OWN deposits append here in lived current order and
//! are partitioned at every event boundary.  Sparse cut incidences reference these shared spans;
//! they never copy the deeds or re-run the source event.  The word ABI is an output/receipt surface,
//! not a source-current encoding.

use soma_abi::emission::{
    CurrentEmissionSpan, DeedEmission, EventEmissionSpan, Header, ValidationError, View,
};

use crate::{ActiveCut, ActiveCutError, ValidatedActiveCut};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EmissionJournalError {
    CurrentOrder { expected: u64, actual: u64 },
    EventOrder { expected: u64, actual: u64 },
    BodyEmission,
    Incomplete,
    Structural(ValidationError),
    Active(ActiveCutError),
    ActiveMismatch,
    ResourceExtent,
    ResourceReservation,
    DeedExtent,
}

impl From<ValidationError> for EmissionJournalError {
    fn from(error: ValidationError) -> Self {
        Self::Structural(error)
    }
}

impl From<ActiveCutError> for EmissionJournalError {
    fn from(error: ActiveCutError) -> Self {
        Self::Active(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EmissionJournal {
    pub header: Header,
    pub events: Vec<EventEmissionSpan>,
    pub deeds: Vec<DeedEmission>,
    pub currents: Vec<CurrentEmissionSpan>,
}

impl EmissionJournal {
    pub fn view(&self) -> View<'_> {
        View {
            header: self.header,
            events: &self.events,
            deeds: &self.deeds,
            currents: &self.currents,
        }
    }

    pub fn validate(&self) -> Result<(), EmissionJournalError> {
        self.view().validate().map_err(Into::into)
    }

    pub fn validate_against(&self, active: &ActiveCut) -> Result<(), EmissionJournalError> {
        self.validate()?;
        if self.header.events() != active.header.events()
            || self.header.currents() != active.header.currents()
            || self.currents.len() != active.currents.len()
        {
            return Err(EmissionJournalError::ActiveMismatch);
        }
        let mut current = 0usize;
        while current < self.currents.len() {
            let emitted = self.currents[current];
            let admitted = active.currents[current];
            if emitted.event_offset() != admitted.event_offset()
                || emitted.events() != admitted.events()
            {
                return Err(EmissionJournalError::ActiveMismatch);
            }
            current += 1;
        }
        Ok(())
    }

    /// Assemble independently conducted current-local journals into the active cut's canonical
    /// population order.  The supplied vector may arrive in any execution order.  Sorting is only
    /// a placement of already-lived current ordinals into their admitted ABI rows; it cannot
    /// choose, suppress, or re-enact a current.
    pub fn assemble(
        active: &ActiveCut,
        parts: Vec<CurrentEmissionPart>,
    ) -> Result<Self, EmissionJournalError> {
        Self::assemble_validated(active.validated()?, parts)
    }

    pub(crate) fn assemble_validated(
        active: ValidatedActiveCut<'_>,
        mut parts: Vec<CurrentEmissionPart>,
    ) -> Result<Self, EmissionJournalError> {
        let expected_currents = usize::try_from(active.header.currents())
            .map_err(|_| EmissionJournalError::ResourceExtent)?;
        if parts.len() != expected_currents {
            return Err(EmissionJournalError::Incomplete);
        }
        parts.sort_unstable_by_key(CurrentEmissionPart::current);

        let events = usize::try_from(active.header.events())
            .map_err(|_| EmissionJournalError::ResourceExtent)?;
        let mut deeds = 0usize;
        for (ordinal, part) in parts.iter().enumerate() {
            part.validate_against(active.active(), ordinal as u64)?;
            deeds = deeds
                .checked_add(part.deeds.len())
                .ok_or(EmissionJournalError::ResourceExtent)?;
        }

        let mut event_rows = Vec::new();
        event_rows
            .try_reserve_exact(events)
            .map_err(|_| EmissionJournalError::ResourceReservation)?;
        let mut deed_rows = Vec::new();
        deed_rows
            .try_reserve_exact(deeds)
            .map_err(|_| EmissionJournalError::ResourceReservation)?;
        let mut current_rows = Vec::new();
        current_rows
            .try_reserve_exact(expected_currents)
            .map_err(|_| EmissionJournalError::ResourceReservation)?;

        for part in parts {
            let deed_offset =
                u64::try_from(deed_rows.len()).map_err(|_| EmissionJournalError::ResourceExtent)?;
            for event in part.events {
                let shifted = event
                    .deed_offset()
                    .checked_add(deed_offset)
                    .and_then(|offset| EventEmissionSpan::new(offset, event.deeds()))
                    .ok_or(EmissionJournalError::ResourceExtent)?;
                event_rows.push(shifted);
            }
            let part_deeds = u64::try_from(part.deeds.len())
                .map_err(|_| EmissionJournalError::ResourceExtent)?;
            deed_rows.extend(part.deeds);
            current_rows.push(
                CurrentEmissionSpan::new(
                    part.event_offset,
                    part.event_extent,
                    deed_offset,
                    part_deeds,
                )
                .ok_or(EmissionJournalError::ResourceExtent)?,
            );
        }

        let journal = Self {
            header: Header::new(
                event_rows.len() as u64,
                deed_rows.len() as u64,
                current_rows.len() as u64,
            )
            .ok_or(EmissionJournalError::Incomplete)?,
            events: event_rows,
            deeds: deed_rows,
            currents: current_rows,
        };
        journal.validate_against(active.active())?;
        Ok(journal)
    }
}

/// One independently conducted current's immutable accepted-deed surface.  Event and deed offsets
/// are local to this current until [`EmissionJournal::assemble`] places the part into the complete
/// active population.  Cause spans remain current-local by body law in both forms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentEmissionPart {
    current: u64,
    event_offset: u64,
    event_extent: u64,
    events: Vec<EventEmissionSpan>,
    deeds: Vec<DeedEmission>,
}

impl CurrentEmissionPart {
    /// Close one independently executed substrate return against its admitted current. The rows
    /// are already-lived output; this constructor only validates their exact local partition
    /// before the complete population is assembled.
    pub fn from_substrate_rows(
        active: &ActiveCut,
        current: u64,
        events: Vec<EventEmissionSpan>,
        deeds: Vec<DeedEmission>,
    ) -> Result<Self, EmissionJournalError> {
        active.validate()?;
        let admitted = active
            .currents
            .get(usize::try_from(current).map_err(|_| EmissionJournalError::ResourceExtent)?)
            .copied()
            .ok_or(EmissionJournalError::Incomplete)?;
        let part = Self {
            current,
            event_offset: admitted.event_offset(),
            event_extent: admitted.events(),
            events,
            deeds,
        };
        part.validate_against(active, current)?;
        Ok(part)
    }

    pub fn current(&self) -> u64 {
        self.current
    }

    pub fn event_offset(&self) -> u64 {
        self.event_offset
    }

    pub fn events(&self) -> &[EventEmissionSpan] {
        &self.events
    }

    pub fn deeds(&self) -> &[DeedEmission] {
        &self.deeds
    }

    fn validate_against(
        &self,
        active: &ActiveCut,
        expected_current: u64,
    ) -> Result<(), EmissionJournalError> {
        if self.current != expected_current {
            return Err(EmissionJournalError::CurrentOrder {
                expected: expected_current,
                actual: self.current,
            });
        }
        let admitted = active
            .currents
            .get(
                usize::try_from(expected_current)
                    .map_err(|_| EmissionJournalError::ResourceExtent)?,
            )
            .ok_or(EmissionJournalError::Incomplete)?;
        if self.event_offset != admitted.event_offset()
            || self.event_extent != admitted.events()
            || self.events.len() as u64 != self.event_extent
        {
            return Err(EmissionJournalError::ActiveMismatch);
        }
        let mut expected_deed = 0u64;
        for event in &self.events {
            if event.deed_offset() != expected_deed {
                return Err(EmissionJournalError::Incomplete);
            }
            expected_deed = expected_deed
                .checked_add(event.deeds())
                .ok_or(EmissionJournalError::ResourceExtent)?;
        }
        if expected_deed != self.deeds.len() as u64 {
            return Err(EmissionJournalError::Incomplete);
        }
        Ok(())
    }
}

/// Allocation-closed target for one independently conducted current.  It owns no global journal
/// cursor, so distinct co-present currents can act from one immutable receiver-before face on
/// separate bodies and output reservations.
pub struct CurrentEmissionBuilder {
    current: u64,
    event_offset: u64,
    event_extent: u64,
    next_event: u64,
    events: Vec<EventEmissionSpan>,
    deeds: Vec<DeedEmission>,
    begun: bool,
    closed: bool,
}

impl CurrentEmissionBuilder {
    /// Reserve the exact event population while letting accepted deeds grow fallibly with actual
    /// conduct.  The current-local body is an uncommitted successor, so allocation refusal can
    /// discard it whole without requiring an exponential maximum-deed allocation up front.
    pub(crate) fn preflight_validated(
        active: ValidatedActiveCut<'_>,
        current: u64,
    ) -> Result<Self, EmissionJournalError> {
        let admitted = active
            .currents
            .get(usize::try_from(current).map_err(|_| EmissionJournalError::ResourceExtent)?)
            .ok_or(EmissionJournalError::Incomplete)?;
        let event_extent =
            usize::try_from(admitted.events()).map_err(|_| EmissionJournalError::ResourceExtent)?;
        let mut events = Vec::new();
        events
            .try_reserve_exact(event_extent)
            .map_err(|_| EmissionJournalError::ResourceReservation)?;
        Ok(Self {
            current,
            event_offset: admitted.event_offset(),
            event_extent: admitted.events(),
            next_event: admitted.event_offset(),
            events,
            deeds: Vec::new(),
            begun: false,
            closed: false,
        })
    }

    pub fn finish(self) -> Result<CurrentEmissionPart, EmissionJournalError> {
        let after_event = self
            .event_offset
            .checked_add(self.event_extent)
            .ok_or(EmissionJournalError::ResourceExtent)?;
        if !self.begun
            || !self.closed
            || self.next_event != after_event
            || self.events.len() as u64 != self.event_extent
        {
            return Err(EmissionJournalError::Incomplete);
        }
        let part = CurrentEmissionPart {
            current: self.current,
            event_offset: self.event_offset,
            event_extent: self.event_extent,
            events: self.events,
            deeds: self.deeds,
        };
        Ok(part)
    }
}

impl EmissionTarget for CurrentEmissionBuilder {
    fn begin_current(
        &mut self,
        current_ordinal: u64,
        event_offset: u64,
    ) -> Result<(), EmissionJournalError> {
        if self.begun || self.closed || current_ordinal != self.current {
            return Err(EmissionJournalError::CurrentOrder {
                expected: self.current,
                actual: current_ordinal,
            });
        }
        if event_offset != self.event_offset {
            return Err(EmissionJournalError::EventOrder {
                expected: self.event_offset,
                actual: event_offset,
            });
        }
        self.begun = true;
        Ok(())
    }

    fn deed_offset(&self) -> u64 {
        self.deeds.len() as u64
    }

    fn push_deed(&mut self, deed: DeedEmission) -> Result<(), EmissionJournalError> {
        if DeedEmission::from_words(deed.words()).is_none() {
            return Err(EmissionJournalError::BodyEmission);
        }
        self.deeds
            .try_reserve(1)
            .map_err(|_| EmissionJournalError::ResourceReservation)?;
        self.deeds.push(deed);
        Ok(())
    }

    fn close_event(
        &mut self,
        event_ordinal: u64,
        deed_offset: u64,
    ) -> Result<(), EmissionJournalError> {
        if !self.begun || self.closed || event_ordinal != self.next_event {
            return Err(EmissionJournalError::EventOrder {
                expected: self.next_event,
                actual: event_ordinal,
            });
        }
        let deeds = (self.deeds.len() as u64)
            .checked_sub(deed_offset)
            .ok_or(EmissionJournalError::BodyEmission)?;
        self.events.push(
            EventEmissionSpan::new(deed_offset, deeds).ok_or(EmissionJournalError::BodyEmission)?,
        );
        self.next_event = self
            .next_event
            .checked_add(1)
            .ok_or(EmissionJournalError::ResourceExtent)?;
        Ok(())
    }

    fn close_current(
        &mut self,
        current_ordinal: u64,
        event_offset: u64,
        events: u64,
    ) -> Result<(), EmissionJournalError> {
        let after = event_offset
            .checked_add(events)
            .ok_or(EmissionJournalError::ResourceExtent)?;
        if !self.begun
            || self.closed
            || current_ordinal != self.current
            || event_offset != self.event_offset
            || events != self.event_extent
            || after != self.next_event
        {
            return Err(EmissionJournalError::CurrentOrder {
                expected: self.current,
                actual: current_ordinal,
            });
        }
        self.closed = true;
        Ok(())
    }
}

pub(crate) trait EmissionTarget {
    fn begin_current(
        &mut self,
        current_ordinal: u64,
        event_offset: u64,
    ) -> Result<(), EmissionJournalError>;
    fn deed_offset(&self) -> u64;
    fn push_deed(&mut self, deed: DeedEmission) -> Result<(), EmissionJournalError>;
    fn close_event(
        &mut self,
        event_ordinal: u64,
        deed_offset: u64,
    ) -> Result<(), EmissionJournalError>;
    fn close_current(
        &mut self,
        current_ordinal: u64,
        event_offset: u64,
        events: u64,
    ) -> Result<(), EmissionJournalError>;
}

/// Append-only builder.  Currents and events must be conducted in their admitted order; this is
/// their own worldline, not a scheduler for independent configurations.
pub struct EmissionJournalBuilder {
    expected_events: u64,
    expected_currents: u64,
    next_event: u64,
    next_current: u64,
    current_deed_offset: u64,
    events: Vec<EventEmissionSpan>,
    deeds: Vec<DeedEmission>,
    currents: Vec<CurrentEmissionSpan>,
    deed_extent: Option<usize>,
}

impl EmissionJournalBuilder {
    pub fn new(active: &ActiveCut) -> Self {
        Self {
            expected_events: active.header.events(),
            expected_currents: active.header.currents(),
            next_event: 0,
            next_current: 0,
            current_deed_offset: 0,
            events: Vec::new(),
            deeds: Vec::new(),
            currents: Vec::new(),
            deed_extent: None,
        }
    }

    /// Form the complete allocation boundary before any body deed can occur.  `maximum_deeds` is
    /// the body-derived conservative envelope for this exact active population and carrier depth;
    /// it is not a workload cap or a semantic aperture.  Events and currents reserve their exact
    /// admitted extents, and every accepted push within this envelope is allocation-free.
    pub fn preflight(active: &ActiveCut, maximum_deeds: u64) -> Result<Self, EmissionJournalError> {
        active.validate()?;
        let events = usize::try_from(active.header.events())
            .map_err(|_| EmissionJournalError::ResourceExtent)?;
        let currents = usize::try_from(active.header.currents())
            .map_err(|_| EmissionJournalError::ResourceExtent)?;
        let deeds =
            usize::try_from(maximum_deeds).map_err(|_| EmissionJournalError::ResourceExtent)?;

        let mut event_rows = Vec::new();
        event_rows
            .try_reserve_exact(events)
            .map_err(|_| EmissionJournalError::ResourceReservation)?;
        let mut deed_rows = Vec::new();
        deed_rows
            .try_reserve_exact(deeds)
            .map_err(|_| EmissionJournalError::ResourceReservation)?;
        let mut current_rows = Vec::new();
        current_rows
            .try_reserve_exact(currents)
            .map_err(|_| EmissionJournalError::ResourceReservation)?;

        Ok(Self {
            expected_events: active.header.events(),
            expected_currents: active.header.currents(),
            next_event: 0,
            next_current: 0,
            current_deed_offset: 0,
            events: event_rows,
            deeds: deed_rows,
            currents: current_rows,
            deed_extent: Some(deeds),
        })
    }

    pub fn maximum_deeds(&self) -> Option<usize> {
        self.deed_extent
    }

    pub(crate) fn begin_current(
        &mut self,
        current_ordinal: u64,
        event_offset: u64,
    ) -> Result<(), EmissionJournalError> {
        if current_ordinal != self.next_current {
            return Err(EmissionJournalError::CurrentOrder {
                expected: self.next_current,
                actual: current_ordinal,
            });
        }
        if event_offset != self.next_event {
            return Err(EmissionJournalError::EventOrder {
                expected: self.next_event,
                actual: event_offset,
            });
        }
        self.current_deed_offset = self.deeds.len() as u64;
        Ok(())
    }

    pub(crate) fn deed_offset(&self) -> u64 {
        self.deeds.len() as u64
    }

    pub(crate) fn push_deed(&mut self, deed: DeedEmission) -> Result<(), EmissionJournalError> {
        if DeedEmission::from_words(deed.words()).is_none() {
            return Err(EmissionJournalError::BodyEmission);
        }
        if self
            .deed_extent
            .is_some_and(|extent| self.deeds.len() >= extent)
        {
            return Err(EmissionJournalError::DeedExtent);
        }
        self.deeds.push(deed);
        Ok(())
    }

    pub(crate) fn close_event(
        &mut self,
        event_ordinal: u64,
        deed_offset: u64,
    ) -> Result<(), EmissionJournalError> {
        if event_ordinal != self.next_event {
            return Err(EmissionJournalError::EventOrder {
                expected: self.next_event,
                actual: event_ordinal,
            });
        }
        let deeds = (self.deeds.len() as u64)
            .checked_sub(deed_offset)
            .ok_or(EmissionJournalError::BodyEmission)?;
        self.events.push(
            EventEmissionSpan::new(deed_offset, deeds).ok_or(EmissionJournalError::BodyEmission)?,
        );
        self.next_event += 1;
        Ok(())
    }

    pub(crate) fn close_current(
        &mut self,
        current_ordinal: u64,
        event_offset: u64,
        events: u64,
    ) -> Result<(), EmissionJournalError> {
        if current_ordinal != self.next_current
            || event_offset.checked_add(events) != Some(self.next_event)
        {
            return Err(EmissionJournalError::CurrentOrder {
                expected: self.next_current,
                actual: current_ordinal,
            });
        }
        let deeds = (self.deeds.len() as u64)
            .checked_sub(self.current_deed_offset)
            .ok_or(EmissionJournalError::BodyEmission)?;
        self.currents.push(
            CurrentEmissionSpan::new(event_offset, events, self.current_deed_offset, deeds)
                .ok_or(EmissionJournalError::BodyEmission)?,
        );
        self.next_current += 1;
        Ok(())
    }

    pub fn finish(self, active: &ActiveCut) -> Result<EmissionJournal, EmissionJournalError> {
        if self.next_event != self.expected_events
            || self.next_current != self.expected_currents
            || self.next_event != active.header.events()
            || self.next_current != active.header.currents()
        {
            return Err(EmissionJournalError::Incomplete);
        }
        let journal = EmissionJournal {
            header: Header::new(
                self.events.len() as u64,
                self.deeds.len() as u64,
                self.currents.len() as u64,
            )
            .ok_or(EmissionJournalError::Incomplete)?,
            events: self.events,
            deeds: self.deeds,
            currents: self.currents,
        };
        journal.validate_against(active)?;
        Ok(journal)
    }
}

impl EmissionTarget for EmissionJournalBuilder {
    fn begin_current(
        &mut self,
        current_ordinal: u64,
        event_offset: u64,
    ) -> Result<(), EmissionJournalError> {
        EmissionJournalBuilder::begin_current(self, current_ordinal, event_offset)
    }

    fn deed_offset(&self) -> u64 {
        EmissionJournalBuilder::deed_offset(self)
    }

    fn push_deed(&mut self, deed: DeedEmission) -> Result<(), EmissionJournalError> {
        EmissionJournalBuilder::push_deed(self, deed)
    }

    fn close_event(
        &mut self,
        event_ordinal: u64,
        deed_offset: u64,
    ) -> Result<(), EmissionJournalError> {
        EmissionJournalBuilder::close_event(self, event_ordinal, deed_offset)
    }

    fn close_current(
        &mut self,
        current_ordinal: u64,
        event_offset: u64,
        events: u64,
    ) -> Result<(), EmissionJournalError> {
        EmissionJournalBuilder::close_current(self, current_ordinal, event_offset, events)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::channel::WindingQuantum;
    use body::manifold::{FeltDeed, FeltEmission};
    use body::medium::FeltTerm;
    use body::num::Cog;
    use body::place;
    use body::soul::Chi;
    use soma_abi::active::{
        ActionCurrent, CurrentSpan, CutSpan, EventSpan, Incidence, OriginRef, RelationAtom,
    };

    fn active() -> ActiveCut {
        ActiveCut::new(
            vec![RelationAtom::new(Cog::lit(3)).unwrap()],
            vec![EventSpan::new(0, 1).unwrap()],
            vec![ActionCurrent::new(Cog::lit(5)).unwrap()],
            vec![OriginRef::new(1, 0)],
            vec![CurrentSpan::new(0, 1, 0, 1).unwrap()],
            vec![CutSpan::new(0, 1, 0, 0).unwrap()],
            vec![Incidence::new(0, 0, 1).unwrap()],
            Vec::new(),
        )
        .unwrap()
    }

    fn deed() -> DeedEmission {
        DeedEmission::new(
            FeltEmission {
                position: place::origin(),
                term: FeltTerm {
                    chi: Chi {
                        same: Cog::lit(7),
                        other: Cog::ZERO,
                    },
                    winding: WindingQuantum::None,
                },
                deed: FeltDeed::Ride,
                standing_read: None,
            },
            0,
            1,
        )
        .unwrap()
    }

    #[test]
    fn the_complete_journal_reservation_precedes_every_deed() {
        let active = active();
        let mut builder = EmissionJournalBuilder::preflight(&active, 1).unwrap();
        assert_eq!(builder.events.capacity(), active.events.len());
        assert_eq!(builder.currents.capacity(), active.currents.len());
        assert!(builder.deeds.capacity() >= 1);
        builder.begin_current(0, 0).unwrap();
        builder.push_deed(deed()).unwrap();
        assert_eq!(
            builder.push_deed(deed()),
            Err(EmissionJournalError::DeedExtent)
        );
        builder.close_event(0, 0).unwrap();
        builder.close_current(0, 0, 1).unwrap();
        assert_eq!(builder.finish(&active).unwrap().header.deeds(), 1);
    }
}
