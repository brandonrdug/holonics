//! Borrowed sparse cut topology over shared active events and accepted-deed journals.
//!
//! One source event and one deed row stand once.  Every [`IncidenceSurface`] is an independent
//! physical contact which references that immutable topology; repeated incidences therefore remain
//! plural without copying a deed or re-enacting a body transition.  Directed hand is returned in
//! its supplied order and is never sorted into a transport-layout fiction.

use soma_abi::active::DirectedIncidence;
use soma_abi::emission::{DeedEmission, EventEmissionSpan};

use crate::{ActiveCut, ActiveCutError, EmissionJournal, EmissionJournalError};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CutSurfaceError {
    Active(ActiveCutError),
    Emission(EmissionJournalError),
    CutAbsent,
    ForeignSurface,
    HostExtent,
}

impl From<ActiveCutError> for CutSurfaceError {
    fn from(error: ActiveCutError) -> Self {
        Self::Active(error)
    }
}

impl From<EmissionJournalError> for CutSurfaceError {
    fn from(error: EmissionJournalError) -> Self {
        Self::Emission(error)
    }
}

/// One cut-local incidence node. Event and deed offsets are global ordinals into the shared active
/// body and emission journal. The node's own ordinal remains distinct even when two nodes reference
/// the same source span.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IncidenceSurface {
    cut: u64,
    incidence: u64,
    current: u64,
    event_offset: u64,
    events: u64,
    deed_offset: u64,
    deeds: u64,
}

impl IncidenceSurface {
    pub fn incidence(self) -> u64 {
        self.incidence
    }

    pub fn current(self) -> u64 {
        self.current
    }

    pub fn event_offset(self) -> u64 {
        self.event_offset
    }

    pub fn events(self) -> u64 {
        self.events
    }

    pub fn deed_offset(self) -> u64 {
        self.deed_offset
    }

    pub fn deeds(self) -> u64 {
        self.deeds
    }
}

pub struct CutSurface<'a> {
    active: &'a ActiveCut,
    emissions: &'a EmissionJournal,
    cut: u64,
    incidence_offset: u64,
    incidences: u64,
    directed_offset: u64,
    directed: u64,
}

impl<'a> CutSurface<'a> {
    pub fn new(
        active: &'a ActiveCut,
        emissions: &'a EmissionJournal,
        cut: u64,
    ) -> Result<Self, CutSurfaceError> {
        active.validate()?;
        emissions.validate_against(active)?;
        let cut_index = usize::try_from(cut).map_err(|_| CutSurfaceError::HostExtent)?;
        let span = active
            .cuts
            .get(cut_index)
            .ok_or(CutSurfaceError::CutAbsent)?;
        Ok(Self {
            active,
            emissions,
            cut,
            incidence_offset: span.incidence_offset(),
            incidences: span.incidences(),
            directed_offset: span.directed_offset(),
            directed: span.directed(),
        })
    }

    pub fn cut(&self) -> u64 {
        self.cut
    }

    pub fn incidence_count(&self) -> u64 {
        self.incidences
    }

    pub fn incidence(&self, local: u64) -> Result<IncidenceSurface, CutSurfaceError> {
        if local >= self.incidences {
            return Err(CutSurfaceError::HostExtent);
        }
        let ordinal = self
            .incidence_offset
            .checked_add(local)
            .ok_or(CutSurfaceError::HostExtent)?;
        let incidence = self
            .active
            .incidences
            .get(usize::try_from(ordinal).map_err(|_| CutSurfaceError::HostExtent)?)
            .ok_or(CutSurfaceError::HostExtent)?;
        let current = self
            .active
            .currents
            .get(usize::try_from(incidence.current()).map_err(|_| CutSurfaceError::HostExtent)?)
            .ok_or(CutSurfaceError::HostExtent)?;
        let event_offset = current
            .event_offset()
            .checked_add(incidence.current_event_offset())
            .ok_or(CutSurfaceError::HostExtent)?;
        let after_event = event_offset
            .checked_add(incidence.current_events())
            .ok_or(CutSurfaceError::HostExtent)?;
        let first_event = self
            .emissions
            .events
            .get(usize::try_from(event_offset).map_err(|_| CutSurfaceError::HostExtent)?)
            .ok_or(CutSurfaceError::HostExtent)?;
        let last_event = self
            .emissions
            .events
            .get(usize::try_from(after_event - 1).map_err(|_| CutSurfaceError::HostExtent)?)
            .ok_or(CutSurfaceError::HostExtent)?;
        let deed_offset = first_event.deed_offset();
        let after_deed = last_event
            .deed_offset()
            .checked_add(last_event.deeds())
            .ok_or(CutSurfaceError::HostExtent)?;
        Ok(IncidenceSurface {
            cut: self.cut,
            incidence: ordinal,
            current: incidence.current(),
            event_offset,
            events: incidence.current_events(),
            deed_offset,
            deeds: after_deed - deed_offset,
        })
    }

    fn validate_surface(&self, surface: IncidenceSurface) -> Result<(), CutSurfaceError> {
        if surface.cut != self.cut {
            return Err(CutSurfaceError::ForeignSurface);
        }
        let local = surface
            .incidence
            .checked_sub(self.incidence_offset)
            .ok_or(CutSurfaceError::ForeignSurface)?;
        if local >= self.incidences || self.incidence(local)? != surface {
            return Err(CutSurfaceError::ForeignSurface);
        }
        Ok(())
    }

    pub fn event_rows(
        &self,
        surface: IncidenceSurface,
    ) -> Result<&'a [EventEmissionSpan], CutSurfaceError> {
        self.validate_surface(surface)?;
        let after_event = surface
            .event_offset
            .checked_add(surface.events)
            .ok_or(CutSurfaceError::HostExtent)?;
        let first =
            usize::try_from(surface.event_offset).map_err(|_| CutSurfaceError::HostExtent)?;
        let after = usize::try_from(after_event).map_err(|_| CutSurfaceError::HostExtent)?;
        self.emissions
            .events
            .get(first..after)
            .ok_or(CutSurfaceError::HostExtent)
    }

    pub fn deed_rows(
        &self,
        surface: IncidenceSurface,
    ) -> Result<&'a [DeedEmission], CutSurfaceError> {
        self.validate_surface(surface)?;
        let after_deed = surface
            .deed_offset
            .checked_add(surface.deeds)
            .ok_or(CutSurfaceError::HostExtent)?;
        let first =
            usize::try_from(surface.deed_offset).map_err(|_| CutSurfaceError::HostExtent)?;
        let after = usize::try_from(after_deed).map_err(|_| CutSurfaceError::HostExtent)?;
        self.emissions
            .deeds
            .get(first..after)
            .ok_or(CutSurfaceError::HostExtent)
    }

    /// Source-supplied A2/contact hand. Endpoints retain global incidence ordinals exactly as the
    /// active ABI supplied them; consumers may not silently rewrite them as local sorted members.
    pub fn directed(&self) -> Result<&'a [DirectedIncidence], CutSurfaceError> {
        if self.directed == 0 {
            return Ok(&[]);
        }
        let first =
            usize::try_from(self.directed_offset).map_err(|_| CutSurfaceError::HostExtent)?;
        let after = usize::try_from(self.directed_offset + self.directed)
            .map_err(|_| CutSurfaceError::HostExtent)?;
        self.active
            .directed
            .get(first..after)
            .ok_or(CutSurfaceError::HostExtent)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::manifold::{FeltDeed, FeltEmission};
    use body::medium::FeltTerm;
    use body::num::Cog;
    use body::place;
    use body::soul::Chi;
    use soma_abi::active::{
        ActionCurrent, CurrentSpan, CutSpan, EventSpan, Incidence, OriginRef, RelationAtom,
    };
    use soma_abi::emission::{CurrentEmissionSpan, DeedEmission, EventEmissionSpan, Header};

    fn fixture(reverse: bool) -> (ActiveCut, EmissionJournal) {
        let active = ActiveCut::new(
            vec![
                RelationAtom::new(Cog::lit(2)).unwrap(),
                RelationAtom::new(Cog::lit(3)).unwrap(),
            ],
            vec![EventSpan::new(0, 1).unwrap(), EventSpan::new(1, 1).unwrap()],
            vec![
                ActionCurrent::new(Cog::lit(5)).unwrap(),
                ActionCurrent::new(Cog::lit(7)).unwrap(),
            ],
            vec![OriginRef::new(1, 0), OriginRef::new(2, 0)],
            vec![
                CurrentSpan::new(0, 1, 0, 1).unwrap(),
                CurrentSpan::new(1, 1, 1, 1).unwrap(),
            ],
            vec![CutSpan::new(0, 3, 0, 1).unwrap()],
            vec![
                Incidence::new(0, 0, 1).unwrap(),
                Incidence::new(0, 0, 1).unwrap(),
                Incidence::new(1, 0, 1).unwrap(),
            ],
            vec![if reverse {
                DirectedIncidence::new(2, 0)
            } else {
                DirectedIncidence::new(0, 2)
            }],
        )
        .unwrap();
        let deed = |value| {
            DeedEmission::new(
                FeltEmission {
                    position: place::origin(),
                    term: FeltTerm {
                        chi: Chi {
                            same: Cog::lit(value),
                            other: Cog::lit(0),
                        },
                        winding: body::channel::WindingQuantum::None,
                    },
                    deed: FeltDeed::Ride,
                    standing_read: None,
                },
                0,
                1,
            )
            .unwrap()
        };
        let journal = EmissionJournal {
            header: Header::new(2, 2, 2).unwrap(),
            events: vec![
                EventEmissionSpan::new(0, 1).unwrap(),
                EventEmissionSpan::new(1, 1).unwrap(),
            ],
            deeds: vec![deed(11), deed(13)],
            currents: vec![
                CurrentEmissionSpan::new(0, 1, 0, 1).unwrap(),
                CurrentEmissionSpan::new(1, 1, 1, 1).unwrap(),
            ],
        };
        journal.validate_against(&active).unwrap();
        (active, journal)
    }

    #[test]
    fn repeated_incidence_is_plural_while_its_event_surface_stands_once() {
        let (active, journal) = fixture(false);
        let cut = CutSurface::new(&active, &journal, 0).unwrap();
        let first = cut.incidence(0).unwrap();
        let repeated = cut.incidence(1).unwrap();
        assert_ne!(first.incidence(), repeated.incidence());
        assert_eq!(first.deed_offset(), repeated.deed_offset());
        assert_eq!(
            cut.deed_rows(first).unwrap().as_ptr(),
            cut.deed_rows(repeated).unwrap().as_ptr()
        );
        assert_eq!(journal.deeds.len(), 2);
    }

    #[test]
    fn reversing_hand_changes_the_cut_topology_without_changing_shared_deeds() {
        let (forward_active, forward_journal) = fixture(false);
        let (reverse_active, reverse_journal) = fixture(true);
        let forward = CutSurface::new(&forward_active, &forward_journal, 0).unwrap();
        let reverse = CutSurface::new(&reverse_active, &reverse_journal, 0).unwrap();
        assert_eq!(forward_journal.deeds, reverse_journal.deeds);
        assert_ne!(forward.directed().unwrap(), reverse.directed().unwrap());
    }
}
