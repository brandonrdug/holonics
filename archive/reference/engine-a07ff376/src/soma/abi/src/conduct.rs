//! Substrate-neutral conduct of one native active current.
//!
//! This is the common event-time mouth for host and card execution.  It consumes canonical
//! relation atoms and one action per complete event, retains one unresolved dark interval, and
//! reports every accepted body deed through a caller-owned output target.  Allocation, launch
//! shape, journal storage, directed-incidence indexing, and world interpretation remain outside.

use body::manifold::{AtomEvent, ErosBody, FeltEmission, FeltEmissionTarget};
use body::num::Cog;

use crate::active::{relation_span_node, ValidationError, View};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EventContact {
    pub event: u64,
    pub atom_offset: u64,
    pub atoms: u64,
    pub action: Cog,
    pub consequence: AtomEvent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CurrentConduct {
    pub current: u64,
    pub events: u64,
    pub dark_events: u64,
    pub relation_atoms: u64,
    pub folds: u64,
    pub perceptions: u64,
    pub steps: u64,
    pub dark_resolutions: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConductError<E> {
    Structural(ValidationError),
    CurrentAbsent(u64),
    HostExtent,
    ResourceExtent,
    BodyResource,
    RelationSpan,
    Incomplete,
    Target(E),
}

/// Physical output boundary for a conducted current.  Methods are chronological.  A target may
/// retain event spans, CUDA rows, or host journals, but none of its return values can alter body
/// law: any refusal aborts the disposable current whole.
pub trait ConductTarget {
    type Error;

    fn begin_current(&mut self, current: u64, event_offset: u64) -> Result<(), Self::Error>;

    fn before_event(&mut self, event: u64, body: &mut ErosBody<'_>) -> Result<(), Self::Error>;

    fn emit(
        &mut self,
        emission: FeltEmission,
        cause_event_offset: u64,
        cause_events: u64,
    ) -> Result<(), Self::Error>;

    fn contact(&mut self, contact: EventContact) -> Result<(), Self::Error>;

    fn close_event(&mut self, event: u64) -> Result<(), Self::Error>;

    fn close_current(
        &mut self,
        current: u64,
        event_offset: u64,
        events: u64,
    ) -> Result<(), Self::Error>;
}

struct EmissionForwarder<'a, T: ConductTarget> {
    target: &'a mut T,
    cause_event_offset: u64,
    cause_events: u64,
    error: &'a mut Option<T::Error>,
}

impl<T: ConductTarget> FeltEmissionTarget for EmissionForwarder<'_, T> {
    #[inline]
    fn emit(&mut self, emission: FeltEmission) {
        if self.error.is_none() {
            if let Err(error) =
                self.target
                    .emit(emission, self.cause_event_offset, self.cause_events)
            {
                *self.error = Some(error);
            }
        }
    }
}

#[inline]
fn add_count<E>(slot: &mut u64, value: u64) -> Result<(), ConductError<E>> {
    *slot = slot
        .checked_add(value)
        .ok_or(ConductError::ResourceExtent)?;
    Ok(())
}

/// Conduct one current from a complete active view.  Validation happens before the first body
/// mutation so a malformed card buffer cannot turn into partial topology.
pub fn conduct_current<T: ConductTarget>(
    active: &View<'_>,
    current_ordinal: u64,
    body: &mut ErosBody<'_>,
    target: &mut T,
) -> Result<CurrentConduct, ConductError<T::Error>> {
    active.validate().map_err(ConductError::Structural)?;
    let current_index = usize::try_from(current_ordinal).map_err(|_| ConductError::HostExtent)?;
    let current = active
        .currents
        .get(current_index)
        .copied()
        .ok_or(ConductError::CurrentAbsent(current_ordinal))?;
    let first_event =
        usize::try_from(current.event_offset()).map_err(|_| ConductError::HostExtent)?;
    let after_event_u64 = current
        .event_offset()
        .checked_add(current.events())
        .ok_or(ConductError::ResourceExtent)?;
    let after_event = usize::try_from(after_event_u64).map_err(|_| ConductError::HostExtent)?;

    target
        .begin_current(current_ordinal, current.event_offset())
        .map_err(ConductError::Target)?;

    let mut pending = Cog::ZERO;
    let mut pending_event_offset = 0u64;
    let mut pending_events = 0u64;
    let mut receipt = CurrentConduct {
        current: current_ordinal,
        events: current.events(),
        dark_events: 0,
        relation_atoms: 0,
        folds: 0,
        perceptions: 0,
        steps: 0,
        dark_resolutions: 0,
    };

    let mut event_index = first_event;
    while event_index < after_event {
        let event = active.events[event_index];
        let action = active.actions[event_index].cog();
        target
            .before_event(event_index as u64, body)
            .map_err(ConductError::Target)?;
        if body.resource_refused() {
            return Err(ConductError::BodyResource);
        }

        let local_event = event_index as u64 - current.event_offset();
        let first_atom =
            usize::try_from(event.atom_offset()).map_err(|_| ConductError::HostExtent)?;
        let after_atom_u64 = event
            .atom_offset()
            .checked_add(event.atoms())
            .ok_or(ConductError::ResourceExtent)?;
        let after_atom = usize::try_from(after_atom_u64).map_err(|_| ConductError::HostExtent)?;
        let event_atoms = active
            .atoms
            .get(first_atom..after_atom)
            .ok_or(ConductError::HostExtent)?;
        let resolving_atoms = event_atoms
            .iter()
            .filter(|atom| atom.cog().mag != 0)
            .count();
        let wholly_dark = resolving_atoms == 0;

        if wholly_dark {
            pending = pending.add(action);
            if pending_events == 0 {
                pending_event_offset = local_event;
            }
            pending_events = pending_events
                .checked_add(1)
                .ok_or(ConductError::ResourceExtent)?;
            add_count(&mut receipt.dark_events, 1)?;

            if event_index + 1 == after_event && pending_events != 0 {
                if pending.mag != 0 {
                    let mut output_error = None;
                    let mut forward = EmissionForwarder {
                        target,
                        cause_event_offset: pending_event_offset,
                        cause_events: pending_events,
                        error: &mut output_error,
                    };
                    body.resolve_dark_action_emitting(pending, &mut forward);
                    if let Some(error) = output_error {
                        return Err(ConductError::Target(error));
                    }
                }
                if body.resource_refused() {
                    return Err(ConductError::BodyResource);
                }
                pending = Cog::ZERO;
                pending_events = 0;
                add_count(&mut receipt.dark_resolutions, 1)?;
            }
            target
                .close_event(event_index as u64)
                .map_err(ConductError::Target)?;
            event_index += 1;
            continue;
        }

        if pending_events != 0 {
            if pending.mag != 0 {
                let mut output_error = None;
                let mut forward = EmissionForwarder {
                    target,
                    cause_event_offset: pending_event_offset,
                    cause_events: pending_events,
                    error: &mut output_error,
                };
                body.resolve_dark_action_emitting(pending, &mut forward);
                if let Some(error) = output_error {
                    return Err(ConductError::Target(error));
                }
            }
            if body.resource_refused() {
                return Err(ConductError::BodyResource);
            }
            pending = Cog::ZERO;
            pending_events = 0;
            add_count(&mut receipt.dark_resolutions, 1)?;
        }

        let event_node = relation_span_node(event_atoms).ok_or(ConductError::RelationSpan)?;
        let mut output_error = None;
        let consequence = {
            let mut forward = EmissionForwarder {
                target,
                cause_event_offset: local_event,
                cause_events: 1,
                error: &mut output_error,
            };
            body.live_event_node_emitting(event_node, action, &mut forward)
        };
        if let Some(error) = output_error {
            return Err(ConductError::Target(error));
        }
        if body.resource_refused() {
            return Err(ConductError::BodyResource);
        }
        add_count(
            &mut receipt.relation_atoms,
            u64::try_from(resolving_atoms).map_err(|_| ConductError::ResourceExtent)?,
        )?;
        add_count(&mut receipt.folds, consequence.fold.is_some() as u64)?;
        add_count(
            &mut receipt.perceptions,
            consequence.perception.is_some() as u64,
        )?;
        add_count(&mut receipt.steps, consequence.step.is_some() as u64)?;
        target
            .contact(EventContact {
                event: event_index as u64,
                atom_offset: event.atom_offset(),
                atoms: event.atoms(),
                action,
                consequence,
            })
            .map_err(ConductError::Target)?;
        target
            .close_event(event_index as u64)
            .map_err(ConductError::Target)?;
        event_index += 1;
    }

    if pending.mag != 0 || pending_events != 0 {
        return Err(ConductError::Incomplete);
    }
    target
        .close_current(current_ordinal, current.event_offset(), current.events())
        .map_err(ConductError::Target)?;
    Ok(receipt)
}
