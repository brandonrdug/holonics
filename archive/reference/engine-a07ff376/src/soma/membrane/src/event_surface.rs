//! Exact event-level construction retained beside scalar body conduct.
//!
//! An event is not one storage word and a plural event is not several unrelated instants.  This
//! module composes each event's complete ordered relation-atom span through Soma's existing
//! placement algebra and retains the one supplied action current beside it.  It does not yet
//! invent the still-open universal `ACTUATE(action, body, world)` law: action remains a distinct
//! tangent/current face, never an added relation term.  Directed cut incidence can consequently
//! refer to complete event-span endpoints without using source tags, ordinals, or serialized
//! payloads as material.

use std::vec::Vec;

use body::manifold::Node;
use soma_abi::active::{ActionCurrent, DirectedIncidence, Incidence, RelationAtom};

use crate::{ActiveCut, ActiveCutError, ValidatedActiveCut};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EventSurfaceError {
    Active(ActiveCutError),
    EventAbsent(u64),
    IncidenceAbsent(u64),
    CutAbsent(u64),
    ResourceExtent,
    ResourceReservation,
}

impl From<ActiveCutError> for EventSurfaceError {
    fn from(error: ActiveCutError) -> Self {
        Self::Active(error)
    }
}

/// One complete event face.  `node` is the ordered composition of every relation atom in the
/// event; `action` is the one A1 current under which that event occurred.  Neither can substitute
/// for the other.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EventSurface {
    event: u64,
    atom_offset: u64,
    atoms: u64,
    node: Node,
    action: ActionCurrent,
}

impl EventSurface {
    pub fn event(self) -> u64 {
        self.event
    }

    pub fn atom_offset(self) -> u64 {
        self.atom_offset
    }

    pub fn atoms(self) -> u64 {
        self.atoms
    }

    pub fn node(self) -> Node {
        self.node
    }

    pub fn action(self) -> ActionCurrent {
        self.action
    }
}

/// One physical occurrence of a complete ordered event section.  Repeated incidence rows remain
/// distinct even when they borrow the same event slice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IncidenceEventSurface {
    incidence: u64,
    current: u64,
    event_offset: u64,
    events: u64,
}

impl IncidenceEventSurface {
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
}

/// One supplied causal edge between two complete incidence event sections.  This row retains hand
/// only; forming its A2 crossing still requires the later receiver's real frame and fourth contact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DirectedEventSurface {
    edge: DirectedIncidence,
    from: IncidenceEventSurface,
    to: IncidenceEventSurface,
}

impl DirectedEventSurface {
    pub fn edge(self) -> DirectedIncidence {
        self.edge
    }

    pub fn from(self) -> IncidenceEventSurface {
        self.from
    }

    pub fn to(self) -> IncidenceEventSurface {
        self.to
    }
}

/// The event faces of one validated active population.  The vector is indexed by admitted event
/// ordinal only as a locator; all causal relations continue to use explicit ABI references.
pub struct EventTopology<'a> {
    active: &'a ActiveCut,
    events: Vec<EventSurface>,
}

impl<'a> EventTopology<'a> {
    pub fn new(active: &'a ActiveCut) -> Result<Self, EventSurfaceError> {
        Self::new_validated(active.validated()?)
    }

    pub(crate) fn new_validated(active: ValidatedActiveCut<'a>) -> Result<Self, EventSurfaceError> {
        let extent = usize::try_from(active.header.events())
            .map_err(|_| EventSurfaceError::ResourceExtent)?;
        let mut events = Vec::new();
        events
            .try_reserve_exact(extent)
            .map_err(|_| EventSurfaceError::ResourceReservation)?;
        for (event, span) in active.events.iter().copied().enumerate() {
            let first = usize::try_from(span.atom_offset())
                .map_err(|_| EventSurfaceError::ResourceExtent)?;
            let after = usize::try_from(
                span.atom_offset()
                    .checked_add(span.atoms())
                    .ok_or(EventSurfaceError::ResourceExtent)?,
            )
            .map_err(|_| EventSurfaceError::ResourceExtent)?;
            let atoms = active
                .atoms
                .get(first..after)
                .ok_or(EventSurfaceError::EventAbsent(event as u64))?;
            events.push(EventSurface {
                event: event as u64,
                atom_offset: span.atom_offset(),
                atoms: span.atoms(),
                node: relation_span_node(atoms)?,
                action: active.actions[event],
            });
        }
        Ok(Self {
            active: active.active(),
            events,
        })
    }

    pub fn events(&self) -> &[EventSurface] {
        &self.events
    }

    pub(crate) fn into_events(self) -> Vec<EventSurface> {
        self.events
    }

    pub fn event(&self, event: u64) -> Option<EventSurface> {
        self.events.get(usize::try_from(event).ok()?).copied()
    }

    pub fn incidence(&self, incidence: u64) -> Result<IncidenceEventSurface, EventSurfaceError> {
        let row = self
            .active
            .incidences
            .get(usize::try_from(incidence).map_err(|_| EventSurfaceError::ResourceExtent)?)
            .copied()
            .ok_or(EventSurfaceError::IncidenceAbsent(incidence))?;
        incidence_event_surface(self.active, incidence, row)
    }

    pub fn incidence_events(
        &self,
        incidence: IncidenceEventSurface,
    ) -> Result<&[EventSurface], EventSurfaceError> {
        let after = incidence
            .event_offset
            .checked_add(incidence.events)
            .ok_or(EventSurfaceError::ResourceExtent)?;
        let first = usize::try_from(incidence.event_offset)
            .map_err(|_| EventSurfaceError::ResourceExtent)?;
        let after = usize::try_from(after).map_err(|_| EventSurfaceError::ResourceExtent)?;
        self.events
            .get(first..after)
            .ok_or(EventSurfaceError::IncidenceAbsent(incidence.incidence))
    }

    pub fn directed(&self, cut: u64) -> Result<Vec<DirectedEventSurface>, EventSurfaceError> {
        let cut_span = self
            .active
            .cuts
            .get(usize::try_from(cut).map_err(|_| EventSurfaceError::ResourceExtent)?)
            .copied()
            .ok_or(EventSurfaceError::CutAbsent(cut))?;
        let extent =
            usize::try_from(cut_span.directed()).map_err(|_| EventSurfaceError::ResourceExtent)?;
        let mut surfaces = Vec::new();
        surfaces
            .try_reserve_exact(extent)
            .map_err(|_| EventSurfaceError::ResourceReservation)?;
        if extent == 0 {
            return Ok(surfaces);
        }
        let first = usize::try_from(cut_span.directed_offset())
            .map_err(|_| EventSurfaceError::ResourceExtent)?;
        let after = first
            .checked_add(extent)
            .ok_or(EventSurfaceError::ResourceExtent)?;
        let edges = self
            .active
            .directed
            .get(first..after)
            .ok_or(EventSurfaceError::CutAbsent(cut))?;
        for edge in edges {
            surfaces.push(DirectedEventSurface {
                edge: *edge,
                from: self.incidence(edge.from_incidence())?,
                to: self.incidence(edge.to_incidence())?,
            });
        }
        Ok(surfaces)
    }
}

fn incidence_event_surface(
    active: &ActiveCut,
    incidence: u64,
    row: Incidence,
) -> Result<IncidenceEventSurface, EventSurfaceError> {
    let current = active
        .currents
        .get(usize::try_from(row.current()).map_err(|_| EventSurfaceError::ResourceExtent)?)
        .copied()
        .ok_or(EventSurfaceError::IncidenceAbsent(incidence))?;
    let event_offset = current
        .event_offset()
        .checked_add(row.current_event_offset())
        .ok_or(EventSurfaceError::ResourceExtent)?;
    Ok(IncidenceEventSurface {
        incidence,
        current: row.current(),
        event_offset,
        events: row.current_events(),
    })
}

/// The source-neutral generalization of `manifold::locate`: relation atoms are already the exact
/// material differences, so no byte/container boundary is revisited.
pub(crate) fn relation_span_node(atoms: &[RelationAtom]) -> Result<Node, EventSurfaceError> {
    soma_abi::active::relation_span_node(atoms).ok_or(EventSurfaceError::ResourceExtent)
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::num::Cog;
    use soma_abi::active::{CurrentSpan, CutSpan, EventSpan, OriginRef};

    fn fixture(reverse_atoms: bool, reverse_hand: bool, action: Cog) -> ActiveCut {
        let first = if reverse_atoms {
            [Cog::lit(3), Cog::lit(2)]
        } else {
            [Cog::lit(2), Cog::lit(3)]
        };
        ActiveCut::new(
            vec![
                RelationAtom::new(first[0]).unwrap(),
                RelationAtom::new(first[1]).unwrap(),
                RelationAtom::new(Cog::lit(5)).unwrap(),
            ],
            vec![EventSpan::new(0, 2).unwrap(), EventSpan::new(2, 1).unwrap()],
            vec![
                ActionCurrent::new(action).unwrap(),
                ActionCurrent::new(Cog::lit(11)).unwrap(),
            ],
            vec![OriginRef::new(7, 0), OriginRef::new(13, 0)],
            vec![
                CurrentSpan::new(0, 1, 0, 2).unwrap(),
                CurrentSpan::new(1, 1, 2, 1).unwrap(),
            ],
            vec![CutSpan::new(0, 2, 0, 1).unwrap()],
            vec![
                Incidence::new(0, 0, 1).unwrap(),
                Incidence::new(1, 0, 1).unwrap(),
            ],
            vec![if reverse_hand {
                DirectedIncidence::new(1, 0)
            } else {
                DirectedIncidence::new(0, 1)
            }],
        )
        .unwrap()
    }

    #[test]
    fn the_complete_event_span_forms_one_node_and_retains_action_beside_it() {
        let active = fixture(false, false, Cog::lit(7));
        let changed_action = fixture(false, false, Cog::lit(7).turn_up(2));
        let reversed_atoms = fixture(true, false, Cog::lit(7));
        let topology = EventTopology::new(&active).unwrap();
        let changed = EventTopology::new(&changed_action).unwrap();
        let reversed = EventTopology::new(&reversed_atoms).unwrap();

        let event = topology.event(0).unwrap();
        assert_eq!((event.atom_offset(), event.atoms()), (0, 2));
        assert_eq!(event.node().len, 18);
        assert_eq!(event.node().well, Cog::lit(2).mul(Cog::lit(3)));
        assert_eq!(event.node().place, changed.event(0).unwrap().node().place);
        assert_ne!(event.action(), changed.event(0).unwrap().action());
        assert_ne!(event.node().place, reversed.event(0).unwrap().node().place);
    }

    #[test]
    fn plural_atom_order_retains_rank_and_turn_even_when_magnitudes_match() {
        let ranked = Cog::lit(3).turn_up(7);
        let handed = Cog::lit(3).turned(1);
        let make = |atoms: [Cog; 2]| {
            ActiveCut::new(
                atoms
                    .into_iter()
                    .map(|atom| RelationAtom::new(atom).unwrap())
                    .collect(),
                vec![EventSpan::new(0, 2).unwrap()],
                vec![ActionCurrent::new(Cog::lit(5)).unwrap()],
                vec![OriginRef::new(17, 0)],
                vec![CurrentSpan::new(0, 1, 0, 2).unwrap()],
                vec![CutSpan::new(0, 1, 0, 0).unwrap()],
                vec![Incidence::new(0, 0, 1).unwrap()],
                Vec::new(),
            )
            .unwrap()
        };
        let forward_cut = make([ranked, handed]);
        let reverse_cut = make([handed, ranked]);
        let forward = EventTopology::new(&forward_cut).unwrap();
        let reverse = EventTopology::new(&reverse_cut).unwrap();

        assert_eq!(
            forward.event(0).unwrap().node().well,
            reverse.event(0).unwrap().node().well
        );
        assert_ne!(
            forward.event(0).unwrap().node().place,
            reverse.event(0).unwrap().node().place,
            "the ordered plural event cannot collapse equal magnitudes with different rank/turn"
        );
    }

    #[test]
    fn directed_hand_swaps_complete_incidence_sections_without_reordering_events() {
        let forward = fixture(false, false, Cog::lit(7));
        let reverse = fixture(false, true, Cog::lit(7));
        let forward_topology = EventTopology::new(&forward).unwrap();
        let reverse_topology = EventTopology::new(&reverse).unwrap();
        let forward_edge = forward_topology.directed(0).unwrap()[0];
        let reverse_edge = reverse_topology.directed(0).unwrap()[0];

        assert_eq!(forward_edge.from(), reverse_edge.to());
        assert_eq!(forward_edge.to(), reverse_edge.from());
        assert_eq!(
            forward_topology
                .incidence_events(forward_edge.from())
                .unwrap()[0]
                .node()
                .place,
            reverse_topology
                .incidence_events(reverse_edge.to())
                .unwrap()[0]
                .node()
                .place,
        );
    }
}
