//! Native host event conduct over an [`ActiveCut`](crate::ActiveCut).
//!
//! The relation population, not an event's storage encoding, enters Soma. One supplied action
//! marks each actual event under A1. Raw Flow does not cross a bright horizon as a second term;
//! its whole construction remains in the active cut and Holon. When every component is zero, the
//! action has the one derived numeric consequence licensed by the dark-tread law: it extends one
//! unresolved interval, deposited whole at the next resolving event or the current's actual end.
//! A mixed event is resolving as a whole: its complete ordered span crosses once, including the
//! positional consequence of zero coordinates, without manufacturing component-local instants.

use body::manifold::{current_conduct_envelope, ErosBody, FeltEmission};
#[cfg(test)]
use body::num::Cog;
use soma_abi::conduct::{
    conduct_current as conduct_native_current, ConductError as NativeConductError, ConductTarget,
};
use soma_abi::emission::DeedEmission;

use crate::emission_journal::EmissionTarget;
use crate::{
    ActiveCut, ActiveCutError, CurrentEmissionBuilder, EmissionJournalBuilder,
    EmissionJournalError, EventSurfaceError, ValidatedActiveCut,
};

pub use soma_abi::conduct::{CurrentConduct, EventContact};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConductError {
    Structural(ActiveCutError),
    Emission(EmissionJournalError),
    CurrentAbsent(u64),
    HostExtent,
    ResourceExtent,
    BodyResource,
    EventSurface(EventSurfaceError),
}

impl From<ActiveCutError> for ConductError {
    fn from(error: ActiveCutError) -> Self {
        Self::Structural(error)
    }
}

impl From<EmissionJournalError> for ConductError {
    fn from(error: EmissionJournalError) -> Self {
        Self::Emission(error)
    }
}

impl From<EventSurfaceError> for ConductError {
    fn from(error: EventSurfaceError) -> Self {
        Self::EventSurface(error)
    }
}

/// Exact pre-mutation source extent for one admitted current.  Bright relations and unresolved
/// dark intervals are properties of the active event topology; the maximum deed population is
/// derived by the body from those extents and the receiver's actual carrier depth.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CurrentPreflight {
    pub current: u64,
    pub bright_events: u64,
    pub bright_atoms: u64,
    pub dark_intervals: u64,
    pub carrier_depth: u64,
}

impl CurrentPreflight {
    /// Conservative historical fixed-reservation observer.  Production growable storage does not
    /// use this exponential face as a gate.
    pub fn maximum_deeds(self) -> Option<u64> {
        current_conduct_envelope(
            self.bright_events,
            self.dark_intervals,
            usize::try_from(self.carrier_depth).ok()?,
        )
        .map(|envelope| envelope.maximum_deeds)
    }
}

pub fn preflight_current(
    active: &ActiveCut,
    current_ordinal: u64,
    carrier_depth: usize,
) -> Result<CurrentPreflight, ConductError> {
    preflight_validated_current(active.validated()?, current_ordinal, carrier_depth)
}

/// Form the only public production output reservation for a current.  The body-derived envelope
/// remains exact testimony, while deed storage grows from actual accepted topology inside the
/// disposable successor.  Callers cannot inject a smaller semantic cap.
pub fn preflight_current_partition(
    active: &ActiveCut,
    current_ordinal: u64,
    carrier_depth: usize,
) -> Result<(CurrentPreflight, CurrentEmissionBuilder), ConductError> {
    preflight_current_partition_validated(active.validated()?, current_ordinal, carrier_depth)
}

pub(crate) fn preflight_current_partition_validated(
    active: ValidatedActiveCut<'_>,
    current_ordinal: u64,
    carrier_depth: usize,
) -> Result<(CurrentPreflight, CurrentEmissionBuilder), ConductError> {
    let preflight = preflight_validated_current(active, current_ordinal, carrier_depth)?;
    let journal = CurrentEmissionBuilder::preflight_validated(active, current_ordinal)?;
    Ok((preflight, journal))
}

/// Body-derived conservative deed extent for the complete co-present population.  This sums
/// physical source envelopes only; it does not serialize the currents or prescribe execution
/// order.  Each current may still conduct from the same receiver-before body in an independent
/// lineage surface.
pub fn preflight_active_deeds(
    active: &ActiveCut,
    carrier_depth: usize,
) -> Result<u64, ConductError> {
    let active = active.validated()?;
    let mut maximum = 0u64;
    let mut current = 0u64;
    while current < active.header.currents() {
        maximum = maximum
            .checked_add(
                preflight_validated_current(active, current, carrier_depth)?
                    .maximum_deeds()
                    .ok_or(ConductError::ResourceExtent)?,
            )
            .ok_or(ConductError::ResourceExtent)?;
        current += 1;
    }
    Ok(maximum)
}

fn preflight_validated_current(
    active: ValidatedActiveCut<'_>,
    current_ordinal: u64,
    carrier_depth: usize,
) -> Result<CurrentPreflight, ConductError> {
    let current = active
        .currents
        .get(usize::try_from(current_ordinal).map_err(|_| ConductError::HostExtent)?)
        .copied()
        .ok_or(ConductError::CurrentAbsent(current_ordinal))?;
    let first_event =
        usize::try_from(current.event_offset()).map_err(|_| ConductError::HostExtent)?;
    let after_event = usize::try_from(
        current
            .event_offset()
            .checked_add(current.events())
            .ok_or(ConductError::ResourceExtent)?,
    )
    .map_err(|_| ConductError::HostExtent)?;

    let mut bright_events = 0u64;
    let mut bright_atoms = 0u64;
    let mut dark_intervals = 0u64;
    let mut dark_open = false;
    let mut event_index = first_event;
    while event_index < after_event {
        let event = active.events[event_index];
        let first_atom =
            usize::try_from(event.atom_offset()).map_err(|_| ConductError::HostExtent)?;
        let after_atom = usize::try_from(
            event
                .atom_offset()
                .checked_add(event.atoms())
                .ok_or(ConductError::ResourceExtent)?,
        )
        .map_err(|_| ConductError::HostExtent)?;
        let mut event_bright = 0u64;
        for atom in &active.atoms[first_atom..after_atom] {
            if atom.cog().mag != 0 {
                event_bright = event_bright
                    .checked_add(1)
                    .ok_or(ConductError::ResourceExtent)?;
            }
        }
        if event_bright == 0 {
            if !dark_open {
                dark_intervals = dark_intervals
                    .checked_add(1)
                    .ok_or(ConductError::ResourceExtent)?;
                dark_open = true;
            }
        } else {
            bright_events = bright_events
                .checked_add(1)
                .ok_or(ConductError::ResourceExtent)?;
            bright_atoms = bright_atoms
                .checked_add(event_bright)
                .ok_or(ConductError::ResourceExtent)?;
            dark_open = false;
        }
        event_index += 1;
    }
    Ok(CurrentPreflight {
        current: current_ordinal,
        bright_events,
        bright_atoms,
        dark_intervals,
        carrier_depth: u64::try_from(carrier_depth).map_err(|_| ConductError::ResourceExtent)?,
    })
}

/// Conduct one current's admitted events exactly once. Sparse cut incidence is intentionally not
/// folded here: it is the next native receiving seam and must cross as actual cut topology rather
/// than being smuggled into this lineage walk.
pub fn conduct_current(
    active: &ActiveCut,
    current_ordinal: u64,
    body: &mut ErosBody<'_>,
    observe: impl FnMut(EventContact),
) -> Result<CurrentConduct, ConductError> {
    conduct_current_inner(
        active.validated()?,
        current_ordinal,
        body,
        None,
        None,
        observe,
    )
}

/// Conduct one current while appending every accepted OWN deed to the active population's shared
/// immutable output journal.  Currents must be supplied in admitted order so event chronology is
/// retained without a scheduler or a sorting pass.
pub fn conduct_current_emitting(
    active: &ActiveCut,
    current_ordinal: u64,
    body: &mut ErosBody<'_>,
    journal: &mut EmissionJournalBuilder,
    observe: impl FnMut(EventContact),
) -> Result<CurrentConduct, ConductError> {
    conduct_current_inner(
        active.validated()?,
        current_ordinal,
        body,
        Some(journal),
        None,
        observe,
    )
}

/// Conduct one current into its own fully reserved output partition.  This is the production
/// plural-current mouth: it has no observer callback and no shared journal cursor.  Distinct
/// current-local bodies may therefore act independently from the same immutable receiver-before
/// face; their completed parts join only afterward through `EmissionJournal::assemble`.
pub fn conduct_current_partition(
    active: &ActiveCut,
    current_ordinal: u64,
    body: &mut ErosBody<'_>,
    journal: &mut CurrentEmissionBuilder,
) -> Result<CurrentConduct, ConductError> {
    conduct_current_partition_validated(active.validated()?, current_ordinal, body, journal, |_| {})
}

pub(crate) fn conduct_current_partition_validated(
    active: ValidatedActiveCut<'_>,
    current_ordinal: u64,
    body: &mut ErosBody<'_>,
    journal: &mut CurrentEmissionBuilder,
    observe: impl FnMut(EventContact),
) -> Result<CurrentConduct, ConductError> {
    conduct_current_inner(active, current_ordinal, body, Some(journal), None, observe)
}

pub(crate) fn conduct_current_partition_with_event_receiver(
    active: ValidatedActiveCut<'_>,
    current_ordinal: u64,
    body: &mut ErosBody<'_>,
    journal: &mut CurrentEmissionBuilder,
    before_event: &mut dyn FnMut(u64, &mut ErosBody<'_>) -> Result<(), ConductError>,
    observe: impl FnMut(EventContact),
) -> Result<CurrentConduct, ConductError> {
    conduct_current_inner(
        active,
        current_ordinal,
        body,
        Some(journal),
        Some(before_event),
        observe,
    )
}

fn conduct_current_inner(
    active: ValidatedActiveCut<'_>,
    current_ordinal: u64,
    body: &mut ErosBody<'_>,
    journal: Option<&mut dyn EmissionTarget>,
    before_event: Option<&mut dyn FnMut(u64, &mut ErosBody<'_>) -> Result<(), ConductError>>,
    observe: impl FnMut(EventContact),
) -> Result<CurrentConduct, ConductError> {
    struct HostTarget<'journal, 'before, O> {
        journal: Option<&'journal mut dyn EmissionTarget>,
        before_event:
            Option<&'before mut dyn FnMut(u64, &mut ErosBody<'_>) -> Result<(), ConductError>>,
        observe: O,
        event_deed_offset: u64,
    }

    impl<O: FnMut(EventContact)> ConductTarget for HostTarget<'_, '_, O> {
        type Error = ConductError;

        fn begin_current(&mut self, current: u64, event_offset: u64) -> Result<(), Self::Error> {
            if let Some(journal) = self.journal.as_deref_mut() {
                journal.begin_current(current, event_offset)?;
            }
            Ok(())
        }

        fn before_event(&mut self, event: u64, body: &mut ErosBody<'_>) -> Result<(), Self::Error> {
            self.event_deed_offset = self
                .journal
                .as_deref()
                .map_or(0, EmissionTarget::deed_offset);
            if let Some(before_event) = self.before_event.as_deref_mut() {
                before_event(event, body)?;
            }
            Ok(())
        }

        fn emit(
            &mut self,
            emission: FeltEmission,
            cause_event_offset: u64,
            cause_events: u64,
        ) -> Result<(), Self::Error> {
            let Some(journal) = self.journal.as_deref_mut() else {
                return Ok(());
            };
            let row = DeedEmission::new(emission, cause_event_offset, cause_events)
                .ok_or(EmissionJournalError::BodyEmission)?;
            journal.push_deed(row)?;
            Ok(())
        }

        fn contact(&mut self, contact: EventContact) -> Result<(), Self::Error> {
            (self.observe)(contact);
            Ok(())
        }

        fn close_event(&mut self, event: u64) -> Result<(), Self::Error> {
            if let Some(journal) = self.journal.as_deref_mut() {
                journal.close_event(event, self.event_deed_offset)?;
            }
            Ok(())
        }

        fn close_current(
            &mut self,
            current: u64,
            event_offset: u64,
            events: u64,
        ) -> Result<(), Self::Error> {
            if let Some(journal) = self.journal.as_deref_mut() {
                journal.close_current(current, event_offset, events)?;
            }
            Ok(())
        }
    }

    fn map_native(error: NativeConductError<ConductError>) -> ConductError {
        match error {
            NativeConductError::Structural(error) => {
                ConductError::Structural(ActiveCutError::Structural(error))
            }
            NativeConductError::CurrentAbsent(current) => ConductError::CurrentAbsent(current),
            NativeConductError::HostExtent => ConductError::HostExtent,
            NativeConductError::ResourceExtent => ConductError::ResourceExtent,
            NativeConductError::BodyResource => ConductError::BodyResource,
            NativeConductError::RelationSpan => {
                ConductError::EventSurface(EventSurfaceError::ResourceExtent)
            }
            NativeConductError::Incomplete => {
                ConductError::Emission(EmissionJournalError::Incomplete)
            }
            NativeConductError::Target(error) => error,
        }
    }

    let mut target = HostTarget {
        journal,
        before_event,
        observe,
        event_deed_offset: 0,
    };
    conduct_native_current(&active.view(), current_ordinal, body, &mut target).map_err(map_native)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::vec::Vec;

    use body::manifold::{
        carrier_row_words, narrow_own_cells, zero_extend_own_cells, FeltEmissionSurface, OwnRecast,
        SparseOwnCell, ENCLOSURE_WORDS, OWN_CELL_WORDS,
    };
    use body::medium::{RegionalForm, FORM_WORDS};
    use body::place;
    use soma_abi::active::{
        ActionCurrent, CurrentSpan, CutSpan, EventSpan, Incidence, OriginRef, RelationAtom,
    };
    use soma_abi::emission::DeedKind;

    const AXIS: i64 = 1 << 8;
    const DEPTH: usize = 8;

    struct VecChart {
        words: Vec<u32>,
        recasts: usize,
    }

    impl VecChart {
        fn born() -> Self {
            Self {
                words: vec![0u32; OWN_CELL_WORDS],
                recasts: 0,
            }
        }
    }

    impl OwnRecast for VecChart {
        fn words(&self) -> &[u32] {
            &self.words
        }

        fn words_mut(&mut self) -> &mut [u32] {
            &mut self.words
        }

        fn recast(&mut self, old_axis: i64, new_axis: i64) {
            let mut fresh = vec![0u32; (new_axis * new_axis) as usize * OWN_CELL_WORDS];
            if new_axis > old_axis {
                zero_extend_own_cells(&self.words, &mut fresh, old_axis, new_axis);
            } else {
                narrow_own_cells(&self.words, &mut fresh, old_axis, new_axis);
            }
            self.words = fresh;
            self.recasts += 1;
        }
    }

    fn one_current(events: &[(&[Cog], Cog)]) -> ActiveCut {
        let mut atoms = Vec::new();
        let mut event_rows = Vec::new();
        let mut actions = Vec::new();
        let mut origins = Vec::new();
        for (ordinal, (relations, action)) in events.iter().enumerate() {
            let offset = atoms.len() as u64;
            atoms.extend(
                relations
                    .iter()
                    .copied()
                    .map(|relation| RelationAtom::new(relation).unwrap()),
            );
            event_rows.push(EventSpan::new(offset, relations.len() as u64).unwrap());
            actions.push(ActionCurrent::new(*action).unwrap());
            origins.push(OriginRef::new(1, ordinal as u64));
        }
        ActiveCut::new(
            atoms,
            event_rows,
            actions,
            origins,
            vec![CurrentSpan::new(
                0,
                events.len() as u64,
                0,
                events.iter().map(|e| e.0.len() as u64).sum(),
            )
            .unwrap()],
            vec![CutSpan::new(0, 1, 0, 0).unwrap()],
            vec![Incidence::new(0, 0, events.len() as u64).unwrap()],
            Vec::new(),
        )
        .unwrap()
    }

    fn two_currents() -> ActiveCut {
        let relations = [
            Cog::lit(3),
            Cog::lit(-5),
            Cog::lit(8),
            Cog::lit(13),
            Cog::lit(-21),
            Cog::lit(34),
            Cog::lit(257).turn_up(1),
            Cog::lit(-65_537).turn_down(2).turned(1),
            Cog::lit(144),
            Cog::lit(233),
            Cog::lit(-377),
            Cog::lit(610),
        ];
        ActiveCut::new(
            relations
                .iter()
                .copied()
                .map(|relation| RelationAtom::new(relation).unwrap())
                .collect(),
            (0..relations.len())
                .map(|event| EventSpan::new(event as u64, 1).unwrap())
                .collect(),
            vec![ActionCurrent::new(Cog::lit(1)).unwrap(); relations.len()],
            (0..relations.len())
                .map(|event| {
                    let organ = if event < 6 { 11 } else { 29 };
                    OriginRef::new(organ, event as u64)
                })
                .collect(),
            vec![
                CurrentSpan::new(0, 6, 0, 6).unwrap(),
                CurrentSpan::new(6, 6, 6, 6).unwrap(),
            ],
            vec![CutSpan::new(0, 2, 0, 1).unwrap()],
            vec![
                Incidence::new(0, 0, 6).unwrap(),
                Incidence::new(1, 0, 6).unwrap(),
            ],
            vec![soma_abi::active::DirectedIncidence::new(0, 1)],
        )
        .unwrap()
    }

    type PartitionFace = (
        u32,
        u64,
        (u64, u64),
        Vec<SparseOwnCell>,
        crate::GrowingCarrier,
    );

    fn run_partitions(
        active: &ActiveCut,
        order: &[u64],
    ) -> (crate::EmissionJournal, Vec<PartitionFace>) {
        let standing = crate::SparseStandingSurface::empty(64).unwrap();
        let event_topology = crate::EventTopology::new(active).unwrap();
        let mut parts = Vec::new();
        let mut faces: Vec<Option<PartitionFace>> = Vec::new();
        faces.resize_with(active.currents.len(), || None);
        for &ordinal in order {
            let (_preflight, mut builder) =
                preflight_current_partition(active, ordinal, DEPTH).unwrap();
            let mut storage = crate::GrowingSparseOwn::new();
            let mut carrier = crate::GrowingCarrier::with_depth(DEPTH).unwrap();
            let current = active.currents[ordinal as usize];
            let first_event = event_topology.event(current.event_offset()).unwrap();
            let face = {
                let mut body = ErosBody::over_sparse_world_storage_from_first_difference(
                    standing.flat_cells().unwrap(),
                    &mut storage,
                    standing.flat_axis().unwrap() as i64,
                    first_event.node().place,
                    &mut carrier,
                )
                .unwrap();
                conduct_current_partition(active, ordinal, &mut body, &mut builder).unwrap();
                (
                    body.own_axis() as u32,
                    body.own_occupancy(),
                    body.breath(),
                    body.sparse_own_cells().unwrap().to_vec(),
                )
            };
            faces[ordinal as usize] = Some((face.0, face.1, face.2, face.3, carrier));
            parts.push(builder.finish().unwrap());
        }
        (
            crate::EmissionJournal::assemble(active, parts).unwrap(),
            faces.into_iter().map(Option::unwrap).collect(),
        )
    }

    fn run_native(
        active: &ActiveCut,
    ) -> (Vec<u32>, Vec<u32>, Vec<u32>, body::manifold::TermCounts) {
        let standing = vec![0u32; (AXIS * AXIS) as usize * FORM_WORDS];
        let mut own = vec![0u32; (AXIS * AXIS) as usize * FORM_WORDS];
        let mut carrier = vec![0u32; DEPTH * ENCLOSURE_WORDS];
        let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
        conduct_current(active, 0, &mut body, |_| {}).unwrap();
        let mut carried = vec![0u32; carrier_row_words(DEPTH)];
        assert!(body.pack_carried_frame(active.header.events(), &mut carried));
        let terms = body.deposited_terms();
        drop(body);
        (own, carrier, carried, terms)
    }

    fn run_native_emitting(
        active: &ActiveCut,
    ) -> (Vec<u32>, crate::EmissionJournal, body::manifold::TermCounts) {
        let standing = vec![0u32; (AXIS * AXIS) as usize * FORM_WORDS];
        let mut own = vec![0u32; (AXIS * AXIS) as usize * FORM_WORDS];
        let mut carrier = vec![0u32; DEPTH * ENCLOSURE_WORDS];
        let mut builder = crate::EmissionJournalBuilder::new(active);
        let terms;
        {
            let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
            conduct_current_emitting(active, 0, &mut body, &mut builder, |_| {}).unwrap();
            terms = body.deposited_terms();
        }
        let journal = builder.finish(active).unwrap();
        (own, journal, terms)
    }

    #[test]
    fn the_octet_organ_is_exactly_one_native_event_species() {
        let light = b"native relations preserve 00  11 and every historical fold";
        let relations: Vec<Cog> = light
            .windows(2)
            .map(|pair| body::boundary::difference(pair[1], pair[0]))
            .collect();
        let event_storage: Vec<([Cog; 1], Cog)> = relations
            .iter()
            .copied()
            .map(|relation| ([relation], Cog::lit(137)))
            .collect();
        let event_refs: Vec<(&[Cog], Cog)> = event_storage
            .iter()
            .map(|(relations, action)| (&relations[..], *action))
            .collect();
        let active = one_current(&event_refs);
        let native = run_native(&active);

        let standing = vec![0u32; (AXIS * AXIS) as usize * FORM_WORDS];
        let mut own = vec![0u32; (AXIS * AXIS) as usize * FORM_WORDS];
        let mut carrier = vec![0u32; DEPTH * ENCLOSURE_WORDS];
        let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
        for pair in light.windows(2) {
            body.live_atom(pair[0], pair[1], 137);
        }
        body.flush_dark();
        let mut carried = vec![0u32; carrier_row_words(DEPTH)];
        assert!(body.pack_carried_frame(relations.len() as u64, &mut carried));
        let terms = body.deposited_terms();
        drop(body);
        let historical = (own, carrier, carried, terms);
        assert_eq!(native, historical);
    }

    #[test]
    fn co_present_currents_act_independently_and_join_without_execution_order() {
        let active = two_currents();
        let forward = run_partitions(&active, &[0, 1]);
        let reverse = run_partitions(&active, &[1, 0]);
        assert_eq!(forward, reverse);
        assert_eq!(forward.0.header.currents(), 2);
        assert_ne!(forward.1[0], forward.1[1]);
    }

    #[test]
    fn one_plural_dark_event_consumes_its_action_once() {
        let zeros = [Cog::ZERO, Cog::ZERO, Cog::ZERO, Cog::ZERO];
        let one_zero = [Cog::ZERO];
        let edge = [Cog::lit(65_537).turn_down(2).turned(1)];
        let action = Cog::lit(19).turn_up(1);
        let plural = one_current(&[(&zeros, action), (&edge, Cog::lit(1))]);
        let singular = one_current(&[(&one_zero, action), (&edge, Cog::lit(1))]);
        assert_eq!(
            run_native(&plural),
            run_native(&singular),
            "component count cannot multiply one event's supplied action"
        );
    }

    #[test]
    fn a_non_octet_action_current_changes_the_resolved_construction_whole() {
        let zero = [Cog::ZERO];
        let edge = [Cog::lit(257).turn_down(3).turned(1)];
        let lower = one_current(&[(&zero, Cog::lit(3)), (&edge, Cog::lit(1))]);
        let carried = one_current(&[
            (&zero, Cog::lit(3).turn_up(2).turned(1)),
            (&edge, Cog::lit(1)),
        ]);
        assert_ne!(run_native(&lower), run_native(&carried));
    }

    #[test]
    fn bright_action_crosses_once_without_fabricating_a_flow_term() {
        let mixed = [Cog::ZERO, Cog::lit(257).turn_down(3).turned(1), Cog::ZERO];
        let one = one_current(&[(&mixed, Cog::lit(3))]);
        let another = one_current(&[(&mixed, Cog::lit(3).turn_up(2).turned(1))]);
        assert_ne!(
            one.actions, another.actions,
            "the active cuts retain distinct supplied-current constructions"
        );
        let one_run = run_native(&one);
        let another_run = run_native(&another);
        assert_eq!(
            one_run, another_run,
            "the universal body may not fabricate an action-to-relation map; the exact actions remain distinct in the enacted event surface"
        );
        assert_eq!(
            one_run.3.dark, 0,
            "zero coordinates inside a resolving plural event are not a dark interval"
        );
    }

    #[test]
    fn one_mixed_event_retains_every_coordinate_but_crosses_only_once() {
        let first = Cog::lit(257).turn_down(3).turned(1);
        let second = Cog::lit(65_537).turn_up(2);
        let mixed = [Cog::ZERO, first, Cog::ZERO, second];
        let bright = [first, second];
        let action = Cog::lit(29).turn_up(1);
        let active = one_current(&[(&mixed, action)]);
        let stripped = one_current(&[(&bright, action)]);
        assert_ne!(
            crate::EventTopology::new(&active)
                .unwrap()
                .event(0)
                .unwrap()
                .node(),
            crate::EventTopology::new(&stripped)
                .unwrap()
                .event(0)
                .unwrap()
                .node(),
            "zero coordinates remain positional members of the co-present construction"
        );

        let standing = vec![0u32; (AXIS * AXIS) as usize * FORM_WORDS];
        let mut own = vec![0u32; (AXIS * AXIS) as usize * FORM_WORDS];
        let mut carrier = vec![0u32; DEPTH * ENCLOSURE_WORDS];
        let mut body = ErosBody::over(&standing, &mut own, AXIS, b"  ", 20, &mut carrier);
        let mut contacts = Vec::new();
        let receipt =
            conduct_current(&active, 0, &mut body, |contact| contacts.push(contact)).unwrap();
        assert_eq!(receipt.relation_atoms, 2);
        assert_eq!(contacts.len(), 1, "one event is one body occurrence");
        assert_eq!((contacts[0].atom_offset, contacts[0].atoms), (0, 4));
    }

    #[test]
    fn a_resolving_mixed_event_closes_only_the_preceding_dark_interval() {
        let zero = [Cog::ZERO];
        let mixed = [Cog::ZERO, Cog::lit(17), Cog::ZERO];
        let active = one_current(&[
            (&zero, Cog::lit(3)),
            (&zero, Cog::lit(5)),
            (&mixed, Cog::lit(11)),
        ]);
        let (_, journal, _) = run_native_emitting(&active);
        let closure = journal.deeds[journal.events[2].deed_offset() as usize];
        assert_eq!(closure.kind(), DeedKind::Dark);
        assert_eq!(closure.cause_event_offset(), 0);
        assert_eq!(closure.cause_events(), 2);
    }

    #[test]
    fn every_accepted_deed_has_one_event_sourced_emission_and_replays_the_dense_surface() {
        let relations = [
            Cog::lit(3),
            Cog::lit(-5),
            Cog::lit(8),
            Cog::lit(13),
            Cog::lit(-21),
            Cog::lit(34),
        ];
        let event_storage: Vec<([Cog; 1], Cog)> = relations
            .iter()
            .copied()
            .map(|relation| ([relation], Cog::lit(1)))
            .collect();
        let event_refs: Vec<(&[Cog], Cog)> = event_storage
            .iter()
            .map(|(relations, action)| (&relations[..], *action))
            .collect();
        let active = one_current(&event_refs);
        let (own, journal, terms) = run_native_emitting(&active);

        assert_eq!(journal.deeds.len() as u64, terms.total());
        assert_eq!(journal.events.len(), relations.len());
        assert_eq!(journal.currents.len(), 1);

        let mut replay = vec![RegionalForm::UNBORN; (AXIS * AXIS) as usize];
        for deed in &journal.deeds {
            let grip = place::ground(deed.position(), AXIS) as usize;
            replay[grip] = replay[grip].deposit(deed.term());
        }
        let mut replay_words = vec![0u32; own.len()];
        for (grip, form) in replay.iter().copied().enumerate() {
            form.pack(&mut replay_words, grip * FORM_WORDS);
        }
        assert_eq!(replay_words, own);
    }

    #[test]
    fn a_completed_dark_interval_retains_its_full_cause_without_deeds_per_static_event() {
        let zero = [Cog::ZERO];
        let edge = [Cog::lit(17)];
        let active = one_current(&[
            (&zero, Cog::lit(3)),
            (&zero, Cog::lit(5)),
            (&edge, Cog::lit(7)),
        ]);
        let (_, journal, _) = run_native_emitting(&active);
        assert_eq!(journal.events[0].deeds(), 0);
        assert_eq!(journal.events[1].deeds(), 0);
        assert!(journal.events[2].deeds() >= 1);
        let closure = journal.deeds[journal.events[2].deed_offset() as usize];
        assert_eq!(closure.kind(), DeedKind::Dark);
        assert_eq!(closure.cause_event_offset(), 0);
        assert_eq!(closure.cause_events(), 2);
    }

    #[test]
    fn plural_cut_incidence_does_not_reexecute_or_copy_one_source_event() {
        let edge = [Cog::lit(257).turn_up(1)];
        let single = one_current(&[(&edge, Cog::lit(1))]);
        let plural = ActiveCut::new(
            single.atoms.clone(),
            single.events.clone(),
            single.actions.clone(),
            single.origins.clone(),
            single.currents.clone(),
            vec![CutSpan::new(0, 2, 0, 1).unwrap()],
            vec![
                Incidence::new(0, 0, 1).unwrap(),
                Incidence::new(0, 0, 1).unwrap(),
            ],
            vec![soma_abi::active::DirectedIncidence::new(0, 1)],
        )
        .unwrap();
        let single_run = run_native_emitting(&single);
        let plural_run = run_native_emitting(&plural);
        assert_eq!(single_run.0, plural_run.0);
        assert_eq!(single_run.1.events, plural_run.1.events);
        assert_eq!(single_run.1.deeds, plural_run.1.deeds);
        assert_eq!(single_run.1.currents, plural_run.1.currents);
        assert_eq!(plural.incidences.len(), 2);
        assert_eq!(plural.directed.len(), 1);
    }

    #[test]
    fn one_ordered_emission_sweep_reconstructs_the_production_register_surface() {
        let relations = [
            Cog::lit(3),
            Cog::lit(-5),
            Cog::lit(8),
            Cog::lit(13),
            Cog::lit(-21),
            Cog::lit(34),
            Cog::lit(-55),
            Cog::lit(89),
            Cog::lit(-144),
            Cog::lit(233),
        ];
        let event_storage: Vec<([Cog; 1], Cog)> = relations
            .iter()
            .copied()
            .map(|relation| ([relation], Cog::lit(1)))
            .collect();
        let event_refs: Vec<(&[Cog], Cog)> = event_storage
            .iter()
            .map(|(relations, action)| (&relations[..], *action))
            .collect();
        let active = one_current(&event_refs);

        let standing = vec![0u32; 64 * 64 * FORM_WORDS];
        let mut chart = VecChart::born();
        let mut carrier = vec![0u32; DEPTH * ENCLOSURE_WORDS];
        let mut builder = crate::EmissionJournalBuilder::new(&active);
        let (axis, occupancy, breath, terms) = {
            let mut body =
                ErosBody::over_register(&standing, &mut chart, 64, b"  ", 20, &mut carrier);
            conduct_current_emitting(&active, 0, &mut body, &mut builder, |_| {}).unwrap();
            (
                body.own_axis() as u32,
                body.own_occupancy(),
                body.breath(),
                body.deposited_terms(),
            )
        };
        let journal = builder.finish(&active).unwrap();
        assert_eq!(journal.deeds.len() as u64, terms.total());
        assert!(chart.recasts > 0);

        let mut replay = VecChart::born();
        let replay_face = {
            let mut surface = FeltEmissionSurface::over_register(&mut replay);
            for deed in &journal.deeds {
                assert!(surface.deposit(deed.felt_emission()));
            }
            (surface.axis(), surface.occupancy(), surface.breath())
        };
        assert_eq!(replay.words, chart.words);
        assert_eq!(replay_face, (axis, occupancy, breath));
        assert_eq!(replay.recasts, chart.recasts);
    }
}
