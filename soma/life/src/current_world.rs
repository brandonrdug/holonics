//! Thin world organs for the live-current membrane.
//!
//! These adapters own material chronology and adjacency and nothing inside Soma. A native organ
//! supplies one already-derived current face; its world separately supplies any actual hand among
//! co-present faces. The octet organ retains only the preceding octet needed to derive the next
//! actual adjacency, so arbitrary storage chunks cannot become lineage cuts.

use body::{
    boundary,
    incidence::{
        EventCell, EventCellId, EventComplex, EventPort, IncidenceHand, OrientedIncidence,
    },
};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, ContemporaryRadiation, CurrentBoundaryPort, CurrentEvent, CurrentGeometry,
    CurrentLineage, DirectedCurrentRelation, HostLiveCurrentExecutor, InterfaceCapability,
    LiveCurrentError, LiveCurrentExecutor, LiveCurrentMachine, ReceiverCausalPassage,
    RegionalRelationArc, RegionalRelationCell, RegionalSupportSection,
};

/// Stable native layout for one world organ's capability at a direct-machine rest cut.
pub const NATIVE_RELATION_ORGAN_LAYOUT_VERSION: u32 = 1;
pub const NATIVE_RELATION_ORGAN_WORDS: usize = 5;

const ORGAN_NATIVE_MAGIC: u32 = 0x4552_4f47;
const ORGAN_MAGIC_WORD: usize = 0;
const ORGAN_VERSION_WORD: usize = 1;
const ORGAN_PRESENT_WORD: usize = 2;
const ORGAN_LINEAGE_LO: usize = 3;
const ORGAN_LINEAGE_HI: usize = 4;

/// World-owned rest testimony for one native relation organ. The live carrier remains in
/// `LiveCurrentMachine`; the organ retains only the capability naming which current it continues.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeRelationOrganImage {
    lineage: Option<CurrentLineage>,
}

impl NativeRelationOrganImage {
    pub const fn lineage(self) -> Option<CurrentLineage> {
        self.lineage
    }

    /// Encode only the live lineage capability. No source material, chronology, relation row, or
    /// carrier is duplicated into the organ wire.
    pub fn encode_native_words(self) -> [u32; NATIVE_RELATION_ORGAN_WORDS] {
        let mut words = [0u32; NATIVE_RELATION_ORGAN_WORDS];
        words[ORGAN_MAGIC_WORD] = ORGAN_NATIVE_MAGIC;
        words[ORGAN_VERSION_WORD] = NATIVE_RELATION_ORGAN_LAYOUT_VERSION;
        if let Some(lineage) = self.lineage {
            let ordinal = lineage.ordinal();
            words[ORGAN_PRESENT_WORD] = 1;
            words[ORGAN_LINEAGE_LO] = ordinal as u32;
            words[ORGAN_LINEAGE_HI] = (ordinal >> 32) as u32;
        }
        words
    }

    /// Reopen one organ capability only if the remounted machine still carries that exact live
    /// lineage. A durable ordinal cannot create a replacement capability.
    pub fn from_native_words(
        words: &[u32],
        machine: &LiveCurrentMachine,
    ) -> Result<Self, LiveCurrentError> {
        if words.len() != NATIVE_RELATION_ORGAN_WORDS
            || words[ORGAN_MAGIC_WORD] != ORGAN_NATIVE_MAGIC
            || words[ORGAN_VERSION_WORD] != NATIVE_RELATION_ORGAN_LAYOUT_VERSION
        {
            return Err(LiveCurrentError::InvalidRestWire);
        }
        let lineage = match words[ORGAN_PRESENT_WORD] {
            0 if words[ORGAN_LINEAGE_LO] == 0 && words[ORGAN_LINEAGE_HI] == 0 => None,
            1 => {
                let ordinal =
                    words[ORGAN_LINEAGE_LO] as u64 | ((words[ORGAN_LINEAGE_HI] as u64) << 32);
                Some(
                    machine
                        .resolve_lineage_ordinal(ordinal)
                        .ok_or(LiveCurrentError::InvalidRestWire)?,
                )
            }
            _ => return Err(LiveCurrentError::InvalidRestWire),
        };
        Ok(Self { lineage })
    }

    pub fn encode_native_bytes(self) -> [u8; NATIVE_RELATION_ORGAN_WORDS * 4] {
        let words = self.encode_native_words();
        let mut bytes = [0u8; NATIVE_RELATION_ORGAN_WORDS * 4];
        for (at, word) in words.into_iter().enumerate() {
            bytes[at * 4..at * 4 + 4].copy_from_slice(&word.to_le_bytes());
        }
        bytes
    }

    pub fn from_native_bytes(
        bytes: &[u8],
        machine: &LiveCurrentMachine,
    ) -> Result<Self, LiveCurrentError> {
        if bytes.len() != NATIVE_RELATION_ORGAN_WORDS * 4 {
            return Err(LiveCurrentError::InvalidRestWire);
        }
        let mut words = [0u32; NATIVE_RELATION_ORGAN_WORDS];
        for (at, row) in bytes.chunks_exact(4).enumerate() {
            words[at] = u32::from_le_bytes([row[0], row[1], row[2], row[3]]);
        }
        Self::from_native_words(&words, machine)
    }
}

/// Source-neutral organ capability for one live current.
#[derive(Default)]
pub struct NativeRelationOrgan {
    lineage: Option<CurrentLineage>,
}

impl NativeRelationOrgan {
    pub const fn new() -> Self {
        Self { lineage: None }
    }

    pub const fn lineage(&self) -> Option<CurrentLineage> {
        self.lineage
    }

    /// Found this organ from its source-owned first geometry without enacting a successor.
    ///
    /// Founding is causal ingress and therefore remains separate from an exact world's atomic
    /// successor transaction. Retrying an already-founded organ is an idempotent capability
    /// check; a stale capability cannot silently open a replacement lineage.
    pub fn found<'a>(
        &mut self,
        machine: &mut LiveCurrentMachine,
        first_geometry: impl Into<CurrentGeometry<'a>>,
    ) -> Result<CurrentLineage, LiveCurrentError> {
        if let Some(lineage) = self.lineage {
            if machine.contains(lineage) {
                return Ok(lineage);
            }
            return Err(LiveCurrentError::LineageAbsent(lineage));
        }
        let lineage = machine.attach(first_geometry)?;
        self.lineage = Some(lineage);
        Ok(lineage)
    }

    /// Capture only this world organ's live-current capability. Source material and chronology
    /// remain in the source world; the machine's rest image owns the carrier itself.
    pub const fn checkpoint(&self) -> NativeRelationOrganImage {
        NativeRelationOrganImage {
            lineage: self.lineage,
        }
    }

    /// Rebind one world organ after the direct machine remounts. A stale or ended capability is
    /// refused; recovery never opens a replacement lineage or replays the first event.
    pub fn recover(
        image: NativeRelationOrganImage,
        machine: &LiveCurrentMachine,
    ) -> Result<Self, LiveCurrentError> {
        if let Some(lineage) = image.lineage {
            if !machine.contains(lineage) {
                return Err(LiveCurrentError::LineageAbsent(lineage));
            }
        }
        Ok(Self {
            lineage: image.lineage,
        })
    }

    /// Present one irreducible relation cell as one actual event. A successful terminal event
    /// drops the organ's live capability.
    pub fn present<'a>(
        &mut self,
        machine: &mut LiveCurrentMachine,
        relation: impl Into<CurrentGeometry<'a>>,
        action: ActionCurrent,
        ending: bool,
    ) -> Result<ContemporaryRadiation, LiveCurrentError> {
        let mut host = HostLiveCurrentExecutor;
        self.present_with(machine, &mut host, relation, action, ending)
    }

    /// Present through the machine's actual resident physical executor. The organ still owns the
    /// relation cell and chronology; the executor is only the substrate face of the same atomic
    /// `receive_with` transition.
    pub fn present_with<'a>(
        &mut self,
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
        relation: impl Into<CurrentGeometry<'a>>,
        action: ActionCurrent,
        ending: bool,
    ) -> Result<ContemporaryRadiation, LiveCurrentError> {
        let geometry = relation.into();
        let mut current = if ending {
            NativeEventCurrent::ending_geometry(self, geometry, action)
        } else {
            NativeEventCurrent::continuing_geometry(self, geometry, action)
        };
        present_native_event_with(machine, executor, std::slice::from_mut(&mut current), &[])
    }

    /// Present one source-validated oriented incidence complex as one actual event. Cells and
    /// incidence remain borrowed world material and dissipate when this call returns.
    pub fn present_complex(
        &mut self,
        machine: &mut LiveCurrentMachine,
        complex: EventComplex<'_>,
        action: ActionCurrent,
        ending: bool,
    ) -> Result<ContemporaryRadiation, LiveCurrentError> {
        let mut host = HostLiveCurrentExecutor;
        self.present_complex_with(machine, &mut host, complex, action, ending)
    }

    pub fn present_complex_with(
        &mut self,
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
        complex: EventComplex<'_>,
        action: ActionCurrent,
        ending: bool,
    ) -> Result<ContemporaryRadiation, LiveCurrentError> {
        let mut current = if ending {
            NativeEventCurrent::ending_complex(self, complex, action)
        } else {
            NativeEventCurrent::continuing_complex(self, complex, action)
        };
        present_native_event_with(machine, executor, std::slice::from_mut(&mut current), &[])
    }
}

/// One source-owned current participating in one complete co-present native event. Its cell or
/// oriented complex remains borrowed from the organ's world and disappears after the crossing.
pub struct NativeEventCurrent<'a> {
    organ: &'a mut NativeRelationOrgan,
    geometry: CurrentGeometry<'a>,
    action: ActionCurrent,
    ending: bool,
}

impl<'a> NativeEventCurrent<'a> {
    pub fn continuing(
        organ: &'a mut NativeRelationOrgan,
        geometry: impl Into<CurrentGeometry<'a>>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            organ,
            geometry: geometry.into(),
            action,
            ending: false,
        }
    }

    pub fn continuing_complex(
        organ: &'a mut NativeRelationOrgan,
        complex: EventComplex<'a>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            organ,
            geometry: CurrentGeometry::Complex(complex),
            action,
            ending: false,
        }
    }

    fn continuing_geometry(
        organ: &'a mut NativeRelationOrgan,
        geometry: CurrentGeometry<'a>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            organ,
            geometry,
            action,
            ending: false,
        }
    }

    pub fn ending(
        organ: &'a mut NativeRelationOrgan,
        geometry: impl Into<CurrentGeometry<'a>>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            organ,
            geometry: geometry.into(),
            action,
            ending: true,
        }
    }

    pub fn ending_complex(
        organ: &'a mut NativeRelationOrgan,
        complex: EventComplex<'a>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            organ,
            geometry: CurrentGeometry::Complex(complex),
            action,
            ending: true,
        }
    }

    fn ending_geometry(
        organ: &'a mut NativeRelationOrgan,
        geometry: CurrentGeometry<'a>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            organ,
            geometry,
            action,
            ending: true,
        }
    }
}

/// One world-supplied directed hand between members of the borrowed native event cut. `from` and
/// `to` are event-local incidence addresses only: their numeric order carries no chronology or
/// causal meaning. The source world supplies the row, and the mouth translates it to the named
/// live lineage capabilities before the event crosses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeEventRelation {
    from: usize,
    to: usize,
}

/// One world-owned boundary arc inside a higher native relation cell. Participant indices and port
/// slots are valid only for this borrowed event cut. The world supplies the restriction path;
/// neither the organ nor Soma expands two plural regions into a Cartesian population.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeRegionalArc {
    from: usize,
    from_port: CurrentBoundaryPort,
    to: usize,
    to_port: CurrentBoundaryPort,
    capability: NativeRegionalCapability,
    boundary_slot: u32,
    arc_slot: u32,
    hand: IncidenceHand,
}

/// Source lineage of one borrowed regional interface.
///
/// An inherited capability was already named by the source world. A receiver
/// passage carries only witnessed chronology; the membrane derives its
/// receiver-caused candidate and still requires Swing to close the transported
/// paths. Keeping these variants distinct prevents a world adapter from
/// laundering synchronization into an already-learned interface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeRegionalCapability {
    Inherited(InterfaceCapability),
    ReceiverPassage(ReceiverCausalPassage),
}

impl NativeRegionalCapability {
    pub fn inherited(&self) -> Option<&InterfaceCapability> {
        match self {
            Self::Inherited(interface) => Some(interface),
            Self::ReceiverPassage(_) => None,
        }
    }

    pub fn receiver_passage(&self) -> Option<&ReceiverCausalPassage> {
        match self {
            Self::Inherited(_) => None,
            Self::ReceiverPassage(passage) => Some(passage),
        }
    }

    pub const fn namespace(&self) -> u64 {
        match self {
            Self::Inherited(interface) => interface.namespace(),
            Self::ReceiverPassage(passage) => passage.antecedent().identity(),
        }
    }

    pub const fn local(&self) -> u64 {
        match self {
            Self::Inherited(interface) => interface.local(),
            Self::ReceiverPassage(passage) => passage.consequent().identity(),
        }
    }
}

impl NativeRegionalArc {
    pub const fn new(
        from: usize,
        from_port: CurrentBoundaryPort,
        to: usize,
        to_port: CurrentBoundaryPort,
        interface: InterfaceCapability,
        boundary_slot: u32,
        arc_slot: u32,
        hand: IncidenceHand,
    ) -> Self {
        Self {
            from,
            from_port,
            to,
            to_port,
            capability: NativeRegionalCapability::Inherited(interface),
            boundary_slot,
            arc_slot,
            hand,
        }
    }

    /// Carry one actual receiver chronology through the native world mouth.
    ///
    /// The event-local participant ordinals are addresses only. `passage`
    /// supplies the real ordering and the membrane derives the receiver-caused
    /// candidate after the event has been rebound to live lineage capabilities.
    #[allow(clippy::too_many_arguments)]
    pub const fn from_receiver_passage(
        from: usize,
        from_port: CurrentBoundaryPort,
        to: usize,
        to_port: CurrentBoundaryPort,
        passage: ReceiverCausalPassage,
        boundary_slot: u32,
        arc_slot: u32,
        hand: IncidenceHand,
    ) -> Self {
        Self {
            from,
            from_port,
            to,
            to_port,
            capability: NativeRegionalCapability::ReceiverPassage(passage),
            boundary_slot,
            arc_slot,
            hand,
        }
    }

    pub const fn interface(&self) -> &NativeRegionalCapability {
        &self.capability
    }
}

/// One source-declared regional cell and the one participant whose pre-event illicium receives its
/// composite. The cell is borrowed only through `present_native_event_with_regional`; production
/// executors form its receiver-relative contacts against the same standing-before surface, and the
/// membrane composes the exact returned pins into one live graded-cellular constituent.
#[derive(Clone, Copy)]
pub struct NativeRegionalRelation<'a> {
    receiver: usize,
    arcs: &'a [NativeRegionalArc],
    support_sections: Option<&'a [RegionalSupportSection<'a>]>,
    outgoing_factor_slots: Option<&'a [u32]>,
}

impl<'a> NativeRegionalRelation<'a> {
    pub const fn new(receiver: usize, arcs: &'a [NativeRegionalArc]) -> Self {
        Self {
            receiver,
            arcs,
            support_sections: None,
            outgoing_factor_slots: None,
        }
    }

    pub const fn with_support_sections(
        receiver: usize,
        arcs: &'a [NativeRegionalArc],
        support_sections: &'a [RegionalSupportSection<'a>],
    ) -> Self {
        Self {
            receiver,
            arcs,
            support_sections: Some(support_sections),
            outgoing_factor_slots: None,
        }
    }

    pub const fn with_outgoing_factor(
        receiver: usize,
        arcs: &'a [NativeRegionalArc],
        outgoing_factor_slots: &'a [u32],
    ) -> Self {
        Self {
            receiver,
            arcs,
            support_sections: None,
            outgoing_factor_slots: Some(outgoing_factor_slots),
        }
    }

    pub const fn with_support_and_outgoing_factor(
        receiver: usize,
        arcs: &'a [NativeRegionalArc],
        support_sections: &'a [RegionalSupportSection<'a>],
        outgoing_factor_slots: &'a [u32],
    ) -> Self {
        Self {
            receiver,
            arcs,
            support_sections: Some(support_sections),
            outgoing_factor_slots: Some(outgoing_factor_slots),
        }
    }

    pub const fn receiver(self) -> usize {
        self.receiver
    }

    pub const fn arcs(self) -> &'a [NativeRegionalArc] {
        self.arcs
    }

    pub const fn support_sections(self) -> Option<&'a [RegionalSupportSection<'a>]> {
        self.support_sections
    }

    pub const fn outgoing_factor_slots(self) -> Option<&'a [u32]> {
        self.outgoing_factor_slots
    }
}

/// A world-owned lift for a source which explicitly declares one ordered tuple/path inside one
/// event. Each supplied relation is a vertex; each actual adjacency is a one-cell with its exact
/// oriented boundary. This is not a fallback for arbitrary slices: callers choose it only when
/// their own law says the order is material.
pub struct NativePathChart {
    cells: Vec<EventCell>,
    incidences: Vec<OrientedIncidence>,
    ports: Vec<EventPort>,
}

impl NativePathChart {
    pub fn new(path: &[RelationAtom]) -> Result<Self, LiveCurrentError> {
        if path.is_empty() {
            return Err(LiveCurrentError::EventComplex(
                body::incidence::EventComplexError::Empty,
            ));
        }
        let edges = path.len() - 1;
        let mut cells = Vec::new();
        let mut incidences = Vec::new();
        let mut ports = Vec::new();
        cells
            .try_reserve_exact(
                path.len()
                    .checked_add(edges)
                    .ok_or(LiveCurrentError::ResourceReservation)?,
            )
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        incidences
            .try_reserve_exact(
                edges
                    .checked_mul(2)
                    .ok_or(LiveCurrentError::ResourceReservation)?,
            )
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        ports
            .try_reserve_exact(edges.max(1).saturating_add(1))
            .map_err(|_| LiveCurrentError::ResourceReservation)?;

        for (at, relation) in path.iter().copied().enumerate() {
            let id = u64::try_from(at).map_err(|_| LiveCurrentError::ResourceReservation)?;
            cells.push(EventCell::new(EventCellId::new(id), 0, 0, relation.cog()));
        }
        for at in 0..edges {
            let edge_id = path
                .len()
                .checked_add(at)
                .and_then(|id| u64::try_from(id).ok())
                .ok_or(LiveCurrentError::ResourceReservation)?;
            let edge = EventCellId::new(edge_id);
            cells.push(EventCell::new(
                edge,
                0,
                1,
                path[at + 1].cog().sub(path[at].cog()),
            ));
            incidences.push(OrientedIncidence::boundary(
                EventCellId::new(at as u64),
                edge,
                IncidenceHand::Against,
                0,
            ));
            incidences.push(OrientedIncidence::boundary(
                EventCellId::new((at + 1) as u64),
                edge,
                IncidenceHand::With,
                1,
            ));
            ports.push(EventPort::exposed(
                edge,
                IncidenceHand::With,
                u32::try_from(at).map_err(|_| LiveCurrentError::ResourceReservation)?,
            ));
        }
        ports.push(EventPort::ingress(
            EventCellId::new(0),
            IncidenceHand::With,
            0,
        ));
        if edges == 0 {
            ports.push(EventPort::exposed(
                EventCellId::new(0),
                IncidenceHand::With,
                0,
            ));
        }
        ports.sort_unstable_by_key(|port| {
            let kind = match port.kind() {
                body::incidence::EventPortKind::Ingress => 0u8,
                body::incidence::EventPortKind::Exposed => 1u8,
            };
            (kind, port.slot())
        });
        EventComplex::new(&cells, &incidences, &ports)?;
        Ok(Self {
            cells,
            incidences,
            ports,
        })
    }

    pub fn complex(&self) -> EventComplex<'_> {
        EventComplex::new(&self.cells, &self.incidences, &self.ports)
            .expect("an immutable native path retains its validated incidence")
    }
}

impl NativeEventRelation {
    pub const fn new(from: usize, to: usize) -> Self {
        Self { from, to }
    }

    pub const fn from(self) -> usize {
        self.from
    }

    pub const fn to(self) -> usize {
        self.to
    }
}

/// Present one complete native event whose plural organ currents all read one standing-before
/// body. Caller order survives only as outward correspondence; the machine integrates their
/// enacted contributions as one contemporary successor. Cross-current hand exists only where the
/// source world supplies an explicit [`NativeEventRelation`]; no relation is inferred from caller
/// order or co-presence.
pub fn present_native_event(
    machine: &mut LiveCurrentMachine,
    currents: &mut [NativeEventCurrent<'_>],
    relations: &[NativeEventRelation],
) -> Result<ContemporaryRadiation, LiveCurrentError> {
    let mut host = HostLiveCurrentExecutor;
    present_native_event_with(machine, &mut host, currents, relations)
}

/// The same plural native event through one caller-retained physical executor. Opening a new
/// lineage is organ ingress, not an execution transaction; a failed event leaves that seed bound
/// for an exact retry and cannot close the machine's rest boundary.
pub fn present_native_event_with(
    machine: &mut LiveCurrentMachine,
    executor: &mut dyn LiveCurrentExecutor,
    currents: &mut [NativeEventCurrent<'_>],
    relations: &[NativeEventRelation],
) -> Result<ContemporaryRadiation, LiveCurrentError> {
    present_native_event_with_regional(machine, executor, currents, relations, &[])
}

/// Present one complete native event together with explicit higher regional cells. Flat relations
/// remain available for genuinely atomic hand; a regional cell instead lends exact constituent
/// ports and one receiving lineage. Host and CUDA executors form the same pre-state contacts; the
/// direct machine closes every co-present regional component before its one atomic successor
/// becomes visible.
pub fn present_native_event_with_regional(
    machine: &mut LiveCurrentMachine,
    executor: &mut dyn LiveCurrentExecutor,
    currents: &mut [NativeEventCurrent<'_>],
    relations: &[NativeEventRelation],
    regional: &[NativeRegionalRelation<'_>],
) -> Result<ContemporaryRadiation, LiveCurrentError> {
    for relation in relations {
        if relation.from >= currents.len() {
            return Err(LiveCurrentError::EventMemberAbsent(relation.from));
        }
        if relation.to >= currents.len() {
            return Err(LiveCurrentError::EventMemberAbsent(relation.to));
        }
    }
    for region in regional {
        if region.receiver >= currents.len() {
            return Err(LiveCurrentError::EventMemberAbsent(region.receiver));
        }
        for arc in region.arcs {
            if arc.from >= currents.len() {
                return Err(LiveCurrentError::EventMemberAbsent(arc.from));
            }
            if arc.to >= currents.len() {
                return Err(LiveCurrentError::EventMemberAbsent(arc.to));
            }
        }
    }

    let mut lineages = Vec::new();
    lineages
        .try_reserve_exact(currents.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    for current in currents.iter_mut() {
        let lineage = match current.organ.lineage {
            Some(lineage) => lineage,
            None => {
                let lineage = machine.attach(current.geometry)?;
                current.organ.lineage = Some(lineage);
                lineage
            }
        };
        lineages.push(lineage);
    }

    let mut events = Vec::new();
    events
        .try_reserve_exact(currents.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    for (current, lineage) in currents.iter().zip(lineages) {
        events.push(if current.ending {
            CurrentEvent::ending_geometry(lineage, current.geometry, current.action)
        } else {
            CurrentEvent::continuing_geometry(lineage, current.geometry, current.action)
        });
    }

    let mut directed = Vec::new();
    directed
        .try_reserve_exact(relations.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    for relation in relations {
        directed.push(DirectedCurrentRelation::new(
            events[relation.from].lineage(),
            events[relation.to].lineage(),
        ));
    }

    let mut regional_arcs = Vec::new();
    regional_arcs
        .try_reserve_exact(regional.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    for region in regional {
        let mut arcs = Vec::new();
        arcs.try_reserve_exact(region.arcs.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for arc in region.arcs {
            arcs.push(match &arc.capability {
                NativeRegionalCapability::Inherited(interface) => RegionalRelationArc::new(
                    events[arc.from].lineage(),
                    arc.from_port,
                    events[arc.to].lineage(),
                    arc.to_port,
                    interface.clone(),
                    arc.boundary_slot,
                    arc.arc_slot,
                    arc.hand,
                ),
                NativeRegionalCapability::ReceiverPassage(passage) => {
                    RegionalRelationArc::from_receiver_passage(
                        events[arc.from].lineage(),
                        arc.from_port,
                        events[arc.to].lineage(),
                        arc.to_port,
                        passage.clone(),
                        arc.boundary_slot,
                        arc.arc_slot,
                        arc.hand,
                    )
                }
            });
        }
        regional_arcs.push(arcs);
    }
    let mut regional_cells = Vec::new();
    regional_cells
        .try_reserve_exact(regional.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    for (region, arcs) in regional.iter().zip(&regional_arcs) {
        let receiver = events[region.receiver].lineage();
        regional_cells.push(
            match (region.support_sections, region.outgoing_factor_slots) {
                (Some(sections), Some(factor)) => {
                    RegionalRelationCell::with_support_and_outgoing_factor(
                        receiver, arcs, sections, factor,
                    )
                }
                (Some(sections), None) => {
                    RegionalRelationCell::with_support_sections(receiver, arcs, sections)
                }
                (None, Some(factor)) => {
                    RegionalRelationCell::with_outgoing_factor(receiver, arcs, factor)
                }
                (None, None) => RegionalRelationCell::new(receiver, arcs),
            },
        );
    }

    let radiation = machine.receive_with(
        ContemporaryEvent::with_regional(&events, &directed, &regional_cells),
        executor,
    )?;
    for current in currents.iter_mut() {
        if current.ending {
            current.organ.lineage = None;
        }
    }
    Ok(radiation)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StreamChunkReceipt {
    pub events: u64,
    pub retained_adjacency_octets: usize,
    pub lineage: Option<CurrentLineage>,
}

/// One octet-world illicium.  The source chunk is borrowed and released by the caller; only its
/// final octet remains in the organ to preserve the next genuine adjacency.
#[derive(Default)]
pub struct StreamedOctetOrgan {
    relation: NativeRelationOrgan,
    previous: Option<u8>,
}

impl StreamedOctetOrgan {
    pub const fn new() -> Self {
        Self {
            relation: NativeRelationOrgan::new(),
            previous: None,
        }
    }

    pub const fn lineage(&self) -> Option<CurrentLineage> {
        self.relation.lineage()
    }

    pub const fn retained_adjacency_octets(&self) -> usize {
        if self.previous.is_some() {
            1
        } else {
            0
        }
    }

    /// Cross every actual adjacency in this physical chunk one event at a time.  Radiation is
    /// returned immediately to the world callback, so neither the organ nor Soma accumulates a
    /// chunk-sized result population. `final_chunk` makes the last actual adjacency terminal.
    pub fn present_chunk(
        &mut self,
        machine: &mut LiveCurrentMachine,
        chunk: &[u8],
        action: ActionCurrent,
        final_chunk: bool,
        world: impl FnMut(ContemporaryRadiation),
    ) -> Result<StreamChunkReceipt, LiveCurrentError> {
        let mut host = HostLiveCurrentExecutor;
        self.present_chunk_with(machine, &mut host, chunk, action, final_chunk, world)
    }

    /// Stream through one retained physical executor. Storage chunks remain world-side carriage;
    /// every actual adjacency still crosses as one complete event and emits its successor before
    /// the next adjacency is presented.
    pub fn present_chunk_with(
        &mut self,
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
        chunk: &[u8],
        action: ActionCurrent,
        final_chunk: bool,
        mut world: impl FnMut(ContemporaryRadiation),
    ) -> Result<StreamChunkReceipt, LiveCurrentError> {
        let mut events = 0u64;
        let mut at = 0usize;
        if self.previous.is_none() {
            let Some(first) = chunk.first().copied() else {
                return Ok(StreamChunkReceipt {
                    events,
                    retained_adjacency_octets: 0,
                    lineage: self.lineage(),
                });
            };
            self.previous = Some(first);
            at = 1;
        }

        while at < chunk.len() {
            let previous = self
                .previous
                .expect("the first world octet establishes adjacency");
            let current = chunk[at];
            let relation = RelationAtom::new(boundary::difference(current, previous))
                .expect("an octet difference is one canonical relation atom");
            let ending = final_chunk && at + 1 == chunk.len();
            let radiation = self
                .relation
                .present_with(machine, executor, relation, action, ending)?;
            self.previous = Some(current);
            events = events
                .checked_add(1)
                .ok_or(LiveCurrentError::CursorExtent)?;
            world(radiation);
            at += 1;
        }

        Ok(StreamChunkReceipt {
            events,
            retained_adjacency_octets: self.retained_adjacency_octets(),
            lineage: self.lineage(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::num::Cog;
    use soma_membrane::SparseStandingSurface;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum ProgramLaw {
        Independent,
        LeftWritesRight,
        RightWritesLeft,
        LeftWritesRightTwice,
    }

    struct ProgramEvent {
        left: [RelationAtom; 1],
        right: [RelationAtom; 1],
        relations: Vec<NativeEventRelation>,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct ProgramReturn {
        changes: [Option<RelationAtom>; 2],
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct ProgramWorldImage {
        state: [i64; 2],
        law: ProgramLaw,
    }

    const PROGRAM_WORLD_MAGIC: u32 = 0x5057_524c;
    const PROGRAM_WORLD_VERSION: u32 = 1;
    const PROGRAM_WORLD_IMAGE_BYTES: usize = 28;
    const PROGRAM_REST_MAGIC: u32 = 0x4552_4452;
    const PROGRAM_REST_VERSION: u32 = 1;
    const PROGRAM_REST_HEADER_BYTES: usize = 16;
    const ORGAN_IMAGE_BYTES: usize = NATIVE_RELATION_ORGAN_WORDS * 4;

    impl ProgramWorldImage {
        fn encode_native_bytes(self) -> [u8; PROGRAM_WORLD_IMAGE_BYTES] {
            let mut bytes = [0u8; PROGRAM_WORLD_IMAGE_BYTES];
            bytes[0..4].copy_from_slice(&PROGRAM_WORLD_MAGIC.to_le_bytes());
            bytes[4..8].copy_from_slice(&PROGRAM_WORLD_VERSION.to_le_bytes());
            bytes[8..16].copy_from_slice(&self.state[0].to_le_bytes());
            bytes[16..24].copy_from_slice(&self.state[1].to_le_bytes());
            let law = match self.law {
                ProgramLaw::Independent => 0u32,
                ProgramLaw::LeftWritesRight => 1,
                ProgramLaw::RightWritesLeft => 2,
                ProgramLaw::LeftWritesRightTwice => 3,
            };
            bytes[24..28].copy_from_slice(&law.to_le_bytes());
            bytes
        }

        fn from_native_bytes(bytes: &[u8]) -> Result<Self, LiveCurrentError> {
            if bytes.len() != PROGRAM_WORLD_IMAGE_BYTES
                || u32::from_le_bytes(bytes[0..4].try_into().unwrap()) != PROGRAM_WORLD_MAGIC
                || u32::from_le_bytes(bytes[4..8].try_into().unwrap()) != PROGRAM_WORLD_VERSION
            {
                return Err(LiveCurrentError::InvalidRestWire);
            }
            let law = match u32::from_le_bytes(bytes[24..28].try_into().unwrap()) {
                0 => ProgramLaw::Independent,
                1 => ProgramLaw::LeftWritesRight,
                2 => ProgramLaw::RightWritesLeft,
                3 => ProgramLaw::LeftWritesRightTwice,
                _ => return Err(LiveCurrentError::InvalidRestWire),
            };
            Ok(Self {
                state: [
                    i64::from_le_bytes(bytes[8..16].try_into().unwrap()),
                    i64::from_le_bytes(bytes[16..24].try_into().unwrap()),
                ],
                law,
            })
        }
    }

    /// The bounded program world owns this composition. Soma supplies only its body wire and each
    /// organ supplies only its capability wire; no generic world serializer enters the mouth.
    fn encode_program_rest(
        machine: &soma_membrane::LiveCurrentRestImage,
        left: NativeRelationOrganImage,
        right: NativeRelationOrganImage,
        world: ProgramWorldImage,
    ) -> Result<Vec<u8>, LiveCurrentError> {
        let machine = machine.encode_native_bytes()?;
        let left = left.encode_native_bytes();
        let right = right.encode_native_bytes();
        let world = world.encode_native_bytes();
        let total = PROGRAM_REST_HEADER_BYTES
            .checked_add(machine.len())
            .and_then(|extent| extent.checked_add(left.len()))
            .and_then(|extent| extent.checked_add(right.len()))
            .and_then(|extent| extent.checked_add(world.len()))
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(total)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        bytes.extend_from_slice(&PROGRAM_REST_MAGIC.to_le_bytes());
        bytes.extend_from_slice(&PROGRAM_REST_VERSION.to_le_bytes());
        bytes.extend_from_slice(
            &u64::try_from(machine.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?
                .to_le_bytes(),
        );
        bytes.extend_from_slice(&machine);
        bytes.extend_from_slice(&left);
        bytes.extend_from_slice(&right);
        bytes.extend_from_slice(&world);
        debug_assert_eq!(bytes.len(), total);
        Ok(bytes)
    }

    fn decode_program_rest(
        bytes: &[u8],
    ) -> Result<
        (
            LiveCurrentMachine,
            NativeRelationOrganImage,
            NativeRelationOrganImage,
            ProgramWorldImage,
        ),
        LiveCurrentError,
    > {
        let fixed_tail = ORGAN_IMAGE_BYTES
            .checked_mul(2)
            .and_then(|extent| extent.checked_add(PROGRAM_WORLD_IMAGE_BYTES))
            .ok_or(LiveCurrentError::ResourceReservation)?;
        if bytes.len() < PROGRAM_REST_HEADER_BYTES + fixed_tail
            || u32::from_le_bytes(bytes[0..4].try_into().unwrap()) != PROGRAM_REST_MAGIC
            || u32::from_le_bytes(bytes[4..8].try_into().unwrap()) != PROGRAM_REST_VERSION
        {
            return Err(LiveCurrentError::InvalidRestWire);
        }
        let machine_bytes = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
        let machine_bytes =
            usize::try_from(machine_bytes).map_err(|_| LiveCurrentError::InvalidRestWire)?;
        let machine_end = PROGRAM_REST_HEADER_BYTES
            .checked_add(machine_bytes)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let expected = machine_end
            .checked_add(fixed_tail)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        if expected != bytes.len() {
            return Err(LiveCurrentError::InvalidRestWire);
        }
        let image = soma_membrane::LiveCurrentRestImage::from_native_bytes(
            &bytes[PROGRAM_REST_HEADER_BYTES..machine_end],
        )?;
        let machine = LiveCurrentMachine::from_rest_image(image)?;
        let left_end = machine_end + ORGAN_IMAGE_BYTES;
        let right_end = left_end + ORGAN_IMAGE_BYTES;
        let left =
            NativeRelationOrganImage::from_native_bytes(&bytes[machine_end..left_end], &machine)?;
        let right =
            NativeRelationOrganImage::from_native_bytes(&bytes[left_end..right_end], &machine)?;
        let world = ProgramWorldImage::from_native_bytes(&bytes[right_end..])?;
        Ok((machine, left, right, world))
    }

    /// A bounded material world whose chronology is its changing pair of registers. The exact
    /// same register transition can be enacted under three different program laws; the values do
    /// not let the membrane infer which register caused the other one.
    struct ProgramWorld {
        state: [i64; 2],
        law: ProgramLaw,
        pending: Option<ProgramReturn>,
        received_contacts: usize,
    }

    impl ProgramWorld {
        fn new(state: [i64; 2], law: ProgramLaw) -> Self {
            Self {
                state,
                law,
                pending: None,
                received_contacts: 0,
            }
        }

        fn change(&mut self, next: [i64; 2]) -> ProgramEvent {
            let left = next[0] - self.state[0];
            let right = next[1] - self.state[1];
            self.state = next;
            let relations = match self.law {
                ProgramLaw::Independent => Vec::new(),
                ProgramLaw::LeftWritesRight => vec![NativeEventRelation::new(0, 1)],
                ProgramLaw::RightWritesLeft => vec![NativeEventRelation::new(1, 0)],
                ProgramLaw::LeftWritesRightTwice => vec![
                    NativeEventRelation::new(0, 1),
                    NativeEventRelation::new(0, 1),
                ],
            };
            ProgramEvent {
                left: [relation(left)],
                right: [relation(right)],
                relations,
            }
        }

        fn observe_by(&mut self, difference: [i64; 2]) -> ProgramEvent {
            let next = [
                self.state[0]
                    .checked_add(difference[0])
                    .expect("the bounded program register remains exact"),
                self.state[1]
                    .checked_add(difference[1])
                    .expect("the bounded program register remains exact"),
            ];
            self.state = next;
            ProgramEvent {
                left: [relation(difference[0])],
                right: [relation(difference[1])],
                relations: Vec::new(),
            }
        }

        fn receive(
            &mut self,
            relations: &[NativeEventRelation],
            radiation: &ContemporaryRadiation,
        ) {
            assert!(
                self.pending.is_none(),
                "an actual world return is still open"
            );
            assert_eq!(relations.len(), radiation.relations().len());
            let mut changes = [0i64; 2];
            for (relation, row) in relations.iter().zip(radiation.relations()) {
                self.received_contacts += 1;
                let Some(emission) = row.contact().emission else {
                    continue;
                };
                let change = [emission.term.chi.other, emission.term.chi.same]
                    .into_iter()
                    .find(|arm| arm.mag != 0)
                    .expect("a formed program deed carries a nonzero arm")
                    .face();
                changes[relation.to()] = changes[relation.to()]
                    .checked_add(change)
                    .expect("co-present program deeds remain inside the bounded register");
            }

            let mut returned = [None, None];
            for member in 0..2 {
                if changes[member] != 0 {
                    self.state[member] = self.state[member]
                        .checked_add(changes[member])
                        .expect("the bounded program register remains exact");
                    returned[member] = Some(relation(changes[member]));
                }
            }
            if returned.iter().any(Option::is_some) {
                self.pending = Some(ProgramReturn { changes: returned });
            }
        }

        fn take_return(&mut self) -> Option<ProgramReturn> {
            self.pending.take()
        }

        fn checkpoint(&self) -> Option<ProgramWorldImage> {
            self.pending.is_none().then_some(ProgramWorldImage {
                state: self.state,
                law: self.law,
            })
        }

        fn recover(image: ProgramWorldImage) -> Self {
            Self {
                state: image.state,
                law: image.law,
                pending: None,
                received_contacts: 0,
            }
        }
    }

    fn relation(value: i64) -> RelationAtom {
        RelationAtom::new(Cog::lit(value)).unwrap()
    }

    fn action() -> ActionCurrent {
        ActionCurrent::new(Cog::lit(137)).unwrap()
    }

    fn prime_native_pair() -> (LiveCurrentMachine, NativeRelationOrgan, NativeRelationOrgan) {
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let mut left = NativeRelationOrgan::new();
        let mut right = NativeRelationOrgan::new();
        for value in [13, 29, 17, 31, -63_245, 47] {
            let left_face = [relation(value)];
            let right_face = [relation(value)];
            let mut currents = [
                NativeEventCurrent::continuing(&mut left, &left_face, action()),
                NativeEventCurrent::continuing(&mut right, &right_face, action()),
            ];
            present_native_event(&mut machine, &mut currents, &[]).unwrap();
        }
        let right_ahead = [relation(71)];
        right
            .present(&mut machine, &right_ahead, action(), false)
            .unwrap();
        let left_turn = [relation(71)];
        let right_turn = [relation(-89)];
        let mut currents = [
            NativeEventCurrent::continuing(&mut left, &left_turn, action()),
            NativeEventCurrent::continuing(&mut right, &right_turn, action()),
        ];
        present_native_event(&mut machine, &mut currents, &[]).unwrap();
        (machine, left, right)
    }

    fn enact_program_event(
        machine: &mut LiveCurrentMachine,
        left: &mut NativeRelationOrgan,
        right: &mut NativeRelationOrgan,
        world: &mut ProgramWorld,
    ) -> ContemporaryRadiation {
        let event = world.change([911, -903]);
        let radiation = {
            let mut currents = [
                NativeEventCurrent::continuing(left, &event.left, action()),
                NativeEventCurrent::continuing(right, &event.right, action()),
            ];
            present_native_event(machine, &mut currents, &event.relations).unwrap()
        };
        world.receive(&event.relations, &radiation);
        radiation
    }

    fn return_program_consequence(
        machine: &mut LiveCurrentMachine,
        left: &mut NativeRelationOrgan,
        right: &mut NativeRelationOrgan,
        world: &mut ProgramWorld,
    ) -> ContemporaryRadiation {
        let returned = world
            .take_return()
            .expect("the formed world deed supplies one genuinely later event");
        let radiation = match returned.changes {
            [Some(left_change), Some(right_change)] => {
                let left_face = [left_change];
                let right_face = [right_change];
                let mut currents = [
                    NativeEventCurrent::continuing(left, &left_face, action()),
                    NativeEventCurrent::continuing(right, &right_face, action()),
                ];
                present_native_event(machine, &mut currents, &[]).unwrap()
            }
            [Some(left_change), None] => {
                let left_face = [left_change];
                left.present(machine, &left_face, action(), false).unwrap()
            }
            [None, Some(right_change)] => {
                let right_face = [right_change];
                right
                    .present(machine, &right_face, action(), false)
                    .unwrap()
            }
            [None, None] => unreachable!("an empty world return is natural rest"),
        };
        world.receive(&[], &radiation);
        radiation
    }

    struct BondEvent {
        faces: [[RelationAtom; 1]; 3],
        relations: [NativeEventRelation; 3],
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct BondReturn {
        degree_changes: [Option<RelationAtom>; 3],
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct BondWorldImage {
        bonds: [[bool; 3]; 3],
    }

    /// A materially structured world: emitted directed deeds found actual component joints. Its
    /// later current is the resulting degree change, not an arithmetic write to the target face.
    struct BondWorld {
        bonds: [[bool; 3]; 3],
        pending: Option<BondReturn>,
    }

    impl BondWorld {
        fn new() -> Self {
            Self {
                bonds: [[false; 3]; 3],
                pending: None,
            }
        }

        fn contact(&self) -> BondEvent {
            BondEvent {
                faces: [[relation(-89)], [relation(97)], [relation(97)]],
                relations: [
                    NativeEventRelation::new(0, 1),
                    NativeEventRelation::new(0, 2),
                    NativeEventRelation::new(1, 0),
                ],
            }
        }

        fn receive(
            &mut self,
            relations: &[NativeEventRelation],
            radiation: &ContemporaryRadiation,
        ) -> (usize, usize) {
            assert!(
                self.pending.is_none(),
                "the joint consequence is still open"
            );
            assert_eq!(relations.len(), radiation.relations().len());
            let mut formed = Vec::new();
            let mut open = 0usize;
            for (relation, row) in relations.iter().zip(radiation.relations()) {
                if row.contact().emission.is_some() {
                    formed.push((relation.from(), relation.to()));
                } else {
                    open += 1;
                }
            }

            // Every deed above was read against one world-before. Only now does the structured
            // world compose the complete cut; iteration order cannot expose a partial bond field.
            let mut degree_changes = [0i64; 3];
            for (from, to) in formed.iter().copied() {
                if !self.bonds[from][to] {
                    self.bonds[from][to] = true;
                    self.bonds[to][from] = true;
                    degree_changes[from] += 1;
                    degree_changes[to] += 1;
                }
            }
            if degree_changes.iter().any(|change| *change != 0) {
                self.pending = Some(BondReturn {
                    degree_changes: degree_changes
                        .map(|change| (change != 0).then(|| relation(change))),
                });
            }
            (formed.len(), open)
        }

        fn take_return(&mut self) -> Option<BondReturn> {
            self.pending.take()
        }

        fn checkpoint(&self) -> Option<BondWorldImage> {
            self.pending
                .is_none()
                .then_some(BondWorldImage { bonds: self.bonds })
        }

        fn recover(image: BondWorldImage) -> Self {
            Self {
                bonds: image.bonds,
                pending: None,
            }
        }

        fn probe(&self) -> [[RelationAtom; 1]; 3] {
            let mut degrees = [0i64; 3];
            for (member, row) in self.bonds.iter().enumerate() {
                degrees[member] = row.iter().filter(|joined| **joined).count() as i64;
            }
            [
                [relation(11 + degrees[0])],
                [relation(13 + degrees[1])],
                [relation(17 + degrees[2])],
            ]
        }
    }

    fn prime_native_triple() -> (
        LiveCurrentMachine,
        NativeRelationOrgan,
        NativeRelationOrgan,
        NativeRelationOrgan,
    ) {
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let mut source = NativeRelationOrgan::new();
        let mut target_a = NativeRelationOrgan::new();
        let mut target_b = NativeRelationOrgan::new();
        for value in [13, 29, 17, 31, -63_245, 47] {
            let source_face = [relation(value)];
            let target_a_face = [relation(value)];
            let target_b_face = [relation(value)];
            let mut currents = [
                NativeEventCurrent::continuing(&mut source, &source_face, action()),
                NativeEventCurrent::continuing(&mut target_a, &target_a_face, action()),
                NativeEventCurrent::continuing(&mut target_b, &target_b_face, action()),
            ];
            present_native_event(&mut machine, &mut currents, &[]).unwrap();
        }
        let target_a_ahead = [relation(71)];
        let target_b_ahead = [relation(71)];
        let mut targets = [
            NativeEventCurrent::continuing(&mut target_a, &target_a_ahead, action()),
            NativeEventCurrent::continuing(&mut target_b, &target_b_ahead, action()),
        ];
        present_native_event(&mut machine, &mut targets, &[]).unwrap();
        let source_turn = [relation(71)];
        let target_a_turn = [relation(-89)];
        let target_b_turn = [relation(-89)];
        let mut currents = [
            NativeEventCurrent::continuing(&mut source, &source_turn, action()),
            NativeEventCurrent::continuing(&mut target_a, &target_a_turn, action()),
            NativeEventCurrent::continuing(&mut target_b, &target_b_turn, action()),
        ];
        present_native_event(&mut machine, &mut currents, &[]).unwrap();
        (machine, source, target_a, target_b)
    }

    #[test]
    fn plural_bond_deeds_return_one_later_cut_and_remount_without_a_world_decoder() {
        let (mut machine, mut source, mut target_a, mut target_b) = prime_native_triple();
        let mut world = BondWorld::new();
        let event = world.contact();
        let contact = {
            let mut currents = [
                NativeEventCurrent::continuing(&mut source, &event.faces[0], action()),
                NativeEventCurrent::continuing(&mut target_a, &event.faces[1], action()),
                NativeEventCurrent::continuing(&mut target_b, &event.faces[2], action()),
            ];
            present_native_event(&mut machine, &mut currents, &event.relations).unwrap()
        };
        let (formed, open) = world.receive(&event.relations, &contact);
        assert_eq!((formed, open), (2, 1));
        assert!(world.checkpoint().is_none());
        let before_return = machine.rest_image().unwrap();

        let returned = world
            .take_return()
            .expect("both founded joints return as one later world cut");
        assert_eq!(
            returned
                .degree_changes
                .map(|change| change.unwrap().cog().face()),
            [2, 1, 1]
        );
        let degree_changes = returned.degree_changes.map(Option::unwrap);
        let later = {
            let mut currents = [
                NativeEventCurrent::continuing(&mut source, degree_changes[0], action()),
                NativeEventCurrent::continuing(&mut target_a, degree_changes[1], action()),
                NativeEventCurrent::continuing(&mut target_b, degree_changes[2], action()),
            ];
            present_native_event(&mut machine, &mut currents, &[]).unwrap()
        };
        world.receive(&[], &later);
        assert_eq!(later.currents().len(), 3);
        assert_ne!(machine.rest_image().unwrap(), before_return);
        let world_image = world
            .checkpoint()
            .expect("the complete plural return rests");
        assert!(world_image.bonds[0][1]);
        assert!(world_image.bonds[0][2]);
        assert!(!world_image.bonds[1][2]);

        let machine_image = machine.rest_image().unwrap();
        let source_wire = source.checkpoint().encode_native_bytes();
        let target_a_wire = target_a.checkpoint().encode_native_bytes();
        let target_b_wire = target_b.checkpoint().encode_native_bytes();
        let machine_wire = machine_image.encode_native_bytes().unwrap();
        let reopened_image =
            soma_membrane::LiveCurrentRestImage::from_native_bytes(&machine_wire).unwrap();
        let mut reopened = LiveCurrentMachine::from_rest_image(reopened_image).unwrap();
        let mut reopened_source = NativeRelationOrgan::recover(
            NativeRelationOrganImage::from_native_bytes(&source_wire, &reopened).unwrap(),
            &reopened,
        )
        .unwrap();
        let mut reopened_target_a = NativeRelationOrgan::recover(
            NativeRelationOrganImage::from_native_bytes(&target_a_wire, &reopened).unwrap(),
            &reopened,
        )
        .unwrap();
        let mut reopened_target_b = NativeRelationOrgan::recover(
            NativeRelationOrganImage::from_native_bytes(&target_b_wire, &reopened).unwrap(),
            &reopened,
        )
        .unwrap();
        let reopened_world = BondWorld::recover(world_image);

        let probe = world.probe();
        let reopened_probe = reopened_world.probe();
        assert_eq!(probe, reopened_probe);
        let uninterrupted = {
            let mut currents = [
                NativeEventCurrent::continuing(&mut source, &probe[0], action()),
                NativeEventCurrent::continuing(&mut target_a, &probe[1], action()),
                NativeEventCurrent::continuing(&mut target_b, &probe[2], action()),
            ];
            present_native_event(&mut machine, &mut currents, &[]).unwrap()
        };
        let after_reopen = {
            let mut currents = [
                NativeEventCurrent::continuing(&mut reopened_source, &reopened_probe[0], action()),
                NativeEventCurrent::continuing(
                    &mut reopened_target_a,
                    &reopened_probe[1],
                    action(),
                ),
                NativeEventCurrent::continuing(
                    &mut reopened_target_b,
                    &reopened_probe[2],
                    action(),
                ),
            ];
            present_native_event(&mut reopened, &mut currents, &[]).unwrap()
        };
        assert_eq!(uninterrupted, after_reopen);
        assert_eq!(
            machine.rest_image().unwrap(),
            reopened.rest_image().unwrap()
        );
    }

    #[test]
    fn program_world_supplies_hand_and_receives_its_consequence() {
        let (baseline, left, right) = prime_native_pair();
        let rest = baseline.rest_image().unwrap();
        let left_image = left.checkpoint();
        let right_image = right.checkpoint();

        let mut forward = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
        let mut forward_left = NativeRelationOrgan::recover(left_image, &forward).unwrap();
        let mut forward_right = NativeRelationOrgan::recover(right_image, &forward).unwrap();
        let mut forward_world = ProgramWorld::new([1_000, -1_000], ProgramLaw::LeftWritesRight);
        let forward_return = enact_program_event(
            &mut forward,
            &mut forward_left,
            &mut forward_right,
            &mut forward_world,
        );
        let forward_before_world_return = forward.rest_image().unwrap();

        let mut reverse = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
        let mut reverse_left = NativeRelationOrgan::recover(left_image, &reverse).unwrap();
        let mut reverse_right = NativeRelationOrgan::recover(right_image, &reverse).unwrap();
        let mut reverse_world = ProgramWorld::new([1_000, -1_000], ProgramLaw::RightWritesLeft);
        let reverse_return = enact_program_event(
            &mut reverse,
            &mut reverse_left,
            &mut reverse_right,
            &mut reverse_world,
        );

        let mut independent = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
        let mut independent_left = NativeRelationOrgan::recover(left_image, &independent).unwrap();
        let mut independent_right =
            NativeRelationOrgan::recover(right_image, &independent).unwrap();
        let mut independent_world = ProgramWorld::new([1_000, -1_000], ProgramLaw::Independent);
        let independent_return = enact_program_event(
            &mut independent,
            &mut independent_left,
            &mut independent_right,
            &mut independent_world,
        );

        let mut repeated = LiveCurrentMachine::from_rest_image(rest).unwrap();
        let mut repeated_left = NativeRelationOrgan::recover(left_image, &repeated).unwrap();
        let mut repeated_right = NativeRelationOrgan::recover(right_image, &repeated).unwrap();
        let mut repeated_world =
            ProgramWorld::new([1_000, -1_000], ProgramLaw::LeftWritesRightTwice);
        let repeated_return = enact_program_event(
            &mut repeated,
            &mut repeated_left,
            &mut repeated_right,
            &mut repeated_world,
        );

        assert_eq!(forward_return.currents(), reverse_return.currents());
        assert_eq!(forward_return.currents(), independent_return.currents());
        assert_eq!(forward_return.relations().len(), 1);
        assert_eq!(reverse_return.relations().len(), 1);
        assert!(independent_return.relations().is_empty());
        assert_eq!(repeated_return.relations().len(), 2);
        assert_eq!(
            repeated_return.relations()[0],
            repeated_return.relations()[1]
        );
        assert_ne!(
            forward_return.relations()[0].contact(),
            reverse_return.relations()[0].contact()
        );
        assert_ne!(forward.standing(), reverse.standing());
        assert_ne!(forward.standing(), independent.standing());
        assert!(forward_return.relations()[0].contact().emission.is_some());
        assert!(reverse_return.relations()[0].contact().emission.is_none());
        assert!(forward_world.pending.is_some());
        assert!(forward_world.checkpoint().is_none());
        assert!(reverse_world.pending.is_none());
        assert!(independent_world.pending.is_none());

        // The material world enacts its formed directed deed once. The resulting register change
        // returns through its addressed organ as genuinely later current; ordinary current
        // radiation affords no further register action, so the world reaches natural rest.
        let returned_radiation = return_program_consequence(
            &mut forward,
            &mut forward_left,
            &mut forward_right,
            &mut forward_world,
        );
        assert_eq!(returned_radiation.currents().len(), 1);
        assert!(returned_radiation.relations().is_empty());
        assert!(forward_world.pending.is_none());
        assert_ne!(forward.rest_image().unwrap(), forward_before_world_return);

        let forward_machine_image = forward.rest_image().unwrap();
        let forward_left_image = forward_left.checkpoint();
        let forward_right_image = forward_right.checkpoint();
        let forward_world_image = forward_world
            .checkpoint()
            .expect("no actual program event remains unreturned");

        // Waiting at joint rest is not an event and changes none of the three owners.
        assert!(forward_world.take_return().is_none());
        assert_eq!(forward.rest_image().unwrap(), forward_machine_image);
        assert_eq!(forward_left.checkpoint(), forward_left_image);
        assert_eq!(forward_right.checkpoint(), forward_right_image);
        assert_eq!(forward_world.checkpoint().unwrap(), forward_world_image);

        // The program world composes its own outer rest cut and carries it through an actual file.
        // Machine and organ wires remain typed constituents; the file is not replay light.
        let durable = encode_program_rest(
            &forward_machine_image,
            forward_left_image,
            forward_right_image,
            forward_world_image,
        )
        .unwrap();
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "eros-direct-program-rest-{}-{nonce}.bin",
            std::process::id()
        ));
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .unwrap();
        std::io::Write::write_all(&mut file, &durable).unwrap();
        file.sync_all().unwrap();
        drop(file);
        let reopened = std::fs::read(&path).unwrap();
        std::fs::remove_file(&path).unwrap();
        assert_eq!(reopened, durable);
        let (mut remounted, remounted_left_image, remounted_right_image, remounted_world_image) =
            decode_program_rest(&reopened).unwrap();
        assert_eq!(remounted.rest_image().unwrap(), forward_machine_image);
        let mut remounted_left =
            NativeRelationOrgan::recover(remounted_left_image, &remounted).unwrap();
        let mut remounted_right =
            NativeRelationOrgan::recover(remounted_right_image, &remounted).unwrap();
        let mut remounted_world = ProgramWorld::recover(remounted_world_image);

        let uninterrupted_probe = forward_world.observe_by([-253, 257]);
        let remounted_probe = remounted_world.observe_by([-253, 257]);
        assert_eq!(uninterrupted_probe.left, remounted_probe.left);
        assert_eq!(uninterrupted_probe.right, remounted_probe.right);
        let uninterrupted_radiation = {
            let mut currents = [
                NativeEventCurrent::continuing(
                    &mut forward_left,
                    &uninterrupted_probe.left,
                    action(),
                ),
                NativeEventCurrent::continuing(
                    &mut forward_right,
                    &uninterrupted_probe.right,
                    action(),
                ),
            ];
            present_native_event(&mut forward, &mut currents, &[]).unwrap()
        };
        forward_world.receive(&[], &uninterrupted_radiation);
        let remounted_radiation = {
            let mut currents = [
                NativeEventCurrent::continuing(
                    &mut remounted_left,
                    &remounted_probe.left,
                    action(),
                ),
                NativeEventCurrent::continuing(
                    &mut remounted_right,
                    &remounted_probe.right,
                    action(),
                ),
            ];
            present_native_event(&mut remounted, &mut currents, &[]).unwrap()
        };
        remounted_world.receive(&[], &remounted_radiation);

        assert_eq!(uninterrupted_radiation, remounted_radiation);
        assert_eq!(
            forward.rest_image().unwrap(),
            remounted.rest_image().unwrap()
        );
        assert_eq!(forward_world.checkpoint(), remounted_world.checkpoint());
    }

    #[test]
    fn storage_chunks_do_not_cut_the_octet_lineage_or_retain_the_source() {
        let material = b"the lineage is the live current; storage chunks are not events";
        let mut whole = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let mut whole_organ = StreamedOctetOrgan::new();
        let mut whole_rows = Vec::new();
        whole_organ
            .present_chunk(&mut whole, material, action(), false, |row| {
                whole_rows.push(row)
            })
            .unwrap();

        let mut chunked = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let mut chunked_organ = StreamedOctetOrgan::new();
        let mut chunked_rows = Vec::new();
        for chunk in [
            &material[..1],
            &material[1..7],
            &material[7..19],
            &material[19..],
        ] {
            chunked_organ
                .present_chunk(&mut chunked, chunk, action(), false, |row| {
                    chunked_rows.push(row)
                })
                .unwrap();
        }

        assert_eq!(whole_rows, chunked_rows);
        assert_eq!(whole.standing(), chunked.standing());
        assert_eq!(whole.memory(), chunked.memory());
        let whole_lineage = whole_organ.lineage().unwrap();
        let chunked_lineage = chunked_organ.lineage().unwrap();
        assert_eq!(
            whole.lineage_cursor(whole_lineage),
            chunked.lineage_cursor(chunked_lineage)
        );
        assert_eq!(
            whole.lineage_channel(whole_lineage),
            chunked.lineage_channel(chunked_lineage)
        );
        assert_eq!(
            whole.lineage_carrier(whole_lineage).unwrap().header(),
            chunked.lineage_carrier(chunked_lineage).unwrap().header()
        );
        assert_eq!(
            whole.lineage_carrier(whole_lineage).unwrap().carrier(),
            chunked.lineage_carrier(chunked_lineage).unwrap().carrier()
        );
        assert_eq!(chunked_organ.retained_adjacency_octets(), 1);
    }

    #[test]
    fn mathematical_and_streamed_organs_cross_one_machine_mouth() {
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let mut mathematics = NativeRelationOrgan::new();
        let theorem_event = [
            RelationAtom::new(Cog::lit(2)).unwrap(),
            RelationAtom::new(Cog::lit(3)).unwrap(),
            RelationAtom::new(Cog::lit(5)).unwrap(),
        ];
        let theorem_chart = NativePathChart::new(&theorem_event).unwrap();
        let mathematical = mathematics
            .present_complex(&mut machine, theorem_chart.complex(), action(), false)
            .unwrap();

        let mut material = StreamedOctetOrgan::new();
        let mut streamed = Vec::new();
        material
            .present_chunk(&mut machine, b"eros", action(), false, |row| {
                streamed.push(row)
            })
            .unwrap();

        assert_eq!(mathematical.currents().len(), 1);
        assert_eq!(streamed.len(), 3);
        assert_eq!(machine.memory().live_lineages, 2);
        assert!(mathematics.lineage().is_some());
        assert!(material.lineage().is_some());
    }

    #[test]
    fn a_path_charts_open_interior_does_not_masquerade_as_a_regional_arm() {
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let mut context = NativeRelationOrgan::new();
        let mut arrival = NativeRelationOrgan::new();
        let context_atoms = [relation(b'o' as i64), relation(b'n' as i64)];
        let context_chart = NativePathChart::new(&context_atoms).unwrap();
        let arrival_atom = [relation(b'e' as i64)];
        let arcs = [NativeRegionalArc::new(
            0,
            CurrentBoundaryPort::Exposed(0),
            1,
            CurrentBoundaryPort::Cell,
            InterfaceCapability::new(0x4355_5252, 0),
            0,
            0,
            IncidenceHand::Against,
        )];
        let regional = [NativeRegionalRelation::new(1, &arcs)];
        let mut currents = [
            NativeEventCurrent::continuing_complex(&mut context, context_chart.complex(), action()),
            NativeEventCurrent::continuing(&mut arrival, &arrival_atom, action()),
        ];
        let mut host = HostLiveCurrentExecutor;
        let radiation = present_native_event_with_regional(
            &mut machine,
            &mut host,
            &mut currents,
            &[],
            &regional,
        )
        .unwrap();
        let constituent = radiation.regional()[0].constituent();

        assert_eq!(constituent.pins().len(), 3);
        assert_eq!(constituent.exposed().len(), 1);
        assert!(machine.rest_image().is_ok());
    }

    fn returned_relation(radiation: &ContemporaryRadiation) -> Option<RelationAtom> {
        radiation
            .currents()
            .iter()
            .flat_map(|current| current.emissions())
            .find_map(|emission| {
                RelationAtom::new(emission.term.chi.other)
                    .or_else(|| RelationAtom::new(emission.term.chi.same))
            })
    }

    #[test]
    fn plural_native_organs_rebind_and_return_actual_world_consequence() {
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let mut mathematics = NativeRelationOrgan::new();
        let mut vision = NativeRelationOrgan::new();
        let mut world_return = None;

        for (left, right) in [
            (13, -43),
            (29, 59),
            (17, -61),
            (31, 67),
            (-63_245, 73),
            (47, -79),
            (71, 83),
            (-89, 97),
        ] {
            let mathematical = [relation(left)];
            let visual = [relation(right)];
            let radiation = {
                let mut currents = [
                    NativeEventCurrent::continuing(&mut mathematics, &mathematical, action()),
                    NativeEventCurrent::continuing(&mut vision, &visual, action()),
                ];
                present_native_event(&mut machine, &mut currents, &[]).unwrap()
            };
            assert_eq!(radiation.currents().len(), 2);
            world_return = world_return.or_else(|| returned_relation(&radiation));
        }
        let world_return = world_return.expect("the enacted world receives an oriented emission");

        let machine_image = machine.rest_image().unwrap();
        let mathematics_image = mathematics.checkpoint();
        let vision_image = vision.checkpoint();
        assert_eq!(machine_image.lineages().len(), 2);

        let mut direct = LiveCurrentMachine::from_rest_image(machine_image.clone()).unwrap();
        let mut direct_mathematics =
            NativeRelationOrgan::recover(mathematics_image, &direct).unwrap();
        let mut direct_vision = NativeRelationOrgan::recover(vision_image, &direct).unwrap();

        let mut returned = LiveCurrentMachine::from_rest_image(machine_image).unwrap();
        let mut returned_mathematics =
            NativeRelationOrgan::recover(mathematics_image, &returned).unwrap();
        let mut returned_vision = NativeRelationOrgan::recover(vision_image, &returned).unwrap();

        // This declared world's material law returns an actual emitted chi arm through both
        // source-neutral organs. It is ordinary later light, not a receipt replay or universal
        // radiation decoder.
        let consequence = [world_return];
        {
            let mut currents = [
                NativeEventCurrent::continuing(&mut returned_mathematics, &consequence, action()),
                NativeEventCurrent::continuing(&mut returned_vision, &consequence, action()),
            ];
            present_native_event(&mut returned, &mut currents, &[]).unwrap();
        }

        let mathematical_probe = [relation(-253)];
        let visual_probe = [relation(257)];
        let direct_probe = {
            let mut currents = [
                NativeEventCurrent::continuing(
                    &mut direct_mathematics,
                    &mathematical_probe,
                    action(),
                ),
                NativeEventCurrent::continuing(&mut direct_vision, &visual_probe, action()),
            ];
            present_native_event(&mut direct, &mut currents, &[]).unwrap()
        };
        let returned_probe = {
            let mut currents = [
                NativeEventCurrent::continuing(
                    &mut returned_mathematics,
                    &mathematical_probe,
                    action(),
                ),
                NativeEventCurrent::continuing(&mut returned_vision, &visual_probe, action()),
            ];
            present_native_event(&mut returned, &mut currents, &[]).unwrap()
        };

        assert_ne!(direct_probe, returned_probe);
        assert_ne!(direct.rest_image().unwrap(), returned.rest_image().unwrap());
        assert_eq!(direct_probe.currents().len(), 2);
        assert_eq!(returned_probe.currents().len(), 2);
    }
}
