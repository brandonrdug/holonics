//! The live-current membrane: one contemporary event in, one bounded radiation population out.
//!
//! This is the production lifetime owner of [`body::manifold::ErosBody`].  World material and
//! hardware chunks remain outside.  A live lineage retains only its first-person body header,
//! dynamic carrier, and a genuinely open dark tread.  Every current-local OWN surface lives for
//! one complete event, every co-present current reads the same standing-before body, and their
//! completed surfaces integrate only after all of them have crossed.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use body::channel::LineageChannel;

/// WHERE THE POLE STANDS RELATIVE TO THE PAIR IT RELATES. `arrow::relate` reads `a, b` from the
/// pole `f = receiver.channel.frame().tip()`, and `at_horizon` (both faces null) holds exactly when
/// `f` coincides with `a` or with `b` — a two-body contact wearing three-body arithmetic. These
/// separate the three ways that can happen, so the producer is measured rather than inferred.
///
/// `SWEEP_IDLE` is the one that names a cause: `LivingFrame::tip` returns the **anchor** whenever
/// `sweep == place::origin()`, so a lineage channel that has never swept reads every relating from
/// its own starting place.
pub(crate) static POLE_SWEEP_IDLE: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static POLE_ON_FROM: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static POLE_ON_TO: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static POLE_DISTINCT: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static RELATA_COINCIDE: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);

/// THE STANDING LATTICE. `LivingFrame::basis` is the perspective's own interaction term — the lens
/// that is invariant across an instant. Genesis sets it to `FormedRotor::identity()`, and it
/// advances in the same fold as the sweep. Counting it separates two different diagnoses that look
/// identical from outside: free propagation through a *static lattice* against free propagation
/// through *no lattice at all*.
pub(crate) static BASIS_IDENTITY: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);

/// THE DISTINGUISHABLE POPULATION. Every distinct `Place` ever handed to a relating, as a set. An
/// upper bound on the block count of any receiver family's partition of the material, so a small
/// number here bounds how many irreducible axes the body could ever found.
pub(crate) static DISTINCT_PLACES: std::sync::OnceLock<
    std::sync::Mutex<std::collections::BTreeSet<(u32, u32, i32, bool, u32)>>,
> = std::sync::OnceLock::new();

type Word = (u32, u32, i32, bool, u32);
type PlaceKey = (Word, Word);

/// THE VALENCE CENSUS. The distinct places, the distinct `(from, to, pole)` triples, and the
/// triangle classification of every contact. A contact is a *triangle* only when its three places
/// are pairwise distinct, and it has *area* only when `cross != 0` — and `|cross| = 2·Area(f,a,b)`,
/// so the area population is exactly the population that can deposit a founding.
pub(crate) static CENSUS_PLACES: std::sync::OnceLock<
    std::sync::Mutex<std::collections::BTreeSet<PlaceKey>>,
> = std::sync::OnceLock::new();
pub(crate) static CENSUS_TRIPLES: std::sync::OnceLock<
    std::sync::Mutex<std::collections::BTreeSet<(PlaceKey, PlaceKey, PlaceKey)>>,
> = std::sync::OnceLock::new();
/// three pairwise-distinct places
pub(crate) static TRIANGLE: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
/// a triangle whose `cross` is non-zero — non-collinear, with area
pub(crate) static TRIANGLE_WITH_AREA: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
/// a triangle that is collinear — `cross == 0` with `aim != 0`: a lawful RIDE, never a FOUND
pub(crate) static TRIANGLE_COLLINEAR: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
/// the arrow the producer would form, entirely null
pub(crate) static ARROW_AT_HORIZON: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
/// of the area population, how many pass the founding band `cross² >= aim²`
pub(crate) static WOULD_FOUND: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);

/// THE REFUSAL FIBER of the emission, read from the returned contact rather than inferred. Every
/// counter is conditioned on the meeting ALREADY having area and passing the founding band, so this
/// is predicted-versus-happened at the one boundary where a founding could have been deposited.
pub(crate) static ARMED: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
/// THE FOURTH BODY, over EVERY contact rather than only the armed ones. `soul.rs` states the law:
/// the three-body triangle is frame-local and is not yet a soul; the held flywheel supplies the
/// fourth contact, and the rotor of those two rotors is the first invariant content which may
/// cross. If this is zero across a whole run, the body never formed an invariant at all.
pub(crate) static HELD_LIVE_ANY: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static ARMED_HELD_NOT_LIVE: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static ARMED_NO_EMISSION: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static ARMED_RIDE: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static ARMED_FOUND: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);

/// EXPERIMENT B-PRIME — THE FLYWHEEL SUPPLIED. `perceive_grain` sets `e.fly = met` on the
/// continuing thought, so the flywheel IS the previously formed meeting; holding the previous armed
/// meeting is the mechanism's own assignment rather than an authored value. With that held face
/// supplied, ask the two questions the producer would ask: does `chi_against` return an invariant,
/// and does it wind? This decides whether the missing fourth body would yield RIDES or FOUNDINGS,
/// which are materially different outcomes. Nothing here reaches conduct.
pub(crate) static BPRIME_HELD_SUPPLIED: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static BPRIME_CHI_FORMS: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static BPRIME_CHI_NONE: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static BPRIME_WOUND: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static BPRIME_FLAT: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
static BPRIME_PREVIOUS: std::sync::Mutex<Option<body::manifold::Face>> =
    std::sync::Mutex::new(None);

#[inline]
fn observe_supplied_flywheel(meeting: body::manifold::Face) {
    use core::sync::atomic::Ordering::Relaxed;
    let Ok(mut previous) = BPRIME_PREVIOUS.lock() else {
        return;
    };
    if let Some(held) = *previous {
        BPRIME_HELD_SUPPLIED.fetch_add(1, Relaxed);
        match meeting.chi_against(&held) {
            None => {
                BPRIME_CHI_NONE.fetch_add(1, Relaxed);
            }
            Some(_) => {
                BPRIME_CHI_FORMS.fetch_add(1, Relaxed);
                if meeting.wound_against(&held) {
                    BPRIME_WOUND.fetch_add(1, Relaxed);
                } else {
                    BPRIME_FLAT.fetch_add(1, Relaxed);
                }
            }
        }
    }
    *previous = Some(meeting);
}

/// Read what the producer actually returned for a contact whose meeting was founding-capable.
#[inline]
pub(crate) fn observe_contact_outcome(contact: &body::manifold::DirectedEventContact) {
    use core::sync::atomic::Ordering::Relaxed;
    let arrow = contact.meeting.arrow;
    if arrow.cross.mag == 0 || !arrow.founds() {
        return;
    }
    ARMED.fetch_add(1, Relaxed);
    observe_supplied_flywheel(contact.meeting);
    if !contact.receiver.held_live {
        ARMED_HELD_NOT_LIVE.fetch_add(1, Relaxed);
    }
    match contact.emission {
        None => ARMED_NO_EMISSION.fetch_add(1, Relaxed),
        Some(emission) => match emission.deed {
            body::manifold::FeltDeed::Ride => ARMED_RIDE.fetch_add(1, Relaxed),
            _ => ARMED_FOUND.fetch_add(1, Relaxed),
        },
    };
}

#[inline]
fn word_of(c: body::num::Cog) -> Word {
    (c.mag, c.rank.mag, c.rank.rank, c.rank.neg, c.turn)
}

#[inline]
fn place_key(p: Place) -> [Word; 2] {
    [word_of(p.0), word_of(p.1)]
}

#[inline]
fn key_of(p: Place) -> PlaceKey {
    (word_of(p.0), word_of(p.1))
}

/// ★ REVISION 0 — THE GATE MEASUREMENT. Does the stance founder write at the depth the directed
/// contacts read?
///
/// The contacts read `enclosure(source_grain − 1)` and run at `:3546-3590`; the founder writes
/// through `perceive_grain` and runs at `:3607-3637`, both inside `enact_cpu_current`. The
/// Cell-branch founder calls `perceive_grain(0, …)` (`manifold.rs:5125`) — **depth 0** — while
/// `thicken_branch` calls `perceive_grain(k, …)` at a growing depth (`:5183`). So the two agree
/// exactly when `source_grain == 1` and not otherwise, and reasoning is not enough to say which.
///
/// These read `held_live` at the SAME depth twice: once as the contacts saw it, and once after the
/// founder has run. The pair decides between two very different repairs.
///
/// ```text
///   before false, after TRUE    the founder writes where the contact reads — it is an ORDERING
///   before false, after false   the founder writes elsewhere — it is the DEPTH MAP
/// ```
pub(crate) static GRAIN_ONE: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static GRAIN_DEEPER: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static HELD_LIVE_AFTER_FOUNDER: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static HELD_DEAD_AFTER_FOUNDER: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);

/// Does the founder run at all, and does it fold? The whole `else` arm at `:3654` is gated on
/// `request.wholly_dark`, so a wholly-dark event skips the founder entirely.
pub(crate) static EVENT_WHOLLY_DARK: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static FOUNDER_CELL: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static FOUNDER_COMPLEX: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static FOUNDER_FOLDED: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
/// Did the LINEAGE CHANNEL move across the founder, in the same event? `AtomEvent.fold` is a
/// completed node handing up, NOT the channel fold — `fold_channel` runs separately at
/// `manifold.rs:5736`. Reading the frame either side of the founder is the only direct answer.
pub(crate) static CHANNEL_MOVED: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static CHANNEL_STILL: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);

/// Read the depth the contacts will use, before they run.
#[inline]
pub(crate) fn observe_read_depth(source_grain: u32) {
    use core::sync::atomic::Ordering::Relaxed;
    if source_grain == 1 {
        GRAIN_ONE.fetch_add(1, Relaxed);
    } else {
        GRAIN_DEEPER.fetch_add(1, Relaxed);
    }
}

/// Read `held_live` at the contacts' own depth AFTER the founder has run in the same event.
#[inline]
pub(crate) fn observe_after_founder(receiver: &body::manifold::EventReceiver) {
    use core::sync::atomic::Ordering::Relaxed;
    if receiver.held_live {
        HELD_LIVE_AFTER_FOUNDER.fetch_add(1, Relaxed);
    } else {
        HELD_DEAD_AFTER_FOUNDER.fetch_add(1, Relaxed);
    }
}

/// Read the pole's placement against the pair, once per formed contact. No verdict, no threshold —
/// four disjoint tallies and one overlapping one, exactly as `ArrivalResponse` reports.
#[inline]
pub(crate) fn observe_pole_placement(receiver: &body::manifold::EventReceiver, from: Place, to: Place) {
    use core::sync::atomic::Ordering::Relaxed;
    let frame = receiver.channel.frame();
    if frame.sweep == body::place::origin() {
        POLE_SWEEP_IDLE.fetch_add(1, Relaxed);
    }
    if frame.basis == body::soul::FormedRotor::identity() {
        BASIS_IDENTITY.fetch_add(1, Relaxed);
    }
    if receiver.held_live {
        HELD_LIVE_ANY.fetch_add(1, Relaxed);
    }
    let pole = frame.tip();
    if let Ok(mut set) = DISTINCT_PLACES
        .get_or_init(|| std::sync::Mutex::new(std::collections::BTreeSet::new()))
        .lock()
    {
        for p in [from, to, pole] {
            for word in place_key(p) {
                set.insert(word);
            }
        }
    }
    // THE VALENCE CENSUS. Population first, classification second — no verdict is formed here and
    // nothing read here reaches conduct.
    let (kf, kt, kp) = (key_of(from), key_of(to), key_of(pole));
    if let Ok(mut set) = CENSUS_PLACES
        .get_or_init(|| std::sync::Mutex::new(std::collections::BTreeSet::new()))
        .lock()
    {
        set.insert(kf);
        set.insert(kt);
        set.insert(kp);
    }
    if let Ok(mut set) = CENSUS_TRIPLES
        .get_or_init(|| std::sync::Mutex::new(std::collections::BTreeSet::new()))
        .lock()
    {
        set.insert((kf, kt, kp));
    }
    // The producer's own argument order, so this reads the arrow that will actually be formed.
    let arrow = body::manifold::face(to, from, pole).arrow;
    if arrow.aim.mag == 0 && arrow.cross.mag == 0 {
        ARROW_AT_HORIZON.fetch_add(1, Relaxed);
    }
    if kf != kt && kf != kp && kt != kp {
        TRIANGLE.fetch_add(1, Relaxed);
        if arrow.cross.mag == 0 {
            TRIANGLE_COLLINEAR.fetch_add(1, Relaxed);
        } else {
            TRIANGLE_WITH_AREA.fetch_add(1, Relaxed);
            if arrow.founds() {
                WOULD_FOUND.fetch_add(1, Relaxed);
            }
        }
    }
    let pole = frame.tip();
    if from == to {
        RELATA_COINCIDE.fetch_add(1, Relaxed);
    }
    match (pole == from, pole == to) {
        (true, _) => POLE_ON_FROM.fetch_add(1, Relaxed),
        (false, true) => POLE_ON_TO.fetch_add(1, Relaxed),
        (false, false) => POLE_DISTINCT.fetch_add(1, Relaxed),
    };
}
use body::incidence::{
    EventCellId, EventComplex, EventComplexError, EventPortKind, IncidenceHand, IncidenceKind,
    OrientedIncidence,
};
use body::manifold::{
    atom_node, compose_place, node_packed_word, DirectedEventContact, Enclosure, ErosBody,
    EventEmanation, EventReceiver, FeltEmission, FeltEmissionTarget, LiveBodyHeader, Node,
    ENCLOSURE_WORDS, NODE_WORDS,
};
use body::medium::{RegionalForm, COMPACT_FORM_LAYOUT_VERSION, COMPACT_FORM_WORDS};
use body::num::{cog_packed_word, packed_cog_is_canonical, read_cog, Cog, COG_WORDS};
use body::place::Place;
use holonic_structure::{CausalMembrane, OrdinalAtlasError, SparseOrdinalAtlas};
use soma_abi::active::{ActionCurrent, RelationAtom};

use crate::live_constituent::{
    cellular_cycle_edges, PopulationSectionOrigin, SharedOccurrenceKey, StandingIncidenceAperture,
};
use crate::sparse_standing::CellularStandingChange;
use crate::support_family::LiveSupportExpression;
use crate::{
    ChartAddress, ChartAddressError, GrowingCarrier, GrowingRankedOwn, InterfaceCapability,
    LiveBoundary, LiveBoundaryTransition, LiveCarrierError, LiveCarrierSnapshot, LiveCell,
    LiveConstituent, LiveConstituentError, LiveIncidence, LiveIncidenceKind, LivePath,
    LivePathStep, LivePin, LiveSupportSection, LocalAxis, ReceiverFiberIdentity,
    SparseStandingError, SparseStandingSurface, StandingCell,
};

/// Stable native layout for one direct-production body at natural rest. This wire carries no
/// source event, radiation, contact, receipt, provenance, or application-world material.
pub const LIVE_CURRENT_REST_LAYOUT_VERSION: u32 = 2;

const REST_NATIVE_MAGIC: u32 = 0x4552_5354;
const REST_MAGIC_WORD: usize = 0;
const REST_VERSION_WORD: usize = 1;
const REST_FORM_VERSION_WORD: usize = 2;
const REST_RANK_LO: usize = 3;
const REST_RANK_HI: usize = 4;
const REST_NEXT_LINEAGE_LO: usize = 5;
const REST_NEXT_LINEAGE_HI: usize = 6;
const REST_STANDING_CELLS_LO: usize = 7;
const REST_STANDING_CELLS_HI: usize = 8;
const REST_LINEAGES_LO: usize = 9;
const REST_LINEAGES_HI: usize = 10;
const REST_STANDING_CONSTITUENTS_LO: usize = 11;
const REST_STANDING_CONSTITUENTS_HI: usize = 12;
const REST_PAYLOAD_WORDS_LO: usize = 13;
const REST_PAYLOAD_WORDS_HI: usize = 14;
const REST_HEADER_WORDS: usize = 15;
const REST_V1_PAYLOAD_WORDS_LO: usize = 11;
const REST_V1_PAYLOAD_WORDS_HI: usize = 12;
const REST_V1_HEADER_WORDS: usize = 13;

const REST_LINEAGE_ORDINAL: usize = 0;
const REST_LINEAGE_PENDING: usize = 2;
const REST_LINEAGE_CARRIER_WORDS: usize = REST_LINEAGE_PENDING + COG_WORDS;
const REST_LINEAGE_HEADER_WORDS: usize = REST_LINEAGE_CARRIER_WORDS + 2;

#[inline]
fn rest_split_u64(value: u64) -> [u32; 2] {
    [value as u32, (value >> 32) as u32]
}

#[inline]
fn rest_join_u64(words: &[u32], lo: usize, hi: usize) -> Option<u64> {
    Some(*words.get(lo)? as u64 | ((*words.get(hi)? as u64) << 32))
}

/// Apparatus-local capability for one genuinely live current.  The number is not a source,
/// occurrence, ancestry, or material identity; it only locates the live carrier in this owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CurrentLineage(u64);

impl CurrentLineage {
    pub const fn ordinal(self) -> u64 {
        self.0
    }
}

/// The source-native material geometry of one current at one actual event. A single canonical
/// relation is the irreducible cell face. A complex carries its cells and oriented incidence
/// whole; neither representation is reconstructed from an ordered relation slice.
#[derive(Clone, Copy)]
pub enum CurrentGeometry<'a> {
    Cell(RelationAtom),
    Complex(EventComplex<'a>),
}

/// One exact constituent on a current event's source boundary. A scalar relation has one material
/// cell. A complex must name an ingress or exposed slot; it cannot silently collapse its plural
/// region back to the whole-event `Place` compatibility quotient.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CurrentBoundaryPort {
    Cell,
    Ingress(u32),
    Exposed(u32),
}

impl From<RelationAtom> for CurrentGeometry<'_> {
    fn from(relation: RelationAtom) -> Self {
        Self::Cell(relation)
    }
}

/// A one-element cpu array is only a storage wrapper around one cell. No implementation exists
/// for a plural slice, so this convenience cannot restore the rejected ordered-population mouth.
impl<'a> From<&'a [RelationAtom; 1]> for CurrentGeometry<'a> {
    fn from(relation: &'a [RelationAtom; 1]) -> Self {
        Self::Cell(relation[0])
    }
}

impl<'a> From<EventComplex<'a>> for CurrentGeometry<'a> {
    fn from(complex: EventComplex<'a>) -> Self {
        Self::Complex(complex)
    }
}

/// Event-local dynamic-programming read of one borrowed incidence complex.
///
/// `EventComplex` is allocation-free and therefore composes a selected cell recursively. That is
/// exact for a tree, but a lawful shared dependency DAG (for example a CTC forward trellis) would
/// cause the same predecessor interior to be recomposed once per complete route. The physical
/// membrane instead evaluates every event cell once in its declared `(dependency rank,
/// topological dimension)` order and keeps this disposable atlas only for the duration of the one
/// atomic call. It is not rest, lineage, ancestry, a scheduler, or a second event representation.
pub struct EventNodeAtlas {
    nodes: SparseOrdinalAtlas<Node>,
}

impl EventNodeAtlas {
    pub fn new(complex: EventComplex<'_>) -> Result<Self, LiveCurrentError> {
        let mut cells = Vec::new();
        cells
            .try_reserve_exact(complex.cells().len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        cells.extend_from_slice(complex.cells());
        cells.sort_unstable_by_key(|cell| {
            (
                cell.dependency_rank(),
                cell.dimension(),
                cell.id().ordinal(),
            )
        });

        let mut incidences = Vec::new();
        incidences
            .try_reserve_exact(complex.incidences().len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        incidences.extend_from_slice(complex.incidences());
        incidences.sort_unstable_by_key(|incidence| (incidence.to().ordinal(), incidence.slot()));

        let mut nodes = SparseOrdinalAtlas::new();
        for cell in cells {
            let target = cell.id().ordinal();
            let start = incidences.partition_point(|incidence| incidence.to().ordinal() < target);
            let end = incidences[start..]
                .partition_point(|incidence| incidence.to().ordinal() == target)
                + start;
            let mut node = cell.node();
            for incidence in &incidences[start..end] {
                let constituent = *nodes.get(incidence.from().ordinal()).ok_or(
                    LiveCurrentError::EventComplex(EventComplexError::InvalidDependency(
                        incidence.from(),
                        incidence.to(),
                    )),
                )?;
                node = compose_event_node(node, constituent, incidence.hand())?;
            }
            nodes
                .try_found(cell.id().ordinal(), node)
                .map_err(|error| match error {
                    OrdinalAtlasError::Occupied(_) => {
                        LiveCurrentError::EventComplex(EventComplexError::RepeatedCell(cell.id()))
                    }
                    OrdinalAtlasError::Extent | OrdinalAtlasError::Reservation => {
                        LiveCurrentError::ResourceReservation
                    }
                })?;
        }
        Ok(Self { nodes })
    }

    pub fn cell_node(&self, id: EventCellId) -> Result<Node, LiveCurrentError> {
        self.nodes
            .get(id.ordinal())
            .copied()
            .ok_or(LiveCurrentError::EventComplex(
                EventComplexError::MissingCell(id),
            ))
    }

    pub fn incidence_nodes(
        &self,
        incidence: OrientedIncidence,
    ) -> Result<(Node, Node), LiveCurrentError> {
        let from = self.cell_node(incidence.from())?;
        let to = self.cell_node(incidence.to())?;
        Ok(match incidence.hand() {
            IncidenceHand::With => (from, to),
            IncidenceHand::Against => (to, from),
        })
    }

    pub fn port_node(
        &self,
        complex: EventComplex<'_>,
        kind: EventPortKind,
        slot: u32,
    ) -> Result<Node, LiveCurrentError> {
        let port = complex
            .port(kind, slot)
            .ok_or(EventComplexError::MissingPort(kind, slot))?;
        self.cell_node(port.cell())
    }

    fn compose_ports(
        &self,
        complex: EventComplex<'_>,
        kind: EventPortKind,
    ) -> Result<Node, LiveCurrentError> {
        let mut ports = Vec::new();
        ports
            .try_reserve_exact(complex.ports().len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        ports.extend(
            complex
                .ports()
                .iter()
                .copied()
                .filter(|port| port.kind() == kind),
        );
        ports.sort_unstable_by_key(|port| port.slot());
        let mut node = None;
        for port in ports {
            let constituent = self.cell_node(port.cell())?;
            node = Some(match node {
                None => constituent,
                Some(current) => compose_event_node(current, constituent, port.hand())?,
            });
        }
        node.ok_or_else(|| {
            LiveCurrentError::EventComplex(match kind {
                EventPortKind::Ingress => EventComplexError::MissingIngress,
                EventPortKind::Exposed => EventComplexError::MissingExposed,
            })
        })
    }

    pub fn emanated_node(&self, complex: EventComplex<'_>) -> Result<Node, LiveCurrentError> {
        self.compose_ports(complex, EventPortKind::Exposed)
    }

    pub fn ingress_node(&self, complex: EventComplex<'_>) -> Result<Node, LiveCurrentError> {
        self.compose_ports(complex, EventPortKind::Ingress)
    }

    pub fn ingress_anchor_node(&self, complex: EventComplex<'_>) -> Result<Node, LiveCurrentError> {
        let mut ports = Vec::new();
        ports
            .try_reserve_exact(complex.ports().len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        ports.extend(
            complex
                .ports()
                .iter()
                .copied()
                .filter(|port| port.kind() == EventPortKind::Ingress),
        );
        ports.sort_unstable_by_key(|port| port.slot());
        for port in ports {
            let constituent = self.cell_node(port.cell())?;
            if constituent.well.mag != 0 {
                return Ok(constituent);
            }
        }
        self.ingress_node(complex)
    }
}

fn compose_event_node(
    current: Node,
    constituent: Node,
    hand: IncidenceHand,
) -> Result<Node, LiveCurrentError> {
    let (left, right) = match hand {
        IncidenceHand::With => (current, constituent),
        IncidenceHand::Against => (constituent, current),
    };
    Ok(Node {
        well: left.well.mul(right.well),
        place: compose_place(left, right),
        len: left
            .len
            .checked_add(right.len)
            .ok_or(LiveCurrentError::EventComplex(EventComplexError::Extent))?,
    })
}

fn geometry_face_with_atlas(
    geometry: CurrentGeometry<'_>,
    nodes: Option<&EventNodeAtlas>,
) -> Result<Node, LiveCurrentError> {
    match geometry {
        CurrentGeometry::Cell(relation) => Ok(atom_node(relation.cog())),
        CurrentGeometry::Complex(complex) => nodes
            .ok_or(LiveCurrentError::UnsupportedEventComplex)?
            .emanated_node(complex),
    }
}

fn geometry_anchor_with_atlas(
    geometry: CurrentGeometry<'_>,
    nodes: Option<&EventNodeAtlas>,
) -> Result<Node, LiveCurrentError> {
    match geometry {
        CurrentGeometry::Cell(relation) => Ok(atom_node(relation.cog())),
        CurrentGeometry::Complex(complex) => nodes
            .ok_or(LiveCurrentError::UnsupportedEventComplex)?
            .ingress_anchor_node(complex),
    }
}

fn geometry_boundary_with_atlas(
    geometry: CurrentGeometry<'_>,
    nodes: Option<&EventNodeAtlas>,
    port: CurrentBoundaryPort,
) -> Result<Node, LiveCurrentError> {
    match (geometry, port) {
        (CurrentGeometry::Cell(relation), CurrentBoundaryPort::Cell) => {
            Ok(atom_node(relation.cog()))
        }
        (CurrentGeometry::Complex(complex), CurrentBoundaryPort::Ingress(slot)) => nodes
            .ok_or(LiveCurrentError::UnsupportedEventComplex)?
            .port_node(complex, EventPortKind::Ingress, slot),
        (CurrentGeometry::Complex(complex), CurrentBoundaryPort::Exposed(slot)) => nodes
            .ok_or(LiveCurrentError::UnsupportedEventComplex)?
            .port_node(complex, EventPortKind::Exposed, slot),
        (CurrentGeometry::Cell(_), CurrentBoundaryPort::Ingress(_))
        | (CurrentGeometry::Cell(_), CurrentBoundaryPort::Exposed(_))
        | (CurrentGeometry::Complex(_), CurrentBoundaryPort::Cell) => {
            Err(EventComplexError::InvalidPortSpecies.into())
        }
    }
}

impl<'a> CurrentGeometry<'a> {
    pub fn face(self) -> Result<Node, EventComplexError> {
        match self {
            Self::Cell(relation) => Ok(atom_node(relation.cog())),
            Self::Complex(complex) => complex.emanated_node(),
        }
    }

    pub fn ingress(self) -> Result<Node, EventComplexError> {
        match self {
            Self::Cell(relation) => Ok(atom_node(relation.cog())),
            Self::Complex(complex) => complex.ingress_node(),
        }
    }

    pub const fn complex(self) -> Option<EventComplex<'a>> {
        match self {
            Self::Cell(_) => None,
            Self::Complex(complex) => Some(complex),
        }
    }

    pub fn cells(self) -> u64 {
        match self {
            Self::Cell(_) => 1,
            Self::Complex(complex) => complex.cells().len() as u64,
        }
    }

    pub fn resolving_cells(self) -> u64 {
        match self {
            Self::Cell(relation) => u64::from(relation.cog().mag != 0),
            Self::Complex(complex) => complex.resolving_cells(),
        }
    }

    pub fn incidences(self) -> u64 {
        match self {
            Self::Cell(_) => 0,
            Self::Complex(complex) => complex.incidences().len() as u64,
        }
    }

    pub fn compounds(self) -> u64 {
        match self {
            Self::Cell(_) => 0,
            Self::Complex(complex) => complex.compound_cells(),
        }
    }

    /// Only one isolated zero relation is a wholly static current. A complex carries incidence as
    /// material even when every scalar face is zero.
    pub fn wholly_flat(self) -> bool {
        match self {
            Self::Cell(relation) => relation.cog().mag == 0,
            Self::Complex(_) => false,
        }
    }

    /// The grain at which this already-completed source constituent enters its live carrier. A
    /// scalar cell retains the historical grain-one mouth; a complex derives its grain only from
    /// its declared exposed boundary.
    pub fn source_grain(self) -> Result<u32, EventComplexError> {
        match self {
            Self::Cell(_) => Ok(1),
            Self::Complex(complex) => complex.outer_grain(),
        }
    }
}

/// One current participating in one actual contemporary event.
#[derive(Clone, Copy)]
pub struct CurrentEvent<'a> {
    lineage: CurrentLineage,
    geometry: CurrentGeometry<'a>,
    action: ActionCurrent,
    ending: bool,
}

impl<'a> CurrentEvent<'a> {
    pub const fn continuing_geometry(
        lineage: CurrentLineage,
        geometry: CurrentGeometry<'a>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            lineage,
            geometry,
            action,
            ending: false,
        }
    }

    pub fn continuing(
        lineage: CurrentLineage,
        geometry: impl Into<CurrentGeometry<'a>>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            lineage,
            geometry: geometry.into(),
            action,
            ending: false,
        }
    }

    pub const fn continuing_complex(
        lineage: CurrentLineage,
        complex: EventComplex<'a>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            lineage,
            geometry: CurrentGeometry::Complex(complex),
            action,
            ending: false,
        }
    }

    /// The same event also supplies the current's actual terminal boundary.  Any open dark tread
    /// closes here; after its radiation is integrated, the local carrier departs.
    pub fn ending(
        lineage: CurrentLineage,
        geometry: impl Into<CurrentGeometry<'a>>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            lineage,
            geometry: geometry.into(),
            action,
            ending: true,
        }
    }

    pub const fn ending_complex(
        lineage: CurrentLineage,
        complex: EventComplex<'a>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            lineage,
            geometry: CurrentGeometry::Complex(complex),
            action,
            ending: true,
        }
    }

    pub const fn ending_geometry(
        lineage: CurrentLineage,
        geometry: CurrentGeometry<'a>,
        action: ActionCurrent,
    ) -> Self {
        Self {
            lineage,
            geometry,
            action,
            ending: true,
        }
    }

    pub const fn lineage(self) -> CurrentLineage {
        self.lineage
    }

    pub const fn geometry(self) -> CurrentGeometry<'a> {
        self.geometry
    }

    pub const fn action(self) -> ActionCurrent {
        self.action
    }

    pub const fn ends_lineage(self) -> bool {
        self.ending
    }
}

/// One source-supplied causal hand between two currents which are incident at the same
/// contemporary event.  The endpoints are live capabilities rather than storage ordinals, so
/// caller or hardware order cannot reverse the relation.  Repeating a row retains real
/// multiplicity; no pairwise population is inferred by the membrane.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DirectedCurrentRelation {
    from: CurrentLineage,
    to: CurrentLineage,
}

impl DirectedCurrentRelation {
    pub const fn new(from: CurrentLineage, to: CurrentLineage) -> Self {
        Self { from, to }
    }

    pub const fn from(self) -> CurrentLineage {
        self.from
    }

    pub const fn to(self) -> CurrentLineage {
        self.to
    }
}

/// Durable identity of one receiver-local chart as supplied by a world membrane. The integer is
/// opaque to Soma. It does not identify a semantic modality, a storage row, or an absolute
/// coordinate system.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReceiverChartIdentity(u64);

impl ReceiverChartIdentity {
    pub const fn new(identity: u64) -> Self {
        Self(identity)
    }

    pub const fn identity(self) -> u64 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiverCausalPassageError {
    NonIncreasingChronology,
}

/// One witnessed chronological passage between receiver-local charts. This is inherited
/// occurrence material, not a supplied coupling and not a learned successor. Absolute event
/// orders validate and orient the occurrence, remain inspectable on its borrowed arc and immediate
/// radiation, then depart before Standing. The ordered chart pair and, when supplied, its exact
/// end fiber become a receiver-caused interface candidate; exact recurrence and transported path
/// agreement still have to close through [`LiveCurrentMachine`] before the association changes
/// Standing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverCausalPassage {
    antecedent: ReceiverChartIdentity,
    consequent: ReceiverChartIdentity,
    antecedent_order: u64,
    consequent_order: u64,
    receiver_fiber: Option<(ReceiverFiberIdentity, ReceiverFiberIdentity)>,
}

impl ReceiverCausalPassage {
    pub fn new(
        antecedent: ReceiverChartIdentity,
        antecedent_order: u64,
        consequent: ReceiverChartIdentity,
        consequent_order: u64,
    ) -> Result<Self, ReceiverCausalPassageError> {
        if antecedent_order >= consequent_order {
            return Err(ReceiverCausalPassageError::NonIncreasingChronology);
        }
        Ok(Self {
            antecedent,
            consequent,
            antecedent_order,
            consequent_order,
            receiver_fiber: None,
        })
    }

    /// Enrich one witnessed chart passage by the exact local material faces which actually occupy
    /// its ends. The fiber only narrows which historical paths are physically eligible to meet;
    /// it does not supply a coupling or a deed. Swing still compares the complete transported
    /// paths and returns RIDE or OPEN.
    pub fn with_fiber(
        antecedent: ReceiverChartIdentity,
        antecedent_fiber: ReceiverFiberIdentity,
        antecedent_order: u64,
        consequent: ReceiverChartIdentity,
        consequent_fiber: ReceiverFiberIdentity,
        consequent_order: u64,
    ) -> Result<Self, ReceiverCausalPassageError> {
        let mut passage = Self::new(antecedent, antecedent_order, consequent, consequent_order)?;
        passage.receiver_fiber = Some((antecedent_fiber, consequent_fiber));
        Ok(passage)
    }

    pub const fn antecedent(&self) -> ReceiverChartIdentity {
        self.antecedent
    }

    pub const fn consequent(&self) -> ReceiverChartIdentity {
        self.consequent
    }

    pub const fn antecedent_order(&self) -> u64 {
        self.antecedent_order
    }

    pub const fn consequent_order(&self) -> u64 {
        self.consequent_order
    }

    pub const fn chronological_separation(&self) -> u64 {
        self.consequent_order - self.antecedent_order
    }

    pub fn receiver_fiber(&self) -> Option<(&ReceiverFiberIdentity, &ReceiverFiberIdentity)> {
        self.receiver_fiber
            .as_ref()
            .map(|(antecedent, consequent)| (antecedent, consequent))
    }

    fn interface(&self) -> InterfaceCapability {
        match self.receiver_fiber.as_ref() {
            Some((antecedent, consequent)) => InterfaceCapability::receiver_caused_fiber(
                self.antecedent.0,
                antecedent.clone(),
                self.consequent.0,
                consequent.clone(),
            ),
            None => InterfaceCapability::receiver_caused(self.antecedent.0, self.consequent.0),
        }
    }
}

/// One actual boundary-to-boundary arc inside a higher regional relation cell. The two ports are
/// exact source constituents; `boundary_slot` orders the cell's four-or-more boundary factors,
/// while `arc_slot` orders the declared restriction path within one factor. Neither is chronology.
/// `hand` orients the completed factor when it enters the higher cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionalRelationArc {
    from: CurrentLineage,
    from_port: CurrentBoundaryPort,
    to: CurrentLineage,
    to_port: CurrentBoundaryPort,
    interface: InterfaceCapability,
    receiver_passage: Option<ReceiverCausalPassage>,
    boundary_slot: u32,
    arc_slot: u32,
    hand: IncidenceHand,
}

impl RegionalRelationArc {
    pub const fn new(
        from: CurrentLineage,
        from_port: CurrentBoundaryPort,
        to: CurrentLineage,
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
            interface,
            receiver_passage: None,
            boundary_slot,
            arc_slot,
            hand,
        }
    }

    /// Carry one actually witnessed receiver chronology into this regional boundary without
    /// supplying the cross-event association as a fact. Repeating the same ordered chart pair
    /// only selects a possible temporal seam. The complete path comparison may RIDE or remain
    /// OPEN, and reversed receiver order names a different candidate.
    #[allow(clippy::too_many_arguments)]
    pub fn from_receiver_passage(
        from: CurrentLineage,
        from_port: CurrentBoundaryPort,
        to: CurrentLineage,
        to_port: CurrentBoundaryPort,
        passage: ReceiverCausalPassage,
        boundary_slot: u32,
        arc_slot: u32,
        hand: IncidenceHand,
    ) -> Self {
        Self {
            from,
            to,
            from_port,
            to_port,
            interface: passage.interface(),
            receiver_passage: Some(passage),
            boundary_slot,
            arc_slot,
            hand,
        }
    }

    pub const fn from(&self) -> CurrentLineage {
        self.from
    }

    pub const fn from_port(&self) -> CurrentBoundaryPort {
        self.from_port
    }

    pub const fn to(&self) -> CurrentLineage {
        self.to
    }

    pub const fn to_port(&self) -> CurrentBoundaryPort {
        self.to_port
    }

    pub fn interface(&self) -> InterfaceCapability {
        self.interface.clone()
    }

    /// The witnessed receiver chronology which caused this candidate, when it was not inherited
    /// as an already named world interface. Radiation retains this occurrence testimony; durable
    /// Standing retains its receiver-caused lineage, ordered chart pair, and exact end fiber when
    /// the source passage carried one.
    pub fn receiver_passage(&self) -> Option<&ReceiverCausalPassage> {
        self.receiver_passage.as_ref()
    }

    pub const fn boundary_slot(&self) -> u32 {
        self.boundary_slot
    }

    pub const fn arc_slot(&self) -> u32 {
        self.arc_slot
    }

    pub const fn hand(&self) -> IncidenceHand {
        self.hand
    }
}

/// One borrowed higher relation cell. Every arc is evaluated against this one receiving lineage's
/// exact pre-event illicium. `outgoing_factor_slots`, when present, is the source's declaration of
/// the complete boundaries which the event emits at its outgoing cut. It does not authorize
/// deletion: the machine accepts that factor only after every other exposed arm has actually
/// closed in the joint event.
#[derive(Clone, Copy)]
pub struct RegionalRelationCell<'a> {
    receiver: CurrentLineage,
    arcs: &'a [RegionalRelationArc],
    support_sections: Option<&'a [RegionalSupportSection<'a>]>,
    outgoing_factor_slots: Option<&'a [u32]>,
}

/// One source-declared coface of a regional event. The slots name complete regional boundaries;
/// their shared source cells remain shared occurrences in the event complex.
#[derive(Clone, Copy)]
pub struct RegionalSupportSection<'a> {
    boundary_slots: &'a [u32],
}

impl<'a> RegionalSupportSection<'a> {
    pub const fn new(boundary_slots: &'a [u32]) -> Self {
        Self { boundary_slots }
    }

    pub const fn boundary_slots(self) -> &'a [u32] {
        self.boundary_slots
    }
}

impl<'a> RegionalRelationCell<'a> {
    pub const fn new(receiver: CurrentLineage, arcs: &'a [RegionalRelationArc]) -> Self {
        Self {
            receiver,
            arcs,
            support_sections: None,
            outgoing_factor_slots: None,
        }
    }

    pub const fn with_support_sections(
        receiver: CurrentLineage,
        arcs: &'a [RegionalRelationArc],
        support_sections: &'a [RegionalSupportSection<'a>],
    ) -> Self {
        Self {
            receiver,
            arcs,
            support_sections: Some(support_sections),
            outgoing_factor_slots: None,
        }
    }

    /// Declare the event's outgoing boundary presentation `q`. Every named slot must be present
    /// exactly as one complete boundary in `arcs`. Unnamed boundaries still participate in the
    /// event; they may depart only if joint closure proves that none remains exposed.
    pub const fn with_outgoing_factor(
        receiver: CurrentLineage,
        arcs: &'a [RegionalRelationArc],
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
        receiver: CurrentLineage,
        arcs: &'a [RegionalRelationArc],
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

    pub const fn receiver(self) -> CurrentLineage {
        self.receiver
    }

    pub const fn arcs(self) -> &'a [RegionalRelationArc] {
        self.arcs
    }

    pub const fn support_sections(self) -> Option<&'a [RegionalSupportSection<'a>]> {
        self.support_sections
    }

    pub const fn outgoing_factor_slots(self) -> Option<&'a [u32]> {
        self.outgoing_factor_slots
    }
}

/// One complete borrowed event configuration.  Every [`CurrentEvent`] is already one physical
/// incidence at this cut; `relations` supplies only the actual directed adjacency between those
/// incidences.  Neither population survives the call.
#[derive(Clone, Copy)]
pub struct ContemporaryEvent<'a> {
    currents: &'a [CurrentEvent<'a>],
    relations: &'a [DirectedCurrentRelation],
    regional: &'a [RegionalRelationCell<'a>],
}

impl<'a> ContemporaryEvent<'a> {
    pub const fn new(
        currents: &'a [CurrentEvent<'a>],
        relations: &'a [DirectedCurrentRelation],
    ) -> Self {
        Self {
            currents,
            relations,
            regional: &[],
        }
    }

    pub const fn with_regional(
        currents: &'a [CurrentEvent<'a>],
        relations: &'a [DirectedCurrentRelation],
        regional: &'a [RegionalRelationCell<'a>],
    ) -> Self {
        Self {
            currents,
            relations,
            regional,
        }
    }

    pub const fn unrelated(currents: &'a [CurrentEvent<'a>]) -> Self {
        Self::new(currents, &[])
    }

    pub const fn currents(self) -> &'a [CurrentEvent<'a>] {
        self.currents
    }

    pub const fn relations(self) -> &'a [DirectedCurrentRelation] {
        self.relations
    }

    pub const fn regional(self) -> &'a [RegionalRelationCell<'a>] {
        self.regional
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiveCurrentError {
    EmptyEvent,
    EmptyRelation(CurrentLineage),
    EventComplex(EventComplexError),
    EventMemberAbsent(usize),
    LineageAbsent(CurrentLineage),
    LineageRepeated(CurrentLineage),
    DirectedEndpointAbsent(CurrentLineage),
    EmptyRegionalRelation(CurrentLineage),
    RegionalTopology(CurrentLineage),
    FirstEventChanged(CurrentLineage),
    CursorExtent,
    ResourceReservation,
    BodyRefused(CurrentLineage),
    ExecutionMismatch(CurrentLineage),
    /// A physical executor returned a non-canonical or incomplete exact receipt at a named
    /// boundary. The stage is apparatus testimony, not an application-level semantic label.
    ExecutionMismatchAt(CurrentLineage, &'static str),
    ExecutionMismatchStatus(CurrentLineage, &'static str, u32),
    PhysicalSettlement,
    UnsupportedEventComplex,
    UnsupportedRegionalRelation,
    UnsupportedStandingRank(u64),
    UnsettledRest(CurrentLineage),
    InvalidRestImage,
    InvalidRestWire,
    Substrate(i32),
    /// **A contemporary population the mounted device cannot hold, named rather than surfaced as a
    /// bare driver code.**
    ///
    /// Enacting `lanes` currents co-presently reserves `lanes` copies of the per-thread local-memory
    /// stack plus one region per lane of every buffer, so the demand scales with the front. Without
    /// this the driver returns `CUDA_ERROR_OUT_OF_MEMORY` with no numbers and nothing says which
    /// quantity was short. Every field here is read off the device or computed from the material.
    PopulationExceedsDevice {
        lanes: usize,
        demanded_bytes: u64,
        free_bytes: u64,
        per_lane_stack_bytes: u64,
    },
    Carrier(LiveCarrierError),
    Constituent(LiveConstituentError),
    Standing(SparseStandingError),
}

impl From<LiveCarrierError> for LiveCurrentError {
    fn from(error: LiveCarrierError) -> Self {
        Self::Carrier(error)
    }
}

impl From<SparseStandingError> for LiveCurrentError {
    fn from(error: SparseStandingError) -> Self {
        Self::Standing(error)
    }
}

impl From<LiveConstituentError> for LiveCurrentError {
    fn from(error: LiveConstituentError) -> Self {
        Self::Constituent(error)
    }
}

impl From<ChartAddressError> for LiveCurrentError {
    fn from(error: ChartAddressError) -> Self {
        Self::Standing(error.into())
    }
}

impl From<EventComplexError> for LiveCurrentError {
    fn from(error: EventComplexError) -> Self {
        Self::EventComplex(error)
    }
}

/// One event-internal incidence after it met the current's exact pre-event receiver. The row is
/// immediate radiation only; the live body retains the changed topology, not an incidence ledger.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EventIncidenceRadiation {
    incidence: OrientedIncidence,
    contact: DirectedEventContact,
}

impl EventIncidenceRadiation {
    pub const fn new(incidence: OrientedIncidence, contact: DirectedEventContact) -> Self {
        Self { incidence, contact }
    }

    pub const fn incidence(self) -> OrientedIncidence {
        self.incidence
    }

    pub const fn contact(self) -> DirectedEventContact {
        self.contact
    }
}

/// The bounded outward face of one enacted current.  The machine does not retain this row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentRadiation {
    lineage: CurrentLineage,
    consequence: EventEmanation,
    emissions: Vec<FeltEmission>,
    incidences: Vec<EventIncidenceRadiation>,
    ended: bool,
}

impl CurrentRadiation {
    pub const fn lineage(&self) -> CurrentLineage {
        self.lineage
    }

    pub const fn consequence(&self) -> EventEmanation {
        self.consequence
    }

    pub fn emissions(&self) -> &[FeltEmission] {
        &self.emissions
    }

    pub fn incidences(&self) -> &[EventIncidenceRadiation] {
        &self.incidences
    }

    pub const fn ended(&self) -> bool {
        self.ended
    }
}

/// The outward face of one supplied directed relation.  An open fourth contact remains explicit
/// in `contact`; a formed crossing contributes to the same successor as the current-local deeds.
/// The machine returns this row and retains none of it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DirectedRelationRadiation {
    relation: DirectedCurrentRelation,
    contact: DirectedEventContact,
}

impl DirectedRelationRadiation {
    pub const fn relation(self) -> DirectedCurrentRelation {
        self.relation
    }

    pub const fn contact(self) -> DirectedEventContact {
        self.contact
    }
}

/// One exact constituent arc of a returned regional cell. Open fourth contacts remain explicit;
/// these rows are immediate testimony and never become an incidence ledger in live memory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionalArcRadiation {
    arc: RegionalRelationArc,
    contact: DirectedEventContact,
}

impl RegionalArcRadiation {
    pub const fn arc(&self) -> &RegionalRelationArc {
        &self.arc
    }

    pub const fn contact(&self) -> DirectedEventContact {
        self.contact
    }
}

/// The immediate factor testimony of one source-declared regional relation cell. The completed
/// constituent accompanies these rows so no scalar product or point projection can replace it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionalRelationRadiation {
    receiver: CurrentLineage,
    arcs: Vec<RegionalArcRadiation>,
    constituent: LiveConstituent,
    support_transitions: Vec<Vec<LiveBoundaryTransition>>,
    touched_constituents: usize,
    front_depth: u32,
}

impl RegionalRelationRadiation {
    pub const fn receiver(&self) -> CurrentLineage {
        self.receiver
    }

    pub fn arcs(&self) -> &[RegionalArcRadiation] {
        &self.arcs
    }

    pub const fn constituent(&self) -> &LiveConstituent {
        &self.constituent
    }

    /// Exact returned transition of each support section declared by this regional source cell,
    /// in source section order. These are immediate observation receipts; Standing retains only
    /// the composed constituent.
    pub fn support_transitions(&self) -> &[Vec<LiveBoundaryTransition>] {
        &self.support_transitions
    }

    /// Exact number of immutable standing occurrences reached by this event's propagated local
    /// front. The ordinals themselves are event-transient storage addresses and deliberately do
    /// not radiate.
    pub const fn touched_constituents(&self) -> usize {
        self.touched_constituents
    }

    /// Successive standing-local front layers crossed after the source event. A zero-depth
    /// regional constituent did not meet prior standing.
    pub const fn front_depth(&self) -> u32 {
        self.front_depth
    }
}

/// Complete result of one co-present event.  Currents remain in caller order only as outward
/// correspondence; their standing integration is order-free.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContemporaryRadiation {
    before_rank: u64,
    after_rank: u64,
    before_cells: usize,
    after_cells: usize,
    currents: Vec<CurrentRadiation>,
    relations: Vec<DirectedRelationRadiation>,
    regional: Vec<RegionalRelationRadiation>,
}

impl ContemporaryRadiation {
    pub const fn before_rank(&self) -> u64 {
        self.before_rank
    }

    pub const fn after_rank(&self) -> u64 {
        self.after_rank
    }

    pub const fn before_cells(&self) -> usize {
        self.before_cells
    }

    pub const fn after_cells(&self) -> usize {
        self.after_cells
    }

    pub fn currents(&self) -> &[CurrentRadiation] {
        &self.currents
    }

    pub fn relations(&self) -> &[DirectedRelationRadiation] {
        &self.relations
    }

    pub fn regional(&self) -> &[RegionalRelationRadiation] {
        &self.regional
    }
}

/// Physical live-memory census.  There is intentionally no event, contact, receipt, source, or
/// journal population to count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LiveMemory {
    pub standing_cells: usize,
    pub standing_constituents: usize,
    pub constituent_cells: usize,
    pub constituent_incidences: usize,
    pub constituent_pins: usize,
    pub constituent_paths: usize,
    pub constituent_transport_terms: usize,
    pub live_lineages: usize,
    pub carrier_words: usize,
    pub overflow_nodes: usize,
}

/// Exact rest face for one genuinely live current. The carrier is the canonical native
/// continuation wire; source material, event testimony, and world provenance remain outside.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiveLineageRestImage {
    lineage: CurrentLineage,
    pending_dark: Cog,
    native_carrier: Vec<u32>,
}

impl LiveLineageRestImage {
    pub const fn lineage(&self) -> CurrentLineage {
        self.lineage
    }

    pub const fn pending_dark(&self) -> Cog {
        self.pending_dark
    }

    pub fn native_carrier_words(&self) -> &[u32] {
        &self.native_carrier
    }
}

/// Complete active body at one receiving-edge rest boundary. This is not a replay population:
/// reopening mounts the same standing construction and live current continuations without
/// presenting a deed, emitting radiation, or advancing a lineage cursor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiveCurrentRestImage {
    standing: SparseStandingSurface,
    lineages: Vec<LiveLineageRestImage>,
    next_lineage: u64,
}

impl LiveCurrentRestImage {
    pub fn standing(&self) -> &SparseStandingSurface {
        &self.standing
    }

    pub fn lineages(&self) -> &[LiveLineageRestImage] {
        &self.lineages
    }

    pub const fn next_lineage(&self) -> u64 {
        self.next_lineage
    }

    /// Encode the direct live body at rest into one exact native word population. Standing cells
    /// retain rank-qualified addresses, each live lineage retains its canonical carrier wire, and
    /// every dynamic extent is explicit. This is a persistence boundary, never input light.
    pub fn encode_native_words(&self) -> Result<Vec<u32>, LiveCurrentError> {
        let address_words = ChartAddress::native_word_extent(self.standing.rank())?;
        let standing_row_words = address_words
            .checked_add(COMPACT_FORM_WORDS)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let standing_words = self
            .standing
            .cells()
            .len()
            .checked_mul(standing_row_words)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let mut constituent_rows = Vec::new();
        constituent_rows
            .try_reserve_exact(self.standing.constituents().len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        let mut constituent_words = 0usize;
        for constituent in self.standing.constituents() {
            let row = constituent.native_words()?;
            constituent_words = constituent_words
                .checked_add(2)
                .and_then(|extent| extent.checked_add(row.len()))
                .ok_or(LiveCurrentError::ResourceReservation)?;
            constituent_rows.push(row);
        }
        let mut lineage_words = 0usize;
        for lineage in &self.lineages {
            lineage_words = lineage_words
                .checked_add(REST_LINEAGE_HEADER_WORDS)
                .and_then(|extent| extent.checked_add(lineage.native_carrier.len()))
                .ok_or(LiveCurrentError::ResourceReservation)?;
        }
        let payload_words = standing_words
            .checked_add(constituent_words)
            .and_then(|extent| extent.checked_add(lineage_words))
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let total_words = REST_HEADER_WORDS
            .checked_add(payload_words)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let mut words = Vec::new();
        words
            .try_reserve_exact(total_words)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        words.resize(total_words, 0);

        words[REST_MAGIC_WORD] = REST_NATIVE_MAGIC;
        words[REST_VERSION_WORD] = LIVE_CURRENT_REST_LAYOUT_VERSION;
        words[REST_FORM_VERSION_WORD] = COMPACT_FORM_LAYOUT_VERSION;
        let rank = rest_split_u64(self.standing.rank());
        words[REST_RANK_LO] = rank[0];
        words[REST_RANK_HI] = rank[1];
        let next_lineage = rest_split_u64(self.next_lineage);
        words[REST_NEXT_LINEAGE_LO] = next_lineage[0];
        words[REST_NEXT_LINEAGE_HI] = next_lineage[1];
        let standing_cells = rest_split_u64(
            u64::try_from(self.standing.cells().len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?,
        );
        words[REST_STANDING_CELLS_LO] = standing_cells[0];
        words[REST_STANDING_CELLS_HI] = standing_cells[1];
        let lineages = rest_split_u64(
            u64::try_from(self.lineages.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?,
        );
        words[REST_LINEAGES_LO] = lineages[0];
        words[REST_LINEAGES_HI] = lineages[1];
        let standing_constituents = rest_split_u64(
            u64::try_from(self.standing.constituents().len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?,
        );
        words[REST_STANDING_CONSTITUENTS_LO] = standing_constituents[0];
        words[REST_STANDING_CONSTITUENTS_HI] = standing_constituents[1];
        let payload = rest_split_u64(
            u64::try_from(payload_words).map_err(|_| LiveCurrentError::ResourceReservation)?,
        );
        words[REST_PAYLOAD_WORDS_LO] = payload[0];
        words[REST_PAYLOAD_WORDS_HI] = payload[1];

        let mut cursor = REST_HEADER_WORDS;
        for cell in self.standing.cells() {
            let address_end = cursor
                .checked_add(address_words)
                .ok_or(LiveCurrentError::ResourceReservation)?;
            cell.address()
                .write_native_words(&mut words[cursor..address_end])?;
            cursor = address_end;
            cell.form().pack(&mut words, cursor);
            cursor += COMPACT_FORM_WORDS;
        }
        for row in constituent_rows {
            let extent = rest_split_u64(
                u64::try_from(row.len()).map_err(|_| LiveCurrentError::ResourceReservation)?,
            );
            words[cursor] = extent[0];
            words[cursor + 1] = extent[1];
            cursor += 2;
            let end = cursor
                .checked_add(row.len())
                .ok_or(LiveCurrentError::ResourceReservation)?;
            words[cursor..end].copy_from_slice(&row);
            cursor = end;
        }
        for lineage in &self.lineages {
            let ordinal = rest_split_u64(lineage.lineage.ordinal());
            words[cursor + REST_LINEAGE_ORDINAL] = ordinal[0];
            words[cursor + REST_LINEAGE_ORDINAL + 1] = ordinal[1];
            for word in 0..COG_WORDS {
                words[cursor + REST_LINEAGE_PENDING + word] =
                    cog_packed_word(lineage.pending_dark, word);
            }
            let carrier_words = rest_split_u64(
                u64::try_from(lineage.native_carrier.len())
                    .map_err(|_| LiveCurrentError::ResourceReservation)?,
            );
            words[cursor + REST_LINEAGE_CARRIER_WORDS] = carrier_words[0];
            words[cursor + REST_LINEAGE_CARRIER_WORDS + 1] = carrier_words[1];
            cursor += REST_LINEAGE_HEADER_WORDS;
            let carrier_end = cursor
                .checked_add(lineage.native_carrier.len())
                .ok_or(LiveCurrentError::ResourceReservation)?;
            words[cursor..carrier_end].copy_from_slice(&lineage.native_carrier);
            cursor = carrier_end;
        }
        debug_assert_eq!(cursor, words.len());
        Ok(words)
    }

    /// Reopen one complete native rest word population. Every extent, address, form, lineage,
    /// pending current, and carrier closes before a body image is returned.
    pub fn from_native_words(words: &[u32]) -> Result<Self, LiveCurrentError> {
        if words.len() < REST_V1_HEADER_WORDS
            || words[REST_MAGIC_WORD] != REST_NATIVE_MAGIC
            || words[REST_FORM_VERSION_WORD] != COMPACT_FORM_LAYOUT_VERSION
        {
            return Err(LiveCurrentError::InvalidRestWire);
        }
        let (header_words, constituent_count, payload_lo, payload_hi) =
            match words[REST_VERSION_WORD] {
                1 => (
                    REST_V1_HEADER_WORDS,
                    0usize,
                    REST_V1_PAYLOAD_WORDS_LO,
                    REST_V1_PAYLOAD_WORDS_HI,
                ),
                LIVE_CURRENT_REST_LAYOUT_VERSION if words.len() >= REST_HEADER_WORDS => {
                    let constituents = rest_join_u64(
                        words,
                        REST_STANDING_CONSTITUENTS_LO,
                        REST_STANDING_CONSTITUENTS_HI,
                    )
                    .and_then(|extent| usize::try_from(extent).ok())
                    .ok_or(LiveCurrentError::InvalidRestWire)?;
                    (
                        REST_HEADER_WORDS,
                        constituents,
                        REST_PAYLOAD_WORDS_LO,
                        REST_PAYLOAD_WORDS_HI,
                    )
                }
                _ => return Err(LiveCurrentError::InvalidRestWire),
            };
        let payload_words = rest_join_u64(words, payload_lo, payload_hi)
            .and_then(|extent| usize::try_from(extent).ok())
            .ok_or(LiveCurrentError::InvalidRestWire)?;
        if payload_words
            != words
                .len()
                .checked_sub(header_words)
                .ok_or(LiveCurrentError::InvalidRestWire)?
        {
            return Err(LiveCurrentError::InvalidRestWire);
        }
        let rank = rest_join_u64(words, REST_RANK_LO, REST_RANK_HI)
            .ok_or(LiveCurrentError::InvalidRestWire)?;
        let next_lineage = rest_join_u64(words, REST_NEXT_LINEAGE_LO, REST_NEXT_LINEAGE_HI)
            .ok_or(LiveCurrentError::InvalidRestWire)?;
        let standing_cells = rest_join_u64(words, REST_STANDING_CELLS_LO, REST_STANDING_CELLS_HI)
            .and_then(|extent| usize::try_from(extent).ok())
            .ok_or(LiveCurrentError::InvalidRestWire)?;
        let lineage_count = rest_join_u64(words, REST_LINEAGES_LO, REST_LINEAGES_HI)
            .and_then(|extent| usize::try_from(extent).ok())
            .ok_or(LiveCurrentError::InvalidRestWire)?;
        let address_words = ChartAddress::native_word_extent(rank)?;
        let standing_row_words = address_words
            .checked_add(COMPACT_FORM_WORDS)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let standing_extent = standing_cells
            .checked_mul(standing_row_words)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let standing_end = header_words
            .checked_add(standing_extent)
            .filter(|end| *end <= words.len())
            .ok_or(LiveCurrentError::InvalidRestWire)?;

        let mut cells = Vec::new();
        cells
            .try_reserve_exact(standing_cells)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        let mut cursor = header_words;
        for _ in 0..standing_cells {
            let address_end = cursor
                .checked_add(address_words)
                .ok_or(LiveCurrentError::ResourceReservation)?;
            let address = ChartAddress::from_native_words(rank, &words[cursor..address_end])?;
            cursor = address_end;
            let form = RegionalForm::unpack_compact_checked(words, cursor)
                .map_err(|_| LiveCurrentError::InvalidRestWire)?;
            cursor += COMPACT_FORM_WORDS;
            cells.push(StandingCell::new(address, form).ok_or(LiveCurrentError::InvalidRestWire)?);
        }
        debug_assert_eq!(cursor, standing_end);
        let mut constituents = Vec::new();
        constituents
            .try_reserve_exact(constituent_count)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for _ in 0..constituent_count {
            let extent_at = cursor
                .checked_add(2)
                .filter(|end| *end <= words.len())
                .ok_or(LiveCurrentError::InvalidRestWire)?;
            let extent = rest_join_u64(words, cursor, cursor + 1)
                .and_then(|extent| usize::try_from(extent).ok())
                .ok_or(LiveCurrentError::InvalidRestWire)?;
            cursor = extent_at;
            let end = cursor
                .checked_add(extent)
                .filter(|end| *end <= words.len())
                .ok_or(LiveCurrentError::InvalidRestWire)?;
            constituents.push(
                LiveConstituent::from_native_words(&words[cursor..end])
                    .map_err(|_| LiveCurrentError::InvalidRestWire)?,
            );
            cursor = end;
        }
        let standing =
            SparseStandingSurface::from_ranked_cells_with_constituents(rank, cells, constituents)?;

        let minimum_lineage_words = lineage_count
            .checked_mul(REST_LINEAGE_HEADER_WORDS)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        if minimum_lineage_words > words.len() - cursor {
            return Err(LiveCurrentError::InvalidRestWire);
        }

        let mut lineages = Vec::new();
        lineages
            .try_reserve_exact(lineage_count)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for _ in 0..lineage_count {
            let header_end = cursor
                .checked_add(REST_LINEAGE_HEADER_WORDS)
                .filter(|end| *end <= words.len())
                .ok_or(LiveCurrentError::InvalidRestWire)?;
            let ordinal = rest_join_u64(
                words,
                cursor + REST_LINEAGE_ORDINAL,
                cursor + REST_LINEAGE_ORDINAL + 1,
            )
            .ok_or(LiveCurrentError::InvalidRestWire)?;
            let pending_at = cursor + REST_LINEAGE_PENDING;
            if !packed_cog_is_canonical(words, pending_at) {
                return Err(LiveCurrentError::InvalidRestWire);
            }
            let pending_dark = read_cog(words, pending_at);
            let carrier_words = rest_join_u64(
                words,
                cursor + REST_LINEAGE_CARRIER_WORDS,
                cursor + REST_LINEAGE_CARRIER_WORDS + 1,
            )
            .and_then(|extent| usize::try_from(extent).ok())
            .ok_or(LiveCurrentError::InvalidRestWire)?;
            cursor = header_end;
            let carrier_end = cursor
                .checked_add(carrier_words)
                .filter(|end| *end <= words.len())
                .ok_or(LiveCurrentError::InvalidRestWire)?;
            let mut native_carrier = Vec::new();
            native_carrier
                .try_reserve_exact(carrier_words)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            native_carrier.extend_from_slice(&words[cursor..carrier_end]);
            cursor = carrier_end;
            lineages.push(LiveLineageRestImage {
                lineage: CurrentLineage(ordinal),
                pending_dark,
                native_carrier,
            });
        }
        if cursor != words.len() {
            return Err(LiveCurrentError::InvalidRestWire);
        }
        let image = Self {
            standing,
            lineages,
            next_lineage,
        };
        LiveCurrentMachine::from_rest_image(image)?.rest_image()
    }

    /// Little-endian durable byte face for files, databases, or application-owned object stores.
    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, LiveCurrentError> {
        let words = self.encode_native_words()?;
        let extent = words
            .len()
            .checked_mul(core::mem::size_of::<u32>())
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(extent)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for word in words {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        Ok(bytes)
    }

    /// Reopen one exact little-endian durable byte face. Partial words refuse before allocation of
    /// the live body.
    pub fn from_native_bytes(bytes: &[u8]) -> Result<Self, LiveCurrentError> {
        if bytes.len() % core::mem::size_of::<u32>() != 0 {
            return Err(LiveCurrentError::InvalidRestWire);
        }
        let mut words = Vec::new();
        words
            .try_reserve_exact(bytes.len() / core::mem::size_of::<u32>())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for row in bytes.chunks_exact(core::mem::size_of::<u32>()) {
            words.push(u32::from_le_bytes([row[0], row[1], row[2], row[3]]));
        }
        Self::from_native_words(&words)
    }
}

/// Exact live body mounted for one physical event execution.  The birth seed exists only until
/// its first event; a continuation borrows the complete live snapshot.
#[derive(Clone, Copy)]
pub enum CurrentBodyMount<'a> {
    Seed {
        first_event: Place,
        anchor: Place,
        carrier: &'a GrowingCarrier,
    },
    Live(&'a LiveCarrierSnapshot),
}

impl<'a> CurrentBodyMount<'a> {
    pub const fn first_event(self) -> Option<Place> {
        match self {
            Self::Seed { first_event, .. } => Some(first_event),
            Self::Live(_) => None,
        }
    }

    pub fn header(self) -> Option<LiveBodyHeader> {
        match self {
            Self::Seed { .. } => None,
            Self::Live(snapshot) => Some(snapshot.header()),
        }
    }

    pub fn carrier(self) -> &'a GrowingCarrier {
        match self {
            Self::Seed { carrier, .. } => carrier,
            Self::Live(snapshot) => snapshot.carrier(),
        }
    }

    /// Gauge anchor for an unborn lineage. It is the first actual resolving relation, never the
    /// plural event's boundary address. A resumed body already carries this anchor in `K`.
    pub const fn seed_anchor(self) -> Option<Place> {
        match self {
            Self::Seed { anchor, .. } => Some(anchor),
            Self::Live(_) => None,
        }
    }

    /// Capture the exact immutable receiver at the grain where one already-completed source
    /// constituent will enter.  This read contains no event act and permits a physical executor to
    /// form co-present contacts independently of the mutable carrier lane.
    pub fn event_receiver_at_source_grain(self, source_grain: u32) -> Option<EventReceiver> {
        let depth = usize::try_from(source_grain.checked_sub(1)?).ok()?;
        let enclosure =
            Enclosure::unpack_at(self.carrier().words(), depth.checked_mul(ENCLOSURE_WORDS)?);
        let channel = match self {
            Self::Seed { anchor, .. } => LineageChannel::from_first_difference(anchor)?,
            Self::Live(snapshot) => snapshot.header().channel(),
        };
        Some(EventReceiver {
            channel,
            held: enclosure.fly,
            held_live: enclosure.fly_live,
        })
    }
}

/// Substrate-neutral input for one current in the contemporary population. `face` is the complete
/// event's canonical boundary address for attachment and directed meeting. For a complex, its
/// exposed boundary also declares the grain at which that already-completed constituent enters the
/// carrier; no internal cell is replayed as an additional instant.
#[derive(Clone, Copy)]
pub struct CurrentExecutionRequest<'a> {
    event: CurrentEvent<'a>,
    face: Node,
    event_nodes: Option<&'a EventNodeAtlas>,
    wholly_dark: bool,
    mount: CurrentBodyMount<'a>,
    pending_dark: Cog,
}

impl<'a> CurrentExecutionRequest<'a> {
    pub const fn event(self) -> CurrentEvent<'a> {
        self.event
    }

    pub const fn lineage(self) -> CurrentLineage {
        self.event.lineage
    }

    pub const fn face(self) -> Node {
        self.face
    }

    pub const fn event_nodes(self) -> Option<&'a EventNodeAtlas> {
        self.event_nodes
    }

    pub const fn wholly_dark(self) -> bool {
        self.wholly_dark
    }

    pub const fn mount(self) -> CurrentBodyMount<'a> {
        self.mount
    }

    pub const fn pending_dark(self) -> Cog {
        self.pending_dark
    }
}

/// Substrate-neutral input for one source-supplied hand in the complete contemporary event.
/// Capabilities retain the event-local identity while the two composed positions are the exact
/// geometry the physical executor meets.  No source material or retained incidence accompanies
/// this borrowed row.
#[derive(Clone, Copy)]
pub struct DirectedExecutionRequest {
    relation: DirectedCurrentRelation,
    from: Place,
    to: Place,
}

impl DirectedExecutionRequest {
    const fn new(relation: DirectedCurrentRelation, from: Place, to: Place) -> Self {
        Self { relation, from, to }
    }

    pub const fn relation(self) -> DirectedCurrentRelation {
        self.relation
    }

    pub const fn from(self) -> Place {
        self.from
    }

    pub const fn to(self) -> Place {
        self.to
    }
}

/// One regional arc borrowed at the physical executor boundary. The complete source geometries
/// and selected ports remain available; no `Node`, `Place`, rotor, scalar product, or testimony
/// quotient is allowed to replace them before the receiving body forms contextual chi.
#[derive(Clone)]
pub struct RegionalArcExecution<'a> {
    arc: RegionalRelationArc,
    from_geometry: CurrentGeometry<'a>,
    from_nodes: Option<&'a EventNodeAtlas>,
    to_geometry: CurrentGeometry<'a>,
    to_nodes: Option<&'a EventNodeAtlas>,
}

impl<'a> RegionalArcExecution<'a> {
    const fn new(
        arc: RegionalRelationArc,
        from_geometry: CurrentGeometry<'a>,
        from_nodes: Option<&'a EventNodeAtlas>,
        to_geometry: CurrentGeometry<'a>,
        to_nodes: Option<&'a EventNodeAtlas>,
    ) -> Self {
        Self {
            arc,
            from_geometry,
            from_nodes,
            to_geometry,
            to_nodes,
        }
    }

    pub const fn arc(&self) -> &RegionalRelationArc {
        &self.arc
    }

    pub const fn from_geometry(&self) -> CurrentGeometry<'a> {
        self.from_geometry
    }

    pub const fn from_port(&self) -> CurrentBoundaryPort {
        self.arc.from_port
    }

    pub const fn from_nodes(&self) -> Option<&EventNodeAtlas> {
        self.from_nodes
    }

    pub const fn to_geometry(&self) -> CurrentGeometry<'a> {
        self.to_geometry
    }

    pub const fn to_port(&self) -> CurrentBoundaryPort {
        self.arc.to_port
    }

    pub const fn to_nodes(&self) -> Option<&EventNodeAtlas> {
        self.to_nodes
    }
}

/// One complete higher relation cell lowered for a physical body mount. Arc order is canonical by
/// declared boundary/arc slots; slice storage order from the world has already become gauge.
pub struct RegionalExecutionRequest<'a> {
    receiver: CurrentLineage,
    arcs: Vec<RegionalArcExecution<'a>>,
    support_sections: Option<&'a [RegionalSupportSection<'a>]>,
    outgoing_factor_slots: Option<&'a [u32]>,
}

impl<'a> RegionalExecutionRequest<'a> {
    fn new(
        receiver: CurrentLineage,
        arcs: Vec<RegionalArcExecution<'a>>,
        support_sections: Option<&'a [RegionalSupportSection<'a>]>,
        outgoing_factor_slots: Option<&'a [u32]>,
    ) -> Self {
        Self {
            receiver,
            arcs,
            support_sections,
            outgoing_factor_slots,
        }
    }

    pub const fn receiver(&self) -> CurrentLineage {
        self.receiver
    }

    pub fn arcs(&self) -> &[RegionalArcExecution<'a>] {
        &self.arcs
    }

    pub const fn support_sections(&self) -> Option<&[RegionalSupportSection<'a>]> {
        self.support_sections
    }

    pub const fn outgoing_factor_slots(&self) -> Option<&[u32]> {
        self.outgoing_factor_slots
    }
}

fn collect_complex_contact_pairs(
    complex: EventComplex<'_>,
    nodes: &EventNodeAtlas,
    cell: EventCellId,
    visited: &mut std::collections::BTreeSet<EventCellId>,
    pairs: &mut BTreeMap<[u32; 4 * COG_WORDS], (Place, Place)>,
) -> Result<(), LiveCurrentError> {
    if !visited.insert(cell) {
        return Ok(());
    }
    complex
        .cell(cell)
        .ok_or(EventComplexError::MissingCell(cell))?;
    let mut incoming: Vec<OrientedIncidence> = complex
        .incidences()
        .iter()
        .copied()
        .filter(|incidence| incidence.to() == cell)
        .collect();
    incoming.sort_unstable_by_key(|incidence| incidence.slot());
    for incidence in incoming {
        collect_complex_contact_pairs(complex, nodes, incidence.from(), visited, pairs)?;
        let (from, to) = nodes.incidence_nodes(incidence)?;
        pairs.insert(
            regional_pair_key(from.place, to.place),
            (from.place, to.place),
        );
    }
    Ok(())
}

fn collect_port_contact_pairs(
    geometry: CurrentGeometry<'_>,
    nodes: Option<&EventNodeAtlas>,
    port: CurrentBoundaryPort,
    pairs: &mut BTreeMap<[u32; 4 * COG_WORDS], (Place, Place)>,
) -> Result<Node, LiveCurrentError> {
    match (geometry, port) {
        (CurrentGeometry::Cell(relation), CurrentBoundaryPort::Cell) => {
            Ok(atom_node(relation.cog()))
        }
        (CurrentGeometry::Complex(complex), CurrentBoundaryPort::Ingress(slot))
        | (CurrentGeometry::Complex(complex), CurrentBoundaryPort::Exposed(slot)) => {
            let nodes = nodes.ok_or(LiveCurrentError::UnsupportedEventComplex)?;
            let kind = match port {
                CurrentBoundaryPort::Ingress(_) => EventPortKind::Ingress,
                CurrentBoundaryPort::Exposed(_) => EventPortKind::Exposed,
                CurrentBoundaryPort::Cell => unreachable!(),
            };
            let selected = complex
                .port(kind, slot)
                .ok_or(EventComplexError::MissingPort(kind, slot))?;
            let mut visited = std::collections::BTreeSet::new();
            collect_complex_contact_pairs(complex, nodes, selected.cell(), &mut visited, pairs)?;
            nodes.cell_node(selected.cell())
        }
        _ => Err(EventComplexError::InvalidPortSpecies.into()),
    }
}

fn regional_pair_key(from: Place, to: Place) -> [u32; 4 * COG_WORDS] {
    let mut key = [0u32; 4 * COG_WORDS];
    for (at, cog) in [from.0, from.1, to.0, to.1].into_iter().enumerate() {
        for word in 0..COG_WORDS {
            key[at * COG_WORDS + word] = cog_packed_word(cog, word);
        }
    }
    key
}

/// Canonical population of actual receiver-relative meetings needed to form one regional cell.
/// This is a physical work description only: contacts and topology are not retained in it, and
/// unselected branches of a source complex do not become speculative GPU work.
pub fn regional_contact_pairs(
    request: &RegionalExecutionRequest<'_>,
) -> Result<Vec<(Place, Place)>, LiveCurrentError> {
    let mut pairs = BTreeMap::new();
    for requested in &request.arcs {
        let from = collect_port_contact_pairs(
            requested.from_geometry,
            requested.from_nodes,
            requested.arc.from_port,
            &mut pairs,
        )?;
        let to = collect_port_contact_pairs(
            requested.to_geometry,
            requested.to_nodes,
            requested.arc.to_port,
            &mut pairs,
        )?;
        match requested.arc.hand {
            IncidenceHand::With => {
                pairs.insert(
                    regional_pair_key(from.place, to.place),
                    (from.place, to.place),
                );
            }
            IncidenceHand::Against => {
                pairs.insert(
                    regional_pair_key(to.place, from.place),
                    (to.place, from.place),
                );
            }
        }
    }
    Ok(pairs.into_values().collect())
}

/// One current physically enacted against the immutable standing-before surface.  The next live
/// snapshot is returned even for a terminal current and simply dissipates at machine commit.
pub struct ExecutedLiveCurrent {
    lineage: CurrentLineage,
    next: LiveCarrierSnapshot,
    pending_dark: Cog,
    consequence: EventEmanation,
    emissions: Vec<FeltEmission>,
    incidences: Vec<EventIncidenceRadiation>,
    contributions: Vec<(Place, RegionalForm)>,
}

impl ExecutedLiveCurrent {
    pub fn new(
        lineage: CurrentLineage,
        next: LiveCarrierSnapshot,
        pending_dark: Cog,
        consequence: EventEmanation,
        emissions: Vec<FeltEmission>,
        incidences: Vec<EventIncidenceRadiation>,
        contributions: Vec<(Place, RegionalForm)>,
    ) -> Self {
        Self {
            lineage,
            next,
            pending_dark,
            consequence,
            emissions,
            incidences,
            contributions,
        }
    }

    pub const fn lineage(&self) -> CurrentLineage {
        self.lineage
    }

    pub const fn next(&self) -> &LiveCarrierSnapshot {
        &self.next
    }

    pub const fn pending_dark(&self) -> Cog {
        self.pending_dark
    }

    pub const fn consequence(&self) -> EventEmanation {
        self.consequence
    }

    pub fn emissions(&self) -> &[FeltEmission] {
        &self.emissions
    }

    pub fn incidences(&self) -> &[EventIncidenceRadiation] {
        &self.incidences
    }

    pub fn contributions(&self) -> &[(Place, RegionalForm)] {
        &self.contributions
    }

    fn into_parts(
        self,
    ) -> (
        CurrentLineage,
        LiveCarrierSnapshot,
        Cog,
        EventEmanation,
        Vec<FeltEmission>,
        Vec<EventIncidenceRadiation>,
        Vec<(Place, RegionalForm)>,
    ) {
        (
            self.lineage,
            self.next,
            self.pending_dark,
            self.consequence,
            self.emissions,
            self.incidences,
            self.contributions,
        )
    }
}

/// One directed meeting formed by the same physical executor that mounted its target's pre-event
/// body.  The machine validates correspondence and integrates the returned crossing; it does not
/// reconstruct this contact after conduct.
#[derive(Clone, Copy)]
pub struct ExecutedDirectedRelation {
    relation: DirectedCurrentRelation,
    contact: DirectedEventContact,
}

/// One regional cell physically completed by the same mounted receiver which formed its pins.
/// The machine integrates this constituent directly and never reconstructs it from `arcs`.
pub struct ExecutedRegionalRelation {
    receiver: CurrentLineage,
    arcs: Vec<RegionalArcRadiation>,
    touched: Vec<usize>,
    constituent: LiveConstituent,
    cell_origins: Vec<Option<SharedOccurrenceKey>>,
    outgoing_factor_boundaries: Option<Vec<usize>>,
    commit_component: bool,
    support_transitions: Vec<Vec<LiveBoundaryTransition>>,
    front_depth: u32,
}

impl ExecutedRegionalRelation {
    pub fn new(
        receiver: CurrentLineage,
        arcs: Vec<RegionalArcRadiation>,
        touched: Vec<usize>,
        constituent: LiveConstituent,
    ) -> Self {
        let cell_origins = vec![None; constituent.cells().len()];
        let support_transitions = constituent_support_transitions(&constituent);
        Self::with_outgoing_factor(
            receiver,
            arcs,
            touched,
            constituent,
            cell_origins,
            None,
            true,
            support_transitions,
            0,
        )
    }

    fn with_outgoing_factor(
        receiver: CurrentLineage,
        arcs: Vec<RegionalArcRadiation>,
        touched: Vec<usize>,
        constituent: LiveConstituent,
        cell_origins: Vec<Option<SharedOccurrenceKey>>,
        outgoing_factor_boundaries: Option<Vec<usize>>,
        commit_component: bool,
        support_transitions: Vec<Vec<LiveBoundaryTransition>>,
        front_depth: u32,
    ) -> Self {
        Self {
            receiver,
            arcs,
            touched,
            constituent,
            cell_origins,
            outgoing_factor_boundaries,
            commit_component,
            support_transitions,
            front_depth,
        }
    }

    pub const fn receiver(&self) -> CurrentLineage {
        self.receiver
    }

    pub fn arcs(&self) -> &[RegionalArcRadiation] {
        &self.arcs
    }

    /// Event-transient storage ordinals of the immutable Standing factors physically imported
    /// while this replacement was formed. They are consumed by machine commit and never radiate.
    pub fn touched(&self) -> &[usize] {
        &self.touched
    }

    pub const fn constituent(&self) -> &LiveConstituent {
        &self.constituent
    }

    fn into_parts(
        self,
    ) -> (
        CurrentLineage,
        Vec<RegionalArcRadiation>,
        Vec<usize>,
        LiveConstituent,
        Vec<Option<SharedOccurrenceKey>>,
        Option<Vec<usize>>,
        bool,
        Vec<Vec<LiveBoundaryTransition>>,
        u32,
    ) {
        (
            self.receiver,
            self.arcs,
            self.touched,
            self.constituent,
            self.cell_origins,
            self.outgoing_factor_boundaries,
            self.commit_component,
            self.support_transitions,
            self.front_depth,
        )
    }
}

fn constituent_support_transitions(
    constituent: &LiveConstituent,
) -> Vec<Vec<LiveBoundaryTransition>> {
    constituent
        .support_factor_boundary_sets()
        .into_iter()
        .map(|boundaries| {
            boundaries
                .into_iter()
                .map(|boundary| {
                    constituent
                        .boundary_transition(
                            usize::try_from(boundary)
                                .expect("u32 boundary is addressable on this cpu"),
                        )
                        .expect("a validated factor references one complete boundary")
                })
                .collect()
        })
        .collect()
}

impl ExecutedDirectedRelation {
    pub const fn new(relation: DirectedCurrentRelation, contact: DirectedEventContact) -> Self {
        Self { relation, contact }
    }

    pub const fn relation(self) -> DirectedCurrentRelation {
        self.relation
    }

    pub const fn contact(self) -> DirectedEventContact {
        self.contact
    }
}

/// Complete physical result of one contemporary event.  Current enactments and directed meetings
/// cross one executor boundary together; only [`LiveCurrentMachine`] owns successor integration.
pub struct ExecutedContemporaryEvent {
    currents: Vec<ExecutedLiveCurrent>,
    relations: Vec<ExecutedDirectedRelation>,
    regional: Vec<ExecutedRegionalRelation>,
}

impl ExecutedContemporaryEvent {
    pub fn new(
        currents: Vec<ExecutedLiveCurrent>,
        relations: Vec<ExecutedDirectedRelation>,
    ) -> Self {
        Self {
            currents,
            relations,
            regional: Vec::new(),
        }
    }

    pub fn with_regional(
        currents: Vec<ExecutedLiveCurrent>,
        relations: Vec<ExecutedDirectedRelation>,
        regional: Vec<ExecutedRegionalRelation>,
    ) -> Self {
        Self {
            currents,
            relations,
            regional,
        }
    }

    pub fn currents(&self) -> &[ExecutedLiveCurrent] {
        &self.currents
    }

    pub fn relations(&self) -> &[ExecutedDirectedRelation] {
        &self.relations
    }

    pub fn regional(&self) -> &[ExecutedRegionalRelation] {
        &self.regional
    }

    fn into_parts(
        self,
    ) -> (
        Vec<ExecutedLiveCurrent>,
        Vec<ExecutedDirectedRelation>,
        Vec<ExecutedRegionalRelation>,
    ) {
        (self.currents, self.relations, self.regional)
    }
}

/// Physical realization of the event-local body transition.  Implementations may own a resident
/// cpu pool, CUDA context/module/buffers, or another substrate, but receive no source material,
/// cut, journal, receipt, or standing-after authority.
pub trait LiveCurrentExecutor {
    fn enact(
        &mut self,
        physical_revision: u64,
        standing: &SparseStandingSurface,
        currents: &[CurrentExecutionRequest<'_>],
        relations: &[DirectedExecutionRequest],
        regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError>;

    /// Settle an already-prepared logical successor into discardable substrate residency.  The
    /// machine calls this only after it has validated the complete event and reserved every
    /// fallible logical result.  Implementations may refuse settlement, but may neither alter nor
    /// reconstruct `successor`.
    fn settle_physical_successor(
        &mut self,
        _physical_revision: u64,
        _successor: &SparseStandingSurface,
    ) -> Result<(), LiveCurrentError> {
        Ok(())
    }
}

#[derive(Default)]
pub struct CpuLiveCurrentExecutor;

enum LineageBody {
    /// The first actual event has located K's anchor but has not crossed yet.
    Seed {
        first_event: Place,
        anchor: Place,
        carrier: GrowingCarrier,
    },
    Live(LiveCarrierSnapshot),
}

struct LiveLineage {
    body: LineageBody,
    pending_dark: Cog,
}

struct EventOutput {
    emissions: Vec<FeltEmission>,
    refused: bool,
}

impl EventOutput {
    fn new() -> Self {
        Self {
            emissions: Vec::new(),
            refused: false,
        }
    }
}

fn event_node_words(node: Node) -> [u32; NODE_WORDS] {
    let mut words = [0u32; NODE_WORDS];
    for (word, value) in words.iter_mut().enumerate() {
        *value = node_packed_word(node, word);
    }
    words
}

/// Canonical outward ordering for incidence radiation only. Conduct remains co-present against
/// one receiver; this sort cannot parent a cell. It prevents storage order from leaking into the
/// returned testimony by ordering on declared stage/grain/slot and complete geometric faces.
/// Exact storage-gauge-independent incidence order for one borrowed source complex. Physical
/// executors use this order only to return radiation; the complex crosses the body at one grain.
pub fn canonical_event_incidences(
    complex: EventComplex<'_>,
) -> Result<Vec<OrientedIncidence>, LiveCurrentError> {
    let mut incidences = Vec::new();
    incidences
        .try_reserve_exact(complex.incidences().len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    incidences.extend_from_slice(complex.incidences());
    incidences.sort_unstable_by_key(|incidence| {
        let from = complex
            .cell(incidence.from())
            .expect("a validated incidence retains its source cell");
        let to = complex
            .cell(incidence.to())
            .expect("a validated incidence retains its target cell");
        let kind = match incidence.kind() {
            body::incidence::IncidenceKind::Boundary => 0u32,
            body::incidence::IncidenceKind::Dependency => 1u32,
            body::incidence::IncidenceKind::RewriteInterface => 2u32,
        };
        (
            (
                to.dependency_rank(),
                to.dimension(),
                to.grain(),
                incidence.slot(),
                kind,
                incidence.hand().coefficient(),
            ),
            (from.dependency_rank(), from.dimension(), from.grain()),
            (event_node_words(from.node()), event_node_words(to.node())),
            (incidence.from().ordinal(), incidence.to().ordinal()),
        )
    });
    Ok(incidences)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum BorrowedRegionalCell {
    Atom(CurrentLineage),
    Complex(CurrentLineage, EventCellId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct BorrowedRegionalIncidence {
    lineage: CurrentLineage,
    target: EventCellId,
    slot: u32,
}

struct RegionalCellBuilder {
    cells: Vec<LiveCell>,
    cell_origins: Vec<SharedOccurrenceKey>,
    incidences: Vec<LiveIncidence>,
    pins: Vec<LivePin>,
    cell_map: BTreeMap<BorrowedRegionalCell, u32>,
    incidence_map: BTreeMap<BorrowedRegionalIncidence, u32>,
    pin_map: BTreeMap<Vec<u32>, u32>,
}

struct BorrowedPortPath {
    root: u32,
    node: Node,
    trace: Vec<u32>,
}

struct BorrowedBoundary {
    slot: u32,
    hand: IncidenceHand,
    paths: Vec<Vec<u32>>,
}

struct CompletedRegionalCell {
    constituent: LiveConstituent,
    cell_origins: Vec<Option<SharedOccurrenceKey>>,
}

impl RegionalCellBuilder {
    fn new() -> Self {
        Self {
            cells: Vec::new(),
            cell_origins: Vec::new(),
            incidences: Vec::new(),
            pins: Vec::new(),
            cell_map: BTreeMap::new(),
            incidence_map: BTreeMap::new(),
            pin_map: BTreeMap::new(),
        }
    }

    fn atom(&mut self, lineage: CurrentLineage) -> Result<u32, LiveCurrentError> {
        let key = BorrowedRegionalCell::Atom(lineage);
        if let Some(cell) = self.cell_map.get(&key) {
            return Ok(*cell);
        }
        let cell =
            u32::try_from(self.cells.len()).map_err(|_| LiveCurrentError::ResourceReservation)?;
        self.cells
            .try_reserve(1)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        self.cell_origins
            .try_reserve(1)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        self.cells.push(LiveCell::new(0, 0, 0));
        self.cell_origins
            .push(SharedOccurrenceKey::new(0, lineage.ordinal(), 0));
        self.cell_map.insert(key, cell);
        Ok(cell)
    }

    fn ensure_complex_cell<F>(
        &mut self,
        lineage: CurrentLineage,
        complex: EventComplex<'_>,
        nodes: &EventNodeAtlas,
        id: EventCellId,
        contact: &mut F,
    ) -> Result<u32, LiveCurrentError>
    where
        F: FnMut(Place, Place) -> Result<DirectedEventContact, LiveCurrentError>,
    {
        let key = BorrowedRegionalCell::Complex(lineage, id);
        if let Some(cell) = self.cell_map.get(&key) {
            return Ok(*cell);
        }
        let source = complex.cell(id).ok_or(EventComplexError::MissingCell(id))?;
        let mut incoming = Vec::new();
        incoming
            .try_reserve_exact(complex.incidences().len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        incoming.extend(
            complex
                .incidences()
                .iter()
                .copied()
                .filter(|incidence| incidence.to() == id),
        );
        incoming.sort_unstable_by_key(|incidence| incidence.slot());
        for incidence in &incoming {
            self.ensure_complex_cell(lineage, complex, nodes, incidence.from(), contact)?;
        }

        let cell =
            u32::try_from(self.cells.len()).map_err(|_| LiveCurrentError::ResourceReservation)?;
        self.cells
            .try_reserve(1)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        self.cell_origins
            .try_reserve(1)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        self.cells.push(LiveCell::new(
            source.dependency_rank(),
            source.dimension(),
            source.grain(),
        ));
        self.cell_origins
            .push(SharedOccurrenceKey::new(1, lineage.ordinal(), id.ordinal()));
        self.cell_map.insert(key, cell);

        for incidence in incoming {
            let incidence_key = BorrowedRegionalIncidence {
                lineage,
                target: id,
                slot: incidence.slot(),
            };
            if self.incidence_map.contains_key(&incidence_key) {
                continue;
            }
            let from = *self
                .cell_map
                .get(&BorrowedRegionalCell::Complex(lineage, incidence.from()))
                .ok_or(LiveCurrentError::RegionalTopology(lineage))?;
            let (from_node, to_node) = nodes.incidence_nodes(incidence)?;
            let formed = contact(from_node.place, to_node.place)?;
            let pin = self.pin(LivePin::from_contact(formed))?;
            let kind = match incidence.kind() {
                IncidenceKind::Boundary => LiveIncidenceKind::Boundary,
                IncidenceKind::Dependency => LiveIncidenceKind::Dependency,
                IncidenceKind::RewriteInterface => LiveIncidenceKind::RewriteInterface,
            };
            let at = self.incidence(LiveIncidence::new(from, cell, kind, incidence.hand(), pin))?;
            self.incidence_map.insert(incidence_key, at);
        }
        Ok(cell)
    }

    fn trace_complex_cell(
        &self,
        lineage: CurrentLineage,
        complex: EventComplex<'_>,
        id: EventCellId,
        trace: &mut Vec<u32>,
    ) -> Result<(), LiveCurrentError> {
        let mut incoming = Vec::new();
        incoming
            .try_reserve_exact(complex.incidences().len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        incoming.extend(
            complex
                .incidences()
                .iter()
                .copied()
                .filter(|incidence| incidence.to() == id),
        );
        incoming.sort_unstable_by_key(|incidence| incidence.slot());
        for incidence in incoming {
            self.trace_complex_cell(lineage, complex, incidence.from(), trace)?;
            let at = *self
                .incidence_map
                .get(&BorrowedRegionalIncidence {
                    lineage,
                    target: id,
                    slot: incidence.slot(),
                })
                .ok_or(LiveCurrentError::RegionalTopology(lineage))?;
            trace
                .try_reserve(1)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            trace.push(at);
        }
        Ok(())
    }

    fn port<F>(
        &mut self,
        lineage: CurrentLineage,
        geometry: CurrentGeometry<'_>,
        nodes: Option<&EventNodeAtlas>,
        port: CurrentBoundaryPort,
        contact: &mut F,
    ) -> Result<BorrowedPortPath, LiveCurrentError>
    where
        F: FnMut(Place, Place) -> Result<DirectedEventContact, LiveCurrentError>,
    {
        match (geometry, port) {
            (CurrentGeometry::Cell(relation), CurrentBoundaryPort::Cell) => Ok(BorrowedPortPath {
                root: self.atom(lineage)?,
                node: atom_node(relation.cog()),
                trace: Vec::new(),
            }),
            (CurrentGeometry::Complex(complex), CurrentBoundaryPort::Ingress(slot))
            | (CurrentGeometry::Complex(complex), CurrentBoundaryPort::Exposed(slot)) => {
                let nodes = nodes.ok_or(LiveCurrentError::UnsupportedEventComplex)?;
                let kind = match port {
                    CurrentBoundaryPort::Ingress(_) => EventPortKind::Ingress,
                    CurrentBoundaryPort::Exposed(_) => EventPortKind::Exposed,
                    CurrentBoundaryPort::Cell => unreachable!(),
                };
                let selected = complex
                    .port(kind, slot)
                    .ok_or(EventComplexError::MissingPort(kind, slot))?;
                let root =
                    self.ensure_complex_cell(lineage, complex, nodes, selected.cell(), contact)?;
                let mut trace = Vec::new();
                self.trace_complex_cell(lineage, complex, selected.cell(), &mut trace)?;
                Ok(BorrowedPortPath {
                    root,
                    node: nodes.cell_node(selected.cell())?,
                    trace,
                })
            }
            _ => Err(EventComplexError::InvalidPortSpecies.into()),
        }
    }

    fn pin(&mut self, pin: LivePin) -> Result<u32, LiveCurrentError> {
        // Pins are shared interface/contact objects; actual multiplicity remains in the distinct
        // incidence rows which point at them. Interface capability participates in equality, so
        // equal projected geometry cannot merge source-declared distinct interfaces.
        let key = pin.exact_words();
        if let Some(at) = self.pin_map.get(&key) {
            debug_assert_eq!(self.pins[*at as usize], pin);
            return Ok(*at);
        }
        let at =
            u32::try_from(self.pins.len()).map_err(|_| LiveCurrentError::ResourceReservation)?;
        self.pins
            .try_reserve(1)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        self.pins.push(pin);
        self.pin_map.insert(key, at);
        Ok(at)
    }

    fn incidence(&mut self, incidence: LiveIncidence) -> Result<u32, LiveCurrentError> {
        let at = u32::try_from(self.incidences.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        self.incidences
            .try_reserve(1)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        self.incidences.push(incidence);
        Ok(at)
    }

    fn complete(
        self,
        receiver: CurrentLineage,
        grain: u32,
        borrowed: Vec<BorrowedBoundary>,
        support_sections: Option<Vec<LiveSupportSection>>,
    ) -> Result<CompletedRegionalCell, LiveCurrentError> {
        let mut axis_for_pin = vec![None; self.pins.len()];
        let mut axis_anchor = vec![false; self.pins.len()];
        let mut next_axis = 1u32;
        let mut boundaries = Vec::new();
        boundaries
            .try_reserve_exact(borrowed.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        let mut exposure = vec![0i64; self.pins.len()];
        let mut transport_arm = vec![false; self.pins.len()];
        let mut incidence_use = vec![0u32; self.incidences.len()];
        for boundary in borrowed {
            let mut paths = Vec::new();
            paths
                .try_reserve_exact(boundary.paths.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for path in boundary.paths {
                let mut active = LocalAxis::new(0);
                let mut steps = Vec::new();
                steps
                    .try_reserve_exact(path.len())
                    .map_err(|_| LiveCurrentError::ResourceReservation)?;
                for incidence_at in path {
                    let incidence_index = usize::try_from(incidence_at)
                        .map_err(|_| LiveCurrentError::ResourceReservation)?;
                    let incidence = *self
                        .incidences
                        .get(incidence_index)
                        .ok_or(LiveCurrentError::RegionalTopology(receiver))?;
                    incidence_use[incidence_index] = incidence_use[incidence_index]
                        .checked_add(1)
                        .ok_or(LiveCurrentError::ResourceReservation)?;
                    let pin_at = usize::try_from(incidence.pin())
                        .map_err(|_| LiveCurrentError::ResourceReservation)?;
                    let pin = self
                        .pins
                        .get(pin_at)
                        .ok_or(LiveCurrentError::RegionalTopology(receiver))?;
                    let mut effective_winding = body::channel::WindingQuantum::None;
                    if pin.is_found() {
                        if let Some(axis) = axis_for_pin[pin_at] {
                            active = axis;
                        } else {
                            let axis = LocalAxis::new(next_axis);
                            next_axis = next_axis
                                .checked_add(1)
                                .ok_or(LiveCurrentError::ResourceReservation)?;
                            axis_for_pin[pin_at] = Some(axis);
                            axis_anchor[pin_at] = true;
                            active = axis;
                            effective_winding = pin
                                .formed()
                                .map(|formed| formed.winding())
                                .ok_or(LiveCurrentError::RegionalTopology(receiver))?;
                        }
                    }
                    steps.push(LivePathStep::new(incidence_at, active, effective_winding));
                    if incidence.kind() == LiveIncidenceKind::Transport {
                        transport_arm[pin_at] = true;
                        let signed = incidence.hand().coefficient();
                        exposure[pin_at] = exposure[pin_at]
                            .checked_add(signed)
                            .ok_or(LiveCurrentError::ResourceReservation)?;
                    }
                }
                paths.push(LivePath::from_steps(steps, &self.incidences, &self.pins)?);
            }
            boundaries.push(LiveBoundary::new(boundary.hand, paths));
        }

        let cycle = cellular_cycle_edges(self.cells.len(), &self.incidences, &incidence_use)?;
        let mut keep_incidence = vec![false; self.incidences.len()];
        let mut keep_pin = vec![false; self.pins.len()];
        let mut keep_cell = vec![false; self.cells.len()];
        for (at, incidence) in self.incidences.iter().copied().enumerate() {
            let pin_at = usize::try_from(incidence.pin())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            let consequential = incidence_use[at] > 1
                || cycle[at]
                || exposure[pin_at] != 0
                || axis_anchor[pin_at]
                || self.pins[pin_at].is_open();
            if !consequential {
                continue;
            }
            keep_incidence[at] = true;
            keep_pin[pin_at] = true;
            keep_cell[usize::try_from(incidence.from())
                .map_err(|_| LiveCurrentError::ResourceReservation)?] = true;
            keep_cell[usize::try_from(incidence.to())
                .map_err(|_| LiveCurrentError::ResourceReservation)?] = true;
        }

        let mut cell_map = vec![None; self.cells.len()];
        let mut cells = Vec::new();
        let mut cell_origins = Vec::new();
        for (at, cell) in self.cells.iter().copied().enumerate() {
            if keep_cell[at] {
                let rebased = u32::try_from(cells.len())
                    .map_err(|_| LiveCurrentError::ResourceReservation)?;
                cell_map[at] = Some(rebased);
                cells.push(cell);
                cell_origins.push(Some(self.cell_origins[at]));
            }
        }
        let apex_rank = self
            .cells
            .iter()
            .map(|cell| cell.dependency_rank())
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let apex_dimension = self
            .cells
            .iter()
            .map(|cell| cell.dimension())
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        // Completion itself is one higher live cell. Lower cells remain only when an exposed pin,
        // shared branch, open residual, or cycle still factors through them.
        cells.push(LiveCell::new(apex_rank, apex_dimension, grain));
        cell_origins.push(None);

        let mut pin_map = vec![None; self.pins.len()];
        let mut pins = Vec::new();
        for (at, pin) in self.pins.iter().cloned().enumerate() {
            if keep_pin[at] {
                let rebased =
                    u32::try_from(pins.len()).map_err(|_| LiveCurrentError::ResourceReservation)?;
                pin_map[at] = Some(rebased);
                pins.push(pin);
            }
        }

        let mut incidence_map = vec![None; self.incidences.len()];
        let mut incidences = Vec::new();
        for (at, incidence) in self.incidences.iter().copied().enumerate() {
            if !keep_incidence[at] {
                continue;
            }
            let from = cell_map[usize::try_from(incidence.from())
                .map_err(|_| LiveCurrentError::ResourceReservation)?]
            .ok_or(LiveCurrentError::RegionalTopology(receiver))?;
            let to = cell_map[usize::try_from(incidence.to())
                .map_err(|_| LiveCurrentError::ResourceReservation)?]
            .ok_or(LiveCurrentError::RegionalTopology(receiver))?;
            let pin = pin_map[usize::try_from(incidence.pin())
                .map_err(|_| LiveCurrentError::ResourceReservation)?]
            .ok_or(LiveCurrentError::RegionalTopology(receiver))?;
            let rebased = u32::try_from(incidences.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            incidence_map[at] = Some(rebased);
            incidences.push(LiveIncidence::new(
                from,
                to,
                incidence.kind(),
                incidence.hand(),
                pin,
            ));
        }

        let mut completed_boundaries = Vec::new();
        completed_boundaries
            .try_reserve_exact(boundaries.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for boundary in boundaries {
            let mut completed_paths = Vec::new();
            completed_paths
                .try_reserve_exact(boundary.paths().len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for path in boundary.paths() {
                let mut retained = Vec::new();
                for step in path.steps() {
                    let old = usize::try_from(step.incidence())
                        .map_err(|_| LiveCurrentError::ResourceReservation)?;
                    if let Some(incidence) = incidence_map[old] {
                        retained.push(LivePathStep::new(incidence, step.support(), step.winding()));
                    }
                }
                completed_paths.push(path.clone().fold_interior(retained));
            }
            completed_boundaries.push(LiveBoundary::new(boundary.hand(), completed_paths));
        }

        let mut exposed = Vec::new();
        for (at, ((pin, coefficient), transport_arm)) in self
            .pins
            .iter()
            .zip(&exposure)
            .zip(&transport_arm)
            .enumerate()
        {
            if !*transport_arm || (*coefficient == 0 && !pin.is_open()) {
                continue;
            }
            if let Some(rebased) = pin_map[at] {
                exposed.push(rebased);
            }
        }
        let constituent = match support_sections {
            Some(sections) => LiveConstituent::with_support_sections(
                grain,
                next_axis,
                cells,
                incidences,
                pins,
                completed_boundaries,
                exposed,
                sections,
            ),
            None => LiveConstituent::new(
                grain,
                next_axis,
                cells,
                incidences,
                pins,
                completed_boundaries,
                exposed,
            ),
        }
        .map_err(LiveCurrentError::from)?;
        Ok(CompletedRegionalCell {
            constituent,
            cell_origins,
        })
    }
}

/// Complete one regional constituent from contacts already formed by its physical receiver.
/// `contact` is called only for the exact canonical population returned by
/// [`regional_contact_pairs`]; the membrane never reconstructs a missing card result.
pub fn form_executed_regional_relation<F>(
    source_grain: u32,
    request: &RegionalExecutionRequest<'_>,
    mut contact: F,
) -> Result<ExecutedRegionalRelation, LiveCurrentError>
where
    F: FnMut(Place, Place) -> Result<DirectedEventContact, LiveCurrentError>,
{
    let mut builder = RegionalCellBuilder::new();
    let mut radiation = Vec::new();
    radiation
        .try_reserve_exact(request.arcs.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    let mut boundaries: Vec<BorrowedBoundary> = Vec::new();
    for requested in &request.arcs {
        let arc = &requested.arc;
        let from = builder.port(
            arc.from,
            requested.from_geometry,
            requested.from_nodes,
            arc.from_port,
            &mut contact,
        )?;
        let to = builder.port(
            arc.to,
            requested.to_geometry,
            requested.to_nodes,
            arc.to_port,
            &mut contact,
        )?;
        let formed = match arc.hand {
            IncidenceHand::With => contact(from.node.place, to.node.place)?,
            IncidenceHand::Against => contact(to.node.place, from.node.place)?,
        };
        let pin = builder.pin(LivePin::from_interface_contact(
            formed,
            arc.interface.clone(),
        ))?;
        let cross = builder.incidence(LiveIncidence::new(
            from.root,
            to.root,
            LiveIncidenceKind::Transport,
            arc.hand,
            pin,
        ))?;
        let mut path = Vec::new();
        let path_extent = from
            .trace
            .len()
            .checked_add(to.trace.len())
            .and_then(|extent| extent.checked_add(1))
            .ok_or(LiveCurrentError::ResourceReservation)?;
        path.try_reserve_exact(path_extent)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        match arc.hand {
            IncidenceHand::With => {
                path.extend_from_slice(&from.trace);
                path.extend_from_slice(&to.trace);
            }
            IncidenceHand::Against => {
                path.extend_from_slice(&to.trace);
                path.extend_from_slice(&from.trace);
            }
        }
        path.push(cross);
        match boundaries.last_mut() {
            Some(boundary) if boundary.slot == arc.boundary_slot => boundary.paths.push(path),
            _ => boundaries.push(BorrowedBoundary {
                slot: arc.boundary_slot,
                hand: arc.hand,
                paths: vec![path],
            }),
        }
        radiation.push(RegionalArcRadiation {
            arc: arc.clone(),
            contact: formed,
        });
    }
    let grain = source_grain
        .checked_add(1)
        .ok_or(LiveCurrentError::ResourceReservation)?;
    let outgoing_factor_boundaries = request
        .outgoing_factor_slots
        .map(|slots| {
            let mut selected = Vec::new();
            selected
                .try_reserve_exact(slots.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for slot in slots {
                selected.push(
                    boundaries
                        .binary_search_by_key(slot, |boundary| boundary.slot)
                        .map_err(|_| LiveCurrentError::RegionalTopology(request.receiver))?,
                );
            }
            Ok::<Vec<usize>, LiveCurrentError>(selected)
        })
        .transpose()?;
    let support_sections = request
        .support_sections
        .map(|sections| {
            let mut mapped = Vec::new();
            mapped
                .try_reserve_exact(sections.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for section in sections {
                let mut selected = Vec::new();
                selected
                    .try_reserve_exact(section.boundary_slots.len())
                    .map_err(|_| LiveCurrentError::ResourceReservation)?;
                for slot in section.boundary_slots {
                    selected.push(
                        u32::try_from(
                            boundaries
                                .binary_search_by_key(slot, |boundary| boundary.slot)
                                .map_err(|_| {
                                    LiveCurrentError::RegionalTopology(request.receiver)
                                })?,
                        )
                        .map_err(|_| LiveCurrentError::ResourceReservation)?,
                    );
                }
                selected.sort_unstable();
                selected.dedup();
                mapped.push(LiveSupportSection::new(selected));
            }
            mapped.sort();
            mapped.dedup();
            Ok::<Vec<LiveSupportSection>, LiveCurrentError>(mapped)
        })
        .transpose()?;
    let completed = builder.complete(request.receiver, grain, boundaries, support_sections)?;
    let support_transitions = constituent_support_transitions(&completed.constituent);
    Ok(ExecutedRegionalRelation::with_outgoing_factor(
        request.receiver,
        radiation,
        Vec::new(),
        completed.constituent,
        completed.cell_origins,
        outgoing_factor_boundaries,
        true,
        support_transitions,
        0,
    ))
}

/// Close every co-present regional germ as one exact component population against the immutable
/// standing-before surface. The live machine calls this once after its physical executor returns
/// all receiver-local cells; the executor never owns or reconstructs the shared successor.
struct CoalescedRegionalGerm {
    members: Vec<usize>,
    constituent: LiveConstituent,
    section_lineages: Vec<BTreeSet<PopulationSectionOrigin>>,
}

fn coalesce_regional_occurrence_population(
    regional: &[ExecutedRegionalRelation],
) -> Result<Vec<CoalescedRegionalGerm>, LiveCurrentError> {
    let mut parent: Vec<usize> = (0..regional.len()).collect();
    let mut owner: BTreeMap<SharedOccurrenceKey, usize> = BTreeMap::new();

    fn root(parent: &mut [usize], at: usize) -> usize {
        if parent[at] != at {
            let found = root(parent, parent[at]);
            parent[at] = found;
        }
        parent[at]
    }

    fn join(parent: &mut [usize], left: usize, right: usize) {
        let left = root(parent, left);
        let right = root(parent, right);
        if left == right {
            return;
        }
        if left < right {
            parent[right] = left;
        } else {
            parent[left] = right;
        }
    }

    for (at, relation) in regional.iter().enumerate() {
        if relation.cell_origins.len() != relation.constituent.cells().len() {
            return Err(LiveCurrentError::RegionalTopology(relation.receiver));
        }
        for key in relation.cell_origins.iter().flatten().copied() {
            if let Some(prior) = owner.insert(key, at) {
                join(&mut parent, prior, at);
            }
        }
    }
    for at in 0..parent.len() {
        parent[at] = root(&mut parent, at);
    }

    let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (at, component) in parent.into_iter().enumerate() {
        groups.entry(component).or_default().push(at);
    }

    let mut coalesced = Vec::new();
    coalesced
        .try_reserve_exact(groups.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    for (_, mut members) in groups {
        let mut ordered = Vec::new();
        ordered
            .try_reserve_exact(members.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for member in &members {
            ordered.push((
                regional[*member].constituent.native_words()?,
                regional[*member].receiver.ordinal(),
                *member,
            ));
        }
        ordered.sort_by(|left, right| (&left.0, left.1, left.2).cmp(&(&right.0, right.1, right.2)));
        let (constituent, section_lineages) = if let [only] = ordered.as_slice() {
            let constituent = regional[only.2].constituent.clone();
            let section_lineages = (0..constituent.support_factor_count())
                .map(|section| BTreeSet::from([PopulationSectionOrigin::new(only.2, section)]))
                .collect();
            (constituent, section_lineages)
        } else {
            let cofaces = ordered
                .iter()
                .map(|(_, _, at)| {
                    (
                        &regional[*at].constituent,
                        regional[*at].cell_origins.as_slice(),
                    )
                })
                .collect::<Vec<_>>();
            let constituent = LiveConstituent::union_shared_event_cofaces(&cofaces)?;
            let mut boundary_offset = 0_u32;
            let mut lineage_by_section =
                BTreeMap::<LiveSupportExpression, BTreeSet<PopulationSectionOrigin>>::new();
            for (_, _, member) in &ordered {
                let body = &regional[*member].constituent;
                for (section_at, expression) in body
                    .support_family()
                    .root_expressions()
                    .map_err(LiveConstituentError::from)?
                    .into_iter()
                    .enumerate()
                {
                    lineage_by_section
                        .entry(
                            expression
                                .rebased(boundary_offset)
                                .map_err(LiveConstituentError::from)?,
                        )
                        .or_default()
                        .insert(PopulationSectionOrigin::new(*member, section_at));
                }
                boundary_offset = boundary_offset
                    .checked_add(
                        u32::try_from(body.boundaries().len())
                            .map_err(|_| LiveCurrentError::ResourceReservation)?,
                    )
                    .ok_or(LiveCurrentError::ResourceReservation)?;
            }
            let section_lineages = constituent
                .support_family()
                .root_expressions()
                .map_err(LiveConstituentError::from)?
                .into_iter()
                .map(|expression| {
                    lineage_by_section.remove(&expression).ok_or(
                        LiveCurrentError::RegionalTopology(regional[ordered[0].2].receiver),
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            if !lineage_by_section.is_empty() {
                return Err(LiveCurrentError::RegionalTopology(
                    regional[ordered[0].2].receiver,
                ));
            }
            (constituent, section_lineages)
        };
        members.sort_unstable();
        coalesced.push(CoalescedRegionalGerm {
            members,
            constituent,
            section_lineages,
        });
    }
    coalesced.sort_by(|left, right| left.members.cmp(&right.members));
    Ok(coalesced)
}

fn close_executed_regional_population(
    standing: &SparseStandingSurface,
    aperture: &StandingIncidenceAperture,
    mut regional: Vec<ExecutedRegionalRelation>,
) -> Result<Vec<ExecutedRegionalRelation>, LiveCurrentError> {
    if regional.is_empty() {
        return Ok(regional);
    }
    let coalesced = coalesce_regional_occurrence_population(&regional)?;
    let germs: Vec<LiveConstituent> = coalesced
        .iter()
        .map(|germ| germ.constituent.clone())
        .collect();
    let germ_section_lineages = coalesced
        .iter()
        .map(|germ| germ.section_lineages.clone())
        .collect::<Vec<_>>();
    let closure = LiveConstituent::close_population_against_with_aperture_and_section_lineages(
        &germs,
        standing.constituent_standing(),
        aperture,
        &germ_section_lineages,
    )?;
    let mut resolved = Vec::new();
    resolved
        .try_reserve_exact(regional.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    resolved.resize_with(regional.len(), || None);
    for component in closure {
        let returned_factor_transitions = constituent_support_transitions(component.replacement());
        let mut members = Vec::new();
        for germ in component.members() {
            members.extend_from_slice(
                &coalesced
                    .get(*germ)
                    .ok_or(LiveCurrentError::ResourceReservation)?
                    .members,
            );
        }
        members.sort_unstable();
        members.dedup();
        let commit_member = *members
            .first()
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let factor_members = members
            .iter()
            .copied()
            .filter(|member| regional[*member].outgoing_factor_boundaries.is_some())
            .collect::<Vec<_>>();
        if factor_members.len() > 1 {
            return Err(LiveCurrentError::RegionalTopology(
                regional[factor_members[0]].receiver,
            ));
        }
        let replacement = if let [factor_member] = factor_members.as_slice() {
            let raw = regional
                .get(*factor_member)
                .ok_or(LiveCurrentError::ResourceReservation)?;
            if component.touched().is_empty() && members.len() == 1 {
                return Err(LiveCurrentError::RegionalTopology(raw.receiver));
            }
            let selected = raw
                .outgoing_factor_boundaries
                .as_deref()
                .ok_or(LiveCurrentError::RegionalTopology(raw.receiver))?;
            let factor = raw
                .constituent
                .outgoing_boundary_factor(selected, component.replacement().grain())?;
            if !factor.has_same_exposed_boundary(component.replacement())? {
                return Err(LiveCurrentError::RegionalTopology(raw.receiver));
            }
            factor
        } else {
            component.replacement().clone()
        };
        for member in &members {
            let raw = regional
                .get_mut(*member)
                .ok_or(LiveCurrentError::ResourceReservation)?;
            let mut support_transitions = Vec::new();
            support_transitions
                .try_reserve_exact(raw.constituent.support_factor_count())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for source_section in 0..raw.constituent.support_factor_count() {
                let origin = PopulationSectionOrigin::new(*member, source_section);
                let mut returned = Vec::new();
                for (returned_section, lineage) in component.section_lineages().iter().enumerate() {
                    if lineage.contains(&origin) {
                        returned.extend(
                            returned_factor_transitions
                                .get(returned_section)
                                .ok_or(LiveCurrentError::RegionalTopology(raw.receiver))?,
                        );
                    }
                }
                if returned.is_empty() {
                    return Err(LiveCurrentError::RegionalTopology(raw.receiver));
                }
                support_transitions.push(returned);
            }
            resolved[*member] = Some(ExecutedRegionalRelation::with_outgoing_factor(
                raw.receiver,
                core::mem::take(&mut raw.arcs),
                component.touched().to_vec(),
                replacement.clone(),
                vec![None; replacement.cells().len()],
                raw.outgoing_factor_boundaries.take(),
                *member == commit_member,
                support_transitions,
                component.front_depth(),
            ));
        }
    }
    let mut complete = Vec::new();
    complete
        .try_reserve_exact(resolved.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    for (at, relation) in resolved.into_iter().enumerate() {
        complete.push(relation.ok_or_else(|| {
            regional
                .get(at)
                .map_or(LiveCurrentError::ResourceReservation, |raw| {
                    LiveCurrentError::ExecutionMismatch(raw.receiver)
                })
        })?);
    }
    Ok(complete)
}

impl FeltEmissionTarget for EventOutput {
    fn emit(&mut self, emission: FeltEmission) {
        if self.refused {
            return;
        }
        if self.emissions.try_reserve(1).is_err() {
            self.refused = true;
            return;
        }
        self.emissions.push(emission);
    }
}

struct CpuCurrentEnactment {
    current: ExecutedLiveCurrent,
    directed: Vec<(usize, ExecutedDirectedRelation)>,
    regional: Vec<(usize, ExecutedRegionalRelation)>,
}

fn enact_cpu_current(
    standing: &SparseStandingSurface,
    request: CurrentExecutionRequest<'_>,
    relations: &[DirectedExecutionRequest],
    regional: &[RegionalExecutionRequest<'_>],
) -> Result<CpuCurrentEnactment, LiveCurrentError> {
    let mount = request.mount;
    let header = mount.header();
    let mut carrier = mount.carrier().branch_shared();
    let cursor = header.map_or(0, LiveBodyHeader::cursor);
    let next_cursor = cursor
        .checked_add(1)
        .ok_or(LiveCurrentError::CursorExtent)?;
    let mut own = GrowingRankedOwn::new();
    let mut output = EventOutput::new();
    let mut pending_dark = request.pending_dark;
    let mut incidence_radiation = Vec::new();
    let mut directed = Vec::new();
    let mut regional_results = Vec::new();

    let (consequence, next_header) = {
        let body = match header {
            Some(header) => ErosBody::resume_standing_world_ranked_storage_from_live_header(
                standing,
                &mut own,
                header,
                &mut carrier,
            ),
            None => ErosBody::over_standing_world_ranked_storage_from_first_difference(
                standing,
                &mut own,
                mount
                    .seed_anchor()
                    .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?,
                &mut carrier,
            ),
        };
        let mut body = body.ok_or(LiveCurrentError::BodyRefused(request.lineage()))?;
        let source_grain = request.event.geometry.source_grain()?;
        observe_read_depth(source_grain);
        let receiver = body
            .event_receiver_at_source_grain(source_grain)
            .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?;
        if let Some(complex) = request.event.geometry.complex() {
            let nodes = request
                .event_nodes
                .ok_or(LiveCurrentError::UnsupportedEventComplex)?;
            let incidences = canonical_event_incidences(complex)?;
            incidence_radiation
                .try_reserve_exact(incidences.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for incidence in incidences {
                let (from, to) = nodes.incidence_nodes(incidence)?;
                let contact = body.directed_event_contact_at_source_grain(
                    receiver,
                    source_grain,
                    from.place,
                    to.place,
                );
                incidence_radiation.push(EventIncidenceRadiation { incidence, contact });
            }
        }
        for (at, relation) in relations.iter().copied().enumerate() {
            if relation.relation.to != request.lineage() {
                continue;
            }
            observe_pole_placement(&receiver, relation.from, relation.to);
            let contact = body.directed_event_contact_at_source_grain(
                receiver,
                source_grain,
                relation.from,
                relation.to,
            );
            observe_contact_outcome(&contact);
            directed.push((
                at,
                ExecutedDirectedRelation::new(relation.relation, contact),
            ));
        }
        for (at, regional) in regional.iter().enumerate() {
            if regional.receiver != request.lineage() {
                continue;
            }
            regional_results.push((
                at,
                form_executed_regional_relation(source_grain, regional, |from, to| {
                    observe_pole_placement(&receiver, from, to);
                    let contact = body.directed_event_contact_at_source_grain(
                        receiver,
                        source_grain,
                        from,
                        to,
                    );
                    observe_contact_outcome(&contact);
                    Ok(contact)
                })?,
            ));
        }
        let mut consequence = if request.wholly_dark {
            EVENT_WHOLLY_DARK.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
            pending_dark = pending_dark.add(request.event.action.cog());
            EventEmanation {
                cells: request.event.geometry.cells(),
                incidences: request.event.geometry.incidences(),
                resolving_cells: 0,
                formed_incidences: incidence_radiation
                    .iter()
                    .filter(|row| row.contact.emission.is_some())
                    .count() as u64,
                compounds: request.event.geometry.compounds(),
                folds: 0,
                receiver,
            }
        } else {
            if pending_dark.mag != 0 {
                body.resolve_dark_action_emitting(pending_dark, &mut output);
                pending_dark = Cog::ZERO;
            }
            let frame_before = body.channel().frame();
            let folded = match request.event.geometry {
                // A CELL FACE IS AN ATOM — `geometry_face_with_atlas` returns
                // `atom_node(relation.cog())` — so it belongs in the sub-illicium, and this mouth
                // is the right one for it.
                //
                // **A composing entry was wired here on 2026-08-15 and REVERTED the same hour.**
                // The reasoning was that a `Cell` has no interior to have been composed, so the
                // declared grain carries nothing; the error was that the correction pointed the
                // wrong way. Routing an atom straight into `perceive_grain(0)` skips the
                // sub-composition and declares a grain *above* what the material founded, which is
                // the same absolute-frame defect inverted. The supporting measurement was also
                // taken past the mouth's aperture: it fed whole word nodes to an entry built for
                // atoms, so its "zero climbs" was an artifact of the probe.
                //
                // `holon-plate`'s carrier-extent assertion is what caught it, by refusing to let
                // the carrier grow a row on a deed that founds no lineage.
                //
                // **What survives is the real reading, and it is upstream of both mouths:** this
                // mouth reaches `perceive_node_emitting` — the only path in the body from a raw
                // arrival into `thicken` — through its own `match fold { Some(f) => .. }` gate, so
                // the word grain forms exactly when the sub-illicium folds. `FOUNDER_FOLDED` is
                // the counter that answers it, and it is measured by
                // `soma/life/examples/the_grain_is_declared_or_it_is_founded.rs`.
                CurrentGeometry::Cell(_) => {
                    FOUNDER_CELL.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
                    body.live_event_node_emitting(
                        request.face,
                        request.event.action.cog(),
                        &mut output,
                    )
                    .fold
                    .is_some()
                }
                CurrentGeometry::Complex(_) => {
                    FOUNDER_COMPLEX.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
                    body.live_completed_event_node_at_grain_emitting(
                        request.face,
                        source_grain,
                        request.event.action.cog(),
                        &mut output,
                    )
                }
            };
            if folded {
                FOUNDER_FOLDED.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
            }
            if body.channel().frame() == frame_before {
                CHANNEL_STILL.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
            } else {
                CHANNEL_MOVED.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
            }
            EventEmanation {
                cells: request.event.geometry.cells(),
                incidences: request.event.geometry.incidences(),
                resolving_cells: request.event.geometry.resolving_cells(),
                formed_incidences: incidence_radiation
                    .iter()
                    .filter(|row| row.contact.emission.is_some())
                    .count() as u64,
                compounds: request.event.geometry.compounds(),
                folds: u64::from(folded),
                receiver: body
                    .event_receiver_at_source_grain(source_grain)
                    .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?,
            }
        };
        if request.event.ending && pending_dark.mag != 0 {
            body.resolve_dark_action_emitting(pending_dark, &mut output);
            pending_dark = Cog::ZERO;
        }
        consequence.receiver = body
            .event_receiver_at_source_grain(source_grain)
            .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?;
        observe_after_founder(&consequence.receiver);
        if body.resource_refused() || output.refused {
            return Err(LiveCurrentError::BodyRefused(request.lineage()));
        }
        (consequence, body.live_header(next_cursor))
    };

    let mut contributions = Vec::new();
    contributions
        .try_reserve_exact(own.cells().len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    for cell in own.cells() {
        contributions.push((cell.founder(), cell.form()));
    }
    Ok(CpuCurrentEnactment {
        current: ExecutedLiveCurrent::new(
            request.lineage(),
            LiveCarrierSnapshot::new(next_header, carrier)?,
            pending_dark,
            consequence,
            output.emissions,
            incidence_radiation,
            contributions,
        ),
        directed,
        regional: regional_results,
    })
}

/// **The cpu declares its own width. There is no knob.**
///
/// This read `SOMA_LIVE_THREADS` from the process environment until 2026-08-10. That variable was
/// read in exactly one place, set nowhere in the repository, and documented nowhere — so the
/// executor whose contract is *"the complete event result is required to equal
/// `CpuLiveCurrentExecutor`"* had a width that depended on the environment of whoever ran it, and
/// no test pinned it. An environment override is a knob, and a caller that genuinely wants a
/// particular width already has `ParallelCpuLiveCurrentExecutor::new`, which states it in the
/// type rather than in the ambient environment.
fn available_cpu_event_threads() -> usize {
    std::thread::available_parallelism()
        .map(|threads| threads.get())
        .unwrap_or(1)
}

fn enact_cpu_population(
    standing: &SparseStandingSurface,
    currents: &[CurrentExecutionRequest<'_>],
    relations: &[DirectedExecutionRequest],
    regional: &[RegionalExecutionRequest<'_>],
    thread_budget: usize,
    worker_stack_bytes: Option<usize>,
) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
    let threads = thread_budget.max(1).min(currents.len().max(1));
    let mut slots = Vec::new();
    slots
        .try_reserve_exact(currents.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    slots.resize_with(currents.len(), || None);
    if threads == 1 {
        for (at, slot) in slots.iter_mut().enumerate() {
            *slot = Some(enact_cpu_current(
                standing,
                currents[at],
                relations,
                regional,
            ));
        }
    } else {
        // **The front is covered by EXTENT, not by cardinality.**
        //
        // Until 2026-08-10 this read `base = len / threads` with the remainder handed to the first
        // lanes -- every current one unit, so a scalar cell and a ten-thousand-cell complex weighed
        // the same and one lane could draw every heavy current in the population. A current's
        // extent is its event geometry's own cell count, read off the material.
        //
        // The cover is greedy over extents in descending order: each cell of the front goes to the
        // lane carrying least so far. That is a **decomposition and never a schedule** -- it says
        // which lane may carry which cells; the physical order stays the runtime's, and results are
        // still written into position-fixed slots, so worker scheduling never becomes chronology.
        let mut extents: Vec<(usize, u64)> = currents
            .iter()
            .enumerate()
            .map(|(at, current)| (at, current.event().geometry().cells().max(1)))
            .collect();
        extents.sort_by_key(|(at, extent)| (std::cmp::Reverse(*extent), *at));
        let mut cover: Vec<Vec<usize>> = vec![Vec::new(); threads];
        let mut carried = vec![0u128; threads];
        for (at, extent) in extents {
            let lane = carried
                .iter()
                .enumerate()
                .min_by_key(|(lane, load)| (**load, *lane))
                .map(|(lane, _)| lane)
                .unwrap_or(0);
            cover[lane].push(at);
            carried[lane] += u128::from(extent);
        }
        for section in &mut cover {
            section.sort_unstable();
        }
        let sections = std::thread::scope(
            |scope| -> Result<Vec<Vec<(usize, Result<_, LiveCurrentError>)>>, LiveCurrentError> {
                let mut handles = Vec::new();
                handles
                    .try_reserve_exact(threads)
                    .map_err(|_| LiveCurrentError::ResourceReservation)?;
                for section in cover {
                    let mut builder = std::thread::Builder::new();
                    if let Some(bytes) = worker_stack_bytes {
                        builder = builder.stack_size(bytes);
                    }
                    handles.push(
                        builder
                            .spawn_scoped(scope, move || {
                                section
                                    .into_iter()
                                    .map(|at| {
                                        (
                                            at,
                                            enact_cpu_current(
                                                standing,
                                                currents[at],
                                                relations,
                                                regional,
                                            ),
                                        )
                                    })
                                    .collect::<Vec<_>>()
                            })
                            .map_err(|_| LiveCurrentError::ResourceReservation)?,
                    );
                }
                let mut gathered = Vec::new();
                for handle in handles {
                    // A lane's panic propagates exactly as it did before this cover existed.
                    match handle.join() {
                        Ok(section) => gathered.push(section),
                        Err(payload) => std::panic::resume_unwind(payload),
                    }
                }
                Ok(gathered)
            },
        )?;
        for section in sections {
            for (at, result) in section {
                slots[at] = Some(result);
            }
        }
    }

    let mut enacted = Vec::new();
    enacted
        .try_reserve_exact(currents.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    let mut directed = Vec::new();
    directed
        .try_reserve_exact(relations.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    directed.resize_with(relations.len(), || None);
    let mut regional_results = Vec::new();
    regional_results
        .try_reserve_exact(regional.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    regional_results.resize_with(regional.len(), || None);
    for slot in slots {
        let result = slot.ok_or(LiveCurrentError::ResourceReservation)??;
        enacted.push(result.current);
        for (at, relation) in result.directed {
            if directed[at].replace(relation).is_some() {
                return Err(LiveCurrentError::ExecutionMismatch(currents[0].lineage()));
            }
        }
        for (at, relation) in result.regional {
            if regional_results[at].replace(relation).is_some() {
                return Err(LiveCurrentError::ExecutionMismatch(currents[0].lineage()));
            }
        }
    }

    let mut completed_relations = Vec::new();
    completed_relations
        .try_reserve_exact(directed.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    for (request, contact) in relations.iter().zip(directed) {
        completed_relations
            .push(contact.ok_or(LiveCurrentError::ExecutionMismatch(request.relation.to))?);
    }
    let mut completed_regional = Vec::new();
    completed_regional
        .try_reserve_exact(regional_results.len())
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    for (request, result) in regional.iter().zip(regional_results) {
        completed_regional
            .push(result.ok_or(LiveCurrentError::ExecutionMismatch(request.receiver))?);
    }
    Ok(ExecutedContemporaryEvent::with_regional(
        enacted,
        completed_relations,
        completed_regional,
    ))
}

/// Exact cpu realization with an explicit physical worker bound. The bound affects only work
/// placement; the complete event result is required to equal [`CpuLiveCurrentExecutor`].
pub struct ParallelCpuLiveCurrentExecutor {
    threads: usize,
    worker_stack_bytes: Option<usize>,
}

impl ParallelCpuLiveCurrentExecutor {
    pub const fn new(threads: usize) -> Self {
        Self {
            threads,
            worker_stack_bytes: None,
        }
    }

    /// Select an explicit physical stack aperture for each scoped cpu worker. This changes only
    /// worker storage; it cannot change the event population, conduct, or successor.
    pub const fn with_worker_stack(threads: usize, worker_stack_bytes: usize) -> Self {
        Self {
            threads,
            worker_stack_bytes: Some(worker_stack_bytes),
        }
    }
}

impl LiveCurrentExecutor for CpuLiveCurrentExecutor {
    fn enact(
        &mut self,
        _physical_revision: u64,
        standing: &SparseStandingSurface,
        currents: &[CurrentExecutionRequest<'_>],
        relations: &[DirectedExecutionRequest],
        regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
        enact_cpu_population(
            standing,
            currents,
            relations,
            regional,
            available_cpu_event_threads(),
            None,
        )
    }
}

impl LiveCurrentExecutor for ParallelCpuLiveCurrentExecutor {
    fn enact(
        &mut self,
        _physical_revision: u64,
        standing: &SparseStandingSurface,
        currents: &[CurrentExecutionRequest<'_>],
        relations: &[DirectedExecutionRequest],
        regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
        enact_cpu_population(
            standing,
            currents,
            relations,
            regional,
            self.threads,
            self.worker_stack_bytes,
        )
    }
}

/// One living Eros body with a dynamic population of scale-local current carriers.
pub struct LiveCurrentMachine {
    standing: SparseStandingSurface,
    lineages: SparseOrdinalAtlas<LiveLineage>,
    // Rebuildable standing-incidence aperture. It exposes possible local meetings but never
    // supplies a Swing result, and is absent from rest, radiation, and causal identity.
    standing_aperture: Option<Arc<StandingIncidenceAperture>>,
    /// The chronology a standing factor must cross the aperture within, **declared by whoever
    /// mounts this machine**. `u64::MAX` is the inherited setting and admits every factor whole,
    /// which is what the closure did before 2026-08-15.
    ///
    /// It is a receiver declaration over a standing, not part of the caused body, so it is absent
    /// from rest, radiation and identity exactly as the aperture itself is.
    traversal_horizon: u64,
    /// How many propagation hops a front may be informed across — its **vision**. Declared by
    /// whoever mounts this machine; `u32::MAX` is the inherited setting and bounds nothing.
    vision_horizon: u32,
    // Substrate-cache coherence only. It is deliberately absent from rest, radiation, and every
    // causal or geometric identity.
    physical_revision: u64,
}

impl LiveCurrentMachine {
    /// Declare the chronology a standing factor must cross the aperture within.
    ///
    /// **Strictly additive**: the inherited setting is `u64::MAX` and admits every factor whole, so
    /// a machine that never calls this behaves exactly as before. A finite horizon defers the
    /// mismatched factors instead — retained, never dropped — which is what stops the co-present
    /// seam closure from pulling a replicated factor in whole on every round.
    /// Declare how far a signal may have propagated and still inform a front — its **vision**.
    ///
    /// Strictly additive: `u32::MAX` is inherited and bounds nothing. A finite depth means a front
    /// is informed only about what has reached it within that many hops, which is the traffic law's
    /// clause that a unit *"physically cannot be informed about vehicles not within their vision."*
    pub fn declare_vision_horizon(&mut self, horizon: u32) {
        self.vision_horizon = horizon;
        self.standing_aperture = None;
    }

    pub fn declare_traversal_horizon(&mut self, horizon: u64) {
        self.traversal_horizon = horizon;
        // The aperture is rebuilt on the next regional closure; drop any built under the prior
        // declaration rather than letting a stale horizon ride.
        self.standing_aperture = None;
    }

    pub fn new(standing: SparseStandingSurface) -> Self {
        Self {
            standing,
            lineages: SparseOrdinalAtlas::new(),
            standing_aperture: None,
            traversal_horizon: u64::MAX,
            vision_horizon: u32::MAX,
            physical_revision: 0,
        }
    }

    pub fn standing(&self) -> &SparseStandingSurface {
        &self.standing
    }

    /// Open one live current mouth from the first event's actual source geometry. Only its
    /// emanated boundary position and first resolving ingress anchor remain until that event
    /// crosses; cells, incidence, and world material remain caller-owned.
    pub fn attach<'a>(
        &mut self,
        first_event: impl Into<CurrentGeometry<'a>>,
    ) -> Result<CurrentLineage, LiveCurrentError> {
        let first_event = first_event.into();
        let event_nodes = first_event.complex().map(EventNodeAtlas::new).transpose()?;
        let node = geometry_face_with_atlas(first_event, event_nodes.as_ref())?;
        let anchor = geometry_anchor_with_atlas(first_event, event_nodes.as_ref())?.place;
        let carrier =
            GrowingCarrier::with_depth(1).map_err(|_| LiveCurrentError::ResourceReservation)?;
        let ordinal = self
            .lineages
            .try_push(LiveLineage {
                body: LineageBody::Seed {
                    first_event: node.place,
                    anchor,
                    carrier,
                },
                pending_dark: Cog::ZERO,
            })
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        Ok(CurrentLineage(ordinal))
    }

    pub fn contains(&self, lineage: CurrentLineage) -> bool {
        self.lineages.contains(lineage.0)
    }

    /// Resolve a durable organ capability only against this body's actual live population. The
    /// ordinal cannot fabricate a lineage: stale and departed names return `None`.
    pub fn resolve_lineage_ordinal(&self, ordinal: u64) -> Option<CurrentLineage> {
        let lineage = CurrentLineage(ordinal);
        self.lineages.contains(ordinal).then_some(lineage)
    }

    pub fn lineage_channel(&self, lineage: CurrentLineage) -> Option<LineageChannel> {
        match &self.lineages.get(lineage.0)?.body {
            LineageBody::Seed { .. } => None,
            LineageBody::Live(snapshot) => Some(snapshot.header().channel()),
        }
    }

    pub fn lineage_cursor(&self, lineage: CurrentLineage) -> Option<u64> {
        match &self.lineages.get(lineage.0)?.body {
            LineageBody::Seed { .. } => Some(0),
            LineageBody::Live(snapshot) => Some(snapshot.header().cursor()),
        }
    }

    /// Borrow the exact live physical carrier.  This is a persistence/diagnostic face only; the
    /// transition itself consults the session-owned value directly.
    pub fn lineage_carrier(&self, lineage: CurrentLineage) -> Option<&LiveCarrierSnapshot> {
        match &self.lineages.get(lineage.0)?.body {
            LineageBody::Seed { .. } => None,
            LineageBody::Live(snapshot) => Some(snapshot),
        }
    }

    pub fn memory(&self) -> LiveMemory {
        let mut carrier_words = 0usize;
        let mut overflow_nodes = 0usize;
        for lineage in self.lineages.values() {
            let carrier = match &lineage.body {
                LineageBody::Seed { carrier, .. } => carrier,
                LineageBody::Live(snapshot) => snapshot.carrier(),
            };
            carrier_words = carrier_words.saturating_add(carrier.words().len());
            for depth in 0..carrier.depth() {
                overflow_nodes = overflow_nodes
                    .saturating_add(carrier.co_present_overflow(depth).map_or(0, <[_]>::len));
            }
        }
        let constituent_cells = self
            .standing
            .constituents()
            .iter()
            .map(|constituent| constituent.cells().len())
            .fold(0usize, usize::saturating_add);
        let constituent_incidences = self
            .standing
            .constituents()
            .iter()
            .map(|constituent| constituent.incidences().len())
            .fold(0usize, usize::saturating_add);
        let constituent_pins = self
            .standing
            .constituents()
            .iter()
            .map(|constituent| constituent.pins().len())
            .fold(0usize, usize::saturating_add);
        let constituent_paths = self
            .standing
            .constituents()
            .iter()
            .flat_map(|constituent| constituent.boundaries())
            .map(|boundary| boundary.paths().len())
            .fold(0usize, usize::saturating_add);
        let constituent_transport_terms = self
            .standing
            .constituents()
            .iter()
            .flat_map(|constituent| constituent.boundaries())
            .flat_map(|boundary| boundary.paths())
            .map(|path| path.transport().terms().len())
            .fold(0usize, usize::saturating_add);
        LiveMemory {
            standing_cells: self.standing.cells().len(),
            standing_constituents: self.standing.constituents().len(),
            constituent_cells,
            constituent_incidences,
            constituent_pins,
            constituent_paths,
            constituent_transport_terms,
            live_lineages: self.lineages.len(),
            carrier_words,
            overflow_nodes,
        }
    }

    /// Capture the whole direct production body at a real receiving-edge rest. An attached seed
    /// has not yet crossed its first event and is therefore an open ingress rather than a resting
    /// lineage; it must remain with the caller or complete before this boundary can close.
    pub fn rest_image(&self) -> Result<LiveCurrentRestImage, LiveCurrentError> {
        let mut lineages = Vec::new();
        lineages
            .try_reserve_exact(self.lineages.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for (ordinal, state) in self.lineages.iter() {
            let lineage = CurrentLineage(ordinal);
            let LineageBody::Live(snapshot) = &state.body else {
                return Err(LiveCurrentError::UnsettledRest(lineage));
            };
            lineages.push(LiveLineageRestImage {
                lineage,
                pending_dark: state.pending_dark,
                native_carrier: snapshot.encode_native_words()?,
            });
        }
        Ok(LiveCurrentRestImage {
            standing: self.standing.clone(),
            lineages,
            next_lineage: self.lineages.extent(),
        })
    }

    /// Remount one exact direct-production rest face. Native carrier rows are validated before the
    /// machine exists; no receipt, source population, or executor result reconstructs the body.
    pub fn from_rest_image(image: LiveCurrentRestImage) -> Result<Self, LiveCurrentError> {
        let LiveCurrentRestImage {
            standing,
            lineages: images,
            next_lineage,
        } = image;
        let mut lineages = SparseOrdinalAtlas::new();
        lineages
            .try_set_extent(next_lineage)
            .map_err(|_| LiveCurrentError::InvalidRestImage)?;
        let mut previous = None;
        for image in images {
            if previous.is_some_and(|lineage| lineage >= image.lineage)
                || image.lineage.0 >= next_lineage
            {
                return Err(LiveCurrentError::InvalidRestImage);
            }
            let snapshot = LiveCarrierSnapshot::from_native_words(&image.native_carrier)?;
            lineages
                .try_found(
                    image.lineage.0,
                    LiveLineage {
                        body: LineageBody::Live(snapshot),
                        pending_dark: image.pending_dark,
                    },
                )
                .map_err(|_| LiveCurrentError::InvalidRestImage)?;
            previous = Some(image.lineage);
        }
        Ok(Self {
            standing,
            lineages,
            standing_aperture: None,
            // A remount inherits the admit-everything setting; the horizons are live receiver
            // declarations and are not carried in the rest image.
            traversal_horizon: u64::MAX,
            vision_horizon: u32::MAX,
            physical_revision: 0,
        })
    }

    /// Receive one complete event.  This method is the whole transition: no mutation becomes
    /// visible until every current has enacted against the same standing-before surface and the
    /// integrated successor has been prepared in full.
    pub fn receive(
        &mut self,
        event: ContemporaryEvent<'_>,
    ) -> Result<ContemporaryRadiation, LiveCurrentError> {
        let mut cpu = CpuLiveCurrentExecutor;
        self.receive_with(event, &mut cpu)
    }

    /// The same machine transition through an explicitly resident physical executor.
    pub fn receive_with(
        &mut self,
        event: ContemporaryEvent<'_>,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ContemporaryRadiation, LiveCurrentError> {
        let currents = event.currents;
        if currents.is_empty() {
            return Err(LiveCurrentError::EmptyEvent);
        }
        let mut current_index = SparseOrdinalAtlas::new();
        for (at, current) in currents.iter().enumerate() {
            if !self.lineages.contains(current.lineage.0) {
                return Err(LiveCurrentError::LineageAbsent(current.lineage));
            }
            match current_index.try_found(current.lineage.0, at) {
                Ok(()) => {}
                Err(OrdinalAtlasError::Occupied(_)) => {
                    return Err(LiveCurrentError::LineageRepeated(current.lineage));
                }
                Err(OrdinalAtlasError::Extent | OrdinalAtlasError::Reservation) => {
                    return Err(LiveCurrentError::ResourceReservation);
                }
            }
        }
        for relation in event.relations {
            if !current_index.contains(relation.from.0) {
                return Err(LiveCurrentError::DirectedEndpointAbsent(relation.from));
            }
            if !current_index.contains(relation.to.0) {
                return Err(LiveCurrentError::DirectedEndpointAbsent(relation.to));
            }
        }
        for regional in event.regional {
            if !current_index.contains(regional.receiver.0) {
                return Err(LiveCurrentError::DirectedEndpointAbsent(regional.receiver));
            }
            if regional.arcs.is_empty() {
                return Err(LiveCurrentError::EmptyRegionalRelation(regional.receiver));
            }
            let mut occupied_slots = BTreeSet::new();
            let mut boundary_hands = BTreeMap::new();
            for arc in regional.arcs {
                if !current_index.contains(arc.from.0) {
                    return Err(LiveCurrentError::DirectedEndpointAbsent(arc.from));
                }
                if !current_index.contains(arc.to.0) {
                    return Err(LiveCurrentError::DirectedEndpointAbsent(arc.to));
                }
                if !occupied_slots.insert((arc.boundary_slot, arc.arc_slot))
                    || boundary_hands
                        .insert(arc.boundary_slot, arc.hand)
                        .is_some_and(|prior| prior != arc.hand)
                {
                    return Err(LiveCurrentError::RegionalTopology(regional.receiver));
                }
            }
            if let Some(slots) = regional.outgoing_factor_slots {
                if slots.is_empty()
                    || slots.windows(2).any(|pair| pair[0] >= pair[1])
                    || slots.iter().any(|slot| !boundary_hands.contains_key(slot))
                {
                    return Err(LiveCurrentError::RegionalTopology(regional.receiver));
                }
            }
        }

        let before_rank = self.standing.rank();
        let before_cells = self.standing.cells().len();
        let mut event_node_atlases = Vec::new();
        event_node_atlases
            .try_reserve_exact(currents.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for ingress in currents {
            event_node_atlases.push(
                ingress
                    .geometry
                    .complex()
                    .map(EventNodeAtlas::new)
                    .transpose()?,
            );
        }
        let mut requests = Vec::new();
        requests
            .try_reserve_exact(currents.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for (at, ingress) in currents.iter().enumerate() {
            let prior = self
                .lineages
                .get(ingress.lineage.0)
                .ok_or(LiveCurrentError::LineageAbsent(ingress.lineage))?;
            let event_nodes = event_node_atlases[at].as_ref();
            let node = geometry_face_with_atlas(ingress.geometry, event_nodes)?;
            let mount = match &prior.body {
                LineageBody::Seed {
                    first_event,
                    anchor,
                    carrier,
                } => {
                    if *first_event != node.place {
                        return Err(LiveCurrentError::FirstEventChanged(ingress.lineage));
                    }
                    CurrentBodyMount::Seed {
                        first_event: *first_event,
                        anchor: *anchor,
                        carrier,
                    }
                }
                LineageBody::Live(snapshot) => CurrentBodyMount::Live(snapshot),
            };
            let wholly_dark = ingress.geometry.wholly_flat();
            requests.push(CurrentExecutionRequest {
                event: *ingress,
                face: node,
                event_nodes,
                wholly_dark,
                mount,
                pending_dark: prior.pending_dark,
            });
        }

        let mut relation_requests = Vec::new();
        relation_requests
            .try_reserve_exact(event.relations.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for relation in event.relations {
            let from = &requests[*current_index
                .get(relation.from.0)
                .ok_or(LiveCurrentError::DirectedEndpointAbsent(relation.from))?];
            let to = &requests[*current_index
                .get(relation.to.0)
                .ok_or(LiveCurrentError::DirectedEndpointAbsent(relation.to))?];
            relation_requests.push(DirectedExecutionRequest::new(
                *relation,
                from.face.place,
                to.face.place,
            ));
        }
        let mut regional_requests = Vec::new();
        regional_requests
            .try_reserve_exact(event.regional.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for regional in event.regional {
            let mut arcs = Vec::new();
            arcs.try_reserve_exact(regional.arcs.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for arc in regional.arcs {
                let from = &requests[*current_index
                    .get(arc.from.0)
                    .ok_or(LiveCurrentError::DirectedEndpointAbsent(arc.from))?];
                let to = &requests[*current_index
                    .get(arc.to.0)
                    .ok_or(LiveCurrentError::DirectedEndpointAbsent(arc.to))?];
                // Validate both source coordinates while preserving the borrowed geometries and
                // selected ports whole. These scalar point charts are not causal execution input.
                let _ = geometry_boundary_with_atlas(
                    from.event.geometry,
                    from.event_nodes,
                    arc.from_port,
                )?;
                let _ =
                    geometry_boundary_with_atlas(to.event.geometry, to.event_nodes, arc.to_port)?;
                arcs.push(RegionalArcExecution::new(
                    arc.clone(),
                    from.event.geometry,
                    from.event_nodes,
                    to.event.geometry,
                    to.event_nodes,
                ));
            }
            arcs.sort_unstable_by_key(|arc| (arc.arc.boundary_slot, arc.arc.arc_slot));
            regional_requests.push(RegionalExecutionRequest::new(
                regional.receiver,
                arcs,
                regional.support_sections,
                regional.outgoing_factor_slots,
            ));
        }
        let executed = executor.enact(
            self.physical_revision,
            &self.standing,
            &requests,
            &relation_requests,
            &regional_requests,
        )?;
        let (enacted, executed_relations, executed_regional) = executed.into_parts();
        if enacted.len() != currents.len() {
            return Err(LiveCurrentError::ExecutionMismatch(currents[0].lineage));
        }
        if executed_relations.len() != relation_requests.len() {
            return Err(LiveCurrentError::ExecutionMismatch(currents[0].lineage));
        }
        if executed_regional.len() != regional_requests.len() {
            return Err(LiveCurrentError::ExecutionMismatch(currents[0].lineage));
        }
        if !executed_regional.is_empty() && self.standing_aperture.is_none() {
            let mut aperture =
                StandingIncidenceAperture::from_standing(self.standing.constituent_standing())?;
            aperture.declare_traversal_horizon(self.traversal_horizon);
            aperture.declare_vision_horizon(self.vision_horizon);
            self.standing_aperture = Some(Arc::new(aperture));
        }
        let executed_regional = if executed_regional.is_empty() {
            executed_regional
        } else {
            close_executed_regional_population(
                &self.standing,
                self.standing_aperture
                    .as_deref()
                    .ok_or(LiveCurrentError::ResourceReservation)?,
                executed_regional,
            )?
        };
        let mut contributions = Vec::new();
        for (request, current) in requests.iter().zip(&enacted) {
            let expected_incidences = match request.event.geometry.complex() {
                Some(complex) => canonical_event_incidences(complex)?,
                None => Vec::new(),
            };
            if current.lineage != request.lineage()
                || current.next.header().cursor()
                    != request
                        .mount
                        .header()
                        .map_or(0, LiveBodyHeader::cursor)
                        .checked_add(1)
                        .ok_or(LiveCurrentError::CursorExtent)?
                || (request.event.ending && current.pending_dark.mag != 0)
                || current.consequence.cells != request.event.geometry.cells()
                || current.consequence.incidences != request.event.geometry.incidences()
                || current.consequence.resolving_cells != request.event.geometry.resolving_cells()
                || current.consequence.formed_incidences
                    != current
                        .incidences
                        .iter()
                        .filter(|row| row.contact.emission.is_some())
                        .count() as u64
                || current.consequence.formed_incidences > current.consequence.incidences
                || current.consequence.compounds != request.event.geometry.compounds()
                || current.consequence.folds > 1
                || current.incidences.len() != expected_incidences.len()
                || current
                    .incidences
                    .iter()
                    .zip(&expected_incidences)
                    .any(|(actual, expected)| actual.incidence != *expected)
                || current
                    .emissions
                    .iter()
                    .any(|emission| !emission.hand_is_exact())
                || current
                    .incidences
                    .iter()
                    .filter_map(|row| row.contact.emission)
                    .any(|emission| !emission.hand_is_exact())
                || current
                    .contributions
                    .iter()
                    .any(|(_, form)| !form.occupied())
            {
                return Err(LiveCurrentError::ExecutionMismatch(request.lineage()));
            }
            contributions
                .try_reserve(
                    current
                        .contributions
                        .len()
                        .checked_add(current.incidences.len())
                        .ok_or(LiveCurrentError::ResourceReservation)?,
                )
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            contributions.extend_from_slice(&current.contributions);
            for incidence in &current.incidences {
                if let Some(emission) = incidence.contact.emission {
                    contributions.push((
                        emission.position,
                        RegionalForm::UNBORN.deposit(emission.term),
                    ));
                }
            }
        }
        let mut directed = Vec::new();
        directed
            .try_reserve_exact(executed_relations.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for (request, executed) in relation_requests.iter().zip(executed_relations) {
            if executed.relation != request.relation {
                return Err(LiveCurrentError::ExecutionMismatch(request.relation.to));
            }
            let contact = executed.contact;
            if let Some(emission) = contact.emission {
                if !emission.hand_is_exact() {
                    return Err(LiveCurrentError::ExecutionMismatch(request.relation.to));
                }
                contributions
                    .try_reserve(1)
                    .map_err(|_| LiveCurrentError::ResourceReservation)?;
                contributions.push((
                    emission.position,
                    RegionalForm::UNBORN.deposit(emission.term),
                ));
            }
            directed.push(DirectedRelationRadiation {
                relation: executed.relation,
                contact,
            });
        }
        let mut cellular = Vec::new();
        cellular
            .try_reserve_exact(executed_regional.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        let mut regional_radiation = Vec::new();
        regional_radiation
            .try_reserve_exact(executed_regional.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for (request, executed) in regional_requests.iter().zip(executed_regional) {
            let (
                receiver,
                arcs,
                touched,
                constituent,
                _cell_origins,
                outgoing_factor_boundaries,
                commit_component,
                support_transitions,
                front_depth,
            ) = executed.into_parts();
            if receiver != request.receiver
                || arcs.len() != request.arcs.len()
                || arcs
                    .iter()
                    .zip(&request.arcs)
                    .any(|(actual, expected)| actual.arc != expected.arc)
                || arcs
                    .iter()
                    .filter_map(|arc| arc.contact.emission)
                    .any(|emission| !emission.hand_is_exact())
                || outgoing_factor_boundaries.is_some() != request.outgoing_factor_slots.is_some()
                || request
                    .support_sections
                    .is_some_and(|sections| sections.len() != support_transitions.len())
            {
                return Err(LiveCurrentError::ExecutionMismatch(request.receiver));
            }
            let touched_constituents = touched.len();
            if commit_component {
                cellular
                    .try_reserve(1)
                    .map_err(|_| LiveCurrentError::ResourceReservation)?;
                cellular.push(CellularStandingChange::new(touched, constituent.clone())?);
            }
            regional_radiation.push(RegionalRelationRadiation {
                receiver,
                arcs,
                constituent,
                support_transitions,
                touched_constituents,
                front_depth,
            });
        }

        let successor = self
            .standing
            .prepare_contemporary_successor(&contributions, &cellular)?;
        let successor_aperture = if cellular.is_empty() {
            self.standing_aperture.clone()
        } else {
            Some(Arc::new(
                self.standing_aperture
                    .as_deref()
                    .ok_or(LiveCurrentError::ResourceReservation)?
                    .after_replacements(
                        self.standing.constituent_standing(),
                        cellular
                            .iter()
                            .map(|change| (change.touched(), change.replacement())),
                    )?,
            ))
        };
        let after_rank = successor.rank();
        let after_cells = successor.cells().len();

        let mut radiation = Vec::new();
        radiation
            .try_reserve_exact(enacted.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        executor.settle_physical_successor(self.physical_revision, &successor)?;
        for (ingress, current) in currents.iter().zip(enacted) {
            let (lineage, next, pending_dark, consequence, emissions, incidences, _) =
                current.into_parts();
            radiation.push(CurrentRadiation {
                lineage,
                consequence,
                emissions,
                incidences,
                ended: ingress.ending,
            });
            if ingress.ending {
                self.lineages.remove(lineage.0);
            } else {
                let live = self
                    .lineages
                    .get_mut(lineage.0)
                    .expect("the validated live lineage remains mounted until commit");
                live.body = LineageBody::Live(next);
                live.pending_dark = pending_dark;
            }
        }
        self.standing = successor;
        self.standing_aperture = successor_aperture;
        self.physical_revision = self.physical_revision.wrapping_add(1);
        Ok(ContemporaryRadiation {
            before_rank,
            after_rank,
            before_cells,
            after_cells,
            currents: radiation,
            relations: directed,
            regional: regional_radiation,
        })
    }
}

impl CausalMembrane for LiveCurrentMachine {
    type Standing = SparseStandingSurface;
    type Occurrence<'a>
        = ContemporaryEvent<'a>
    where
        Self: 'a;
    type Return = ContemporaryRadiation;
    type Error = LiveCurrentError;

    fn standing(&self) -> &Self::Standing {
        LiveCurrentMachine::standing(self)
    }

    fn receive_occurrence<'a>(
        &mut self,
        occurrence: Self::Occurrence<'a>,
    ) -> Result<Self::Return, Self::Error>
    where
        Self: 'a,
    {
        self.receive(occurrence)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::incidence::{EventCell, EventCellId, EventPort, IncidenceHand, OrientedIncidence};
    use body::manifold::FeltDeed;

    fn relation(value: i64) -> RelationAtom {
        RelationAtom::new(Cog::lit(value)).unwrap()
    }

    fn action() -> ActionCurrent {
        ActionCurrent::new(Cog::lit(1)).unwrap()
    }

    fn assert_same_machine(left: &LiveCurrentMachine, right: &LiveCurrentMachine) {
        assert_eq!(left.standing, right.standing);
        assert_eq!(left.lineages.extent(), right.lineages.extent());
        assert_eq!(left.memory(), right.memory());
        assert_eq!(left.lineages.len(), right.lineages.len());
        for (lineage, left) in left.lineages.iter() {
            let right = right.lineages.get(lineage).unwrap();
            assert_eq!(left.pending_dark, right.pending_dark);
            match (&left.body, &right.body) {
                (
                    LineageBody::Seed {
                        first_event: left_event,
                        anchor: left_anchor,
                        carrier: left_carrier,
                    },
                    LineageBody::Seed {
                        first_event: right_event,
                        anchor: right_anchor,
                        carrier: right_carrier,
                    },
                ) => {
                    assert_eq!(left_event, right_event);
                    assert_eq!(left_anchor, right_anchor);
                    assert_eq!(left_carrier, right_carrier);
                }
                (LineageBody::Live(left), LineageBody::Live(right)) => {
                    assert_eq!(left.header(), right.header());
                    assert_eq!(left.carrier(), right.carrier());
                }
                _ => panic!("equal live machines cannot disagree about a lineage birth"),
            }
        }
    }

    type ButterflyCells = [EventCell; 11];
    type ButterflyIncidences = [OrientedIncidence; 16];
    type ButterflyPorts = [EventPort; 3];

    fn butterfly_fixture() -> (ButterflyCells, ButterflyIncidences, ButterflyPorts) {
        let id = EventCellId::new;
        let cells = [
            EventCell::new(id(0), 0, 0, Cog::lit(2)),
            EventCell::new(id(1), 0, 0, Cog::lit(3)),
            EventCell::new(id(2), 0, 0, Cog::lit(5)),
            EventCell::new(id(3), 0, 0, Cog::lit(7)),
            EventCell::new(id(4), 0, 1, Cog::lit(11)),
            EventCell::new(id(5), 0, 1, Cog::lit(13)),
            EventCell::new(id(6), 0, 1, Cog::lit(17)),
            EventCell::new(id(7), 0, 1, Cog::lit(19)),
            EventCell::new(id(8), 0, 1, Cog::lit(23)),
            EventCell::new(id(9), 0, 2, Cog::lit(29)),
            EventCell::new(id(10), 0, 2, Cog::lit(31)),
        ];
        let incidences = [
            OrientedIncidence::boundary(id(0), id(4), IncidenceHand::Against, 0),
            OrientedIncidence::boundary(id(1), id(4), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(1), id(5), IncidenceHand::Against, 0),
            OrientedIncidence::boundary(id(2), id(5), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(2), id(6), IncidenceHand::Against, 0),
            OrientedIncidence::boundary(id(0), id(6), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(1), id(7), IncidenceHand::Against, 0),
            OrientedIncidence::boundary(id(3), id(7), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(3), id(8), IncidenceHand::Against, 0),
            OrientedIncidence::boundary(id(0), id(8), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(4), id(9), IncidenceHand::With, 0),
            OrientedIncidence::boundary(id(5), id(9), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(6), id(9), IncidenceHand::With, 2),
            OrientedIncidence::boundary(id(4), id(10), IncidenceHand::Against, 0),
            OrientedIncidence::boundary(id(7), id(10), IncidenceHand::Against, 1),
            OrientedIncidence::boundary(id(8), id(10), IncidenceHand::Against, 2),
        ];
        let ports = [
            EventPort::ingress(id(0), IncidenceHand::With, 0),
            EventPort::exposed(id(9), IncidenceHand::With, 0),
            EventPort::exposed(id(10), IncidenceHand::With, 1),
        ];
        (cells, incidences, ports)
    }

    fn enact_complex(
        cells: &ButterflyCells,
        incidences: &ButterflyIncidences,
        ports: &ButterflyPorts,
    ) -> (LiveCurrentMachine, ContemporaryRadiation) {
        let complex = EventComplex::new(cells, incidences, ports).unwrap();
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let primer_face = relation(13);
        let primer = machine.attach(CurrentGeometry::Cell(primer_face)).unwrap();
        drive_values(
            &mut machine,
            primer,
            &[13, 29, 17, 31, -63_245, 47, 71, -89],
        );
        let lineage = machine.attach(CurrentGeometry::Complex(complex)).unwrap();
        let radiation = machine
            .receive(ContemporaryEvent::unrelated(&[
                CurrentEvent::continuing_complex(lineage, complex, action()),
            ]))
            .unwrap();
        (machine, radiation)
    }

    fn drive_values(
        machine: &mut LiveCurrentMachine,
        lineage: CurrentLineage,
        values: &[i64],
    ) -> Vec<CurrentRadiation> {
        let mut radiation = Vec::new();
        for value in values {
            let event = [relation(*value)];
            let returned = machine
                .receive(ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
                    lineage,
                    event[0],
                    action(),
                )]))
                .unwrap();
            radiation.push(returned.currents[0].clone());
        }
        radiation
    }

    fn primed_live_pair() -> (LiveCurrentMachine, CurrentLineage, CurrentLineage) {
        let first = [relation(13)];
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let left = machine.attach(CurrentGeometry::Cell(first[0])).unwrap();
        let right = machine.attach(CurrentGeometry::Cell(first[0])).unwrap();
        for value in [13, 29, 17, 31, -63_245, 47] {
            let face = [relation(value)];
            let currents = [
                CurrentEvent::continuing(left, face[0], action()),
                CurrentEvent::continuing(right, face[0], action()),
            ];
            machine
                .receive(ContemporaryEvent::unrelated(&currents))
                .unwrap();
        }
        let right_ahead = [relation(71)];
        machine
            .receive(ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
                right,
                right_ahead[0],
                action(),
            )]))
            .unwrap();
        let left_turn = [relation(71)];
        let right_turn = [relation(-89)];
        machine
            .receive(ContemporaryEvent::unrelated(&[
                CurrentEvent::continuing(left, left_turn[0], action()),
                CurrentEvent::continuing(right, right_turn[0], action()),
            ]))
            .unwrap();
        (machine, left, right)
    }

    fn primed_equal_lineages(count: usize) -> (LiveCurrentMachine, Vec<CurrentLineage>) {
        let first = relation(13);
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let mut lineages = Vec::new();
        for _ in 0..count {
            lineages.push(machine.attach(CurrentGeometry::Cell(first)).unwrap());
        }
        for value in [13, 29, 17, 31, -63_245, 47, 71, -89] {
            let face = relation(value);
            let currents: Vec<_> = lineages
                .iter()
                .copied()
                .map(|lineage| CurrentEvent::continuing(lineage, face, action()))
                .collect();
            machine
                .receive(ContemporaryEvent::unrelated(&currents))
                .unwrap();
        }
        (machine, lineages)
    }

    fn opposed_regional_arcs(
        left: CurrentLineage,
        right: CurrentLineage,
    ) -> [RegionalRelationArc; 2] {
        let interface = InterfaceCapability::new(left.ordinal(), right.ordinal());
        [
            RegionalRelationArc::new(
                left,
                CurrentBoundaryPort::Cell,
                right,
                CurrentBoundaryPort::Cell,
                interface.clone(),
                0,
                0,
                IncidenceHand::Against,
            ),
            RegionalRelationArc::new(
                right,
                CurrentBoundaryPort::Cell,
                left,
                CurrentBoundaryPort::Cell,
                interface,
                1,
                0,
                IncidenceHand::With,
            ),
        ]
    }

    fn situated_triangle_arcs(
        lineages: [CurrentLineage; 3],
        values: [i64; 3],
        first_hand: IncidenceHand,
    ) -> [RegionalRelationArc; 3] {
        let interface = |from: usize, to: usize| {
            InterfaceCapability::new(values[from] as u64, values[to] as u64)
        };
        [
            RegionalRelationArc::new(
                lineages[0],
                CurrentBoundaryPort::Cell,
                lineages[1],
                CurrentBoundaryPort::Cell,
                interface(0, 1),
                0,
                0,
                first_hand,
            ),
            RegionalRelationArc::new(
                lineages[1],
                CurrentBoundaryPort::Cell,
                lineages[2],
                CurrentBoundaryPort::Cell,
                interface(1, 2),
                1,
                0,
                IncidenceHand::Against,
            ),
            RegionalRelationArc::new(
                lineages[2],
                CurrentBoundaryPort::Cell,
                lineages[0],
                CurrentBoundaryPort::Cell,
                interface(2, 0),
                2,
                0,
                IncidenceHand::Against,
            ),
        ]
    }

    fn receiver_caused_triangle_arcs(
        lineages: [CurrentLineage; 3],
        charts: [ReceiverChartIdentity; 3],
        occurrence_order: u64,
        first_hand: IncidenceHand,
    ) -> [RegionalRelationArc; 3] {
        let arc = |from: usize, to: usize, boundary_slot: u32, hand: IncidenceHand| {
            let passage = ReceiverCausalPassage::new(
                charts[from],
                occurrence_order,
                charts[to],
                occurrence_order + 1,
            )
            .unwrap();
            RegionalRelationArc::from_receiver_passage(
                lineages[from],
                CurrentBoundaryPort::Cell,
                lineages[to],
                CurrentBoundaryPort::Cell,
                passage,
                boundary_slot,
                0,
                hand,
            )
        };
        [
            arc(0, 1, 0, first_hand),
            arc(1, 2, 1, IncidenceHand::Against),
            arc(2, 0, 2, IncidenceHand::Against),
        ]
    }

    #[test]
    fn one_oriented_complex_crosses_once_and_hands_up_its_exposed_boundary() {
        let (cells, incidences, ports) = butterfly_fixture();
        let (machine, radiation) = enact_complex(&cells, &incidences, &ports);
        let current = &radiation.currents()[0];
        let consequence = current.consequence();

        assert_eq!(machine.lineage_cursor(current.lineage()), Some(1));
        assert_eq!(consequence.cells, cells.len() as u64);
        assert_eq!(consequence.incidences, incidences.len() as u64);
        assert_eq!(consequence.resolving_cells, cells.len() as u64);
        assert_eq!(consequence.compounds, 7);
        assert_eq!(current.incidences().len(), incidences.len());
        assert_eq!(
            consequence.formed_incidences,
            current
                .incidences()
                .iter()
                .filter(|row| row.contact().emission.is_some())
                .count() as u64
        );
        assert_eq!(
            current
                .incidences()
                .iter()
                .filter(|row| row.incidence().from() == EventCellId::new(4))
                .count(),
            2
        );
        assert!(machine.lineage_carrier(current.lineage()).is_some());
    }

    #[test]
    fn event_node_atlas_preserves_every_recursive_complex_projection() {
        let (cells, incidences, ports) = butterfly_fixture();
        let complex = EventComplex::new(&cells, &incidences, &ports).unwrap();
        let atlas = EventNodeAtlas::new(complex).unwrap();

        for cell in complex.cells() {
            assert_eq!(
                atlas.cell_node(cell.id()).unwrap(),
                complex.composed_cell_node(cell.id()).unwrap()
            );
        }
        for incidence in complex.incidences() {
            assert_eq!(
                atlas.incidence_nodes(*incidence).unwrap(),
                complex.incidence_nodes(*incidence).unwrap()
            );
        }
        assert_eq!(
            atlas.ingress_node(complex).unwrap(),
            complex.ingress_node().unwrap()
        );
        assert_eq!(
            atlas.ingress_anchor_node(complex).unwrap(),
            complex.ingress_anchor_node().unwrap()
        );
        assert_eq!(
            atlas.emanated_node(complex).unwrap(),
            complex.emanated_node().unwrap()
        );
    }

    #[test]
    fn cell_and_incidence_storage_order_are_gauge_at_the_live_mouth() {
        let (cells, incidences, ports) = butterfly_fixture();
        let mut reversed_cells = cells;
        reversed_cells.reverse();
        let mut reversed_incidences = incidences;
        reversed_incidences.reverse();
        let mut reversed_ports = ports;
        reversed_ports.reverse();

        let (forward_machine, forward) = enact_complex(&cells, &incidences, &ports);
        let (reversed_machine, reversed) =
            enact_complex(&reversed_cells, &reversed_incidences, &reversed_ports);

        assert_eq!(forward, reversed);
        assert_same_machine(&forward_machine, &reversed_machine);
    }

    #[test]
    fn changed_adjacency_changes_conduct_and_open_hand_does_not_fabricate_a_successor() {
        let id = EventCellId::new;
        let (cells, base, ports) = butterfly_fixture();

        // Same cells and extents, but the second face now shares edge 1->2 and closes through
        // 2->3->1. Only declared adjacency changes.
        let mut adjacent = base;
        adjacent[6] = OrientedIncidence::boundary(id(2), id(7), IncidenceHand::Against, 0);
        adjacent[7] = OrientedIncidence::boundary(id(3), id(7), IncidenceHand::With, 1);
        adjacent[8] = OrientedIncidence::boundary(id(3), id(8), IncidenceHand::Against, 0);
        adjacent[9] = OrientedIncidence::boundary(id(1), id(8), IncidenceHand::With, 1);
        adjacent[13] = OrientedIncidence::boundary(id(5), id(10), IncidenceHand::With, 0);
        adjacent[14] = OrientedIncidence::boundary(id(7), id(10), IncidenceHand::With, 1);
        adjacent[15] = OrientedIncidence::boundary(id(8), id(10), IncidenceHand::With, 2);

        // A global orientation reversal of only the second closed face preserves partial²=0.
        let mut reversed_hand = base;
        reversed_hand[13] = OrientedIncidence::boundary(id(4), id(10), IncidenceHand::With, 0);
        reversed_hand[14] = OrientedIncidence::boundary(id(7), id(10), IncidenceHand::With, 1);
        reversed_hand[15] = OrientedIncidence::boundary(id(8), id(10), IncidenceHand::With, 2);

        let (base_machine, base_radiation) = enact_complex(&cells, &base, &ports);
        let (adjacent_machine, adjacent_radiation) = enact_complex(&cells, &adjacent, &ports);
        let (hand_machine, hand_radiation) = enact_complex(&cells, &reversed_hand, &ports);

        assert_ne!(base_radiation, adjacent_radiation);
        assert_ne!(base_radiation, hand_radiation);
        assert_ne!(
            base_radiation.currents()[0]
                .incidences()
                .iter()
                .map(|row| row.contact())
                .collect::<Vec<_>>(),
            hand_radiation.currents()[0]
                .incidences()
                .iter()
                .map(|row| row.contact())
                .collect::<Vec<_>>()
        );
        assert_ne!(
            base_machine.rest_image().unwrap(),
            adjacent_machine.rest_image().unwrap()
        );
        assert_eq!(
            base_radiation.currents()[0].consequence().formed_incidences,
            0
        );
        assert_eq!(
            hand_radiation.currents()[0].consequence().formed_incidences,
            0
        );
        assert_eq!(
            base_machine.rest_image().unwrap(),
            hand_machine.rest_image().unwrap()
        );
    }

    #[test]
    fn physical_chunk_partition_does_not_cut_one_live_lineage() {
        let values = [13, 29, 17, 31, -43, 59, -71, 89, 97, -101];
        let first = [relation(values[0])];
        let mut whole = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(0).unwrap());
        let whole_lineage = whole.attach(CurrentGeometry::Cell(first[0])).unwrap();
        let whole_radiation = drive_values(&mut whole, whole_lineage, &values);

        let mut chunked = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(0).unwrap());
        let chunked_lineage = chunked.attach(CurrentGeometry::Cell(first[0])).unwrap();
        let mut chunked_radiation = Vec::new();
        for chunk in [&values[..1], &values[1..4], &values[4..5], &values[5..]] {
            chunked_radiation.extend(drive_values(&mut chunked, chunked_lineage, chunk));
        }

        assert_eq!(whole_radiation, chunked_radiation);
        assert_same_machine(&whole, &chunked);
        assert_eq!(
            whole.lineage_cursor(whole_lineage),
            Some(values.len() as u64)
        );
    }

    #[test]
    fn co_present_hardware_order_cannot_parent_or_reorder_the_event() {
        let a0 = [relation(13)];
        let b0 = [relation(-43)];
        let mut forward = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(0).unwrap());
        let forward_a = forward.attach(CurrentGeometry::Cell(a0[0])).unwrap();
        let forward_b = forward.attach(CurrentGeometry::Cell(b0[0])).unwrap();
        let mut reverse = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(0).unwrap());
        let reverse_a = reverse.attach(CurrentGeometry::Cell(a0[0])).unwrap();
        let reverse_b = reverse.attach(CurrentGeometry::Cell(b0[0])).unwrap();
        assert_eq!((forward_a, forward_b), (reverse_a, reverse_b));

        let first_forward = [
            CurrentEvent::continuing(forward_a, a0[0], action()),
            CurrentEvent::continuing(forward_b, b0[0], action()),
        ];
        let first_reverse = [
            CurrentEvent::continuing(reverse_b, b0[0], action()),
            CurrentEvent::continuing(reverse_a, a0[0], action()),
        ];
        forward
            .receive(ContemporaryEvent::unrelated(&first_forward))
            .unwrap();
        reverse
            .receive(ContemporaryEvent::unrelated(&first_reverse))
            .unwrap();

        let a1 = [relation(29)];
        let b1 = [relation(59)];
        let later_forward = [
            CurrentEvent::continuing(forward_a, a1[0], action()),
            CurrentEvent::continuing(forward_b, b1[0], action()),
        ];
        let later_reverse = [
            CurrentEvent::continuing(reverse_b, b1[0], action()),
            CurrentEvent::continuing(reverse_a, a1[0], action()),
        ];
        forward
            .receive(ContemporaryEvent::unrelated(&later_forward))
            .unwrap();
        reverse
            .receive(ContemporaryEvent::unrelated(&later_reverse))
            .unwrap();
        assert_same_machine(&forward, &reverse);
    }

    #[test]
    fn the_same_current_faces_with_reversed_hand_form_different_successors() {
        let (mut forward, forward_left, forward_right) = primed_live_pair();
        let (mut reverse, reverse_left, reverse_right) = primed_live_pair();
        assert_same_machine(&forward, &reverse);

        let forward_relations = [DirectedCurrentRelation::new(forward_left, forward_right)];
        let reverse_relations = [DirectedCurrentRelation::new(reverse_right, reverse_left)];
        let left_face = [relation(-89)];
        let right_face = [relation(97)];
        let forward_currents = [
            CurrentEvent::continuing(forward_left, left_face[0], action()),
            CurrentEvent::continuing(forward_right, right_face[0], action()),
        ];
        let reverse_currents = [
            CurrentEvent::continuing(reverse_left, left_face[0], action()),
            CurrentEvent::continuing(reverse_right, right_face[0], action()),
        ];
        let forward_radiation = forward
            .receive(ContemporaryEvent::new(
                &forward_currents,
                &forward_relations,
            ))
            .unwrap();
        let reverse_radiation = reverse
            .receive(ContemporaryEvent::new(
                &reverse_currents,
                &reverse_relations,
            ))
            .unwrap();
        let forward_contact = forward_radiation.relations()[0].contact();
        let reverse_contact = reverse_radiation.relations()[0].contact();

        assert_eq!(forward_radiation.currents(), reverse_radiation.currents());
        assert_eq!(
            forward_radiation.relations()[0].relation(),
            forward_relations[0]
        );
        assert_eq!(
            reverse_radiation.relations()[0].relation(),
            reverse_relations[0]
        );
        assert!(forward_contact.emission.is_some() || reverse_contact.emission.is_some());
        assert_ne!(forward_contact, reverse_contact);
        assert_ne!(forward.standing(), reverse.standing());
    }

    #[test]
    fn regional_cell_becomes_cellular_standing_and_rests_without_the_borrowed_event() {
        let (base, left, right) = primed_live_pair();
        let rest = base.rest_image().unwrap();
        let mut machine = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();

        let forward_arcs = [
            RegionalRelationArc::new(
                left,
                CurrentBoundaryPort::Cell,
                right,
                CurrentBoundaryPort::Cell,
                InterfaceCapability::new(left.ordinal(), right.ordinal()),
                0,
                0,
                IncidenceHand::Against,
            ),
            RegionalRelationArc::new(
                right,
                CurrentBoundaryPort::Cell,
                left,
                CurrentBoundaryPort::Cell,
                InterfaceCapability::new(left.ordinal(), right.ordinal()),
                1,
                0,
                IncidenceHand::With,
            ),
        ];
        let left_face = relation(-89);
        let right_face = relation(97);
        let currents = [
            CurrentEvent::continuing(left, left_face, action()),
            CurrentEvent::continuing(right, right_face, action()),
        ];
        let cells = [RegionalRelationCell::new(right, &forward_arcs)];
        let radiation = machine
            .receive(ContemporaryEvent::with_regional(&currents, &[], &cells))
            .unwrap();
        assert_eq!(radiation.regional().len(), 1);
        let constituent = radiation.regional()[0].constituent();
        assert_eq!(constituent.boundaries().len(), 2);
        assert_eq!(constituent.incidences().len(), 2);
        assert_eq!(machine.standing().constituents(), &[constituent.clone()]);

        // The rest face owns only the rebased local composite. The event's arc rows and source
        // capabilities remain in the caller and are not needed to reopen it.
        let rested = machine.rest_image().unwrap();
        let wire = rested.encode_native_words().unwrap();
        let reopened = LiveCurrentRestImage::from_native_words(&wire).unwrap();
        assert_eq!(reopened, rested);
        assert_eq!(
            LiveCurrentMachine::from_rest_image(reopened)
                .unwrap()
                .standing(),
            machine.standing()
        );
    }

    #[test]
    fn dark_world_extent_does_not_become_retained_execution_extent() {
        let dark = [relation(0)];
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(0).unwrap());
        let lineage = machine.attach(CurrentGeometry::Cell(dark[0])).unwrap();
        machine
            .receive(ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
                lineage,
                dark[0],
                action(),
            )]))
            .unwrap();
        let one = machine.memory();
        for _ in 1..1024 {
            machine
                .receive(ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
                    lineage,
                    dark[0],
                    action(),
                )]))
                .unwrap();
        }
        assert_eq!(machine.memory(), one);
        assert_eq!(machine.lineage_cursor(lineage), Some(1024));
        assert_eq!(machine.standing.cells().len(), 0);
    }

    #[test]
    fn found_departure_and_genuinely_later_ride_share_the_same_transition() {
        let values = [13, 29, 17, 31, -63_245, 47, 71, -89];
        let first = [relation(values[0])];
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let lineage = machine.attach(CurrentGeometry::Cell(first[0])).unwrap();
        let radiation = drive_values(&mut machine, lineage, &values);
        let deeds: Vec<_> = radiation
            .iter()
            .flat_map(|current| current.emissions.iter())
            .map(|emission| (emission.deed, emission.standing_read.is_some()))
            .collect();
        assert!(deeds
            .iter()
            .any(|(deed, _)| { matches!(deed, FeltDeed::FoundThis | FeltDeed::FoundThat) }));

        // A second constituent participates and then genuinely departs.  Its world material and
        // current-local carrier are gone; the standing topology and first lineage remain live.
        let constituent_first = [relation(101)];
        let constituent = machine
            .attach(CurrentGeometry::Cell(constituent_first[0]))
            .unwrap();
        machine
            .receive(ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
                constituent,
                constituent_first[0],
                action(),
            )]))
            .unwrap();
        let constituent_end = [relation(103)];
        machine
            .receive(ContemporaryEvent::unrelated(&[CurrentEvent::ending(
                constituent,
                constituent_end[0],
                action(),
            )]))
            .unwrap();
        assert!(!machine.contains(constituent));
        assert!(machine.contains(lineage));
        assert!(!machine.standing.cells().is_empty());

        let later = [relation(-253)];
        let returned = machine
            .receive(ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
                lineage,
                later[0],
                action(),
            )]))
            .unwrap();
        assert!(returned.currents[0].emissions.iter().any(|emission| {
            emission.deed == FeltDeed::Ride && emission.standing_read.is_some()
        }));
    }

    #[test]
    fn direct_rest_remount_is_gauge_for_the_same_genuinely_later_event() {
        let main_first = [relation(13)];
        let dark_first = [relation(0)];
        let mut uninterrupted =
            LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let main = uninterrupted
            .attach(CurrentGeometry::Cell(main_first[0]))
            .unwrap();
        let dark = uninterrupted
            .attach(CurrentGeometry::Cell(dark_first[0]))
            .unwrap();
        uninterrupted
            .receive(ContemporaryEvent::unrelated(&[
                CurrentEvent::continuing(main, main_first[0], action()),
                CurrentEvent::continuing(dark, dark_first[0], action()),
            ]))
            .unwrap();

        for value in [29, 17, 31, -63_245, 47, 71, -89] {
            let event = [relation(value)];
            uninterrupted
                .receive(ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
                    main,
                    event[0],
                    action(),
                )]))
                .unwrap();
        }
        assert!(!uninterrupted.standing().cells().is_empty());

        let rest = uninterrupted.rest_image().unwrap();
        assert_eq!(rest.lineages().len(), 2);
        assert_eq!(rest.lineages()[0].lineage(), main);
        assert_eq!(rest.lineages()[1].lineage(), dark);
        assert_ne!(rest.lineages()[1].pending_dark().mag, 0);
        let native_words = rest.encode_native_words().unwrap();
        assert_eq!(
            LiveCurrentRestImage::from_native_words(&native_words).unwrap(),
            rest
        );
        let native_bytes = rest.encode_native_bytes().unwrap();
        assert_eq!(
            LiveCurrentRestImage::from_native_bytes(&native_bytes).unwrap(),
            rest
        );
        assert_eq!(
            LiveCurrentRestImage::from_native_bytes(&native_bytes[..native_bytes.len() - 1]),
            Err(LiveCurrentError::InvalidRestWire)
        );
        let mut remounted = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
        assert_same_machine(&uninterrupted, &remounted);
        assert_eq!(remounted.rest_image().unwrap(), rest);

        let later_main = [relation(-253)];
        let later_dark = [relation(0)];
        let expected = uninterrupted
            .receive(ContemporaryEvent::unrelated(&[
                CurrentEvent::continuing(main, later_main[0], action()),
                CurrentEvent::ending(dark, later_dark[0], action()),
            ]))
            .unwrap();
        let returned = remounted
            .receive(ContemporaryEvent::unrelated(&[
                CurrentEvent::continuing(main, later_main[0], action()),
                CurrentEvent::ending(dark, later_dark[0], action()),
            ]))
            .unwrap();
        assert_eq!(expected, returned);
        assert_same_machine(&uninterrupted, &remounted);
        assert!(!remounted.contains(dark));
    }

    #[test]
    fn disjoint_cellular_changes_are_co_present_and_storage_order_is_gauge() {
        let (base, lineages) = primed_equal_lineages(4);
        let rest = base.rest_image().unwrap();
        let mut forward = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
        let mut reverse = LiveCurrentMachine::from_rest_image(rest).unwrap();

        let first_arcs = opposed_regional_arcs(lineages[0], lineages[1]);
        let second_arcs = opposed_regional_arcs(lineages[2], lineages[3]);
        let forward_cells = [
            RegionalRelationCell::new(lineages[1], &first_arcs),
            RegionalRelationCell::new(lineages[3], &second_arcs),
        ];
        let reverse_cells = [forward_cells[1], forward_cells[0]];
        let currents = [
            CurrentEvent::continuing(lineages[0], relation(-89), action()),
            CurrentEvent::continuing(lineages[1], relation(97), action()),
            CurrentEvent::continuing(lineages[2], relation(-83), action()),
            CurrentEvent::continuing(lineages[3], relation(101), action()),
        ];

        let forward_radiation = forward
            .receive(ContemporaryEvent::with_regional(
                &currents,
                &[],
                &forward_cells,
            ))
            .unwrap();
        let reverse_radiation = reverse
            .receive(ContemporaryEvent::with_regional(
                &currents,
                &[],
                &reverse_cells,
            ))
            .unwrap();

        assert_eq!(forward_radiation.regional().len(), 2);
        assert_eq!(reverse_radiation.regional().len(), 2);
        assert_eq!(forward.standing().constituents().len(), 2);
        assert_same_machine(&forward, &reverse);
    }

    #[test]
    fn an_incomplete_outgoing_factor_refuses_before_successor_mutation() {
        let (mut machine, lineages) = primed_equal_lineages(2);
        let before = machine.rest_image().unwrap();
        let arcs = opposed_regional_arcs(lineages[0], lineages[1]);
        let absent_slots = [2u32];
        let regional = [RegionalRelationCell::with_outgoing_factor(
            lineages[1],
            &arcs,
            &absent_slots,
        )];
        let currents = [
            CurrentEvent::continuing(lineages[0], relation(-89), action()),
            CurrentEvent::continuing(lineages[1], relation(97), action()),
        ];

        assert_eq!(
            machine.receive(ContemporaryEvent::with_regional(&currents, &[], &regional)),
            Err(LiveCurrentError::RegionalTopology(lineages[1]))
        );
        assert_eq!(machine.rest_image().unwrap(), before);
    }

    #[test]
    fn disconnected_equal_constituents_remain_plural_at_commit_and_rest() {
        let (mut source, lineages) = primed_equal_lineages(2);
        let arcs = opposed_regional_arcs(lineages[0], lineages[1]);
        let cell = [RegionalRelationCell::new(lineages[1], &arcs)];
        let currents = [
            CurrentEvent::continuing(lineages[0], relation(-89), action()),
            CurrentEvent::continuing(lineages[1], relation(97), action()),
        ];
        let radiation = source
            .receive(ContemporaryEvent::with_regional(&currents, &[], &cell))
            .unwrap();
        let body = radiation.regional()[0].constituent().clone();
        assert!(body.exposed().is_empty());

        let standing = SparseStandingSurface::empty_rank(6).unwrap();
        let aperture = StandingIncidenceAperture::from_standing(standing.constituents()).unwrap();
        let completed = close_executed_regional_population(
            &standing,
            &aperture,
            vec![
                ExecutedRegionalRelation::new(lineages[1], Vec::new(), Vec::new(), body.clone()),
                ExecutedRegionalRelation::new(lineages[1], Vec::new(), Vec::new(), body),
            ],
        )
        .unwrap();
        assert_eq!(completed.len(), 2);
        assert!(completed.iter().all(|relation| relation.commit_component));
        assert_eq!(completed[0].constituent(), completed[1].constituent());

        let changes: Vec<_> = completed
            .into_iter()
            .map(|relation| {
                let (
                    _,
                    _,
                    touched,
                    constituent,
                    _origins,
                    outgoing_factor,
                    commit_component,
                    _support_transitions,
                    _front_depth,
                ) = relation.into_parts();
                assert!(outgoing_factor.is_none());
                assert!(commit_component);
                CellularStandingChange::new(touched, constituent).unwrap()
            })
            .collect();
        let successor = standing
            .prepare_contemporary_successor(&[], &changes)
            .unwrap();
        assert_eq!(successor.constituents().len(), 2);
        let rest = LiveCurrentMachine::new(successor).rest_image().unwrap();
        let remounted =
            LiveCurrentRestImage::from_native_words(&rest.encode_native_words().unwrap()).unwrap();
        assert_eq!(remounted.standing().constituents().len(), 2);
    }

    #[test]
    fn joint_regional_closure_is_exact_across_one_and_many_cpu_cores() {
        let (base, lineages) = primed_equal_lineages(3);
        let rest = base.rest_image().unwrap();
        let mut one = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
        let mut many = LiveCurrentMachine::from_rest_image(rest).unwrap();
        let arcs = [
            RegionalRelationArc::new(
                lineages[0],
                CurrentBoundaryPort::Cell,
                lineages[1],
                CurrentBoundaryPort::Cell,
                InterfaceCapability::new(0x434f_5245, 0),
                0,
                0,
                IncidenceHand::Against,
            ),
            RegionalRelationArc::new(
                lineages[1],
                CurrentBoundaryPort::Cell,
                lineages[2],
                CurrentBoundaryPort::Cell,
                InterfaceCapability::new(0x434f_5245, 1),
                1,
                0,
                IncidenceHand::With,
            ),
        ];
        let cell = RegionalRelationCell::new(lineages[2], &arcs);
        let regional = [cell, cell];
        let currents = [
            CurrentEvent::continuing(lineages[0], relation(17), action()),
            CurrentEvent::continuing(lineages[1], relation(29), action()),
            CurrentEvent::continuing(lineages[2], relation(43), action()),
        ];

        let one_radiation = one
            .receive_with(
                ContemporaryEvent::with_regional(&currents, &[], &regional),
                &mut ParallelCpuLiveCurrentExecutor::new(1),
            )
            .unwrap();
        let many_radiation = many
            .receive_with(
                ContemporaryEvent::with_regional(&currents, &[], &regional),
                &mut ParallelCpuLiveCurrentExecutor::with_worker_stack(8, 4 * 1024 * 1024),
            )
            .unwrap();

        assert_eq!(one_radiation, many_radiation);
        assert_same_machine(&one, &many);
        assert_eq!(one_radiation.regional().len(), 2);
        assert_eq!(
            one_radiation.regional()[0].constituent(),
            one_radiation.regional()[1].constituent()
        );
        assert_eq!(one.standing().constituents().len(), 1);
        assert_eq!(
            LiveCurrentMachine::from_rest_image(one.rest_image().unwrap())
                .unwrap()
                .standing(),
            one.standing()
        );
    }

    /// **The requirement `ParallelCpuLiveCurrentExecutor` states about itself, actually checked.**
    ///
    /// Its own doc says *"the bound affects only work placement; the complete event result is
    /// required to equal `CpuLiveCurrentExecutor`."* Measured 2026-08-10: **no test compared the
    /// two.** The parity test above compares `Parallel(1)` against `Parallel(8)`, so the executor
    /// the requirement names was the one nothing verified — and its width comes from
    /// `available_cpu_event_threads`, which reads `SOMA_LIVE_THREADS` from the process
    /// environment, so it was untested at any specific value.
    ///
    /// This closes that. It also varies the cover: the currents are given deliberately unequal
    /// extents, so the by-extent cover assigns them differently from a by-count one, and a lane
    /// carrying a different section must still return the identical event.
    #[test]
    fn the_parallel_cpu_executor_equals_the_cpu_executor_it_declares_itself_against() {
        let (base, lineages) = primed_equal_lineages(4);
        let rest = base.rest_image().unwrap();
        let mut default_width = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
        let mut single = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
        let mut wide = LiveCurrentMachine::from_rest_image(rest).unwrap();
        let currents = [
            CurrentEvent::continuing(lineages[0], relation(11), action()),
            CurrentEvent::continuing(lineages[1], relation(23), action()),
            CurrentEvent::continuing(lineages[2], relation(37), action()),
            CurrentEvent::continuing(lineages[3], relation(51), action()),
        ];
        let event = || ContemporaryEvent::new(&currents, &[]);

        let by_default = default_width
            .receive_with(event(), &mut CpuLiveCurrentExecutor)
            .unwrap();
        let by_one = single
            .receive_with(event(), &mut ParallelCpuLiveCurrentExecutor::new(1))
            .unwrap();
        let by_many = wide
            .receive_with(event(), &mut ParallelCpuLiveCurrentExecutor::new(7))
            .unwrap();

        assert_eq!(
            by_default, by_one,
            "the declared equality: CpuLiveCurrentExecutor against one lane"
        );
        assert_eq!(
            by_default, by_many,
            "the declared equality: CpuLiveCurrentExecutor against seven lanes"
        );
        assert_same_machine(&default_width, &single);
        assert_same_machine(&default_width, &wide);

        // Seven lanes over four currents is a cover the by-count rule could not produce: it would
        // hand four lanes one current each and leave three empty, while the by-extent cover fills
        // by carried load. Either way the event is identical, which is the whole claim.
        assert!(currents.len() < 7);
    }

    #[test]
    fn shared_cofaces_condition_the_support_fan_and_recur_after_rest() {
        let (mut seed_machine, lineages) = primed_equal_lineages(5);
        let x = InterfaceCapability::new(0x5354_4152, 0);
        let y = InterfaceCapability::new(0x5354_4152, 1);
        let z = InterfaceCapability::new(0x5354_4152, 2);
        let arc = |to: usize, interface: InterfaceCapability, boundary_slot: u32| {
            RegionalRelationArc::new(
                lineages[0],
                CurrentBoundaryPort::Cell,
                lineages[to],
                CurrentBoundaryPort::Cell,
                interface,
                boundary_slot,
                0,
                IncidenceHand::Against,
            )
        };
        let first_arcs = [arc(1, x.clone(), 0), arc(2, y.clone(), 1)];
        let second_arcs = [arc(3, x.clone(), 0), arc(4, z.clone(), 1)];
        let pair_slots = [0u32, 1];
        let pair_section = [RegionalSupportSection::new(&pair_slots)];
        let seed_regions = [
            RegionalRelationCell::with_support_sections(lineages[2], &first_arcs, &pair_section),
            RegionalRelationCell::with_support_sections(lineages[4], &second_arcs, &pair_section),
        ];
        let seed_currents = [
            CurrentEvent::continuing(lineages[0], relation(13), action()),
            CurrentEvent::continuing(lineages[1], relation(13), action()),
            CurrentEvent::continuing(lineages[2], relation(13), action()),
            CurrentEvent::continuing(lineages[3], relation(13), action()),
            CurrentEvent::continuing(lineages[4], relation(13), action()),
        ];
        let seed = seed_machine
            .receive(ContemporaryEvent::with_regional(
                &seed_currents,
                &[],
                &seed_regions,
            ))
            .unwrap();
        assert_eq!(seed.regional().len(), 2);
        assert_eq!(
            seed.regional()[0].constituent(),
            seed.regional()[1].constituent()
        );
        let seed_body = seed.regional()[0].constituent();
        assert_eq!(seed_body.grain(), 2);
        assert_eq!(seed_body.support_sections().len(), 2);
        assert_eq!(seed_body.cells().len(), 6);
        assert_eq!(seed_machine.standing().constituents().len(), 1);

        let seed_rest = seed_machine.rest_image().unwrap();
        let mut contextual = LiveCurrentMachine::from_rest_image(seed_rest.clone()).unwrap();
        let mut broad = LiveCurrentMachine::from_rest_image(seed_rest).unwrap();

        let contextual_arcs = [arc(1, x.clone(), 0), arc(2, y, 1)];
        let contextual_regions = [RegionalRelationCell::with_support_sections(
            lineages[2],
            &contextual_arcs,
            &pair_section,
        )];
        let contextual_radiation = contextual
            .receive(ContemporaryEvent::with_regional(
                &seed_currents,
                &[],
                &contextual_regions,
            ))
            .unwrap();
        let contextual_body = contextual_radiation.regional()[0].constituent();
        assert_eq!(contextual_body.grain(), 3);
        let mut contextual_extents = contextual_body
            .support_sections()
            .iter()
            .map(|section| section.boundaries().len())
            .collect::<Vec<_>>();
        contextual_extents.sort_unstable();
        assert_eq!(contextual_extents, vec![2, 6]);

        let broad_arcs = [arc(1, x.clone(), 0)];
        let broad_regions = [RegionalRelationCell::new(lineages[1], &broad_arcs)];
        let broad_radiation = broad
            .receive(ContemporaryEvent::with_regional(
                &seed_currents,
                &[],
                &broad_regions,
            ))
            .unwrap();
        let broad_body = broad_radiation.regional()[0].constituent();
        assert_eq!(broad_body.grain(), 3);
        let mut broad_extents = broad_body
            .support_sections()
            .iter()
            .map(|section| section.boundaries().len())
            .collect::<Vec<_>>();
        broad_extents.sort_unstable();
        assert_eq!(broad_extents, vec![4, 4]);
        assert_ne!(contextual.standing(), broad.standing());

        let contextual_rest = contextual.rest_image().unwrap();
        let mut remounted = LiveCurrentMachine::from_rest_image(contextual_rest).unwrap();
        assert_same_machine(&contextual, &remounted);
        let next_arcs = [arc(3, x, 0), arc(4, z, 1)];
        let next_regions = [RegionalRelationCell::with_support_sections(
            lineages[4],
            &next_arcs,
            &pair_section,
        )];
        let expected = contextual
            .receive(ContemporaryEvent::with_regional(
                &seed_currents,
                &[],
                &next_regions,
            ))
            .unwrap();
        let actual = remounted
            .receive(ContemporaryEvent::with_regional(
                &seed_currents,
                &[],
                &next_regions,
            ))
            .unwrap();
        assert_eq!(expected, actual);
        assert_same_machine(&contextual, &remounted);
        assert_eq!(actual.regional()[0].constituent().grain(), 4);
    }

    #[test]
    fn receiver_chronology_proposes_the_interface_and_only_exact_recurrence_causes_the_ride() {
        assert_eq!(
            ReceiverCausalPassage::new(
                ReceiverChartIdentity::new(1),
                9,
                ReceiverChartIdentity::new(2),
                9,
            ),
            Err(ReceiverCausalPassageError::NonIncreasingChronology)
        );

        let (mut seed_machine, lineages) = primed_equal_lineages(3);
        let lineages = [lineages[0], lineages[1], lineages[2]];
        let seed_charts = [
            ReceiverChartIdentity::new(0x004c_4947_4854),
            ReceiverChartIdentity::new(0x0053_4f55_4e44),
            ReceiverChartIdentity::new(0x4752_4f55_4e44),
        ];
        let seed_arcs =
            receiver_caused_triangle_arcs(lineages, seed_charts, 10, IncidenceHand::Against);
        assert!(seed_arcs.iter().all(|arc| {
            arc.interface().origin() == crate::InterfaceCapabilityOrigin::ReceiverCaused
        }));
        let seed_region = [RegionalRelationCell::new(lineages[2], &seed_arcs)];
        let seed_currents = [
            CurrentEvent::continuing(lineages[0], relation(17), action()),
            CurrentEvent::continuing(lineages[1], relation(29), action()),
            CurrentEvent::continuing(lineages[2], relation(43), action()),
        ];
        let seed = seed_machine
            .receive(ContemporaryEvent::with_regional(
                &seed_currents,
                &[],
                &seed_region,
            ))
            .unwrap();
        let opening = seed.regional()[0].constituent();
        assert_eq!(opening.grain(), 2);
        assert!(opening
            .pins()
            .iter()
            .filter_map(|pin| pin.interface())
            .all(
                |interface| interface.origin() == crate::InterfaceCapabilityOrigin::ReceiverCaused
            ));

        let wire = seed_machine
            .rest_image()
            .unwrap()
            .encode_native_words()
            .unwrap();
        let rest = LiveCurrentRestImage::from_native_words(&wire).unwrap();
        let mut recurring = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
        let mut reversed = LiveCurrentMachine::from_rest_image(rest).unwrap();

        // Absolute orders differ from the opening occurrence. The same ordered receiver charts
        // still address its candidate interface; the changed third chart leaves the other two
        // boundaries independent.
        let later_charts = [
            seed_charts[0],
            seed_charts[1],
            ReceiverChartIdentity::new(0x0041_4952),
        ];
        let recurring_arcs =
            receiver_caused_triangle_arcs(lineages, later_charts, 40, IncidenceHand::Against);
        let reversed_charts = [later_charts[1], later_charts[0], later_charts[2]];
        let reversed_arcs =
            receiver_caused_triangle_arcs(lineages, reversed_charts, 40, IncidenceHand::Against);
        let later_currents = [
            CurrentEvent::continuing(lineages[0], relation(17), action()),
            CurrentEvent::continuing(lineages[1], relation(29), action()),
            CurrentEvent::continuing(lineages[2], relation(71), action()),
        ];
        let recurring_radiation = recurring
            .receive(ContemporaryEvent::with_regional(
                &later_currents,
                &[],
                &[RegionalRelationCell::new(lineages[2], &recurring_arcs)],
            ))
            .unwrap();
        reversed
            .receive(ContemporaryEvent::with_regional(
                &later_currents,
                &[],
                &[RegionalRelationCell::new(lineages[2], &reversed_arcs)],
            ))
            .unwrap();

        assert_eq!(recurring_radiation.regional()[0].constituent().grain(), 3);
        assert_eq!(
            recurring_radiation.regional()[0].arcs()[0]
                .arc()
                .receiver_passage(),
            recurring_arcs[0].receiver_passage()
        );
        assert_eq!(recurring.standing().constituents().len(), 1);
        assert_eq!(reversed.standing().constituents().len(), 2);
        assert_ne!(recurring.standing(), reversed.standing());
        assert!(recurring_radiation.regional()[0]
            .constituent()
            .pins()
            .iter()
            .any(|pin| {
                pin.interface().is_some_and(|interface| {
                    interface.origin() == crate::InterfaceCapabilityOrigin::ReceiverCaused
                }) && pin
                    .formed()
                    .is_some_and(|formed| formed.deed() == FeltDeed::Ride)
            }));
    }

    #[test]
    fn regional_exposed_well_rebases_triangles_and_open_foil_changes_the_later_probe() {
        let (base, lineages) = primed_equal_lineages(3);
        let rest = base.rest_image().unwrap();
        let mut taught = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
        let mut control = LiveCurrentMachine::from_rest_image(rest).unwrap();
        let seed_arcs = situated_triangle_arcs(
            [lineages[0], lineages[1], lineages[2]],
            [17, 29, 43],
            IncidenceHand::Against,
        );
        let seed_regional = [RegionalRelationCell::new(lineages[2], &seed_arcs)];

        let seed_currents = [
            CurrentEvent::continuing(lineages[0], relation(17), action()),
            CurrentEvent::continuing(lineages[1], relation(29), action()),
            CurrentEvent::continuing(lineages[2], relation(43), action()),
        ];
        let seed = taught
            .receive(ContemporaryEvent::with_regional(
                &seed_currents,
                &[],
                &seed_regional,
            ))
            .unwrap();
        control
            .receive(ContemporaryEvent::unrelated(&seed_currents))
            .unwrap();
        let seed_rest = taught.rest_image().unwrap();
        let mut reversed = LiveCurrentMachine::from_rest_image(seed_rest.clone()).unwrap();
        let mut permuted = LiveCurrentMachine::from_rest_image(seed_rest.clone()).unwrap();
        let mut overlapping = LiveCurrentMachine::from_rest_image(seed_rest).unwrap();

        let bridge_currents = [
            CurrentEvent::continuing(lineages[0], relation(17), action()),
            CurrentEvent::continuing(lineages[1], relation(29), action()),
            CurrentEvent::continuing(lineages[2], relation(71), action()),
        ];
        let bridge_arcs = situated_triangle_arcs(
            [lineages[0], lineages[1], lineages[2]],
            [17, 29, 71],
            IncidenceHand::Against,
        );
        let bridge_regional = [RegionalRelationCell::new(lineages[2], &bridge_arcs)];
        let bridge_taught = taught
            .receive(ContemporaryEvent::with_regional(
                &bridge_currents,
                &[],
                &bridge_regional,
            ))
            .unwrap();
        let bridge_control = control
            .receive(ContemporaryEvent::with_regional(
                &bridge_currents,
                &[],
                &bridge_regional,
            ))
            .unwrap();
        let reversed_arcs = [
            RegionalRelationArc::new(
                lineages[0],
                CurrentBoundaryPort::Cell,
                lineages[1],
                CurrentBoundaryPort::Cell,
                bridge_arcs[0].interface(),
                0,
                0,
                IncidenceHand::With,
            ),
            bridge_arcs[1].clone(),
            bridge_arcs[2].clone(),
        ];
        let reversed_regional = [RegionalRelationCell::new(lineages[2], &reversed_arcs)];
        let bridge_reversed = reversed
            .receive(ContemporaryEvent::with_regional(
                &bridge_currents,
                &[],
                &reversed_regional,
            ))
            .unwrap();
        let permuted_arcs = [
            bridge_arcs[2].clone(),
            bridge_arcs[0].clone(),
            bridge_arcs[1].clone(),
        ];
        let permuted_regional = [RegionalRelationCell::new(lineages[2], &permuted_arcs)];
        permuted
            .receive(ContemporaryEvent::with_regional(
                &bridge_currents,
                &[],
                &permuted_regional,
            ))
            .unwrap();
        assert_same_machine(&taught, &permuted);
        let overlap_before = overlapping.rest_image().unwrap();
        let overlap = overlapping
            .receive(ContemporaryEvent::with_regional(
                &bridge_currents,
                &[],
                &[bridge_regional[0], bridge_regional[0]],
            ))
            .unwrap();
        assert_ne!(overlapping.rest_image().unwrap(), overlap_before);
        assert_eq!(overlap.regional().len(), 2);
        assert_eq!(
            overlap.regional()[0].constituent(),
            overlap.regional()[1].constituent()
        );
        assert_eq!(overlapping.standing().constituents().len(), 1);

        let seed = seed.regional()[0].constituent();
        let bridge_taught = bridge_taught.regional()[0].constituent();
        let bridge_control = bridge_control.regional()[0].constituent();
        let bridge_reversed = bridge_reversed.regional()[0].constituent();
        assert_eq!(seed.grain(), 2);
        assert_eq!(seed.exposed().len(), 3);
        assert!(seed.pins()[1..].iter().all(|pin| {
            pin.transport_position() == seed.pins()[0].transport_position()
                && pin.meeting().arrow.reach != seed.pins()[0].meeting().arrow.reach
        }));
        assert_eq!(
            bridge_control.pins()[0].meeting().arrow.reach,
            seed.pins()[0].meeting().arrow.reach
        );
        assert_ne!(
            bridge_control.pins()[0].transport_position(),
            seed.pins()[0].transport_position()
        );
        assert_eq!(bridge_taught.grain(), 3);
        assert_eq!(bridge_taught.axis_count(), 1);
        assert_eq!(bridge_taught.incidences().len(), 6);
        // Only the recurring first boundary closes. The other two seed sections and the other
        // two arriving sections remain independently exposed instead of being imported as one
        // whole-triangle parent.
        assert_eq!(bridge_taught.exposed().len(), 4);
        assert!(bridge_taught.boundaries().last().unwrap().paths()[0].interior_folded());
        assert!(bridge_taught.boundaries().last().unwrap().paths()[0]
            .steps()
            .is_empty());
        assert!(!bridge_taught.boundaries().last().unwrap().paths()[0]
            .transport()
            .terms()
            .is_empty());
        assert_eq!(bridge_control.grain(), 2);
        assert_eq!(bridge_reversed.grain(), 3);
        assert_eq!(bridge_reversed.axis_count(), 1);
        assert_eq!(bridge_reversed.exposed().len(), 5);
        assert!(bridge_taught.pins().iter().all(|pin| {
            pin.formed()
                .is_some_and(|formed| formed.deed() == FeltDeed::Ride)
        }));
        let reversed_comparison = bridge_reversed.pins().last().unwrap();
        assert!(reversed_comparison.is_open());
        assert!(!reversed_comparison.is_found());
        assert!(reversed_comparison.comparison().chi().is_some());
        assert_eq!(taught.standing().constituents().len(), 1);
        assert_eq!(&taught.standing().constituents()[0], bridge_taught);

        let mut remounted =
            LiveCurrentMachine::from_rest_image(taught.rest_image().unwrap()).unwrap();
        assert_same_machine(&taught, &remounted);

        let probe_currents = [
            CurrentEvent::continuing(lineages[0], relation(29), action()),
            CurrentEvent::continuing(lineages[1], relation(71), action()),
            CurrentEvent::continuing(lineages[2], relation(97), action()),
        ];
        let probe_arcs = situated_triangle_arcs(
            [lineages[0], lineages[1], lineages[2]],
            [29, 71, 97],
            IncidenceHand::Against,
        );
        let probe_regional = [RegionalRelationCell::new(lineages[2], &probe_arcs)];
        let probe_taught = remounted
            .receive(ContemporaryEvent::with_regional(
                &probe_currents,
                &[],
                &probe_regional,
            ))
            .unwrap();
        let probe_control = control
            .receive(ContemporaryEvent::with_regional(
                &probe_currents,
                &[],
                &probe_regional,
            ))
            .unwrap();
        assert_eq!(probe_taught.regional()[0].constituent().grain(), 4);
        assert_eq!(probe_control.regional()[0].constituent().grain(), 3);
        assert_eq!(remounted.standing().constituents().len(), 1);
    }

    #[test]
    fn open_comparison_stands_and_later_interface_contact_is_not_blacklisted() {
        fn fresh() -> (LiveCurrentMachine, [CurrentLineage; 3]) {
            let mut machine =
                LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
            let lineages = [
                machine.attach(CurrentGeometry::Cell(relation(13))).unwrap(),
                machine.attach(CurrentGeometry::Cell(relation(13))).unwrap(),
                machine.attach(CurrentGeometry::Cell(relation(13))).unwrap(),
            ];
            (machine, lineages)
        }

        let (mut situated, lineages) = fresh();
        let (mut control, control_lineages) = fresh();
        assert_eq!(lineages, control_lineages);

        let arcs = situated_triangle_arcs(lineages, [17, 29, 43], IncidenceHand::Against);
        let regional = [RegionalRelationCell::new(lineages[2], &arcs)];
        let opening_currents = [
            CurrentEvent::continuing(lineages[0], relation(13), action()),
            CurrentEvent::continuing(lineages[1], relation(13), action()),
            CurrentEvent::continuing(lineages[2], relation(13), action()),
        ];

        let first = situated
            .receive(ContemporaryEvent::with_regional(
                &opening_currents,
                &[],
                &regional,
            ))
            .unwrap();
        control
            .receive(ContemporaryEvent::unrelated(&opening_currents))
            .unwrap();
        let opening = first.regional()[0].constituent().clone();
        let open_comparisons: Vec<_> = opening
            .pins()
            .iter()
            .filter(|pin| pin.is_open())
            .map(LivePin::comparison)
            .collect();
        assert!(!open_comparisons.is_empty());
        assert!(open_comparisons
            .iter()
            .all(|comparison| comparison.through() != comparison.direct()));
        assert!(opening.pins().iter().all(|pin| !pin.is_found()));

        let first_rest = situated.rest_image().unwrap();
        let first_wire = first_rest.encode_native_words().unwrap();
        let first_reopened = LiveCurrentRestImage::from_native_words(&first_wire).unwrap();
        let mut situated = LiveCurrentMachine::from_rest_image(first_reopened).unwrap();
        assert_eq!(situated.standing().constituents(), &[opening.clone()]);

        // This is the fixed receiver-development sequence already used by
        // `primed_equal_lineages`; it is not selected from this test's outcome. The first failed
        // attempt established that a second timestamp alone does not make a bridge.
        for value in [29, 17, 31, -63_245, 47, 71, -89] {
            let current = [
                CurrentEvent::continuing(lineages[0], relation(value), action()),
                CurrentEvent::continuing(lineages[1], relation(value), action()),
                CurrentEvent::continuing(lineages[2], relation(value), action()),
            ];
            situated
                .receive(ContemporaryEvent::unrelated(&current))
                .unwrap();
            control
                .receive(ContemporaryEvent::unrelated(&current))
                .unwrap();
        }

        let later_currents = [
            CurrentEvent::continuing(lineages[0], relation(17), action()),
            CurrentEvent::continuing(lineages[1], relation(29), action()),
            CurrentEvent::continuing(lineages[2], relation(43), action()),
        ];

        let later = situated
            .receive(ContemporaryEvent::with_regional(
                &later_currents,
                &[],
                &regional,
            ))
            .unwrap();
        let control_later = control
            .receive(ContemporaryEvent::with_regional(
                &later_currents,
                &[],
                &regional,
            ))
            .unwrap();
        let later_body = later.regional()[0].constituent();
        let control_body = control_later.regional()[0].constituent();
        assert!(later.regional()[0]
            .arcs()
            .iter()
            .any(|arc| arc.contact().emission.is_some()));
        assert!(later_body.grain() > control_body.grain());
        assert_ne!(later_body, control_body);

        let new_comparisons: Vec<_> = later_body
            .pins()
            .iter()
            .filter(|pin| !opening.pins().contains(pin) && !control_body.pins().contains(pin))
            .collect();
        assert!(!new_comparisons.is_empty());
        assert!(new_comparisons.iter().all(|pin| !pin.is_found()));
        assert!(new_comparisons.iter().any(|pin| pin.is_open()));
        assert!(open_comparisons.iter().all(|comparison| later_body
            .pins()
            .iter()
            .any(|pin| pin.comparison() == *comparison)));

        let ending = [
            CurrentEvent::ending(lineages[0], relation(17), action()),
            CurrentEvent::ending(lineages[1], relation(29), action()),
            CurrentEvent::ending(lineages[2], relation(43), action()),
        ];
        situated
            .receive(ContemporaryEvent::unrelated(&ending))
            .unwrap();
        assert_eq!(situated.memory().live_lineages, 0);
        assert_eq!(situated.standing().constituents().len(), 1);
        let final_rest = situated.rest_image().unwrap();
        let remounted = LiveCurrentMachine::from_rest_image(
            LiveCurrentRestImage::from_native_words(&final_rest.encode_native_words().unwrap())
                .unwrap(),
        )
        .unwrap();
        assert_eq!(remounted.standing(), situated.standing());
    }

    #[test]
    fn an_unreceived_seed_cannot_masquerade_as_rest() {
        let first = [relation(13)];
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let lineage = machine.attach(CurrentGeometry::Cell(first[0])).unwrap();
        assert!(matches!(
            machine.rest_image(),
            Err(LiveCurrentError::UnsettledRest(open)) if open == lineage
        ));
    }
}
