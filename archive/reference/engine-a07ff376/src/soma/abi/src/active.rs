//! The native active-cut grammar.
//!
//! A source organ keeps ownership of world material and exposes only the exact relation topology
//! which became incident: canonical Soma relation atoms, each event's supplied action current,
//! their ordered event/current extents, sparse cut incidence, and any causal hand actually supplied
//! by that world.  No event tag,
//! serialized payload, path, modality, category, score, or semantic identity appears here.
//!
//! Every extent is 64-bit.  These rows own no allocation and choose no device sharding.  [`View`]
//! validates a borrowed population as one complete cut body before any mutation can occur.

use body::manifold::Node;
use body::num::{self, Cog, COG_WORDS};
use body::place::{self, Place};
use core::mem::{align_of, size_of};

pub const LAYOUT_VERSION: u32 = 1;

#[inline]
const fn u64_words(value: u64) -> [u32; 2] {
    [value as u32, (value >> 32) as u32]
}

#[inline]
const fn u64_from_words(lo: u32, hi: u32) -> u64 {
    lo as u64 | ((hi as u64) << 32)
}

#[inline]
const fn nonempty_extent_fits(offset: u64, extent: u64) -> bool {
    extent != 0 && offset.checked_add(extent).is_some()
}

#[inline]
const fn extent_within(offset: u64, extent: u64, total: u64) -> bool {
    match offset.checked_add(extent) {
        Some(end) => extent != 0 && end <= total,
        None => false,
    }
}

pub const HEADER_VERSION: usize = 0;
pub const HEADER_ATOMS_LO: usize = 1;
pub const HEADER_ATOMS_HI: usize = 2;
pub const HEADER_EVENTS_LO: usize = 3;
pub const HEADER_EVENTS_HI: usize = 4;
pub const HEADER_CURRENTS_LO: usize = 5;
pub const HEADER_CURRENTS_HI: usize = 6;
pub const HEADER_CUTS_LO: usize = 7;
pub const HEADER_CUTS_HI: usize = 8;
pub const HEADER_INCIDENCES_LO: usize = 9;
pub const HEADER_INCIDENCES_HI: usize = 10;
pub const HEADER_DIRECTED_LO: usize = 11;
pub const HEADER_DIRECTED_HI: usize = 12;
pub const HEADER_WORDS: usize = 13;

/// Exact population extents for one active-cut body.  Directed incidence may be empty; every
/// other population is material to a non-empty contact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Header(pub [u32; HEADER_WORDS]);

impl Header {
    #[inline]
    pub const fn new(
        atoms: u64,
        events: u64,
        currents: u64,
        cuts: u64,
        incidences: u64,
        directed: u64,
    ) -> Option<Self> {
        if atoms == 0 || events == 0 || currents == 0 || cuts == 0 || incidences == 0 {
            return None;
        }
        let atoms = u64_words(atoms);
        let events = u64_words(events);
        let currents = u64_words(currents);
        let cuts = u64_words(cuts);
        let incidences = u64_words(incidences);
        let directed = u64_words(directed);
        Some(Self([
            LAYOUT_VERSION,
            atoms[0],
            atoms[1],
            events[0],
            events[1],
            currents[0],
            currents[1],
            cuts[0],
            cuts[1],
            incidences[0],
            incidences[1],
            directed[0],
            directed[1],
        ]))
    }

    #[inline]
    pub const fn from_words(words: [u32; HEADER_WORDS]) -> Option<Self> {
        if words[HEADER_VERSION] != LAYOUT_VERSION {
            return None;
        }
        Self::new(
            u64_from_words(words[HEADER_ATOMS_LO], words[HEADER_ATOMS_HI]),
            u64_from_words(words[HEADER_EVENTS_LO], words[HEADER_EVENTS_HI]),
            u64_from_words(words[HEADER_CURRENTS_LO], words[HEADER_CURRENTS_HI]),
            u64_from_words(words[HEADER_CUTS_LO], words[HEADER_CUTS_HI]),
            u64_from_words(words[HEADER_INCIDENCES_LO], words[HEADER_INCIDENCES_HI]),
            u64_from_words(words[HEADER_DIRECTED_LO], words[HEADER_DIRECTED_HI]),
        )
    }

    #[inline]
    pub const fn atoms(self) -> u64 {
        u64_from_words(self.0[HEADER_ATOMS_LO], self.0[HEADER_ATOMS_HI])
    }

    #[inline]
    pub const fn events(self) -> u64 {
        u64_from_words(self.0[HEADER_EVENTS_LO], self.0[HEADER_EVENTS_HI])
    }

    #[inline]
    pub const fn currents(self) -> u64 {
        u64_from_words(self.0[HEADER_CURRENTS_LO], self.0[HEADER_CURRENTS_HI])
    }

    #[inline]
    pub const fn cuts(self) -> u64 {
        u64_from_words(self.0[HEADER_CUTS_LO], self.0[HEADER_CUTS_HI])
    }

    #[inline]
    pub const fn incidences(self) -> u64 {
        u64_from_words(self.0[HEADER_INCIDENCES_LO], self.0[HEADER_INCIDENCES_HI])
    }

    #[inline]
    pub const fn directed(self) -> u64 {
        u64_from_words(self.0[HEADER_DIRECTED_LO], self.0[HEADER_DIRECTED_HI])
    }

    #[inline]
    pub const fn words(self) -> [u32; HEADER_WORDS] {
        self.0
    }
}

/// One canonical Soma relation atom.  A world transducer derives this from material relation; it
/// is never the transducer's serialized event record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct RelationAtom(pub [u32; COG_WORDS]);

impl RelationAtom {
    #[inline]
    pub fn new(cog: Cog) -> Option<Self> {
        let mut words = [0u32; COG_WORDS];
        let mut word = 0usize;
        while word < COG_WORDS {
            words[word] = num::cog_packed_word(cog, word);
            word += 1;
        }
        Self::from_words(words)
    }

    #[inline]
    pub fn from_words(words: [u32; COG_WORDS]) -> Option<Self> {
        if num::packed_cog_is_canonical(&words, 0) {
            Some(Self(words))
        } else {
            None
        }
    }

    #[inline]
    pub fn cog(self) -> Cog {
        num::read_cog(&self.0, 0)
    }

    #[inline]
    pub const fn words(self) -> [u32; COG_WORDS] {
        self.0
    }
}

fn extend_magnitude(mut position: Place, magnitude: u32) -> (Place, u32) {
    let mut top = 0u32;
    let mut rest = magnitude >> 1;
    while rest != 0 {
        rest >>= 1;
        top += 1;
    }
    let extent = top + 1;
    let mut bit = top as i32;
    while bit >= 0 {
        position = place::extend(position, (magnitude >> bit as u32) & 1 == 1);
        bit -= 1;
    }
    (position, extent)
}

fn extend_gamma(mut position: Place, value: u32) -> (Place, u32) {
    let encoded = value as u64 + 1;
    let top = 63 - encoded.leading_zeros();
    let mut zeros = top;
    while zeros != 0 {
        position = place::extend(position, false);
        zeros -= 1;
    }
    let mut bit = top as i32;
    while bit >= 0 {
        position = place::extend(position, ((encoded >> bit as u32) & 1) == 1);
        bit -= 1;
    }
    (position, top * 2 + 1)
}

fn extend_relation_atom(mut position: Place, atom: RelationAtom) -> (Place, u32) {
    let cog = atom.cog();
    let mut len = 0u32;
    for field in [cog.mag, cog.rank.mag, cog.rank.rank as u32] {
        let (next, added) = extend_gamma(position, field);
        position = next;
        len += added;
    }
    position = place::extend(position, cog.rank.neg);
    position = place::extend(position, (cog.turn & 2) != 0);
    position = place::extend(position, (cog.turn & 1) != 0);
    (position, len + 3)
}

/// Compose one complete ordered event directly from its canonical relation atoms.  This function
/// is part of the substrate-neutral ABI law so host and device mouths cannot silently choose
/// different event geometry.  `None` means only an empty span or a length overflow.
pub fn relation_span_node(atoms: &[RelationAtom]) -> Option<Node> {
    let first = atoms.first().copied()?;
    let mut well = first.cog();
    let (mut position, mut len) = if atoms.len() == 1 {
        extend_magnitude(place::origin(), well.mag)
    } else {
        extend_relation_atom(place::origin(), first)
    };
    for atom in &atoms[1..] {
        let relation = atom.cog();
        well = well.mul(relation);
        let (next, added) = extend_relation_atom(position, *atom);
        position = next;
        len = len.checked_add(added)?;
    }
    Some(Node {
        well,
        place: position,
        len,
    })
}

/// A1's supplied action current for one event.  It shares Soma's canonical number construction
/// with a relation atom but remains a distinct type: what arrived and the action under which it
/// arrived may not be collapsed.  There is exactly one row per [`EventSpan`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct ActionCurrent(pub [u32; COG_WORDS]);

impl ActionCurrent {
    #[inline]
    pub fn new(action: Cog) -> Option<Self> {
        // A1 supplies a real current. A zero construction is absence of an event action, not a
        // second spelling of one; relation atoms may still be zero because sameness is material.
        if action.mag == 0 {
            return None;
        }
        let mut words = [0u32; COG_WORDS];
        let mut word = 0usize;
        while word < COG_WORDS {
            words[word] = num::cog_packed_word(action, word);
            word += 1;
        }
        Self::from_words(words)
    }

    #[inline]
    pub fn from_words(words: [u32; COG_WORDS]) -> Option<Self> {
        if !num::packed_cog_is_canonical(&words, 0) {
            return None;
        }
        let action = num::read_cog(&words, 0);
        (action.mag != 0).then_some(Self(words))
    }

    #[inline]
    pub fn cog(self) -> Cog {
        num::read_cog(&self.0, 0)
    }

    #[inline]
    pub const fn words(self) -> [u32; COG_WORDS] {
        self.0
    }
}

pub const EVENT_ATOM_OFFSET_LO: usize = 0;
pub const EVENT_ATOM_OFFSET_HI: usize = 1;
pub const EVENT_ATOMS_LO: usize = 2;
pub const EVENT_ATOMS_HI: usize = 3;
pub const EVENT_WORDS: usize = 4;

/// One ordered, non-empty atom span making a source-organ event.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct EventSpan(pub [u32; EVENT_WORDS]);

impl EventSpan {
    #[inline]
    pub const fn new(atom_offset: u64, atoms: u64) -> Option<Self> {
        if !nonempty_extent_fits(atom_offset, atoms) {
            return None;
        }
        let offset = u64_words(atom_offset);
        let extent = u64_words(atoms);
        Some(Self([offset[0], offset[1], extent[0], extent[1]]))
    }

    #[inline]
    pub const fn from_words(words: [u32; EVENT_WORDS]) -> Option<Self> {
        Self::new(
            u64_from_words(words[EVENT_ATOM_OFFSET_LO], words[EVENT_ATOM_OFFSET_HI]),
            u64_from_words(words[EVENT_ATOMS_LO], words[EVENT_ATOMS_HI]),
        )
    }

    #[inline]
    pub const fn atom_offset(self) -> u64 {
        u64_from_words(self.0[EVENT_ATOM_OFFSET_LO], self.0[EVENT_ATOM_OFFSET_HI])
    }

    #[inline]
    pub const fn atoms(self) -> u64 {
        u64_from_words(self.0[EVENT_ATOMS_LO], self.0[EVENT_ATOMS_HI])
    }

    #[inline]
    pub const fn words(self) -> [u32; EVENT_WORDS] {
        self.0
    }
}

pub const ORIGIN_ORGAN_LO: usize = 0;
pub const ORIGIN_ORGAN_HI: usize = 1;
pub const ORIGIN_OCCURRENCE_LO: usize = 2;
pub const ORIGIN_OCCURRENCE_HI: usize = 3;
pub const ORIGIN_WORDS: usize = 4;

/// Opaque listener provenance for one event.  The source organ assigns both ordinals and retains
/// their reversible world mapping.  This row joins a later Holon receipt to material occurrence;
/// it is not relation light and must not influence a Soma deed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct OriginRef(pub [u32; ORIGIN_WORDS]);

impl OriginRef {
    #[inline]
    pub const fn new(organ: u64, occurrence: u64) -> Self {
        let organ = u64_words(organ);
        let occurrence = u64_words(occurrence);
        Self([organ[0], organ[1], occurrence[0], occurrence[1]])
    }

    #[inline]
    pub const fn from_words(words: [u32; ORIGIN_WORDS]) -> Self {
        Self(words)
    }

    #[inline]
    pub const fn organ(self) -> u64 {
        u64_from_words(self.0[ORIGIN_ORGAN_LO], self.0[ORIGIN_ORGAN_HI])
    }

    #[inline]
    pub const fn occurrence(self) -> u64 {
        u64_from_words(self.0[ORIGIN_OCCURRENCE_LO], self.0[ORIGIN_OCCURRENCE_HI])
    }

    #[inline]
    pub const fn words(self) -> [u32; ORIGIN_WORDS] {
        self.0
    }
}

pub const CURRENT_EVENT_OFFSET_LO: usize = 0;
pub const CURRENT_EVENT_OFFSET_HI: usize = 1;
pub const CURRENT_EVENTS_LO: usize = 2;
pub const CURRENT_EVENTS_HI: usize = 3;
pub const CURRENT_ATOM_OFFSET_LO: usize = 4;
pub const CURRENT_ATOM_OFFSET_HI: usize = 5;
pub const CURRENT_ATOMS_LO: usize = 6;
pub const CURRENT_ATOMS_HI: usize = 7;
pub const CURRENT_WORDS: usize = 8;

/// One ordered event sequence and its exact atom extent.  The atom extent is retained explicitly
/// so a substrate can shard currents without scanning event rows; validation proves the two faces
/// agree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct CurrentSpan(pub [u32; CURRENT_WORDS]);

impl CurrentSpan {
    #[inline]
    pub const fn new(event_offset: u64, events: u64, atom_offset: u64, atoms: u64) -> Option<Self> {
        if !nonempty_extent_fits(event_offset, events) || !nonempty_extent_fits(atom_offset, atoms)
        {
            return None;
        }
        let event_offset = u64_words(event_offset);
        let events = u64_words(events);
        let atom_offset = u64_words(atom_offset);
        let atoms = u64_words(atoms);
        Some(Self([
            event_offset[0],
            event_offset[1],
            events[0],
            events[1],
            atom_offset[0],
            atom_offset[1],
            atoms[0],
            atoms[1],
        ]))
    }

    #[inline]
    pub const fn from_words(words: [u32; CURRENT_WORDS]) -> Option<Self> {
        Self::new(
            u64_from_words(
                words[CURRENT_EVENT_OFFSET_LO],
                words[CURRENT_EVENT_OFFSET_HI],
            ),
            u64_from_words(words[CURRENT_EVENTS_LO], words[CURRENT_EVENTS_HI]),
            u64_from_words(words[CURRENT_ATOM_OFFSET_LO], words[CURRENT_ATOM_OFFSET_HI]),
            u64_from_words(words[CURRENT_ATOMS_LO], words[CURRENT_ATOMS_HI]),
        )
    }

    #[inline]
    pub const fn event_offset(self) -> u64 {
        u64_from_words(
            self.0[CURRENT_EVENT_OFFSET_LO],
            self.0[CURRENT_EVENT_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn events(self) -> u64 {
        u64_from_words(self.0[CURRENT_EVENTS_LO], self.0[CURRENT_EVENTS_HI])
    }

    #[inline]
    pub const fn atom_offset(self) -> u64 {
        u64_from_words(
            self.0[CURRENT_ATOM_OFFSET_LO],
            self.0[CURRENT_ATOM_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn atoms(self) -> u64 {
        u64_from_words(self.0[CURRENT_ATOMS_LO], self.0[CURRENT_ATOMS_HI])
    }

    #[inline]
    pub const fn words(self) -> [u32; CURRENT_WORDS] {
        self.0
    }
}

pub const CUT_INCIDENCE_OFFSET_LO: usize = 0;
pub const CUT_INCIDENCE_OFFSET_HI: usize = 1;
pub const CUT_INCIDENCES_LO: usize = 2;
pub const CUT_INCIDENCES_HI: usize = 3;
pub const CUT_DIRECTED_OFFSET_LO: usize = 4;
pub const CUT_DIRECTED_OFFSET_HI: usize = 5;
pub const CUT_DIRECTED_LO: usize = 6;
pub const CUT_DIRECTED_HI: usize = 7;
pub const CUT_WORDS: usize = 8;

/// One sparse contact cut.  A cut may carry a single incidence and therefore no directed pair;
/// the canonical empty directed span is `(0, 0)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct CutSpan(pub [u32; CUT_WORDS]);

impl CutSpan {
    #[inline]
    pub const fn new(
        incidence_offset: u64,
        incidences: u64,
        directed_offset: u64,
        directed: u64,
    ) -> Option<Self> {
        if !nonempty_extent_fits(incidence_offset, incidences)
            || (directed == 0 && directed_offset != 0)
            || (directed != 0 && !nonempty_extent_fits(directed_offset, directed))
        {
            return None;
        }
        let incidence_offset = u64_words(incidence_offset);
        let incidences = u64_words(incidences);
        let directed_offset = u64_words(directed_offset);
        let directed = u64_words(directed);
        Some(Self([
            incidence_offset[0],
            incidence_offset[1],
            incidences[0],
            incidences[1],
            directed_offset[0],
            directed_offset[1],
            directed[0],
            directed[1],
        ]))
    }

    #[inline]
    pub const fn from_words(words: [u32; CUT_WORDS]) -> Option<Self> {
        Self::new(
            u64_from_words(
                words[CUT_INCIDENCE_OFFSET_LO],
                words[CUT_INCIDENCE_OFFSET_HI],
            ),
            u64_from_words(words[CUT_INCIDENCES_LO], words[CUT_INCIDENCES_HI]),
            u64_from_words(words[CUT_DIRECTED_OFFSET_LO], words[CUT_DIRECTED_OFFSET_HI]),
            u64_from_words(words[CUT_DIRECTED_LO], words[CUT_DIRECTED_HI]),
        )
    }

    #[inline]
    pub const fn incidence_offset(self) -> u64 {
        u64_from_words(
            self.0[CUT_INCIDENCE_OFFSET_LO],
            self.0[CUT_INCIDENCE_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn incidences(self) -> u64 {
        u64_from_words(self.0[CUT_INCIDENCES_LO], self.0[CUT_INCIDENCES_HI])
    }

    #[inline]
    pub const fn directed_offset(self) -> u64 {
        u64_from_words(
            self.0[CUT_DIRECTED_OFFSET_LO],
            self.0[CUT_DIRECTED_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn directed(self) -> u64 {
        u64_from_words(self.0[CUT_DIRECTED_LO], self.0[CUT_DIRECTED_HI])
    }

    #[inline]
    pub const fn words(self) -> [u32; CUT_WORDS] {
        self.0
    }
}

pub const INCIDENCE_CURRENT_LO: usize = 0;
pub const INCIDENCE_CURRENT_HI: usize = 1;
pub const INCIDENCE_CURRENT_EVENT_OFFSET_LO: usize = 2;
pub const INCIDENCE_CURRENT_EVENT_OFFSET_HI: usize = 3;
pub const INCIDENCE_CURRENT_EVENTS_LO: usize = 4;
pub const INCIDENCE_CURRENT_EVENTS_HI: usize = 5;
pub const INCIDENCE_WORDS: usize = 6;

/// One physical occurrence of a current-local event span in a cut.  Repeated rows retain physical
/// multiplicity.  Event offsets are relative to the named current.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Incidence(pub [u32; INCIDENCE_WORDS]);

impl Incidence {
    #[inline]
    pub const fn new(current: u64, current_event_offset: u64, current_events: u64) -> Option<Self> {
        if !nonempty_extent_fits(current_event_offset, current_events) {
            return None;
        }
        let current = u64_words(current);
        let event_offset = u64_words(current_event_offset);
        let events = u64_words(current_events);
        Some(Self([
            current[0],
            current[1],
            event_offset[0],
            event_offset[1],
            events[0],
            events[1],
        ]))
    }

    #[inline]
    pub const fn from_words(words: [u32; INCIDENCE_WORDS]) -> Option<Self> {
        Self::new(
            u64_from_words(words[INCIDENCE_CURRENT_LO], words[INCIDENCE_CURRENT_HI]),
            u64_from_words(
                words[INCIDENCE_CURRENT_EVENT_OFFSET_LO],
                words[INCIDENCE_CURRENT_EVENT_OFFSET_HI],
            ),
            u64_from_words(
                words[INCIDENCE_CURRENT_EVENTS_LO],
                words[INCIDENCE_CURRENT_EVENTS_HI],
            ),
        )
    }

    #[inline]
    pub const fn current(self) -> u64 {
        u64_from_words(self.0[INCIDENCE_CURRENT_LO], self.0[INCIDENCE_CURRENT_HI])
    }

    #[inline]
    pub const fn current_event_offset(self) -> u64 {
        u64_from_words(
            self.0[INCIDENCE_CURRENT_EVENT_OFFSET_LO],
            self.0[INCIDENCE_CURRENT_EVENT_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn current_events(self) -> u64 {
        u64_from_words(
            self.0[INCIDENCE_CURRENT_EVENTS_LO],
            self.0[INCIDENCE_CURRENT_EVENTS_HI],
        )
    }

    #[inline]
    pub const fn words(self) -> [u32; INCIDENCE_WORDS] {
        self.0
    }
}

pub const DIRECTED_FROM_INCIDENCE_LO: usize = 0;
pub const DIRECTED_FROM_INCIDENCE_HI: usize = 1;
pub const DIRECTED_TO_INCIDENCE_LO: usize = 2;
pub const DIRECTED_TO_INCIDENCE_HI: usize = 3;
pub const DIRECTED_WORDS: usize = 4;

/// One source-supplied causal hand between two incidences in the same cut.  It is an ordered edge,
/// not a semantic predicate or an instruction to select either endpoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct DirectedIncidence(pub [u32; DIRECTED_WORDS]);

impl DirectedIncidence {
    #[inline]
    pub const fn new(from_incidence: u64, to_incidence: u64) -> Self {
        let from = u64_words(from_incidence);
        let to = u64_words(to_incidence);
        Self([from[0], from[1], to[0], to[1]])
    }

    #[inline]
    pub const fn from_words(words: [u32; DIRECTED_WORDS]) -> Self {
        Self(words)
    }

    #[inline]
    pub const fn from_incidence(self) -> u64 {
        u64_from_words(
            self.0[DIRECTED_FROM_INCIDENCE_LO],
            self.0[DIRECTED_FROM_INCIDENCE_HI],
        )
    }

    #[inline]
    pub const fn to_incidence(self) -> u64 {
        u64_from_words(
            self.0[DIRECTED_TO_INCIDENCE_LO],
            self.0[DIRECTED_TO_INCIDENCE_HI],
        )
    }

    #[inline]
    pub const fn words(self) -> [u32; DIRECTED_WORDS] {
        self.0
    }
}

/// Structural refusal from validating a complete borrowed active-cut population.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValidationError {
    PopulationExtent,
    ScratchExtent,
    CoverageOverflow,
    RelationAtom(u64),
    ActionCurrent(u64),
    EventPartition(u64),
    CurrentPartition(u64),
    CurrentEventAtoms(u64),
    CutPartition(u64),
    Incidence(u64),
    DirectedIncidence(u64),
    UnreferencedCurrent(u64),
    UnreferencedEvent(u64),
}

/// A complete borrowed active-cut population.  Validation is allocation-free and makes no
/// observer interpretation; it proves canonical atoms, exact partitions, and in-cut references.
pub struct View<'a> {
    pub header: Header,
    pub atoms: &'a [RelationAtom],
    pub events: &'a [EventSpan],
    pub actions: &'a [ActionCurrent],
    pub origins: &'a [OriginRef],
    pub currents: &'a [CurrentSpan],
    pub cuts: &'a [CutSpan],
    pub incidences: &'a [Incidence],
    pub directed: &'a [DirectedIncidence],
}

impl<'a> View<'a> {
    /// Reborrow one canonical packed active population as its typed rows without allocating or
    /// interpreting the words as relation light.  This is the CUDA transport inverse of the host
    /// owner's durable wire: every row wrapper is transparent over whole `u32` words, all extents
    /// close before a slice exists, and ordinary view validation still precedes conduct.
    pub fn from_wire_words(words: &'a [u32]) -> Option<Self> {
        let header_words: [u32; HEADER_WORDS] = words.get(..HEADER_WORDS)?.try_into().ok()?;
        let header = Header::from_words(header_words)?;
        let mut cursor = HEADER_WORDS;

        unsafe fn take_rows<'a, T>(
            words: &'a [u32],
            cursor: &mut usize,
            rows: u64,
            row_words: usize,
        ) -> Option<&'a [T]> {
            if size_of::<T>() != row_words.checked_mul(size_of::<u32>())?
                || align_of::<T>() > align_of::<u32>()
            {
                return None;
            }
            let rows = usize::try_from(rows).ok()?;
            let extent = rows.checked_mul(row_words)?;
            let after = cursor.checked_add(extent)?;
            let source = words.get(*cursor..after)?;
            *cursor = after;
            Some(unsafe { core::slice::from_raw_parts(source.as_ptr().cast::<T>(), rows) })
        }

        let atoms =
            unsafe { take_rows::<RelationAtom>(words, &mut cursor, header.atoms(), COG_WORDS)? };
        let events =
            unsafe { take_rows::<EventSpan>(words, &mut cursor, header.events(), EVENT_WORDS)? };
        let actions =
            unsafe { take_rows::<ActionCurrent>(words, &mut cursor, header.events(), COG_WORDS)? };
        let origins =
            unsafe { take_rows::<OriginRef>(words, &mut cursor, header.events(), ORIGIN_WORDS)? };
        let currents = unsafe {
            take_rows::<CurrentSpan>(words, &mut cursor, header.currents(), CURRENT_WORDS)?
        };
        let cuts = unsafe { take_rows::<CutSpan>(words, &mut cursor, header.cuts(), CUT_WORDS)? };
        let incidences = unsafe {
            take_rows::<Incidence>(words, &mut cursor, header.incidences(), INCIDENCE_WORDS)?
        };
        let directed = unsafe {
            take_rows::<DirectedIncidence>(words, &mut cursor, header.directed(), DIRECTED_WORDS)?
        };
        if cursor != words.len() {
            return None;
        }
        Some(Self {
            header,
            atoms,
            events,
            actions,
            origins,
            currents,
            cuts,
            incidences,
            directed,
        })
    }
}

impl View<'_> {
    /// Validate canonical rows, exact partitions, and in-cut references.  This portion is linear
    /// in the represented populations and requires no scratch storage.
    pub fn validate_structure(&self) -> Result<(), ValidationError> {
        if self.header.atoms() != self.atoms.len() as u64
            || self.header.events() != self.events.len() as u64
            || self.header.events() != self.actions.len() as u64
            || self.header.events() != self.origins.len() as u64
            || self.header.currents() != self.currents.len() as u64
            || self.header.cuts() != self.cuts.len() as u64
            || self.header.incidences() != self.incidences.len() as u64
            || self.header.directed() != self.directed.len() as u64
        {
            return Err(ValidationError::PopulationExtent);
        }

        let mut atom_index = 0usize;
        while atom_index < self.atoms.len() {
            if RelationAtom::from_words(self.atoms[atom_index].words()).is_none() {
                return Err(ValidationError::RelationAtom(atom_index as u64));
            }
            atom_index += 1;
        }

        let mut atom_cursor = 0u64;
        let mut event_index = 0usize;
        while event_index < self.events.len() {
            if ActionCurrent::from_words(self.actions[event_index].words()).is_none() {
                return Err(ValidationError::ActionCurrent(event_index as u64));
            }
            let event = self.events[event_index];
            if event.atom_offset() != atom_cursor
                || !extent_within(event.atom_offset(), event.atoms(), self.header.atoms())
            {
                return Err(ValidationError::EventPartition(event_index as u64));
            }
            atom_cursor += event.atoms();
            event_index += 1;
        }
        if atom_cursor != self.header.atoms() {
            return Err(ValidationError::EventPartition(self.header.events()));
        }

        let mut event_cursor = 0u64;
        atom_cursor = 0;
        let mut current_index = 0usize;
        while current_index < self.currents.len() {
            let current = self.currents[current_index];
            if current.event_offset() != event_cursor
                || current.atom_offset() != atom_cursor
                || !extent_within(
                    current.event_offset(),
                    current.events(),
                    self.header.events(),
                )
                || !extent_within(current.atom_offset(), current.atoms(), self.header.atoms())
            {
                return Err(ValidationError::CurrentPartition(current_index as u64));
            }

            let first_event = current.event_offset() as usize;
            let last_event = (current.event_offset() + current.events() - 1) as usize;
            let first_atom = self.events[first_event].atom_offset();
            let last = self.events[last_event];
            let after_last_atom = last.atom_offset() + last.atoms();
            if first_atom != current.atom_offset()
                || after_last_atom != current.atom_offset() + current.atoms()
            {
                return Err(ValidationError::CurrentEventAtoms(current_index as u64));
            }

            event_cursor += current.events();
            atom_cursor += current.atoms();
            current_index += 1;
        }
        if event_cursor != self.header.events() || atom_cursor != self.header.atoms() {
            return Err(ValidationError::CurrentPartition(self.header.currents()));
        }

        let mut incidence_cursor = 0u64;
        let mut directed_cursor = 0u64;
        let mut cut_index = 0usize;
        while cut_index < self.cuts.len() {
            let cut = self.cuts[cut_index];
            if cut.incidence_offset() != incidence_cursor
                || !extent_within(
                    cut.incidence_offset(),
                    cut.incidences(),
                    self.header.incidences(),
                )
                || (cut.directed() == 0 && cut.directed_offset() != 0)
                || (cut.directed() != 0
                    && (cut.directed_offset() != directed_cursor
                        || !extent_within(
                            cut.directed_offset(),
                            cut.directed(),
                            self.header.directed(),
                        )))
            {
                return Err(ValidationError::CutPartition(cut_index as u64));
            }

            let first_incidence = cut.incidence_offset();
            let after_incidence = first_incidence + cut.incidences();
            let mut local = first_incidence;
            while local < after_incidence {
                let incidence = self.incidences[local as usize];
                if incidence.current() >= self.header.currents() {
                    return Err(ValidationError::Incidence(local));
                }
                let current = self.currents[incidence.current() as usize];
                if !extent_within(
                    incidence.current_event_offset(),
                    incidence.current_events(),
                    current.events(),
                ) {
                    return Err(ValidationError::Incidence(local));
                }
                local += 1;
            }

            if cut.directed() != 0 {
                let mut edge_index = cut.directed_offset();
                let after_edge = edge_index + cut.directed();
                while edge_index < after_edge {
                    let edge = self.directed[edge_index as usize];
                    if edge.from_incidence() < first_incidence
                        || edge.from_incidence() >= after_incidence
                        || edge.to_incidence() < first_incidence
                        || edge.to_incidence() >= after_incidence
                    {
                        return Err(ValidationError::DirectedIncidence(edge_index));
                    }
                    edge_index += 1;
                }
                directed_cursor += cut.directed();
            }

            incidence_cursor += cut.incidences();
            cut_index += 1;
        }
        if incidence_cursor != self.header.incidences() || directed_cursor != self.header.directed()
        {
            return Err(ValidationError::CutPartition(self.header.cuts()));
        }

        Ok(())
    }

    /// Number of signed scratch cells required by [`Self::validate_with_scratch`].  The first
    /// `events + 1` cells form an interval-difference surface; the remaining cells mark currents
    /// which are actually incident.  This scratch is a physical validation instrument, never an
    /// active-cut row or a source of conduct.
    pub fn coverage_scratch_len(&self) -> Option<usize> {
        self.events
            .len()
            .checked_add(1)?
            .checked_add(self.currents.len())
    }

    /// Complete linear validation using caller-owned scratch.  Incidence may overlap and may
    /// appear in any cut-local order: interval differences prove that every admitted event is
    /// covered without expanding spans or imposing a new ordering law.
    pub fn validate_with_scratch(&self, scratch: &mut [i64]) -> Result<(), ValidationError> {
        self.validate_structure()?;
        let event_scratch = self
            .events
            .len()
            .checked_add(1)
            .ok_or(ValidationError::ScratchExtent)?;
        let required = event_scratch
            .checked_add(self.currents.len())
            .ok_or(ValidationError::ScratchExtent)?;
        if scratch.len() < required {
            return Err(ValidationError::ScratchExtent);
        }
        scratch[..required].fill(0);

        let mut incidence_index = 0usize;
        while incidence_index < self.incidences.len() {
            let incidence = self.incidences[incidence_index];
            let current_index = incidence.current() as usize;
            scratch[event_scratch + current_index] = 1;
            let current = self.currents[current_index];
            let first = (current.event_offset() + incidence.current_event_offset()) as usize;
            let after = (current.event_offset()
                + incidence.current_event_offset()
                + incidence.current_events()) as usize;
            scratch[first] = scratch[first]
                .checked_add(1)
                .ok_or(ValidationError::CoverageOverflow)?;
            scratch[after] = scratch[after]
                .checked_sub(1)
                .ok_or(ValidationError::CoverageOverflow)?;
            incidence_index += 1;
        }

        let mut current_index = 0usize;
        while current_index < self.currents.len() {
            if scratch[event_scratch + current_index] == 0 {
                return Err(ValidationError::UnreferencedCurrent(current_index as u64));
            }
            current_index += 1;
        }

        let mut live = 0i64;
        let mut event_index = 0usize;
        while event_index < self.events.len() {
            live = live
                .checked_add(scratch[event_index])
                .ok_or(ValidationError::CoverageOverflow)?;
            if live <= 0 {
                return Err(ValidationError::UnreferencedEvent(event_index as u64));
            }
            event_index += 1;
        }
        live = live
            .checked_add(scratch[self.events.len()])
            .ok_or(ValidationError::CoverageOverflow)?;
        if live != 0 {
            return Err(ValidationError::CoverageOverflow);
        }
        Ok(())
    }

    /// Allocation-free complete validation retained for substrate callers which have not supplied
    /// scratch.  Host transactions use `validate_with_scratch`, avoiding this compatibility
    /// path's repeated coverage scans.
    pub fn validate(&self) -> Result<(), ValidationError> {
        self.validate_structure()?;
        let mut current_index = 0;
        while current_index < self.currents.len() {
            let mut found = false;
            let mut incidence_index = 0usize;
            while incidence_index < self.incidences.len() {
                if self.incidences[incidence_index].current() == current_index as u64 {
                    found = true;
                    break;
                }
                incidence_index += 1;
            }
            if !found {
                return Err(ValidationError::UnreferencedCurrent(current_index as u64));
            }
            current_index += 1;
        }

        // The active cut contains only admitted light. A current may participate in several cuts,
        // and one event may therefore carry plural incidence, but no event row may cross merely
        // because it was available in a mounted reservoir.
        let mut event_index = 0;
        while event_index < self.events.len() {
            let mut referenced = false;
            let mut incidence_index = 0usize;
            while incidence_index < self.incidences.len() {
                let incidence = self.incidences[incidence_index];
                let current = self.currents[incidence.current() as usize];
                let first = current.event_offset() + incidence.current_event_offset();
                let after = first + incidence.current_events();
                if event_index as u64 >= first && (event_index as u64) < after {
                    referenced = true;
                    break;
                }
                incidence_index += 1;
            }
            if !referenced {
                return Err(ValidationError::UnreferencedEvent(event_index as u64));
            }
            event_index += 1;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn two_current_view<'a>(
        header: Header,
        atoms: &'a [RelationAtom],
        events: &'a [EventSpan],
        actions: &'a [ActionCurrent],
        origins: &'a [OriginRef],
        currents: &'a [CurrentSpan],
        cuts: &'a [CutSpan],
        incidences: &'a [Incidence],
        directed: &'a [DirectedIncidence],
    ) -> View<'a> {
        View {
            header,
            atoms,
            events,
            actions,
            origins,
            currents,
            cuts,
            incidences,
            directed,
        }
    }

    #[test]
    fn canonical_relation_atoms_round_trip_without_event_serialization() {
        for value in [-257, -1, 0, 1, 255, i32::MAX as i64] {
            let cog = Cog::lit(value);
            let atom = RelationAtom::new(cog).unwrap();
            assert_eq!(RelationAtom::from_words(atom.words()), Some(atom));
            assert_eq!(atom.cog(), cog);
        }

        let mut invalid = RelationAtom::new(Cog::lit(3)).unwrap().words();
        invalid[COG_WORDS - 1] = 4;
        assert_eq!(RelationAtom::from_words(invalid), None);

        assert_eq!(ActionCurrent::new(Cog::ZERO), None);
        assert_eq!(ActionCurrent::from_words([0; COG_WORDS]), None);
    }

    #[test]
    fn sparse_cut_retains_directed_hand_and_validates_complete_extents() {
        let atoms = [
            RelationAtom::new(Cog::lit(2)).unwrap(),
            RelationAtom::new(Cog::lit(-3)).unwrap(),
            RelationAtom::new(Cog::lit(5)).unwrap(),
        ];
        let events = [EventSpan::new(0, 2).unwrap(), EventSpan::new(2, 1).unwrap()];
        let actions = [
            ActionCurrent::new(Cog::lit(13)).unwrap(),
            ActionCurrent::new(Cog::lit(17)).unwrap(),
        ];
        let origins = [OriginRef::new(7, 11), OriginRef::new(9, 13)];
        let currents = [
            CurrentSpan::new(0, 1, 0, 2).unwrap(),
            CurrentSpan::new(1, 1, 2, 1).unwrap(),
        ];
        let cuts = [CutSpan::new(0, 2, 0, 1).unwrap()];
        let incidences = [
            Incidence::new(0, 0, 1).unwrap(),
            Incidence::new(1, 0, 1).unwrap(),
        ];
        let forward = [DirectedIncidence::new(0, 1)];
        let reverse = [DirectedIncidence::new(1, 0)];
        let header = Header::new(3, 2, 2, 1, 2, 1).unwrap();

        two_current_view(
            header,
            &atoms,
            &events,
            &actions,
            &origins,
            &currents,
            &cuts,
            &incidences,
            &forward,
        )
        .validate()
        .unwrap();
        two_current_view(
            header,
            &atoms,
            &events,
            &actions,
            &origins,
            &currents,
            &cuts,
            &incidences,
            &reverse,
        )
        .validate()
        .unwrap();
        assert_ne!(forward, reverse);
    }

    #[test]
    fn population_reordering_is_a_layout_gauge_when_references_move_with_it() {
        let atoms_a = [
            RelationAtom::new(Cog::lit(2)).unwrap(),
            RelationAtom::new(Cog::lit(7)).unwrap(),
        ];
        let events = [EventSpan::new(0, 1).unwrap(), EventSpan::new(1, 1).unwrap()];
        let actions = [
            ActionCurrent::new(Cog::lit(19)).unwrap(),
            ActionCurrent::new(Cog::lit(23)).unwrap(),
        ];
        let origins = [OriginRef::new(3, 5), OriginRef::new(3, 8)];
        let currents = [
            CurrentSpan::new(0, 1, 0, 1).unwrap(),
            CurrentSpan::new(1, 1, 1, 1).unwrap(),
        ];
        let cuts = [CutSpan::new(0, 2, 0, 1).unwrap()];
        let incidences = [
            Incidence::new(0, 0, 1).unwrap(),
            Incidence::new(1, 0, 1).unwrap(),
        ];
        let directed = [DirectedIncidence::new(0, 1)];
        let header = Header::new(2, 2, 2, 1, 2, 1).unwrap();
        two_current_view(
            header,
            &atoms_a,
            &events,
            &actions,
            &origins,
            &currents,
            &cuts,
            &incidences,
            &directed,
        )
        .validate()
        .unwrap();

        let atoms_b = [atoms_a[1], atoms_a[0]];
        let swapped_incidences = [incidences[1], incidences[0]];
        let swapped_hand = [DirectedIncidence::new(1, 0)];
        two_current_view(
            header,
            &atoms_b,
            &events,
            &actions,
            &origins,
            &currents,
            &cuts,
            &swapped_incidences,
            &swapped_hand,
        )
        .validate()
        .unwrap();
        assert_ne!(atoms_a, atoms_b);
    }

    #[test]
    fn malformed_partitions_and_cross_cut_edges_are_refused() {
        let atoms = [RelationAtom::new(Cog::lit(1)).unwrap()];
        let events = [EventSpan::new(0, 1).unwrap()];
        let actions = [ActionCurrent::new(Cog::lit(29)).unwrap()];
        let origins = [OriginRef::new(0, 0)];
        let currents = [CurrentSpan::new(0, 1, 0, 1).unwrap()];
        let cuts = [CutSpan::new(0, 1, 0, 1).unwrap()];
        let incidences = [Incidence::new(0, 0, 1).unwrap()];
        let outside = [DirectedIncidence::new(0, 1)];
        let view = View {
            header: Header::new(1, 1, 1, 1, 1, 1).unwrap(),
            atoms: &atoms,
            events: &events,
            actions: &actions,
            origins: &origins,
            currents: &currents,
            cuts: &cuts,
            incidences: &incidences,
            directed: &outside,
        };
        assert_eq!(view.validate(), Err(ValidationError::DirectedIncidence(0)));

        let wrong_events = [EventSpan::new(1, 1).unwrap()];
        let view = View {
            events: &wrong_events,
            ..view
        };
        assert_eq!(view.validate(), Err(ValidationError::EventPartition(0)));

        let atoms = [
            RelationAtom::new(Cog::lit(1)).unwrap(),
            RelationAtom::new(Cog::lit(2)).unwrap(),
        ];
        let events = [EventSpan::new(0, 1).unwrap(), EventSpan::new(1, 1).unwrap()];
        let actions = [
            ActionCurrent::new(Cog::lit(1)).unwrap(),
            ActionCurrent::new(Cog::lit(1)).unwrap(),
        ];
        let origins = [OriginRef::new(0, 0), OriginRef::new(0, 1)];
        let currents = [CurrentSpan::new(0, 2, 0, 2).unwrap()];
        let cuts = [CutSpan::new(0, 1, 0, 0).unwrap()];
        let incidences = [Incidence::new(0, 0, 1).unwrap()];
        let unreferenced = View {
            header: Header::new(2, 2, 1, 1, 1, 0).unwrap(),
            atoms: &atoms,
            events: &events,
            actions: &actions,
            origins: &origins,
            currents: &currents,
            cuts: &cuts,
            incidences: &incidences,
            directed: &[],
        };
        assert_eq!(
            unreferenced.validate(),
            Err(ValidationError::UnreferencedEvent(1))
        );
        let mut scratch = [0i64; 4];
        assert_eq!(
            unreferenced.validate_with_scratch(&mut scratch),
            Err(ValidationError::UnreferencedEvent(1))
        );
        assert_eq!(
            unreferenced.validate_with_scratch(&mut scratch[..2]),
            Err(ValidationError::ScratchExtent)
        );
    }

    #[test]
    fn linear_coverage_accepts_overlapping_plural_incidence_without_expanding_spans() {
        let atoms = [
            RelationAtom::new(Cog::lit(2)).unwrap(),
            RelationAtom::new(Cog::lit(3)).unwrap(),
            RelationAtom::new(Cog::lit(5)).unwrap(),
            RelationAtom::new(Cog::lit(7)).unwrap(),
        ];
        let events = [
            EventSpan::new(0, 1).unwrap(),
            EventSpan::new(1, 1).unwrap(),
            EventSpan::new(2, 1).unwrap(),
            EventSpan::new(3, 1).unwrap(),
        ];
        let actions = [ActionCurrent::new(Cog::lit(11)).unwrap(); 4];
        let origins = [
            OriginRef::new(3, 0),
            OriginRef::new(3, 1),
            OriginRef::new(3, 2),
            OriginRef::new(3, 3),
        ];
        let currents = [CurrentSpan::new(0, 4, 0, 4).unwrap()];
        let cuts = [CutSpan::new(0, 3, 0, 0).unwrap()];
        let incidences = [
            Incidence::new(0, 2, 2).unwrap(),
            Incidence::new(0, 0, 3).unwrap(),
            Incidence::new(0, 1, 1).unwrap(),
        ];
        let view = View {
            header: Header::new(4, 4, 1, 1, 3, 0).unwrap(),
            atoms: &atoms,
            events: &events,
            actions: &actions,
            origins: &origins,
            currents: &currents,
            cuts: &cuts,
            incidences: &incidences,
            directed: &[],
        };
        let mut scratch = [0i64; 6];
        assert_eq!(view.validate(), Ok(()));
        assert_eq!(view.validate_with_scratch(&mut scratch), Ok(()));
    }
}
