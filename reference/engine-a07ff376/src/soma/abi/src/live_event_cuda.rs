//! Compact word ABI for one CUDA-enacted live current event.
//!
//! The event boundary and its ordered internal relation incidence cross together. The boundary
//! face addresses attachment and directed hand; it does not pre-compose the incidence into one
//! completed constituent. This layout carries no cut, source, journal, receipt, ancestry, or
//! future reservation; one reusable physical mouth grows only after actual resource pressure.

use body::channel::{LineageChannel, CHANNEL_WORDS};
use body::manifold::{
    face_packed_word, node_packed_word, packed_face_is_canonical, packed_node_is_canonical,
    unpack_face, unpack_node, DirectedEventContact, EventEmanation, EventReceiver, LiveBodyHeader,
    Node, CARRIER_HEADER_WORDS, FACE_WORDS, NODE_WORDS,
};
use body::num::{self, Cog, COG_WORDS};
use body::place::Place;

use crate::emission::{DeedEmission, DEED_WORDS};

pub const ENTRY_SYMBOL: &str = "lineage_event";
pub const REGIONAL_CONTACT_ENTRY_SYMBOL: &str = "regional_contacts";
pub const LAYOUT_VERSION: u32 = 6;

pub const PARAM_VERSION: usize = 0;
pub const PARAM_STANDING_AXIS: usize = 1;
pub const PARAM_MOUNT: usize = 2;
pub const PARAM_WHOLE_DARK: usize = 3;
pub const PARAM_ENDING: usize = 4;
pub const PARAM_OWN_CAPACITY: usize = 5;
pub const PARAM_CARRIER_DEPTH: usize = 6;
pub const PARAM_CARRIER_MAX_DEPTH: usize = 7;
pub const PARAM_OVERFLOW_CAPACITY: usize = 8;
pub const PARAM_EMISSION_CAPACITY: usize = 9;
pub const PARAM_RELATIONS: usize = 10;
pub const PARAM_DIRECTED_EVENTS: usize = 11;
pub const PARAM_SOURCE_GRAIN: usize = 12;
/// The source supplied an already-completed incidence complex. Grain one does not imply a scalar
/// cell: a one-cell complex retains its declared boundary species and must use the completed-node
/// event law rather than the scalar incidence mouth.
pub const PARAM_COMPLEX: usize = 13;
pub const PARAM_EVENT_CELLS_LO: usize = 14;
pub const PARAM_EVENT_CELLS_HI: usize = 15;
pub const PARAM_EVENT_INCIDENCES_LO: usize = 16;
pub const PARAM_EVENT_INCIDENCES_HI: usize = 17;
pub const PARAM_EVENT_RESOLVING_LO: usize = 18;
pub const PARAM_EVENT_RESOLVING_HI: usize = 19;
pub const PARAM_EVENT_COMPOUNDS_LO: usize = 20;
pub const PARAM_EVENT_COMPOUNDS_HI: usize = 21;
pub const PARAM_EVENT_FORMED_LO: usize = 22;
pub const PARAM_EVENT_FORMED_HI: usize = 23;
pub const PARAM_WORDS: usize = 24;

pub const EVENT_FACE: usize = 0;
pub const EVENT_ANCHOR: usize = EVENT_FACE + NODE_WORDS;
pub const EVENT_ACTION: usize = EVENT_ANCHOR + 2 * COG_WORDS;
pub const EVENT_PENDING_DARK: usize = EVENT_ACTION + COG_WORDS;
pub const EVENT_WORDS: usize = EVENT_PENDING_DARK + COG_WORDS;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct EventRow(pub [u32; EVENT_WORDS]);

impl EventRow {
    pub fn new(face: Node, anchor: Place, action: Cog, pending_dark: Cog) -> Option<Self> {
        if face.len == 0 || action.mag == 0 {
            return None;
        }
        let mut words = [0u32; EVENT_WORDS];
        let mut word = 0usize;
        while word < NODE_WORDS {
            words[EVENT_FACE + word] = node_packed_word(face, word);
            word += 1;
        }
        write_place(&mut words, EVENT_ANCHOR, anchor);
        write_cog(&mut words, EVENT_ACTION, action);
        write_cog(&mut words, EVENT_PENDING_DARK, pending_dark);
        Self::from_words(words)
    }

    pub fn from_words(words: [u32; EVENT_WORDS]) -> Option<Self> {
        if !packed_node_is_canonical(&words, EVENT_FACE)
            || unpack_node(&words, EVENT_FACE).len == 0
            || !num::packed_cog_is_canonical(&words, EVENT_ANCHOR)
            || !num::packed_cog_is_canonical(&words, EVENT_ANCHOR + COG_WORDS)
            || !num::packed_cog_is_canonical(&words, EVENT_ACTION)
            || num::read_cog(&words, EVENT_ACTION).mag == 0
            || !num::packed_cog_is_canonical(&words, EVENT_PENDING_DARK)
        {
            return None;
        }
        Some(Self(words))
    }

    pub fn face(self) -> Node {
        unpack_node(&self.0, EVENT_FACE)
    }

    pub fn anchor(self) -> Place {
        read_place(&self.0, EVENT_ANCHOR)
    }

    pub fn action(self) -> Cog {
        num::read_cog(&self.0, EVENT_ACTION)
    }

    pub fn pending_dark(self) -> Cog {
        num::read_cog(&self.0, EVENT_PENDING_DARK)
    }

    pub const fn words(self) -> [u32; EVENT_WORDS] {
        self.0
    }
}

pub const EMANATION_CELLS: usize = 0;
pub const EMANATION_INCIDENCES: usize = EMANATION_CELLS + 2;
pub const EMANATION_RESOLVING: usize = EMANATION_INCIDENCES + 2;
pub const EMANATION_FORMED_INCIDENCES: usize = EMANATION_RESOLVING + 2;
pub const EMANATION_COMPOUNDS: usize = EMANATION_FORMED_INCIDENCES + 2;
pub const EMANATION_FOLDS: usize = EMANATION_COMPOUNDS + 2;
pub const EMANATION_CHANNEL: usize = EMANATION_FOLDS + 2;
pub const EMANATION_HELD: usize = EMANATION_CHANNEL + CHANNEL_WORDS;
pub const EMANATION_HELD_LIVE: usize = EMANATION_HELD + FACE_WORDS;
pub const EMANATION_WORDS: usize = EMANATION_HELD_LIVE + 1;

/// Fixed exact return of one event-internal incidence sweep. Open construction remains in the
/// carrier; this row carries only the swept extent, completed lower-grain folds, and the resulting
/// receiver aperture.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct EmanationRow(pub [u32; EMANATION_WORDS]);

impl EmanationRow {
    pub fn new(emanation: EventEmanation) -> Option<Self> {
        if emanation.resolving_cells > emanation.cells
            || emanation.formed_incidences > emanation.incidences
            || emanation.compounds > emanation.cells
            || emanation.folds > emanation.resolving_cells
        {
            return None;
        }
        let mut words = [0u32; EMANATION_WORDS];
        put_u64(&mut words, EMANATION_CELLS, emanation.cells);
        put_u64(&mut words, EMANATION_INCIDENCES, emanation.incidences);
        put_u64(&mut words, EMANATION_RESOLVING, emanation.resolving_cells);
        put_u64(
            &mut words,
            EMANATION_FORMED_INCIDENCES,
            emanation.formed_incidences,
        );
        put_u64(&mut words, EMANATION_COMPOUNDS, emanation.compounds);
        put_u64(&mut words, EMANATION_FOLDS, emanation.folds);
        emanation
            .receiver
            .channel
            .pack(&mut words, EMANATION_CHANNEL);
        write_face(&mut words, EMANATION_HELD, emanation.receiver.held);
        words[EMANATION_HELD_LIVE] = emanation.receiver.held_live as u32;
        Some(Self(words))
    }

    pub fn from_words(words: [u32; EMANATION_WORDS]) -> Option<Self> {
        if !LineageChannel::packed_row_is_canonical(&words, EMANATION_CHANNEL)
            || !packed_face_is_canonical(&words, EMANATION_HELD)
            || words[EMANATION_HELD_LIVE] > 1
        {
            return None;
        }
        let row = Self(words);
        (Self::new(row.emanation())?.words() == row.words()).then_some(row)
    }

    pub fn emanation(self) -> EventEmanation {
        EventEmanation {
            cells: join_u64(&self.0, EMANATION_CELLS, EMANATION_CELLS + 1),
            incidences: join_u64(&self.0, EMANATION_INCIDENCES, EMANATION_INCIDENCES + 1),
            resolving_cells: join_u64(&self.0, EMANATION_RESOLVING, EMANATION_RESOLVING + 1),
            formed_incidences: join_u64(
                &self.0,
                EMANATION_FORMED_INCIDENCES,
                EMANATION_FORMED_INCIDENCES + 1,
            ),
            compounds: join_u64(&self.0, EMANATION_COMPOUNDS, EMANATION_COMPOUNDS + 1),
            folds: join_u64(&self.0, EMANATION_FOLDS, EMANATION_FOLDS + 1),
            receiver: EventReceiver {
                channel: LineageChannel::unpack(&self.0, EMANATION_CHANNEL)
                    .expect("a formed event emanation retains canonical K"),
                held: unpack_face(&self.0, EMANATION_HELD),
                held_live: self.0[EMANATION_HELD_LIVE] == 1,
            },
        }
    }

    pub const fn words(self) -> [u32; EMANATION_WORDS] {
        self.0
    }
}

pub const RECEIVER_CHANNEL: usize = 0;
pub const RECEIVER_HELD: usize = RECEIVER_CHANNEL + CHANNEL_WORDS;
pub const RECEIVER_HELD_LIVE: usize = RECEIVER_HELD + FACE_WORDS;
pub const RECEIVER_WORDS: usize = RECEIVER_HELD_LIVE + 1;

/// Immutable first-person field captured before one current changes its carrier.  This row is the
/// only shared input to the parallel regional-contact lanes; it is neither a body snapshot nor a
/// retained event envelope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct ReceiverRow(pub [u32; RECEIVER_WORDS]);

impl ReceiverRow {
    pub fn new(receiver: EventReceiver) -> Self {
        let mut words = [0u32; RECEIVER_WORDS];
        receiver.channel.pack(&mut words, RECEIVER_CHANNEL);
        write_face(&mut words, RECEIVER_HELD, receiver.held);
        words[RECEIVER_HELD_LIVE] = receiver.held_live as u32;
        Self(words)
    }

    pub fn from_words(words: [u32; RECEIVER_WORDS]) -> Option<Self> {
        if !LineageChannel::packed_row_is_canonical(&words, RECEIVER_CHANNEL)
            || !packed_face_is_canonical(&words, RECEIVER_HELD)
            || words[RECEIVER_HELD_LIVE] > 1
        {
            return None;
        }
        let row = Self(words);
        (Self::new(row.receiver()).words() == row.words()).then_some(row)
    }

    pub fn receiver(self) -> EventReceiver {
        EventReceiver {
            channel: LineageChannel::unpack(&self.0, RECEIVER_CHANNEL)
                .expect("a formed receiver row retains canonical K"),
            held: unpack_face(&self.0, RECEIVER_HELD),
            held_live: self.0[RECEIVER_HELD_LIVE] == 1,
        }
    }

    pub const fn words(self) -> [u32; RECEIVER_WORDS] {
        self.0
    }
}

pub const DIRECTED_FROM: usize = 0;
pub const DIRECTED_TO: usize = DIRECTED_FROM + 2 * COG_WORDS;
pub const DIRECTED_EVENT_WORDS: usize = DIRECTED_TO + 2 * COG_WORDS;

/// One exact source-supplied hand incident at the current whose body this launch mounts.  Both
/// event positions cross so the card can reject a row whose target is not the enacted event; no
/// lineage capability, source identity, or storage ordinal enters the device ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct DirectedEventRow(pub [u32; DIRECTED_EVENT_WORDS]);

impl DirectedEventRow {
    pub fn new(from: Place, to: Place) -> Self {
        let mut words = [0u32; DIRECTED_EVENT_WORDS];
        write_place(&mut words, DIRECTED_FROM, from);
        write_place(&mut words, DIRECTED_TO, to);
        Self(words)
    }

    pub fn from_words(words: [u32; DIRECTED_EVENT_WORDS]) -> Option<Self> {
        for at in [
            DIRECTED_FROM,
            DIRECTED_FROM + COG_WORDS,
            DIRECTED_TO,
            DIRECTED_TO + COG_WORDS,
        ] {
            if !num::packed_cog_is_canonical(&words, at) {
                return None;
            }
        }
        let row = Self(words);
        (row.words() == Self::new(row.from(), row.to()).words()).then_some(row)
    }

    pub fn from(self) -> Place {
        read_place(&self.0, DIRECTED_FROM)
    }

    pub fn to(self) -> Place {
        read_place(&self.0, DIRECTED_TO)
    }

    pub const fn words(self) -> [u32; DIRECTED_EVENT_WORDS] {
        self.0
    }
}

pub const CONTACT_PRESENT: usize = 0;
pub const CONTACT_RECEIVER_CHANNEL: usize = CONTACT_PRESENT + 1;
pub const CONTACT_RECEIVER_HELD: usize = CONTACT_RECEIVER_CHANNEL + CHANNEL_WORDS;
pub const CONTACT_RECEIVER_HELD_LIVE: usize = CONTACT_RECEIVER_HELD + FACE_WORDS;
pub const CONTACT_MEETING: usize = CONTACT_RECEIVER_HELD_LIVE + 1;
pub const CONTACT_EMISSION_PRESENT: usize = CONTACT_MEETING + FACE_WORDS;
pub const CONTACT_EMISSION: usize = CONTACT_EMISSION_PRESENT + 1;
pub const DIRECTED_CONTACT_WORDS: usize = CONTACT_EMISSION + DEED_WORDS;

/// The complete card-formed result of one directed event meeting.  The pre-event receiver crosses
/// with the meeting because neither can be reconstructed from the post-event carrier.  A missing
/// fourth contact is represented by `emission_present = 0`, not by dropping the relation row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct DirectedContactRow(pub [u32; DIRECTED_CONTACT_WORDS]);

impl DirectedContactRow {
    pub fn new(contact: DirectedEventContact) -> Option<Self> {
        let mut words = [0u32; DIRECTED_CONTACT_WORDS];
        words[CONTACT_PRESENT] = 1;
        contact
            .receiver
            .channel
            .pack(&mut words, CONTACT_RECEIVER_CHANNEL);
        write_face(&mut words, CONTACT_RECEIVER_HELD, contact.receiver.held);
        words[CONTACT_RECEIVER_HELD_LIVE] = contact.receiver.held_live as u32;
        write_face(&mut words, CONTACT_MEETING, contact.meeting);
        if let Some(emission) = contact.emission {
            let deed = DeedEmission::new(emission, 0, 1)?;
            words[CONTACT_EMISSION_PRESENT] = 1;
            words[CONTACT_EMISSION..CONTACT_EMISSION + DEED_WORDS].copy_from_slice(&deed.words());
        }
        Some(Self(words))
    }

    pub fn from_words(words: [u32; DIRECTED_CONTACT_WORDS]) -> Option<Self> {
        if words[CONTACT_PRESENT] != 1
            || !LineageChannel::packed_row_is_canonical(&words, CONTACT_RECEIVER_CHANNEL)
            || !packed_face_is_canonical(&words, CONTACT_RECEIVER_HELD)
            || words[CONTACT_RECEIVER_HELD_LIVE] > 1
            || !packed_face_is_canonical(&words, CONTACT_MEETING)
            || words[CONTACT_EMISSION_PRESENT] > 1
        {
            return None;
        }
        if words[CONTACT_EMISSION_PRESENT] == 0
            && words[CONTACT_EMISSION..CONTACT_EMISSION + DEED_WORDS]
                .iter()
                .any(|word| *word != 0)
        {
            return None;
        }
        if words[CONTACT_EMISSION_PRESENT] == 1 {
            let deed: [u32; DEED_WORDS] = words[CONTACT_EMISSION..CONTACT_EMISSION + DEED_WORDS]
                .try_into()
                .ok()?;
            DeedEmission::from_words(deed)?;
        }
        let row = Self(words);
        (Self::new(row.contact())?.words() == row.words()).then_some(row)
    }

    pub fn contact(self) -> DirectedEventContact {
        let channel = LineageChannel::unpack(&self.0, CONTACT_RECEIVER_CHANNEL)
            .expect("a formed directed-contact row retains canonical K");
        let emission = (self.0[CONTACT_EMISSION_PRESENT] == 1).then(|| {
            let deed: [u32; DEED_WORDS] = self.0[CONTACT_EMISSION..CONTACT_EMISSION + DEED_WORDS]
                .try_into()
                .expect("the fixed directed-contact deed extent is exact");
            DeedEmission::from_words(deed)
                .expect("a formed directed-contact row retains a canonical deed")
                .felt_emission()
        });
        DirectedEventContact {
            receiver: EventReceiver {
                channel,
                held: unpack_face(&self.0, CONTACT_RECEIVER_HELD),
                held_live: self.0[CONTACT_RECEIVER_HELD_LIVE] == 1,
            },
            meeting: unpack_face(&self.0, CONTACT_MEETING),
            emission,
        }
    }

    pub const fn words(self) -> [u32; DIRECTED_CONTACT_WORDS] {
        self.0
    }
}

#[inline]
pub fn write_cog(words: &mut [u32], at: usize, cog: Cog) {
    let mut word = 0usize;
    while word < COG_WORDS {
        words[at + word] = num::cog_packed_word(cog, word);
        word += 1;
    }
}

#[inline]
pub fn write_place(words: &mut [u32], at: usize, place: Place) {
    write_cog(words, at, place.0);
    write_cog(words, at + COG_WORDS, place.1);
}

#[inline]
pub fn read_place(words: &[u32], at: usize) -> Place {
    (
        num::read_cog(words, at),
        num::read_cog(words, at + COG_WORDS),
    )
}

#[inline]
fn put_u64(words: &mut [u32], at: usize, value: u64) {
    words[at] = value as u32;
    words[at + 1] = (value >> 32) as u32;
}

#[inline]
pub fn write_face(words: &mut [u32], at: usize, face: body::manifold::Face) {
    let mut word = 0usize;
    while word < FACE_WORDS {
        words[at + word] = face_packed_word(face, word);
        word += 1;
    }
}

pub const STATUS_KIND: usize = 0;
pub const STATUS_REQUIRED_OWN: usize = 1;
pub const STATUS_REQUIRED_DEPTH_LO: usize = 2;
pub const STATUS_REQUIRED_DEPTH_HI: usize = 3;
pub const STATUS_REQUIRED_OVERFLOW: usize = 4;
pub const STATUS_REQUIRED_EMISSIONS: usize = 5;
pub const STATUS_WORDS: usize = 6;

pub const STATUS_INVALID: u32 = 0;
pub const STATUS_COMPLETE: u32 = 1;
pub const STATUS_STRUCTURE: u32 = 2;
pub const STATUS_RESOURCE: u32 = 3;

pub const REGIONAL_STATUS_INVALID: u32 = 0;
pub const REGIONAL_STATUS_COMPLETE: u32 = 1;
pub const REGIONAL_STATUS_STRUCTURE: u32 = 2;
pub const REGIONAL_STATUS_QUERY_REFUSED: u32 = 3;

pub const STATE_OWN_AXIS: usize = 0;
pub const STATE_OWN_LIVE: usize = 1;
pub const STATE_RELEASES_LO: usize = 2;
pub const STATE_RELEASES_HI: usize = 3;
pub const STATE_NARROWS_LO: usize = 4;
pub const STATE_NARROWS_HI: usize = 5;
pub const STATE_CARRIER_DEPTH: usize = 6;
pub const STATE_EMISSIONS: usize = 7;
pub const STATE_THOUGHTS: usize = 8;
pub const STATE_WORDS: usize = 9;

pub const CONTROL_PARAMS: usize = 0;
pub const CONTROL_EVENT: usize = CONTROL_PARAMS + PARAM_WORDS;
pub const CONTROL_HEADER: usize = CONTROL_EVENT + EVENT_WORDS;
pub const CONTROL_STATUS: usize = CONTROL_HEADER + CARRIER_HEADER_WORDS;
pub const CONTROL_STATE: usize = CONTROL_STATUS + STATUS_WORDS;
pub const CONTROL_WORDS: usize = CONTROL_STATE + STATE_WORDS;

pub const STANDING_CELLS: usize = 0;
pub const STANDING_HEADER_WORDS: usize = 1;
pub const STANDING_ROW_GRIP: usize = 0;
pub const STANDING_ROW_FORM: usize = 1;
pub const STANDING_ROW_WORDS: usize = STANDING_ROW_FORM + body::medium::FORM_WORDS;

pub fn header_from_control(words: &[u32]) -> Option<LiveBodyHeader> {
    LiveBodyHeader::from_words_checked(
        words.get(CONTROL_HEADER..CONTROL_HEADER + CARRIER_HEADER_WORDS)?,
    )
}

#[inline]
pub const fn join_u64(words: &[u32], lo: usize, hi: usize) -> u64 {
    words[lo] as u64 | ((words[hi] as u64) << 32)
}
