//! Exact output topology emitted by native active events.
//!
//! Input events and their source material stand once in [`crate::active`].  This module records
//! only accepted Soma deeds: one immutable ordered journal per current, partitioned at every event
//! boundary so arbitrary sparse incidences can reference lived subspans without re-enacting the
//! source event or scanning a dense OWN chart.  Durable word spelling is testimony and device ABI;
//! these rows are never converted into source light.

use body::channel::WindingQuantum;
use body::manifold::{FeltDeed, FeltEmission, StandingRead};
use body::medium::{FeltTerm, RegionalForm, FORM_WORDS};
use body::num::{self, COG_WORDS};
use body::place::{self, Place};
use body::soul::Chi;

pub const LAYOUT_VERSION: u32 = 3;

#[inline]
const fn u64_words(value: u64) -> [u32; 2] {
    [value as u32, (value >> 32) as u32]
}

#[inline]
const fn u64_from_words(lo: u32, hi: u32) -> u64 {
    lo as u64 | ((hi as u64) << 32)
}

#[inline]
const fn extent_fits(offset: u64, extent: u64) -> bool {
    offset.checked_add(extent).is_some()
}

#[inline]
const fn nonempty_extent_within(offset: u64, extent: u64, total: u64) -> bool {
    match offset.checked_add(extent) {
        Some(end) => extent != 0 && end <= total,
        None => false,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum DeedKind {
    Ride = 1,
    FoundThis = 2,
    FoundThat = 3,
    Dark = 4,
}

impl DeedKind {
    #[inline]
    pub const fn from_word(word: u32) -> Option<Self> {
        match word {
            1 => Some(Self::Ride),
            2 => Some(Self::FoundThis),
            3 => Some(Self::FoundThat),
            4 => Some(Self::Dark),
            _ => None,
        }
    }

    #[inline]
    pub const fn winding(self) -> WindingQuantum {
        match self {
            Self::Ride | Self::Dark => WindingQuantum::None,
            Self::FoundThis => WindingQuantum::ThisWay,
            Self::FoundThat => WindingQuantum::ThatWay,
        }
    }
}

impl From<FeltDeed> for DeedKind {
    fn from(deed: FeltDeed) -> Self {
        match deed {
            FeltDeed::Ride => Self::Ride,
            FeltDeed::FoundThis => Self::FoundThis,
            FeltDeed::FoundThat => Self::FoundThat,
            FeltDeed::Dark => Self::Dark,
        }
    }
}

pub const HEADER_VERSION: usize = 0;
pub const HEADER_EVENTS_LO: usize = 1;
pub const HEADER_EVENTS_HI: usize = 2;
pub const HEADER_DEEDS_LO: usize = 3;
pub const HEADER_DEEDS_HI: usize = 4;
pub const HEADER_CURRENTS_LO: usize = 5;
pub const HEADER_CURRENTS_HI: usize = 6;
pub const HEADER_WORDS: usize = 7;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Header(pub [u32; HEADER_WORDS]);

impl Header {
    #[inline]
    pub const fn new(events: u64, deeds: u64, currents: u64) -> Option<Self> {
        if events == 0 || currents == 0 {
            return None;
        }
        let events = u64_words(events);
        let deeds = u64_words(deeds);
        let currents = u64_words(currents);
        Some(Self([
            LAYOUT_VERSION,
            events[0],
            events[1],
            deeds[0],
            deeds[1],
            currents[0],
            currents[1],
        ]))
    }

    #[inline]
    pub const fn from_words(words: [u32; HEADER_WORDS]) -> Option<Self> {
        if words[HEADER_VERSION] != LAYOUT_VERSION {
            return None;
        }
        Self::new(
            u64_from_words(words[HEADER_EVENTS_LO], words[HEADER_EVENTS_HI]),
            u64_from_words(words[HEADER_DEEDS_LO], words[HEADER_DEEDS_HI]),
            u64_from_words(words[HEADER_CURRENTS_LO], words[HEADER_CURRENTS_HI]),
        )
    }

    #[inline]
    pub const fn events(self) -> u64 {
        u64_from_words(self.0[HEADER_EVENTS_LO], self.0[HEADER_EVENTS_HI])
    }

    #[inline]
    pub const fn deeds(self) -> u64 {
        u64_from_words(self.0[HEADER_DEEDS_LO], self.0[HEADER_DEEDS_HI])
    }

    #[inline]
    pub const fn currents(self) -> u64 {
        u64_from_words(self.0[HEADER_CURRENTS_LO], self.0[HEADER_CURRENTS_HI])
    }

    #[inline]
    pub const fn words(self) -> [u32; HEADER_WORDS] {
        self.0
    }
}

pub const EVENT_DEED_OFFSET_LO: usize = 0;
pub const EVENT_DEED_OFFSET_HI: usize = 1;
pub const EVENT_DEEDS_LO: usize = 2;
pub const EVENT_DEEDS_HI: usize = 3;
pub const EVENT_WORDS: usize = 4;

/// One immutable slice of the current's accepted-deed journal aligned one-to-one with an input
/// event.  Zero deeds are lawful: first contacts and unresolved dark events may change no OWN cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct EventEmissionSpan(pub [u32; EVENT_WORDS]);

impl EventEmissionSpan {
    #[inline]
    pub const fn new(deed_offset: u64, deeds: u64) -> Option<Self> {
        if !extent_fits(deed_offset, deeds) {
            return None;
        }
        let offset = u64_words(deed_offset);
        let extent = u64_words(deeds);
        Some(Self([offset[0], offset[1], extent[0], extent[1]]))
    }

    #[inline]
    pub const fn from_words(words: [u32; EVENT_WORDS]) -> Option<Self> {
        Self::new(
            u64_from_words(words[EVENT_DEED_OFFSET_LO], words[EVENT_DEED_OFFSET_HI]),
            u64_from_words(words[EVENT_DEEDS_LO], words[EVENT_DEEDS_HI]),
        )
    }

    #[inline]
    pub const fn deed_offset(self) -> u64 {
        u64_from_words(self.0[EVENT_DEED_OFFSET_LO], self.0[EVENT_DEED_OFFSET_HI])
    }

    #[inline]
    pub const fn deeds(self) -> u64 {
        u64_from_words(self.0[EVENT_DEEDS_LO], self.0[EVENT_DEEDS_HI])
    }

    #[inline]
    pub const fn words(self) -> [u32; EVENT_WORDS] {
        self.0
    }
}

pub const DEED_KIND: usize = 0;
pub const DEED_POSITION: usize = 1;
pub const DEED_CHI: usize = DEED_POSITION + 2 * COG_WORDS;
pub const DEED_CAUSE_EVENT_OFFSET_LO: usize = DEED_CHI + 2 * COG_WORDS;
pub const DEED_CAUSE_EVENT_OFFSET_HI: usize = DEED_CAUSE_EVENT_OFFSET_LO + 1;
pub const DEED_CAUSE_EVENTS_LO: usize = DEED_CAUSE_EVENT_OFFSET_HI + 1;
pub const DEED_CAUSE_EVENTS_HI: usize = DEED_CAUSE_EVENTS_LO + 1;
pub const DEED_STANDING_READ_PRESENT: usize = DEED_CAUSE_EVENTS_HI + 1;
pub const DEED_STANDING_GRIP: usize = DEED_STANDING_READ_PRESENT + 1;
pub const DEED_STANDING_FORM: usize = DEED_STANDING_GRIP + 1;
pub const DEED_STANDING_POSITION: usize = DEED_STANDING_FORM + FORM_WORDS;
pub const DEED_STANDING_FLAT_PRESENT: usize = DEED_STANDING_POSITION + 2 * COG_WORDS;
pub const DEED_STANDING_RANK_LO: usize = DEED_STANDING_FLAT_PRESENT + 1;
pub const DEED_STANDING_RANK_HI: usize = DEED_STANDING_RANK_LO + 1;
pub const DEED_WORDS: usize = DEED_STANDING_RANK_HI + 1;

/// One accepted felt crossing.  `cause_event_offset/events` is current-local and retains the whole
/// interval which completed this deed.  Ordinary RIDE/FOUND deeds name their one event; DARK may
/// name several preceding static events and be emitted only when that interval actually closes.
/// A standing read carries its exact construction. `flat_present` types whether the receiver
/// supplies a flat grip; grip zero is never used as a sentinel.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct DeedEmission(pub [u32; DEED_WORDS]);

impl DeedEmission {
    #[inline]
    fn hand_matches(kind: DeedKind, term: FeltTerm) -> bool {
        term.winding == kind.winding()
            && match kind {
                DeedKind::FoundThis => term.chi.other.turn & 2 == 0,
                DeedKind::FoundThat => term.chi.other.turn & 2 != 0,
                DeedKind::Ride | DeedKind::Dark => true,
            }
    }

    #[inline]
    pub fn new(emission: FeltEmission, cause_event_offset: u64, cause_events: u64) -> Option<Self> {
        if cause_events == 0 || !extent_fits(cause_event_offset, cause_events) {
            return None;
        }
        let kind = DeedKind::from(emission.deed);
        if !Self::hand_matches(kind, emission.term) {
            return None;
        }
        let mut words = [0u32; DEED_WORDS];
        words[DEED_KIND] = kind as u32;
        let mut word = 0usize;
        while word < COG_WORDS {
            words[DEED_POSITION + word] = num::cog_packed_word(emission.position.0, word);
            words[DEED_POSITION + COG_WORDS + word] =
                num::cog_packed_word(emission.position.1, word);
            words[DEED_CHI + word] = num::cog_packed_word(emission.term.chi.same, word);
            words[DEED_CHI + COG_WORDS + word] =
                num::cog_packed_word(emission.term.chi.other, word);
            word += 1;
        }
        let offset = u64_words(cause_event_offset);
        let extent = u64_words(cause_events);
        words[DEED_CAUSE_EVENT_OFFSET_LO] = offset[0];
        words[DEED_CAUSE_EVENT_OFFSET_HI] = offset[1];
        words[DEED_CAUSE_EVENTS_LO] = extent[0];
        words[DEED_CAUSE_EVENTS_HI] = extent[1];
        if let Some(read) = emission.standing_read {
            if !read.form.occupied() {
                return None;
            }
            words[DEED_STANDING_READ_PRESENT] = 1;
            if let Some(grip) = read.flat_grip {
                words[DEED_STANDING_GRIP] = grip;
                words[DEED_STANDING_FLAT_PRESENT] = 1;
            }
            let rank = u64_words(read.receiver_rank);
            words[DEED_STANDING_RANK_LO] = rank[0];
            words[DEED_STANDING_RANK_HI] = rank[1];
            word = 0;
            while word < COG_WORDS {
                words[DEED_STANDING_POSITION + word] = num::cog_packed_word(read.position.0, word);
                words[DEED_STANDING_POSITION + COG_WORDS + word] =
                    num::cog_packed_word(read.position.1, word);
                word += 1;
            }
            read.form.pack(&mut words, DEED_STANDING_FORM);
        }
        Self::from_words(words)
    }

    #[inline]
    pub fn from_words(words: [u32; DEED_WORDS]) -> Option<Self> {
        let kind = DeedKind::from_word(words[DEED_KIND])?;
        let spans = [
            DEED_POSITION,
            DEED_POSITION + COG_WORDS,
            DEED_CHI,
            DEED_CHI + COG_WORDS,
        ];
        let mut at = 0usize;
        while at < spans.len() {
            if !num::packed_cog_is_canonical(&words, spans[at]) {
                return None;
            }
            at += 1;
        }
        let cause_offset = u64_from_words(
            words[DEED_CAUSE_EVENT_OFFSET_LO],
            words[DEED_CAUSE_EVENT_OFFSET_HI],
        );
        let cause_events = u64_from_words(words[DEED_CAUSE_EVENTS_LO], words[DEED_CAUSE_EVENTS_HI]);
        if cause_events == 0 || !extent_fits(cause_offset, cause_events) {
            return None;
        }
        match words[DEED_STANDING_READ_PRESENT] {
            0 => {
                if words[DEED_STANDING_GRIP..DEED_WORDS]
                    .iter()
                    .any(|word| *word != 0)
                {
                    return None;
                }
            }
            1 => {
                if !num::packed_cog_is_canonical(&words, DEED_STANDING_POSITION)
                    || !num::packed_cog_is_canonical(&words, DEED_STANDING_POSITION + COG_WORDS)
                {
                    return None;
                }
                let form = RegionalForm::unpack_compact_checked(&words, DEED_STANDING_FORM).ok()?;
                if !form.occupied() {
                    return None;
                }
                let rank =
                    u64_from_words(words[DEED_STANDING_RANK_LO], words[DEED_STANDING_RANK_HI]);
                match (rank <= 16, words[DEED_STANDING_FLAT_PRESENT]) {
                    (false, 0) if words[DEED_STANDING_GRIP] == 0 => {}
                    (true, 1) => {
                        let position = (
                            num::read_cog(&words, DEED_STANDING_POSITION),
                            num::read_cog(&words, DEED_STANDING_POSITION + COG_WORDS),
                        );
                        if words[DEED_STANDING_GRIP] != place::ground(position, 1i64 << rank) {
                            return None;
                        }
                    }
                    _ => return None,
                }
            }
            _ => return None,
        }
        let row = Self(words);
        if !Self::hand_matches(kind, row.term()) {
            return None;
        }
        Some(row)
    }

    #[inline]
    pub fn position(self) -> Place {
        (
            num::read_cog(&self.0, DEED_POSITION),
            num::read_cog(&self.0, DEED_POSITION + COG_WORDS),
        )
    }

    #[inline]
    pub fn term(self) -> FeltTerm {
        FeltTerm {
            chi: Chi {
                same: num::read_cog(&self.0, DEED_CHI),
                other: num::read_cog(&self.0, DEED_CHI + COG_WORDS),
            },
            winding: self.kind().winding(),
        }
    }

    #[inline]
    pub fn felt_emission(self) -> FeltEmission {
        let deed = match self.kind() {
            DeedKind::Ride => FeltDeed::Ride,
            DeedKind::FoundThis => FeltDeed::FoundThis,
            DeedKind::FoundThat => FeltDeed::FoundThat,
            DeedKind::Dark => FeltDeed::Dark,
        };
        FeltEmission {
            position: self.position(),
            term: self.term(),
            deed,
            standing_read: self.standing_read(),
        }
    }

    #[inline]
    pub fn standing_read(self) -> Option<StandingRead> {
        (self.0[DEED_STANDING_READ_PRESENT] == 1).then(|| StandingRead {
            position: (
                num::read_cog(&self.0, DEED_STANDING_POSITION),
                num::read_cog(&self.0, DEED_STANDING_POSITION + COG_WORDS),
            ),
            receiver_rank: u64_from_words(
                self.0[DEED_STANDING_RANK_LO],
                self.0[DEED_STANDING_RANK_HI],
            ),
            flat_grip: (self.0[DEED_STANDING_FLAT_PRESENT] == 1)
                .then_some(self.0[DEED_STANDING_GRIP]),
            form: RegionalForm::unpack_compact_trusted(&self.0, DEED_STANDING_FORM),
        })
    }

    #[inline]
    pub fn kind(self) -> DeedKind {
        DeedKind::from_word(self.0[DEED_KIND]).expect("a formed deed row has one known kind")
    }

    #[inline]
    pub const fn cause_event_offset(self) -> u64 {
        u64_from_words(
            self.0[DEED_CAUSE_EVENT_OFFSET_LO],
            self.0[DEED_CAUSE_EVENT_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn cause_events(self) -> u64 {
        u64_from_words(self.0[DEED_CAUSE_EVENTS_LO], self.0[DEED_CAUSE_EVENTS_HI])
    }

    #[inline]
    pub const fn words(self) -> [u32; DEED_WORDS] {
        self.0
    }
}

pub const CURRENT_EVENT_OFFSET_LO: usize = 0;
pub const CURRENT_EVENT_OFFSET_HI: usize = 1;
pub const CURRENT_EVENTS_LO: usize = 2;
pub const CURRENT_EVENTS_HI: usize = 3;
pub const CURRENT_DEED_OFFSET_LO: usize = 4;
pub const CURRENT_DEED_OFFSET_HI: usize = 5;
pub const CURRENT_DEEDS_LO: usize = 6;
pub const CURRENT_DEEDS_HI: usize = 7;
pub const CURRENT_WORDS: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct CurrentEmissionSpan(pub [u32; CURRENT_WORDS]);

impl CurrentEmissionSpan {
    #[inline]
    pub const fn new(event_offset: u64, events: u64, deed_offset: u64, deeds: u64) -> Option<Self> {
        if events == 0 || !extent_fits(event_offset, events) || !extent_fits(deed_offset, deeds) {
            return None;
        }
        let event_offset = u64_words(event_offset);
        let events = u64_words(events);
        let deed_offset = u64_words(deed_offset);
        let deeds = u64_words(deeds);
        Some(Self([
            event_offset[0],
            event_offset[1],
            events[0],
            events[1],
            deed_offset[0],
            deed_offset[1],
            deeds[0],
            deeds[1],
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
            u64_from_words(words[CURRENT_DEED_OFFSET_LO], words[CURRENT_DEED_OFFSET_HI]),
            u64_from_words(words[CURRENT_DEEDS_LO], words[CURRENT_DEEDS_HI]),
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
    pub const fn deed_offset(self) -> u64 {
        u64_from_words(
            self.0[CURRENT_DEED_OFFSET_LO],
            self.0[CURRENT_DEED_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn deeds(self) -> u64 {
        u64_from_words(self.0[CURRENT_DEEDS_LO], self.0[CURRENT_DEEDS_HI])
    }

    #[inline]
    pub const fn words(self) -> [u32; CURRENT_WORDS] {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValidationError {
    PopulationExtent,
    Deed(u64),
    EventPartition(u64),
    CurrentPartition(u64),
    Cause(u64),
}

pub struct View<'a> {
    pub header: Header,
    pub events: &'a [EventEmissionSpan],
    pub deeds: &'a [DeedEmission],
    pub currents: &'a [CurrentEmissionSpan],
}

impl View<'_> {
    pub fn validate(&self) -> Result<(), ValidationError> {
        if self.header.events() != self.events.len() as u64
            || self.header.deeds() != self.deeds.len() as u64
            || self.header.currents() != self.currents.len() as u64
        {
            return Err(ValidationError::PopulationExtent);
        }

        let mut deed_index = 0usize;
        while deed_index < self.deeds.len() {
            if DeedEmission::from_words(self.deeds[deed_index].words()).is_none() {
                return Err(ValidationError::Deed(deed_index as u64));
            }
            deed_index += 1;
        }

        let mut deed_cursor = 0u64;
        let mut event_index = 0usize;
        while event_index < self.events.len() {
            let event = self.events[event_index];
            if event.deed_offset() != deed_cursor
                || event.deed_offset().checked_add(event.deeds()).is_none()
                || event.deed_offset() + event.deeds() > self.header.deeds()
            {
                return Err(ValidationError::EventPartition(event_index as u64));
            }
            deed_cursor += event.deeds();
            event_index += 1;
        }
        if deed_cursor != self.header.deeds() {
            return Err(ValidationError::EventPartition(self.header.events()));
        }

        let mut current_event_cursor = 0u64;
        let mut current_deed_cursor = 0u64;
        let mut current_index = 0usize;
        while current_index < self.currents.len() {
            let current = self.currents[current_index];
            if current.event_offset() != current_event_cursor
                || current.deed_offset() != current_deed_cursor
                || !nonempty_extent_within(
                    current.event_offset(),
                    current.events(),
                    self.header.events(),
                )
                || current.deed_offset().checked_add(current.deeds()).is_none()
                || current.deed_offset() + current.deeds() > self.header.deeds()
            {
                return Err(ValidationError::CurrentPartition(current_index as u64));
            }
            let first_event = current.event_offset() as usize;
            let last_event = (current.event_offset() + current.events() - 1) as usize;
            if self.events[first_event].deed_offset() != current.deed_offset()
                || self.events[last_event].deed_offset() + self.events[last_event].deeds()
                    != current.deed_offset() + current.deeds()
            {
                return Err(ValidationError::CurrentPartition(current_index as u64));
            }

            let mut local_event = 0u64;
            while local_event < current.events() {
                let global_event = current.event_offset() + local_event;
                let event = self.events[global_event as usize];
                let mut local_deed = event.deed_offset();
                let after_deed = local_deed + event.deeds();
                while local_deed < after_deed {
                    let deed = self.deeds[local_deed as usize];
                    let cause_after = deed
                        .cause_event_offset()
                        .checked_add(deed.cause_events())
                        .ok_or(ValidationError::Cause(local_deed))?;
                    if cause_after > current.events()
                        || (deed.kind() != DeedKind::Dark
                            && (deed.cause_events() != 1
                                || deed.cause_event_offset() != local_event))
                        || (deed.kind() == DeedKind::Dark && cause_after > local_event + 1)
                    {
                        return Err(ValidationError::Cause(local_deed));
                    }
                    local_deed += 1;
                }
                local_event += 1;
            }

            current_event_cursor += current.events();
            current_deed_cursor += current.deeds();
            current_index += 1;
        }
        if current_event_cursor != self.header.events()
            || current_deed_cursor != self.header.deeds()
        {
            return Err(ValidationError::CurrentPartition(self.header.currents()));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::num::{Cog, Rung};

    fn emission(deed: FeltDeed, cause: (u64, u64)) -> DeedEmission {
        let winding = DeedKind::from(deed).winding();
        DeedEmission::new(
            FeltEmission {
                position: (Cog::lit(3), Cog::lit(-5)),
                term: FeltTerm {
                    chi: Chi {
                        same: Cog::lit(7),
                        other: Cog::lit(-11),
                    },
                    winding,
                },
                deed,
                standing_read: None,
            },
            cause.0,
            cause.1,
        )
        .unwrap()
    }

    #[test]
    fn zero_deed_events_and_a_completed_dark_interval_are_exact() {
        let deeds = [
            emission(FeltDeed::Dark, (0, 2)),
            emission(FeltDeed::Ride, (2, 1)),
        ];
        let events = [
            EventEmissionSpan::new(0, 0).unwrap(),
            EventEmissionSpan::new(0, 0).unwrap(),
            EventEmissionSpan::new(0, 2).unwrap(),
        ];
        let currents = [CurrentEmissionSpan::new(0, 3, 0, 2).unwrap()];
        let view = View {
            header: Header::new(3, 2, 1).unwrap(),
            events: &events,
            deeds: &deeds,
            currents: &currents,
        };
        view.validate().unwrap();
        assert_eq!(deeds[0].position(), (Cog::lit(3), Cog::lit(-5)));
        assert_eq!(deeds[0].kind(), DeedKind::Dark);
        assert_eq!(deeds[1].kind(), DeedKind::Ride);
    }

    #[test]
    fn a_deed_cannot_claim_another_current_or_a_false_hand() {
        let deed = emission(FeltDeed::Ride, (1, 1));
        let events = [
            EventEmissionSpan::new(0, 1).unwrap(),
            EventEmissionSpan::new(1, 0).unwrap(),
        ];
        let currents = [
            CurrentEmissionSpan::new(0, 1, 0, 1).unwrap(),
            CurrentEmissionSpan::new(1, 1, 1, 0).unwrap(),
        ];
        assert_eq!(
            View {
                header: Header::new(2, 1, 2).unwrap(),
                events: &events,
                deeds: &[deed],
                currents: &currents,
            }
            .validate(),
            Err(ValidationError::Cause(0))
        );

        let mut words = deed.words();
        words[DEED_KIND] = DeedKind::FoundThis as u32;
        assert!(DeedEmission::from_words(words).is_none());
    }

    #[test]
    fn current_schema_retains_flat_and_deep_standing_reads_without_sentinels() {
        let no_read = emission(FeltDeed::Ride, (0, 1));
        let form =
            RegionalForm::from_components(Cog::lit(13), Cog::lit(-7), Rung::of(2), Rung::of(1))
                .occupy();
        let flat = DeedEmission::new(
            FeltEmission {
                position: (Cog::lit(3), Cog::lit(-5)),
                term: no_read.term(),
                deed: FeltDeed::Ride,
                standing_read: Some(StandingRead {
                    position: (Cog::lit(17), Cog::lit(19)),
                    receiver_rank: 0,
                    flat_grip: Some(0),
                    form,
                }),
            },
            0,
            1,
        )
        .unwrap();
        assert_eq!(flat.words()[DEED_STANDING_READ_PRESENT], 1);
        assert_eq!(flat.words()[DEED_STANDING_GRIP], 0);
        assert_eq!(flat.words()[DEED_STANDING_FLAT_PRESENT], 1);

        let nonzero_position = (Cog::lit(17), Cog::lit(19));
        let nonzero = DeedEmission::new(
            FeltEmission {
                position: (Cog::lit(3), Cog::lit(-5)),
                term: no_read.term(),
                deed: FeltDeed::Ride,
                standing_read: Some(StandingRead {
                    position: nonzero_position,
                    receiver_rank: 6,
                    flat_grip: Some(place::ground(nonzero_position, 64)),
                    form,
                }),
            },
            0,
            1,
        )
        .unwrap();
        assert_eq!(nonzero.standing_read().unwrap().flat_grip, Some(3187));

        let deep = DeedEmission::new(
            FeltEmission {
                position: (Cog::lit(3), Cog::lit(-5)),
                term: no_read.term(),
                deed: FeltDeed::Ride,
                standing_read: Some(StandingRead {
                    position: (Cog::lit(17), Cog::lit(19)),
                    receiver_rank: 80,
                    flat_grip: None,
                    form,
                }),
            },
            0,
            1,
        )
        .unwrap();
        assert_eq!(
            deep.standing_read().unwrap().position,
            (Cog::lit(17), Cog::lit(19))
        );
        assert_eq!(deep.words()[DEED_STANDING_FLAT_PRESENT], 0);
    }

    #[test]
    fn rejected_and_unknown_layout_versions_fail_closed() {
        let header = Header::new(1, 0, 1).unwrap();
        for rejected in [0, 1, 2, LAYOUT_VERSION + 1, u32::MAX] {
            let mut words = header.words();
            words[HEADER_VERSION] = rejected;
            assert_eq!(Header::from_words(words), None);
        }
    }
}
