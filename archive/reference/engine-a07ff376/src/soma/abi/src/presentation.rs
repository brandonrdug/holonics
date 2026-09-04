//! World presentation without a world-specific object model.

pub const LAYOUT_VERSION: u32 = 1;

/// World-local active-event tag used by the membrane when a sparse presentation must carry
/// its incidence relation through Soma rather than leaving it in the listener journal.  The
/// payload is one `CONFIGURATION_EVENT_VERSION`, one 64-bit incidence count, then that many
/// canonical [`Incidence`] rows.  It names no modality, category, score, or semantic class.
pub const CONFIGURATION_EVENT_TAG: u32 = 0x4346_4749; // `CFGI`
pub const CONFIGURATION_EVENT_VERSION: u32 = 1;
pub const CONFIGURATION_EVENT_HEADER_WORDS: usize = 3;

pub const HEADER_VERSION: usize = 0;
pub const HEADER_EVENTS_LO: usize = 1;
pub const HEADER_EVENTS_HI: usize = 2;
pub const HEADER_CURRENTS_LO: usize = 3;
pub const HEADER_CURRENTS_HI: usize = 4;
pub const HEADER_CONFIGURATIONS_LO: usize = 5;
pub const HEADER_CONFIGURATIONS_HI: usize = 6;
pub const HEADER_INCIDENCES_LO: usize = 7;
pub const HEADER_INCIDENCES_HI: usize = 8;
pub const HEADER_WORDS: usize = 9;

pub const CURRENT_EVENT_OFFSET_LO: usize = 0;
pub const CURRENT_EVENT_OFFSET_HI: usize = 1;
pub const CURRENT_EVENTS_LO: usize = 2;
pub const CURRENT_EVENTS_HI: usize = 3;
pub const CURRENT_WORDS: usize = 4;

pub const CONFIGURATION_INCIDENCE_OFFSET_LO: usize = 0;
pub const CONFIGURATION_INCIDENCE_OFFSET_HI: usize = 1;
pub const CONFIGURATION_INCIDENCES_LO: usize = 2;
pub const CONFIGURATION_INCIDENCES_HI: usize = 3;
pub const CONFIGURATION_WORDS: usize = 4;

pub const INCIDENCE_CURRENT_LO: usize = 0;
pub const INCIDENCE_CURRENT_HI: usize = 1;
pub const INCIDENCE_CURRENT_EVENT_OFFSET_LO: usize = 2;
pub const INCIDENCE_CURRENT_EVENT_OFFSET_HI: usize = 3;
pub const INCIDENCE_CURRENT_EVENTS_LO: usize = 4;
pub const INCIDENCE_CURRENT_EVENTS_HI: usize = 5;
pub const INCIDENCE_WORDS: usize = 6;

#[inline]
pub const fn u64_words(value: u64) -> [u32; 2] {
    [value as u32, (value >> 32) as u32]
}

#[inline]
pub const fn u64_from_words(lo: u32, hi: u32) -> u64 {
    lo as u64 | ((hi as u64) << 32)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Header(pub [u32; HEADER_WORDS]);

impl Header {
    #[inline]
    pub const fn new(
        events: u64,
        currents: u64,
        configurations: u64,
        incidences: u64,
    ) -> Option<Self> {
        if events == 0 || currents == 0 || configurations == 0 || incidences == 0 {
            return None;
        }
        let event = u64_words(events);
        let current = u64_words(currents);
        let configuration = u64_words(configurations);
        let incidence = u64_words(incidences);
        Some(Self([
            LAYOUT_VERSION,
            event[0],
            event[1],
            current[0],
            current[1],
            configuration[0],
            configuration[1],
            incidence[0],
            incidence[1],
        ]))
    }

    #[inline]
    pub const fn from_words(words: [u32; HEADER_WORDS]) -> Option<Self> {
        if words[HEADER_VERSION] != LAYOUT_VERSION {
            return None;
        }
        Self::new(
            u64_from_words(words[HEADER_EVENTS_LO], words[HEADER_EVENTS_HI]),
            u64_from_words(words[HEADER_CURRENTS_LO], words[HEADER_CURRENTS_HI]),
            u64_from_words(
                words[HEADER_CONFIGURATIONS_LO],
                words[HEADER_CONFIGURATIONS_HI],
            ),
            u64_from_words(words[HEADER_INCIDENCES_LO], words[HEADER_INCIDENCES_HI]),
        )
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
    pub const fn configurations(self) -> u64 {
        u64_from_words(
            self.0[HEADER_CONFIGURATIONS_LO],
            self.0[HEADER_CONFIGURATIONS_HI],
        )
    }

    #[inline]
    pub const fn incidences(self) -> u64 {
        u64_from_words(self.0[HEADER_INCIDENCES_LO], self.0[HEADER_INCIDENCES_HI])
    }

    #[inline]
    pub const fn words(self) -> [u32; HEADER_WORDS] {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct CurrentSpan(pub [u32; CURRENT_WORDS]);

impl CurrentSpan {
    #[inline]
    pub const fn new(event_offset: u64, events: u64) -> Option<Self> {
        if events == 0 || event_offset.checked_add(events).is_none() {
            return None;
        }
        let offset = u64_words(event_offset);
        let extent = u64_words(events);
        Some(Self([offset[0], offset[1], extent[0], extent[1]]))
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
    pub const fn words(self) -> [u32; CURRENT_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; CURRENT_WORDS]) -> Option<Self> {
        Self::new(
            u64_from_words(
                words[CURRENT_EVENT_OFFSET_LO],
                words[CURRENT_EVENT_OFFSET_HI],
            ),
            u64_from_words(words[CURRENT_EVENTS_LO], words[CURRENT_EVENTS_HI]),
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct ConfigurationSpan(pub [u32; CONFIGURATION_WORDS]);

impl ConfigurationSpan {
    #[inline]
    pub const fn new(incidence_offset: u64, incidences: u64) -> Option<Self> {
        if incidences == 0 || incidence_offset.checked_add(incidences).is_none() {
            return None;
        }
        let offset = u64_words(incidence_offset);
        let extent = u64_words(incidences);
        Some(Self([offset[0], offset[1], extent[0], extent[1]]))
    }

    #[inline]
    pub const fn incidence_offset(self) -> u64 {
        u64_from_words(
            self.0[CONFIGURATION_INCIDENCE_OFFSET_LO],
            self.0[CONFIGURATION_INCIDENCE_OFFSET_HI],
        )
    }

    #[inline]
    pub const fn incidences(self) -> u64 {
        u64_from_words(
            self.0[CONFIGURATION_INCIDENCES_LO],
            self.0[CONFIGURATION_INCIDENCES_HI],
        )
    }

    #[inline]
    pub const fn words(self) -> [u32; CONFIGURATION_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; CONFIGURATION_WORDS]) -> Option<Self> {
        Self::new(
            u64_from_words(
                words[CONFIGURATION_INCIDENCE_OFFSET_LO],
                words[CONFIGURATION_INCIDENCE_OFFSET_HI],
            ),
            u64_from_words(
                words[CONFIGURATION_INCIDENCES_LO],
                words[CONFIGURATION_INCIDENCES_HI],
            ),
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Incidence(pub [u32; INCIDENCE_WORDS]);

impl Incidence {
    #[inline]
    pub const fn new(current: u64, current_event_offset: u64, current_events: u64) -> Option<Self> {
        if current_events == 0 || current_event_offset.checked_add(current_events).is_none() {
            return None;
        }
        let current = u64_words(current);
        let offset = u64_words(current_event_offset);
        let extent = u64_words(current_events);
        Some(Self([
            current[0], current[1], offset[0], offset[1], extent[0], extent[1],
        ]))
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
}
