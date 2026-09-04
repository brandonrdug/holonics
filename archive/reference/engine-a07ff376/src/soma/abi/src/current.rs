//! One substrate-neutral active event row.

pub const EVENT_TAG: usize = 0;
pub const EVENT_PAYLOAD_WORDS: usize = 1;
pub const EVENT_HEADER_WORDS: usize = 2;

pub const U64_WORDS: usize = 2;
pub const U128_WORDS: usize = 4;
pub const SHA256_WORDS: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct EventHeader(pub [u32; EVENT_HEADER_WORDS]);

impl EventHeader {
    #[inline]
    pub const fn new(local_tag: u32, payload_words: u32) -> Option<Self> {
        if local_tag == 0 || payload_words == 0 {
            None
        } else {
            Some(Self([local_tag, payload_words]))
        }
    }

    #[inline]
    pub const fn local_tag(self) -> u32 {
        self.0[EVENT_TAG]
    }

    #[inline]
    pub const fn payload_words(self) -> u32 {
        self.0[EVENT_PAYLOAD_WORDS]
    }

    #[inline]
    pub const fn words(self) -> [u32; EVENT_HEADER_WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_words(words: [u32; EVENT_HEADER_WORDS]) -> Option<Self> {
        Self::new(words[EVENT_TAG], words[EVENT_PAYLOAD_WORDS])
    }
}
