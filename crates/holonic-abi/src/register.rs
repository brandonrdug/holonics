//! Exact REGISTER status, lane, and entry rows.

/// One returned REGISTER status row: kind, diagnosed old axis, diagnosed new axis.
pub const STATUS_WORDS: usize = 3;
pub const STATUS_KIND: usize = 0;
pub const STATUS_OLD_AXIS: usize = 1;
pub const STATUS_NEW_AXIS: usize = 2;

/// One mounted lineage descriptor.
pub const LANE_WORDS: usize = 10;
pub const LANE_RAW_OFFSET: usize = 0;
pub const LANE_RAW_COUNT: usize = 1;
pub const LANE_FRAME_PREVIOUS: usize = 2;
pub const LANE_FRAME_CURRENT: usize = 3;
pub const LANE_WORLDLINE_LO: usize = 4;
pub const LANE_WORLDLINE_HI: usize = 5;
pub const LANE_OWN_WORD_BASE: usize = 6;
pub const LANE_CAPACITY_CELLS: usize = 7;
pub const LANE_CARRIER_WORD_BASE: usize = 8;
pub const LANE_CARRIER_ROW_WORDS: usize = 9;

pub const RECAST_INCOMPLETE: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum StatusKind {
    Complete = 0,
    NeedsOwnRecast = 1,
    Continue = 2,
    NeedsCarrierRebase = 3,
}

impl StatusKind {
    #[inline]
    pub const fn word(self) -> u32 {
        self as u32
    }

    #[inline]
    pub const fn from_word(word: u32) -> Option<Self> {
        match word {
            0 => Some(Self::Complete),
            1 => Some(Self::NeedsOwnRecast),
            2 => Some(Self::Continue),
            3 => Some(Self::NeedsCarrierRebase),
            _ => None,
        }
    }
}

pub const STATUS_COMPLETE: u32 = StatusKind::Complete.word();
pub const STATUS_NEEDS_OWN_RECAST: u32 = StatusKind::NeedsOwnRecast.word();
pub const STATUS_CONTINUE: u32 = StatusKind::Continue.word();
pub const STATUS_NEEDS_CARRIER_REBASE: u32 = StatusKind::NeedsCarrierRebase.word();

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct StatusRow(pub [u32; STATUS_WORDS]);

impl StatusRow {
    #[inline]
    pub const fn complete() -> Self {
        Self([STATUS_COMPLETE, 0, 0])
    }

    #[inline]
    pub const fn continuing() -> Self {
        Self([STATUS_CONTINUE, 0, 0])
    }

    #[inline]
    pub const fn needs_own_recast(old_axis: u32, new_axis: u32) -> Self {
        Self([STATUS_NEEDS_OWN_RECAST, old_axis, new_axis])
    }

    #[inline]
    pub const fn needs_carrier_rebase(required_depth: u64) -> Self {
        Self([
            STATUS_NEEDS_CARRIER_REBASE,
            required_depth as u32,
            (required_depth >> 32) as u32,
        ])
    }

    #[inline]
    pub const fn kind(self) -> Option<StatusKind> {
        StatusKind::from_word(self.0[STATUS_KIND])
    }

    #[inline]
    pub const fn old_axis(self) -> u32 {
        self.0[STATUS_OLD_AXIS]
    }

    #[inline]
    pub const fn new_axis(self) -> u32 {
        self.0[STATUS_NEW_AXIS]
    }

    #[inline]
    pub const fn required_carrier_depth(self) -> u64 {
        self.0[STATUS_OLD_AXIS] as u64 | ((self.0[STATUS_NEW_AXIS] as u64) << 32)
    }

    #[inline]
    pub const fn words(self) -> [u32; STATUS_WORDS] {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct LaneRow(pub [u32; LANE_WORDS]);

impl LaneRow {
    #[inline]
    pub const fn own_word_base(self) -> u32 {
        self.0[LANE_OWN_WORD_BASE]
    }

    #[inline]
    pub const fn capacity_cells(self) -> u32 {
        self.0[LANE_CAPACITY_CELLS]
    }

    #[inline]
    pub const fn carrier_word_base(self) -> u32 {
        self.0[LANE_CARRIER_WORD_BASE]
    }

    #[inline]
    pub const fn carrier_row_words(self) -> u32 {
        self.0[LANE_CARRIER_ROW_WORDS]
    }

    #[inline]
    pub const fn words(self) -> [u32; LANE_WORDS] {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Entry {
    Scope,
    ScopeSurface,
    Recast,
    RecastFinish,
    CarrierRebase,
}

impl Entry {
    #[inline]
    pub const fn symbol(self) -> &'static str {
        match self {
            Self::Scope => "scope_register",
            Self::ScopeSurface => "scope_register_surface",
            Self::Recast => "register_own_recast",
            Self::RecastFinish => "register_own_recast_finish",
            Self::CarrierRebase => "register_carrier_rebase",
        }
    }

    /// Number of `(device pointer, element extent)` pairs in the exact CUDA mouth.
    #[inline]
    pub const fn buffer_pairs(self) -> usize {
        match self {
            Self::Scope => 10,
            Self::ScopeSurface => 11,
            Self::Recast | Self::RecastFinish | Self::CarrierRebase => 7,
        }
    }

    /// Every buffer pair crosses the driver as two 64-bit kernel parameters.
    #[inline]
    pub const fn cuda_parameter_words(self) -> usize {
        self.buffer_pairs() * 2
    }
}
