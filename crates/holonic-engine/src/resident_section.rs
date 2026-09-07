//! **The resident interval-section carrier and the graph-realized passage over it.** The
//! continuing semantic standing enters an operation on the card and leaves it on the card; the
//! whole passage is bound as one CUDA graph before it is launched, launched once, and read once.
//!
//! Contract:
//! [`research/records/2026-08-18_THE_SECTION_MUST_STAY_ON_THE_CARD_THE_CONTRACT_BEFORE_THE_RESIDENT_LAYER.md`].
//! Audit that occasioned this form:
//! `research/records/2026-08-18_THE_SECTION_STAYED_BUT_THE_HOST_STILL_OWNED_THE_PASSAGE_AND_NO_PHOENIX_STATION_PASSED.md`.
//! Kernel: `kernels/exact_resident_section.cu`.
//!
//! # The correction this owner holds, and how the second attempt failed it
//!
//! Brandon, 2026-08-18: *"the GPU should not be 'used more'; the continuing semantic section must
//! remain owned by the GPU surface."* The first attempt crossed a `Vec<Rat>` before every
//! contraction. The second kept the vectors resident and still failed: every local operation
//! launched, globally synchronized, read a receipt word back, and only then did the serial chart
//! decide the next operation — 180 launches, 180 synchronizations, a renamed instruction loop.
//!
//! This form binds the passage before it runs. Every occurrence's launch geometry, parameters,
//! carrier admission and footprint are derived **from the a-priori octave law and the material's
//! extents** before any launch; the launches are captured into one graph whose edges are the
//! diagram's bonds; the graph is launched once; refusals accumulate on the card in one census
//! array; and the serial chart receives one census reading and one terminal face. Between the graph
//! launch and the terminal synchronize the serial chart issues nothing — [`TransferCensus`] counts
//! it, so a renamed loop is caught by measurement rather than by a string.
//!
//! # One apparatus occurrence, through `crates/holonic-mount`
//!
//! Device discovery, attributes, module loading, streams, events, capture and graphs come through
//! [`mount`] — the one CUDA census this tree owns — not a second `#[link(name = "cuda")]` block.
//! The surface adopts the [`ResidentReadout`]'s context as a [`mount::BorrowedContext`], checks the
//! mounted device is the readout's device by name, builds the [`DeviceDeclaration`] from the
//! device's own attributes, builds the [`HardwareCover`] **from that declaration and nowhere else**,
//! and states its [`ModeIdentity`] with the PTX's content digest. A caller cannot hand the passage a
//! cover: it reads the surface's.
//!
//! # The carrier
//!
//! A coordinate is a certified enclosure `[lo, hi]` of two `i64` words at one declared dyadic grain
//! `2^-F` ([`ResidentGrain`]). Every operation rounds outward, so every remainder propagates to the
//! terminal face. `F` and the series aperture ([`SeriesAperture`]) are apparatus apertures the
//! caller declares, and their falsifier is nesting.
//!
//! # The census array, and how a refusal travels — along the lineage, never through a shared word
//!
//! Every occurrence owns twelve 32-bit words on the card ([`SLOT_WORDS`]) and nothing else is
//! shared. A kernel that would leave the exact carrier, meets malformed material, or inverts an
//! enclosure writes its own flags and nothing plausible; the census kernel that follows it measures
//! the widest octave and enclosure and **compares the octave against the a-priori bound the
//! occurrence was admitted under**, writing a refuted bound into the same slot. **A kernel's first
//! act is to inspect the refusal words of its DECLARED predecessors, and only those** — the lineage
//! array is the diagram's own bond structure, uploaded before the capture opens, and the graph's
//! edges place every predecessor's census before the successor's kernel, so every word read is
//! final and every thread reads one value. A refusing lineage makes the occurrence refuse
//! `UPSTREAM`, with the join (union of flags, least refusing predecessor, count) written into its
//! own slot. An unrelated co-present sibling reads no word of the failing branch and cannot be
//! moved by it: the footprint certificate carries every slot read and written.
//!
//! The first form of this owner had one global refusal word every kernel read and every census
//! wrote. That was `FootprintDisjoint` falsely represented — unrelated branches shared mutable
//! standing — and whether a sibling saw a refusal depended on the device's scheduling. It is gone;
//! [`PassageReading::obstruction`] returns the **complete** obstruction lineage instead, and it is
//! one reading under any legal schedule ([`Schedule`] is the control).

use std::cell::RefCell;
use std::ffi::c_void;

use num_bigint::{BigInt, BigUint};
use relational_geometry::Rat;
use serde::Serialize;
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::cuda_aperture::DerivedLaunch;
use crate::embedding_fiber::{MountedReadout, ResidentReadout};
use crate::exact_value::ExactInterval;
use crate::exact_work::ExactWork;
use crate::hardware_cover::{DeviceDeclaration, HardwareCover, ModeIdentity};
use mount::{
    BorrowedContext, Device, DeviceAttribute, DeviceBuffer, Dim3, Event, GraphCensus, GraphExec,
    MemoryInfo, Module, Stream,
};

#[path = "resident_section/geometry.rs"]
mod geometry;
#[path = "resident_section/surface_mount.rs"]
mod surface_mount;
#[path = "resident_section/surface_passage.rs"]
mod surface_passage;
#[path = "resident_section/surface_condition.rs"]
mod surface_condition;
#[path = "resident_section/surface_adjoint.rs"]
mod surface_adjoint;
#[path = "resident_section/surface_intervention.rs"]
mod surface_intervention;
#[path = "resident_section/surface_shapes.rs"]
mod surface_shapes;
#[path = "resident_section/surface_tiled.rs"]
mod surface_tiled;

pub use geometry::*;
pub use surface_intervention::SiteMask;

const PTX: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/exact_resident_section.ptx"));
/// The exact accumulator the kernels carry, read off `__int128`; one octave is the hand.
const WIDE_OCTAVES: u32 = 127;
/// The signed word a section coordinate is stored in, read off `i64`; one octave is the hand.
pub const WORD_OCTAVES: u32 = 63;
/// The census slot: sixteen 32-bit words per occurrence. Layout in the kernel's own header.
pub const SLOT_WORDS: usize = 16;

/// **The register allocation granularity, in registers per warp.** An apparatus coordinate of the
/// mounted architecture: a warp's registers are charged in units of 256 (eight per thread, rounded
/// up), so a kernel using 40 registers per thread is charged 1,280 per warp and not 1,280 − ε. It
/// is stated here because the driver does not expose it as an attribute, and a candidate family
/// computed without it disagrees with the card's own residency reading.
///
/// Falsifier: `resident_blocks` computed with it must reproduce the measured
/// `resident_blocks_per_sm` of every kernel the profiler has already read.
const REGISTER_GRAIN_PER_WARP: u32 = 256;

/// **The warps the block-aggregated census folds across**, mirroring `CENSUS_MAX_WARPS` in
/// `kernels/exact_resident_section.cu`, which sizes the shared cross-warp buffers to it. It is the
/// mounted architecture's own ceiling — the maximum block is 1024 threads and a warp is 32 lanes, so
/// no legal block has more — and it is stated here rather than left as a literal because the kernel's
/// array and this guard must be one number. [`ResidentSurface::refuse_partial_warp_block`] REFUSES a
/// geometry past it by name; nothing is truncated and no fold runs with an incomplete mask.
///
/// Falsifier: a device whose `MAX_THREADS_PER_BLOCK / WARP_SIZE` exceeds this must refuse the census
/// rather than return one, and the refusal names the derived block and the warp.
const CENSUS_MAX_WARPS: u32 = 32;

/// The kernel symbols the module must carry. Loaded at [`ResidentSurface::on`]; a missing symbol
/// refuses there and never at a launch.
pub const KERNELS: [&str; 50] = [
    "section_constitutive_rechart",
    "section_constitutive_circulation",
    "section_constitutive_fibre",
    "section_withdraw_sites",
    "section_from_bfloat16",
    "section_carry",
    "section_terminal_row",
    "section_passive_contact",
    "section_partition_terminal_rows",
    "section_partition_mean",
    "section_withdraw_rows",
    "section_permute_columns",
    "section_contract",
    "section_factorized_contract",
    "section_rms_rebase",
    "section_chronology",
    "section_contact",
    "section_gelu_tanh",
    "section_tanh",
    "section_hadamard",
    "section_re_entry",
    "section_scale",
    "section_scale_by_aligned",
    "section_select_columns",
    "section_withdraw_columns",
    "section_collapse_control",
    "section_census",
    // The per-thread-atomic census the block-aggregated one replaced, kept so a driver can run both
    // on one section and measure the equality rather than argue it.
    "section_census_serial_control",
    // The midpoint quotient fused with its own census — one node, and the predecessor's own words
    // rewritten in place. Declared per occurrence; the passage refuses it unless the predecessor's
    // only consumer is the quotient and no receiver declared the predecessor's face.
    "section_midpoint_seal",
    // The receiver return: the emitted face meets its next occurrence and the differential of the
    // normalized exponential receiver returns through the terminal reactions as a deposit word.
    "section_receiver_return",
    // The adjoint of the contraction over one aligned tile, and the transposed midpoint seal that
    // makes a returning differential the `u` factor of a deposit.
    "section_contract_transposed_partial",
    "section_transpose_seal",
    // The adjoints of the reactions: the chronology turned back, the tanh and GELU derivative
    // factors, and the placement that is the adjoint of a column selection.
    "section_chronology_adjoint",
    "section_one_minus_square",
    "section_gelu_tanh_derivative",
    "section_place_columns",
    "section_rms_rebase_adjoint",
    "section_contact_adjoint_queries",
    "section_contact_adjoint_keys",
    "section_contact_adjoint_values",
    "section_arithmetic_control",
    // The tiled contraction's emitted family. Every wrapper is named here so the module-wide block
    // derivation inspects every instantiation rather than one; each carries `__launch_bounds__(512)`
    // so no instantiation drops `block_x` for the other kernels in the module.
    "section_contract_tiled_r1_l32",
    "section_contract_tiled_r2_l32",
    "section_contract_tiled_r4_l32",
    "section_contract_tiled_r1_l16",
    "section_contract_tiled_r4_l16",
    "section_contract_tiled_r1_l8",
    "section_contract_partial_r1_l32",
    "section_contract_partial_r4_l32",
    "section_contract_join",
];

/// `CUdevice_attribute` selectors from `cuda.h`, fixed by the foreign interface.
const ATTRIBUTE_MAX_THREADS_PER_BLOCK: i32 = 1;
const ATTRIBUTE_MAX_GRID_DIM_X: i32 = 5;
const ATTRIBUTE_MAX_SHARED_MEMORY_PER_BLOCK: i32 = 8;
const ATTRIBUTE_WARP_SIZE: i32 = 10;
const ATTRIBUTE_MULTIPROCESSOR_COUNT: i32 = 16;
const ATTRIBUTE_CONCURRENT_KERNELS: i32 = 31;
const ATTRIBUTE_MAX_THREADS_PER_MULTIPROCESSOR: i32 = 39;
const ATTRIBUTE_ASYNC_ENGINE_COUNT: i32 = 40;
const ATTRIBUTE_UNIFIED_ADDRESSING: i32 = 41;
const ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR: i32 = 75;
const ATTRIBUTE_COMPUTE_CAPABILITY_MINOR: i32 = 76;
const ATTRIBUTE_MAX_SHARED_MEMORY_PER_MULTIPROCESSOR: i32 = 81;
const ATTRIBUTE_MAX_REGISTERS_PER_MULTIPROCESSOR: i32 = 82;
const ATTRIBUTE_MAX_BLOCKS_PER_MULTIPROCESSOR: i32 = 106;

/// The refusal flags the kernels raise, mirrored from the kernel header.
pub const REFUSED_CARRIER: u32 = 1;
pub const REFUSED_MALFORMED: u32 = 2;
pub const REFUSED_INVERTED: u32 = 4;
pub const REFUSED_UPSTREAM: u32 = 8;
pub const REFUSED_BOUND: u32 = 16;

/// **Every way the resident owner refuses.** None of them is answered by a CPU computation.
#[derive(Debug, Error)]
pub enum ResidentRefusal {
    #[error("the CUDA driver reports no device; the resident chart is not mounted")]
    NoResidentChart,
    #[error("CUDA {operation} returned {code} ({name}): {message}")]
    Driver {
        operation: String,
        code: i32,
        name: String,
        message: String,
    },
    /// The mounted device (through `mount`) and the readout's device do not name one card.
    #[error("the readout mounted {readout:?} and the apparatus census names {mounted:?}")]
    DeviceDisagrees { readout: String, mounted: String },
    /// The measured or a-priori octaves plus the operation's own growth would leave the exact
    /// carrier. Decided before the launch; **nothing is truncated**.
    #[error(
        "{operation}: the exact carrier admits {admitted} octaves and this material needs {needed}"
    )]
    CarrierRange {
        operation: &'static str,
        needed: u32,
        admitted: u32,
    },
    /// The card raised the carrier flag during the deed at the named occurrence.
    #[error("{operation}: a coordinate left the exact carrier on the card")]
    CarrierLeft { operation: String },
    #[error(
        "{operation}: malformed material — a non-finite codeword or a non-positive denominator"
    )]
    Malformed { operation: String },
    /// A lawful step produced `lo > hi`. A soundness fault in the law itself, reported by name.
    #[error("{operation}: an enclosure inverted on the card")]
    Inverted { operation: String },
    /// A predecessor refused, so this occurrence wrote nothing; the first refusal names itself.
    #[error("{operation}: a predecessor refused upstream")]
    Upstream { operation: String },
    /// The a-priori octave bound this occurrence was admitted under was refuted by its own census.
    #[error(
        "{operation}: admitted at {admitted} octaves and measured {measured}; the a-priori law is refuted here"
    )]
    BoundRefuted {
        operation: String,
        admitted: u32,
        measured: u32,
    },
    #[error("{operation}: sections of width {left} and {right} do not meet")]
    WidthDisagrees {
        operation: &'static str,
        left: usize,
        right: usize,
    },
    #[error("{operation}: sections of {left} and {right} rows do not meet")]
    RowsDisagree {
        operation: &'static str,
        left: usize,
        right: usize,
    },
    #[error(
        "{operation}: {rows} rows of {width} exceeds the resident chart's declared grid aperture"
    )]
    GridAperture {
        operation: &'static str,
        rows: usize,
        width: usize,
    },
    #[error("{operation}: {words} words is not {rows} rows of {width}")]
    Ragged {
        operation: &'static str,
        words: usize,
        rows: usize,
        width: usize,
    },
    #[error(
        "{operation}: sections at grains {left} and {right} do not meet; a grain is declared once per deed"
    )]
    GrainsDisagree {
        operation: &'static str,
        left: u32,
        right: u32,
    },
    #[error("{operation}: {what}")]
    Declaration {
        operation: &'static str,
        what: String,
    },
    /// The mode the caller declared for the launch is not the mode this surface stands in.
    #[error(
        "the declared mode is not the surface's: expected {expected:?}, the surface is {actual:?}"
    )]
    ModeMismatch {
        expected: Box<ModeIdentity>,
        actual: Box<ModeIdentity>,
    },
    /// The deed's predicted resident octets exceed what the mounted device has free.
    #[error("the deed requires {required} resident octets and the device has {free} free")]
    MemoryAperture { required: u64, free: u64 },
}

impl From<mount::CudaError> for ResidentRefusal {
    fn from(error: mount::CudaError) -> Self {
        Self::Driver {
            operation: error.context.to_owned(),
            code: error.code,
            name: error.name,
            message: error.message,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// exact dyadics and enclosures
// ---------------------------------------------------------------------------------------------

/// An exact dyadic `significand · 2^exponent`. The stored BF16 scale the source casts, the
/// `binary64` words the source's implementation computes with, the source's `eps` — each is one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Dyadic {
    pub significand: i64,
    pub exponent: i32,
}

impl Dyadic {
    pub const ONE: Self = Self {
        significand: 1,
        exponent: 0,
    };

    pub fn octaves(&self) -> u32 {
        64 - self.significand.unsigned_abs().leading_zeros()
    }

    /// The exact dyadic of a `binary64` word, through the workspace's declared float mouth.
    pub fn of_binary64_bits(bits: u64) -> Result<Self, ResidentRefusal> {
        let datum = crate::exact_value::ieee754::decode_binary64_bits(bits).map_err(|error| {
            ResidentRefusal::Declaration {
                operation: "dyadic",
                what: format!("{error:?}"),
            }
        })?;
        let magnitude =
            i64::try_from(&datum.significand).map_err(|_| ResidentRefusal::Declaration {
                operation: "dyadic",
                what: "a binary64 significand exceeds the signed word".to_owned(),
            })?;
        Ok(Self {
            significand: if datum.negative {
                -magnitude
            } else {
                magnitude
            },
            exponent: datum.ulp_exponent,
        })
    }

    /// The exact dyadic of a `bfloat16` word.
    pub fn of_bfloat16_bits(word: u16) -> Result<Self, ResidentRefusal> {
        let datum = crate::exact_value::ieee754::decode_bfloat16_bits(word).map_err(|error| {
            ResidentRefusal::Declaration {
                operation: "dyadic",
                what: format!("{error:?}"),
            }
        })?;
        let magnitude =
            i64::try_from(&datum.significand).map_err(|_| ResidentRefusal::Declaration {
                operation: "dyadic",
                what: "a bfloat16 significand exceeds the signed word".to_owned(),
            })?;
        Ok(Self {
            significand: if datum.negative {
                -magnitude
            } else {
                magnitude
            },
            exponent: datum.ulp_exponent,
        })
    }

    /// The exact rational this dyadic is.
    pub fn value(&self) -> Rat {
        let significand = Rat::from_integer(BigInt::from(self.significand));
        if self.exponent >= 0 {
            significand
                * Rat::from_integer(BigInt::from(BigUint::from(1u8) << self.exponent as usize))
        } else {
            significand
                / Rat::from_integer(BigInt::from(
                    BigUint::from(1u8) << (-self.exponent) as usize,
                ))
        }
    }
}

/// The exact rational a section word denotes at a grain: `word · 2^-F`.
pub fn word_value(word: i64, grain: ResidentGrain) -> Rat {
    Rat::new(
        BigInt::from(word),
        BigInt::from(BigUint::from(1u8) << grain.0 as usize),
    )
}

/// A certified enclosure `[lo, hi] · 2^-grain` of an algebraic or transcendental constant, founded
/// on the serial chart once by `exact_value` and carried onto the card as two words. Never a float.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DyadicEnclosure {
    pub lo: i64,
    pub hi: i64,
    pub grain: u32,
}

impl DyadicEnclosure {
    pub fn octaves(&self) -> u32 {
        64 - self
            .lo
            .unsigned_abs()
            .max(self.hi.unsigned_abs())
            .leading_zeros()
    }

    /// An exact interval widened outward onto the grain: the lower bound floors, the upper ceils,
    /// so the enclosure strictly contains what it was founded from. Refuses a word past the carrier.
    pub fn of_interval(interval: &ExactInterval, grain: u32) -> Result<Self, ResidentRefusal> {
        let scale = Rat::from_integer(BigInt::from(BigUint::from(1u8) << grain as usize));
        let floor = (&interval.lower * &scale).floor().to_integer();
        let ceil = (&interval.upper * &scale).ceil().to_integer();
        let refuse = || ResidentRefusal::Declaration {
            operation: "enclosure",
            what: format!("an enclosure at grain {grain} leaves the signed word"),
        };
        Ok(Self {
            lo: i64::try_from(&floor).map_err(|_| refuse())?,
            hi: i64::try_from(&ceil).map_err(|_| refuse())?,
            grain,
        })
    }
}

/// The declared dyadic grain `2^-F` of every section in one deed. **An apparatus aperture, not a
/// tolerance**: a finer grain must nest the terminal enclosure, and that is a falsifier the driver
/// runs rather than a property assumed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ResidentGrain(pub u32);

/// The declared series aperture: how many terms of the exponential are summed before the
/// alternating tail brackets the value. Same law: a longer series nests.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SeriesAperture(pub u32);

// ---------------------------------------------------------------------------------------------
// the census of what crossed
// ---------------------------------------------------------------------------------------------

/// **What crossed the apparatus boundary, and in which direction, over the life of one surface.**
///
/// The directive's measurement of a resident passage is this table: between the graph launch and
/// the terminal synchronize the serial chart issues no launch and reads nothing, so `deed_launches`
/// moves by one, `synchronizations` by one, and `captured_launches` — the launches recorded into
/// the graph before the deed — by zero. Section egress moves once, at the declared receiver.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct TransferCensus {
    pub ingress_octets: u64,
    pub egress_section_octets: u64,
    pub egress_receipt_octets: u64,
    pub device_to_device_octets: u64,
    /// Kernel launches recorded into a graph at capture — before any deed.
    pub captured_launches: u64,
    /// Graph launches: one per deed.
    pub deed_launches: u64,
    /// Kernel launches issued directly, outside any passage — the arithmetic control only.
    pub control_launches: u64,
    pub synchronizations: u64,
    pub allocations: u64,
    pub resident_octets_now: u64,
    pub resident_octets_peak: u64,
    /// How many times a section crossed to the serial chart as a semantic standing.
    pub section_read_outs: u64,
}

impl TransferCensus {
    fn resident_grew(&mut self, octets: u64) {
        self.resident_octets_now += octets;
        if self.resident_octets_now > self.resident_octets_peak {
            self.resident_octets_peak = self.resident_octets_now;
        }
    }
    fn resident_shrank(&mut self, octets: u64) {
        self.resident_octets_now = self.resident_octets_now.saturating_sub(octets);
    }
}

// ---------------------------------------------------------------------------------------------
// the apparatus surface
// ---------------------------------------------------------------------------------------------

/// **The apparatus occurrence: the mounted device, the readout's context, the exact laws loaded
/// into it, the device's declaration, the cover over it, and the census.** One occurrence, bound
/// once; nothing here is supplied by a caller.
pub struct ResidentSurface<'chart> {
    readout: &'chart ResidentReadout,
    context: BorrowedContext,
    device: Device,
    module: Module,
    ptx_sha256: String,
    declaration: DeviceDeclaration,
    cover: HardwareCover,
    launch: DerivedLaunch,
    /// The largest power of two the reduction kernels may use as a block, taken down from what the
    /// device and the kernels admit. Derived, never chosen.
    reduction_block: u32,
    max_shared_octets: u32,
    memory_at_mount: MemoryInfo,
    /// The `cuMemAlloc` charge grain the card actually levies, measured at mount by two probes
    /// ([`mount::BorrowedContext::allocation_grain_bytes`]). An apparatus coordinate: every
    /// allocation a deed predicts is rounded up to it, so the predicted requirement is what the
    /// card will charge rather than what the words sum to.
    allocation_grain: u64,
    /// The multiprocessor's own residency ceilings, as the device stated them: blocks, registers
    /// and shared octets per multiprocessor. Read at mount; nothing here is remembered from a
    /// specification sheet.
    sm_limits: MultiprocessorLimits,
    /// **Retained apparatus scratch for the split-K partial buffers.** A partial standing is not a
    /// section: it carries the exact 128-bit accumulation of one K slice and never a coordinate at
    /// the grain. It is retained for the surface's life because the kernel that writes it and the
    /// kernel that reads it are recorded into one graph before either runs.
    partials: RefCell<Vec<Option<DeviceBuffer<i64>>>>,
    census: RefCell<TransferCensus>,
}

/// The multiprocessor's declared residency ceilings — the inputs of the resource equation, each
/// read from `cuDeviceGetAttribute` and none of them authored.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MultiprocessorLimits {
    pub max_blocks: u32,
    pub max_threads: u32,
    pub max_registers: u32,
    pub max_shared_octets: u32,
    pub warp: u32,
    pub multiprocessors: u32,
    /// The register allocation granularity, in registers per warp. Ada allocates in units of 256.
    pub register_grain: u32,
}

/// A section resident on the card. **Opaque**: its coordinates are reachable only through the
/// operations of the surface it lives on, and through the terminal [`ResidentSurface::read_out`].
pub struct ResidentSection<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    lo: DeviceBuffer<i64>,
    hi: DeviceBuffer<i64>,
    rows: usize,
    width: usize,
    grain: ResidentGrain,
    octets: u64,
}

impl std::fmt::Debug for ResidentSection<'_> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ResidentSection")
            .field("rows", &self.rows)
            .field("width", &self.width)
            .field("grain", &self.grain)
            .finish_non_exhaustive()
    }
}

impl ResidentSection<'_> {
    pub fn rows(&self) -> usize {
        self.rows
    }
    pub fn width(&self) -> usize {
        self.width
    }
    pub fn grain(&self) -> ResidentGrain {
        self.grain
    }
    /// The resident address of the lower endpoint population, for a sibling owner in this crate
    /// mounting a sealed section (`lo == hi`) as an aligned readout inside the same context.
    pub(crate) fn lo_device_ptr(&self) -> u64 {
        self.lo.device_ptr()
    }
    pub(crate) fn hi_device_ptr(&self) -> u64 {
        self.hi.device_ptr()
    }
    pub fn resident_octets(&self) -> u64 {
        self.octets
    }
    fn count(&self) -> usize {
        self.rows * self.width
    }
    /// The address ranges this section occupies — its footprint as a realization coordinate.
    pub fn ranges(&self) -> [(u64, u64); 2] {
        let octets = (self.count() * std::mem::size_of::<i64>()) as u64;
        [
            (self.lo.device_ptr(), self.lo.device_ptr() + octets),
            (self.hi.device_ptr(), self.hi.device_ptr() + octets),
        ]
    }
}

/// One immutable endpoint population, moved out of an interval section without copying it.
/// A sealed coefficient producer uses this after its two endpoints have become identical.
pub(crate) struct ResidentEndpoint<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    words: DeviceBuffer<i64>,
    rows: usize,
    width: usize,
}

impl<'chart> ResidentSection<'chart> {
    /// Retain the lower endpoint and release the upper allocation. This is an explicit
    /// endpoint projection, not a claim that an arbitrary interval has zero width. Overlay
    /// producers call it only after a successful resident seal; both consumers already read
    /// that exact lower population. No allocation, transfer, or numerical change occurs.
    pub(crate) fn into_lower_endpoint(self) -> ResidentEndpoint<'chart> {
        let section = std::mem::ManuallyDrop::new(self);
        let _ = section.surface.context.make_current();
        // SAFETY: ManuallyDrop suppresses the section's destructor. Each owning buffer is
        // moved exactly once: lo into the endpoint, hi into its destructor. The surface and
        // dimensions are borrowed/Copy; census ownership is split with those two buffers.
        let (words, upper) = unsafe {
            (std::ptr::read(&section.lo), std::ptr::read(&section.hi))
        };
        let retained_octets = (words.len() * std::mem::size_of::<i64>()) as u64;
        drop(upper);
        section.surface.released_octets(section.octets - retained_octets);
        ResidentEndpoint { surface: section.surface, words, rows: section.rows, width: section.width }
    }
}

impl ResidentEndpoint<'_> {
    pub(crate) fn lo_device_ptr(&self) -> u64 { self.words.device_ptr() }
    pub(crate) fn rows(&self) -> usize { self.rows }
    pub(crate) fn width(&self) -> usize { self.width }
}

impl Drop for ResidentEndpoint<'_> {
    fn drop(&mut self) {
        let _ = self.surface.context.make_current();
        self.surface.released_octets((self.words.len() * std::mem::size_of::<i64>()) as u64);
    }
}

const RESIDENT_SECTION_REST_MAGIC: &[u8; 8] = b"HRSRST\0\x01";

fn resident_section_rest_header_octets() -> usize {
    RESIDENT_SECTION_REST_MAGIC.len()
        + std::mem::size_of::<u64>()
        + std::mem::size_of::<u64>()
        + std::mem::size_of::<u32>()
        + std::mem::size_of::<u32>()
        + std::mem::size_of::<u64>()
}

/// Exact detachable testimony for one resident section at an apparatus boundary.
///
/// This is not a second semantic carrier. It is the exterior rest of the same interval section:
/// shape, grain, admitted octave bound, and every directed endpoint. A later surface may remount
/// it and continue the original typed transport without recomputing the predecessor passage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentSectionRest {
    pub rows: usize,
    pub width: usize,
    pub grain: ResidentGrain,
    pub bound_octaves: u32,
    pub intervals: Vec<(i64, i64)>,
}

impl ResidentSectionRest {
    pub fn found(
        rows: usize,
        width: usize,
        grain: ResidentGrain,
        bound_octaves: u32,
        intervals: Vec<(i64, i64)>,
    ) -> Result<Self, String> {
        let rest = Self {
            rows,
            width,
            grain,
            bound_octaves,
            intervals,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn validate(&self) -> Result<(), String> {
        let population = self
            .rows
            .checked_mul(self.width)
            .ok_or_else(|| "resident section rest extent overflow".to_owned())?;
        if self.rows == 0
            || self.width == 0
            || population != self.intervals.len()
            || self.intervals.iter().any(|(lower, upper)| lower > upper)
        {
            return Err("resident section rest does not reconstruct its exact section".to_owned());
        }
        Ok(())
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        let rows = u64::try_from(self.rows)
            .map_err(|_| "resident section row extent left the canonical carrier")?;
        let width = u64::try_from(self.width)
            .map_err(|_| "resident section width left the canonical carrier")?;
        let population = u64::try_from(self.intervals.len())
            .map_err(|_| "resident section population left the canonical carrier")?;
        let body_octets = self
            .intervals
            .len()
            .checked_mul(16)
            .ok_or_else(|| "resident section rest byte extent overflow".to_owned())?;
        let mut bytes =
            Vec::with_capacity(resident_section_rest_header_octets().saturating_add(body_octets));
        bytes.extend_from_slice(RESIDENT_SECTION_REST_MAGIC);
        bytes.extend_from_slice(&rows.to_le_bytes());
        bytes.extend_from_slice(&width.to_le_bytes());
        bytes.extend_from_slice(&self.grain.0.to_le_bytes());
        bytes.extend_from_slice(&self.bound_octaves.to_le_bytes());
        bytes.extend_from_slice(&population.to_le_bytes());
        for (lower, upper) in &self.intervals {
            bytes.extend_from_slice(&lower.to_le_bytes());
            bytes.extend_from_slice(&upper.to_le_bytes());
        }
        Ok(bytes)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, String> {
        let header_octets = resident_section_rest_header_octets();
        if bytes.len() < header_octets || &bytes[..8] != RESIDENT_SECTION_REST_MAGIC {
            return Err("resident section rest magic is absent".to_owned());
        }
        let word = |from: usize| -> Result<[u8; 8], String> {
            bytes
                .get(from..from + 8)
                .ok_or_else(|| "resident section rest header is truncated".to_owned())?
                .try_into()
                .map_err(|_| "resident section rest header word is malformed".to_owned())
        };
        let rows = usize::try_from(u64::from_le_bytes(word(8)?))
            .map_err(|_| "resident section row extent left this apparatus")?;
        let width = usize::try_from(u64::from_le_bytes(word(16)?))
            .map_err(|_| "resident section width left this apparatus")?;
        let grain = u32::from_le_bytes(
            bytes[24..28]
                .try_into()
                .map_err(|_| "resident section grain is malformed")?,
        );
        let bound_octaves = u32::from_le_bytes(
            bytes[28..32]
                .try_into()
                .map_err(|_| "resident section bound is malformed")?,
        );
        let population = usize::try_from(u64::from_le_bytes(word(32)?))
            .map_err(|_| "resident section population left this apparatus")?;
        let body_octets = population
            .checked_mul(16)
            .ok_or_else(|| "resident section rest body extent overflow".to_owned())?;
        if bytes.len() != header_octets.saturating_add(body_octets) {
            return Err("resident section rest byte extent does not reconstruct".to_owned());
        }
        let mut intervals = Vec::with_capacity(population);
        for pair in bytes[header_octets..].chunks_exact(16) {
            let lower = i64::from_le_bytes(
                pair[..8]
                    .try_into()
                    .map_err(|_| "resident section lower endpoint is malformed")?,
            );
            let upper = i64::from_le_bytes(
                pair[8..]
                    .try_into()
                    .map_err(|_| "resident section upper endpoint is malformed")?,
            );
            intervals.push((lower, upper));
        }
        Self::found(rows, width, ResidentGrain(grain), bound_octaves, intervals)
    }

    pub fn sha256(&self) -> Result<String, String> {
        Ok(format!("{:x}", Sha256::digest(self.canonical_bytes()?)))
    }
}

impl Drop for ResidentSection<'_> {
    fn drop(&mut self) {
        let _ = self.surface.context.make_current();
        self.surface
            .census
            .borrow_mut()
            .resident_shrank(self.octets);
    }
}

/// The site's band group elements — `(cos θ_b, sin θ_b)` per band as certified enclosures — resident
/// once. A chronology names them; the transcendental was evaluated when they were founded.
pub struct BandElements<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    cos_lo: DeviceBuffer<i64>,
    cos_hi: DeviceBuffer<i64>,
    sin_lo: DeviceBuffer<i64>,
    sin_hi: DeviceBuffer<i64>,
    bands: usize,
    grain: u32,
    octets: u64,
}

impl BandElements<'_> {
    /// **Where the mounted elements live.** An apparatus coordinate, exposed for the same reason
    /// as [`crate::embedding_fiber::MountedReadout::aligned_address`]: a graph executable's kernel
    /// parameters bake this address in, so a caller keying an instantiated executable must be able
    /// to say which band set it was bound over.
    pub fn resident_address(&self) -> u64 {
        self.cos_lo.device_ptr()
    }
    pub fn bands(&self) -> usize {
        self.bands
    }
    pub fn grain(&self) -> u32 {
        self.grain
    }
    pub fn resident_octets(&self) -> u64 {
        self.octets
    }
    pub fn ranges(&self) -> [(u64, u64); 4] {
        let octets = (self.bands * 8) as u64;
        [&self.cos_lo, &self.cos_hi, &self.sin_lo, &self.sin_hi]
            .map(|b| (b.device_ptr(), b.device_ptr() + octets))
    }
}

impl Drop for BandElements<'_> {
    fn drop(&mut self) {
        let _ = self.surface.context.make_current();
        self.surface
            .census
            .borrow_mut()
            .resident_shrank(self.octets);
    }
}

/// The integer positions of a section's rows, resident. The chronology's exact carrier.
pub struct Positions<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    buffer: DeviceBuffer<u32>,
    rows: usize,
    octets: u64,
}

impl Positions<'_> {
    /// **Where the mounted positions live** — the same apparatus coordinate, for the same reason.
    pub fn resident_address(&self) -> u64 {
        self.buffer.device_ptr()
    }
    pub fn rows(&self) -> usize {
        self.rows
    }
    pub(crate) fn device_ptr(&self) -> u64 {
        self.buffer.device_ptr()
    }
    pub fn resident_octets(&self) -> u64 {
        self.octets
    }
    pub fn range(&self) -> (u64, u64) {
        (
            self.buffer.device_ptr(),
            self.buffer.device_ptr() + (self.rows * 4) as u64,
        )
    }
}

impl Drop for Positions<'_> {
    fn drop(&mut self) {
        let _ = self.surface.context.make_current();
        self.surface
            .census
            .borrow_mut()
            .resident_shrank(self.octets);
    }
}

/// Entering codewords staged on the card, refillable for a later deed of the same extent. The
/// words cross once per deed; the section they become stays.
pub struct StagedWords<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    buffer: DeviceBuffer<u16>,
    rows: usize,
    width: usize,
    octets: u64,
}

impl StagedWords<'_> {
    pub fn rows(&self) -> usize {
        self.rows
    }
    pub fn width(&self) -> usize {
        self.width
    }
    pub fn range(&self) -> (u64, u64) {
        (
            self.buffer.device_ptr(),
            self.buffer.device_ptr() + self.octets,
        )
    }
}

impl Drop for StagedWords<'_> {
    fn drop(&mut self) {
        let _ = self.surface.context.make_current();
        self.surface
            .census
            .borrow_mut()
            .resident_shrank(self.octets);
    }
}

fn ceil_log2(n: usize) -> u32 {
    if n <= 1 { 0 } else { (n - 1).ilog2() + 1 }
}

/// **The mouth's a-priori octave bound, read off the entering words.** For each codeword the mouth
/// decodes, the placed value is `significand · scale · 2^(ulp + scale exponent + F)`; its octaves
/// are the significand's plus the scale's plus that exponent, and the directed ceiling adds one.
/// The greatest over the population is the bound. A non-finite codeword contributes nothing — the
/// kernel refuses it as malformed rather than placing it.
///
/// This is the one reading; [`ResidentSurface::shape_enter`] and [`crate::resident_law::Enter`]'s
/// a-priori law both take it, so a carrier admission and a census comparison cannot disagree.
fn entering_octaves(words: &[u16], scale: Dyadic, grain: ResidentGrain) -> u32 {
    let f = i64::from(grain.0);
    let mut widest = 0i64;
    for word in words {
        if let Ok(dyadic) = Dyadic::of_bfloat16_bits(*word) {
            if dyadic.significand == 0 {
                continue;
            }
            let magnitude = i64::from(dyadic.octaves()) + i64::from(scale.octaves());
            let shifted = magnitude + i64::from(dyadic.exponent) + i64::from(scale.exponent) + f;
            widest = widest.max(shifted);
        }
    }
    u32::try_from(widest + 1).unwrap_or(1).max(1)
}

/// The parameter words of one launch, each in its own 64-bit slot so `cuLaunchKernel` reads every
/// argument from a stable address of its own size (little-endian: a 32-bit argument is the low
/// half of its slot).
struct Params {
    words: Vec<u64>,
}

impl Params {
    fn new() -> Self {
        Self {
            words: Vec::with_capacity(20),
        }
    }
    fn ptr(&mut self, pointer: u64) -> &mut Self {
        self.words.push(pointer);
        self
    }
    fn u32(&mut self, value: u32) -> &mut Self {
        self.words.push(u64::from(value));
        self
    }
    fn u64(&mut self, value: u64) -> &mut Self {
        self.words.push(value);
        self
    }
    fn i32(&mut self, value: i32) -> &mut Self {
        self.words.push(u64::from(value as u32));
        self
    }
    fn i64(&mut self, value: i64) -> &mut Self {
        self.words.push(value as u64);
        self
    }
    fn pointers(&mut self) -> Vec<*mut c_void> {
        self.words
            .iter_mut()
            .map(|word| (word as *mut u64).cast::<c_void>())
            .collect()
    }
}

/// The predicted shape and price of one occurrence, before any launch: what it writes, the octave
/// budget it needs, the work it performs, and the reductions it realizes as named barriers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawShape {
    pub operation: &'static str,
    pub rows: usize,
    pub width: usize,
    /// The octave budget the launch is admitted under.
    pub needed: u32,
    pub predicted: ExactWork,
    /// The within-section global couplings this occurrence realizes as resident reductions.
    pub couplings: Vec<CouplingPlan>,
    /// Kernel launches this occurrence records: the semantic kernel and its census.
    pub launches: u32,
    /// Dynamic shared octets its block reduction uses.
    pub shared_octets: u32,
    /// The block a reduction runs at, or the flat block.
    pub block: u32,
}

/// A within-section global coupling — a term that is not a flux (`H.0219`) — with the resident
/// kernel that realizes it and the extent it reduces over. Typed; the receipt completes it after
/// the deed with the census that proves the kernel ran.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CouplingPlan {
    pub coupling: &'static str,
    /// The kernel symbol, one of [`KERNELS`], which the module loaded at mount.
    pub kernel: &'static str,
    /// The extent the reduction spans — the group, the reach.
    pub extent: u64,
    /// The block the reduction runs at: its capacity per round.
    pub block: u32,
    /// The reduction's own predicted work.
    pub predicted: ExactWork,
}

/// The reading of one occurrence's census slot after the deed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SlotReading {
    pub refused: u32,
    pub reach: u32,
    pub written: bool,
    pub inverted: bool,
    pub max_octave: u32,
    pub bound_violated: bool,
    pub max_width: u64,
    /// The union of the refusal flags of every refusing declared predecessor — the lineage join.
    pub upstream_flags: u32,
    /// The least refusing predecessor in the declared lineage, by passage index.
    pub upstream_first: Option<usize>,
    /// How many declared predecessors had refused.
    pub upstream_count: u32,
    /// How many predecessor slots the kernel inspected at entry — proof the inspection ran, and
    /// equal to the declared lineage's length.
    pub lineage_inspected: u32,
    /// The sum of every enclosure's width in grains, and how many coordinates had width at all —
    /// with `max_width`, the collapsed population a midpoint quotient after this occurrence deletes.
    pub width_sum: u64,
    pub nonzero_widths: u32,
}

impl SlotReading {
    fn of(words: &[u32]) -> Self {
        Self {
            refused: words[0],
            reach: words[1],
            written: words[2] != 0,
            inverted: words[3] != 0,
            max_octave: words[4],
            bound_violated: words[5] != 0,
            max_width: u64::from(words[6]) | (u64::from(words[7]) << 32),
            upstream_flags: words[8],
            upstream_first: if words[9] == 0 {
                None
            } else {
                Some(words[9] as usize - 1)
            },
            upstream_count: words[10],
            lineage_inspected: words[11],
            width_sum: u64::from(words[12]) | (u64::from(words[13]) << 32),
            nonzero_widths: words[14],
        }
    }

    /// Whether this occurrence is where an obstruction ORIGINATED (it refused for a reason of its
    /// own) rather than one it carried from its lineage.
    pub fn originates_refusal(&self) -> bool {
        self.refused & !REFUSED_UPSTREAM != 0
    }

    /// The typed refusal this slot carries, if any, named for the occurrence.
    pub fn refusal(&self, operation: &str, admitted: u32) -> Option<ResidentRefusal> {
        let name = operation.to_owned();
        if self.refused & REFUSED_UPSTREAM != 0 {
            return Some(ResidentRefusal::Upstream { operation: name });
        }
        if self.refused & REFUSED_BOUND != 0 || self.bound_violated {
            return Some(ResidentRefusal::BoundRefuted {
                operation: name,
                admitted,
                measured: self.max_octave,
            });
        }
        if self.refused & REFUSED_CARRIER != 0 {
            return Some(ResidentRefusal::CarrierLeft { operation: name });
        }
        if self.refused & REFUSED_MALFORMED != 0 {
            return Some(ResidentRefusal::Malformed { operation: name });
        }
        if self.refused & REFUSED_INVERTED != 0 || self.inverted {
            return Some(ResidentRefusal::Inverted { operation: name });
        }
        None
    }
}

/// One occurrence's lane in an open capture: its stream, its own census slot, and the lineage it
/// inspects — the census array's base and the addresses of its declared predecessors' indices.
pub struct Lane<'a, 'chart> {
    stream: &'a Stream,
    /// The occurrence's slot base on the card.
    pub slot: u64,
    /// The census array's base: predecessor slots are read at `census + p·SLOT_WORDS·4`.
    pub census: u64,
    /// This occurrence's predecessor indices on the card, and how many.
    pub lineage: u64,
    pub lineage_count: u32,
    pub index: usize,
    _surface: std::marker::PhantomData<&'a ResidentSurface<'chart>>,
}

/// **How the passage's kernels are ordered beyond the diagram's bonds.** A control axis: the
/// lineage a kernel reads never changes with it, so the complete obstruction lineage must not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Schedule {
    /// Only the diagram's bonds order the kernels; co-present members may overlap.
    CoPresent,
    /// Every occurrence also waits on the occurrence opened before it: a total order in the order
    /// the passage opens them. Opening a front's members in another order is another legal
    /// completion order of the same diagram.
    Serialized,
}

/// **An open capture**: the passage being bound, occurrence by occurrence, before any launch.
pub struct PassageBuilder<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    origin: Stream,
    lanes: Vec<Stream>,
    events: Vec<Event>,
    memset_event: Event,
    census_buffer: DeviceBuffer<u32>,
    lineage_buffer: DeviceBuffer<u32>,
    lineage_words: usize,
    /// Every occurrence's declared predecessors, sorted and deduplicated.
    declared: Vec<Vec<usize>>,
    /// `(offset, count)` of each occurrence's list in the lineage array.
    offsets: Vec<(usize, usize)>,
    occurrences: usize,
    nodes: usize,
    edges: usize,
    opened: Vec<bool>,
    closed: Vec<bool>,
    schedule: Schedule,
    last_opened: Option<usize>,
}

impl<'chart> PassageBuilder<'chart> {
    /// The census slot base of an occurrence.
    fn slot_of(&self, index: usize) -> u64 {
        self.census_buffer.device_ptr() + (index * SLOT_WORDS * 4) as u64
    }
    fn lineage_of(&self, index: usize) -> (u64, u32) {
        let (offset, count) = self.offsets[index];
        (
            self.lineage_buffer.device_ptr() + (offset * 4) as u64,
            count as u32,
        )
    }
    fn lane_of(&self, index: usize) -> Lane<'_, 'chart> {
        let (lineage, lineage_count) = self.lineage_of(index);
        Lane {
            stream: &self.lanes[index],
            slot: self.slot_of(index),
            census: self.census_buffer.device_ptr(),
            lineage,
            lineage_count,
            index,
            _surface: std::marker::PhantomData,
        }
    }

    /// The address range of an occurrence's own slot — written by its kernels.
    pub fn slot_range(&self, index: usize) -> (u64, u64) {
        (
            self.slot_of(index),
            self.slot_of(index) + (SLOT_WORDS * 4) as u64,
        )
    }
    /// The address range of an occurrence's list in the lineage array — read by its kernel.
    pub fn lineage_range(&self, index: usize) -> (u64, u64) {
        let (offset, count) = self.offsets[index];
        let from = self.lineage_buffer.device_ptr() + (offset * 4) as u64;
        (from, from + (count.max(1) * 4) as u64)
    }
    /// The declared predecessors of an occurrence, sorted and deduplicated — **the slots its
    /// kernel reads**, for the footprint.
    pub fn declared_lineage(&self, index: usize) -> &[usize] {
        &self.declared[index]
    }
    pub fn schedule(&self) -> Schedule {
        self.schedule
    }

    /// **Open occurrence `index`'s lane after its producers.** Every producer's census event is
    /// waited on (a graph edge each, deduplicated); a source occurrence waits the memset instead.
    /// `producers` must be the lineage declared at [`ResidentSurface::begin_passage`] — a
    /// mismatch is a declaration error, because the kernel will read exactly the declared slots.
    /// The lane is where the occurrence's one semantic kernel is recorded.
    pub fn open(
        &mut self,
        index: usize,
        producers: &[usize],
    ) -> Result<Lane<'_, 'chart>, ResidentRefusal> {
        if index >= self.occurrences || self.opened[index] {
            return Err(ResidentRefusal::Declaration {
                operation: "passage",
                what: format!("occurrence {index} opened twice or out of range"),
            });
        }
        let mut given: Vec<usize> = producers.to_vec();
        given.sort_unstable();
        given.dedup();
        if given != self.declared[index] {
            return Err(ResidentRefusal::Declaration {
                operation: "passage",
                what: format!(
                    "occurrence {index} opens with producers {given:?} but declared lineage {:?}",
                    self.declared[index]
                ),
            });
        }
        let lane = &self.lanes[index];
        for producer in &self.declared[index] {
            if !self.closed[*producer] {
                return Err(ResidentRefusal::Declaration {
                    operation: "passage",
                    what: format!(
                        "occurrence {index} reads occurrence {producer}, which no earlier front wrote"
                    ),
                });
            }
            lane.wait_event(&self.events[*producer])?;
            self.edges += 1;
        }
        if self.declared[index].is_empty() {
            lane.wait_event(&self.memset_event)?;
            self.edges += 1;
        }
        // The serialized control: also after the occurrence opened before this one, whichever it was.
        if self.schedule == Schedule::Serialized {
            if let Some(previous) = self.last_opened {
                if !self.declared[index].contains(&previous) {
                    if !self.closed[previous] {
                        return Err(ResidentRefusal::Declaration {
                            operation: "passage",
                            what: format!(
                                "serialized: occurrence {previous} was not closed before {index}"
                            ),
                        });
                    }
                    lane.wait_event(&self.events[previous])?;
                    self.edges += 1;
                }
            }
        }
        self.opened[index] = true;
        self.last_opened = Some(index);
        Ok(self.lane_of(index))
    }

    /// **Close occurrence `index`**: record its census after its semantic kernel and record the
    /// event successors wait on. The a-priori bound is what the census compares the measured
    /// octave against.
    pub fn close(
        &mut self,
        index: usize,
        out: &ResidentSection<'chart>,
        admitted_octaves: u32,
    ) -> Result<(), ResidentRefusal> {
        if !self.opened[index] || self.closed[index] {
            return Err(ResidentRefusal::Declaration {
                operation: "passage",
                what: format!("occurrence {index} closed before it was opened, or twice"),
            });
        }
        let lane = self.lane_of(index);
        self.surface.record_census(&lane, out, admitted_octaves)?;
        self.events[index].record(&self.lanes[index])?;
        self.closed[index] = true;
        // the semantic kernel and its census: two nodes and the edge between them
        self.nodes += 2;
        self.edges += 1;
        Ok(())
    }

    /// **Close an occurrence whose kernel wrote its own census.** No census node is recorded and no
    /// edge is added: the fused kernel is the only node this occurrence contributes. The a-priori
    /// bound it compares against was handed to that kernel when it was recorded.
    pub fn close_fused(&mut self, index: usize) -> Result<(), ResidentRefusal> {
        if !self.opened[index] || self.closed[index] {
            return Err(ResidentRefusal::Declaration {
                operation: "passage",
                what: format!("occurrence {index} closed before it was opened, or twice"),
            });
        }
        self.events[index].record(&self.lanes[index])?;
        self.closed[index] = true;
        self.nodes += 1;
        Ok(())
    }

    /// **Bind the passage**: join every lane back to the origin, end the capture, read the graph's
    /// own census, instantiate. What comes back is launchable and reads back once.
    pub fn finish(self) -> Result<ResidentPassage<'chart>, ResidentRefusal> {
        for index in 0..self.occurrences {
            if !self.closed[index] {
                return Err(ResidentRefusal::Declaration {
                    operation: "passage",
                    what: format!("occurrence {index} was never bound"),
                });
            }
            self.origin.wait_event(&self.events[index])?;
        }
        let graph = self.origin.end_capture()?;
        let graph_census = graph.census()?;
        let exec = graph.instantiate()?;
        Ok(ResidentPassage {
            surface: self.surface,
            origin: self.origin,
            _lanes: self.lanes,
            _events: self.events,
            _memset_event: self.memset_event,
            census_buffer: self.census_buffer,
            _lineage_buffer: self.lineage_buffer,
            lineage_words: self.lineage_words,
            declared: self.declared,
            occurrences: self.occurrences,
            intended_nodes: self.nodes,
            intended_edges: self.edges,
            schedule: self.schedule,
            graph_census,
            _graph: graph,
            exec,
        })
    }
}

/// **A bound passage**: one graph, launched as one, read as one.
pub struct ResidentPassage<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    origin: Stream,
    _lanes: Vec<Stream>,
    _events: Vec<Event>,
    _memset_event: Event,
    census_buffer: DeviceBuffer<u32>,
    _lineage_buffer: DeviceBuffer<u32>,
    lineage_words: usize,
    declared: Vec<Vec<usize>>,
    occurrences: usize,
    intended_nodes: usize,
    intended_edges: usize,
    schedule: Schedule,
    graph_census: GraphCensus,
    _graph: mount::Graph,
    exec: GraphExec,
}

/// **One occurrence's place in the obstruction lineage of a deed.** `origin` says the refusal is
/// its own (carrier, malformed, inverted, refuted bound); otherwise it carried one from the
/// predecessors named by `upstream_first` and counted by `upstream_count`, with the joined flags.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OccurrenceRefusal {
    pub index: usize,
    pub flags: u32,
    pub origin: bool,
    pub upstream_flags: u32,
    pub upstream_first: Option<usize>,
    pub upstream_count: u32,
}

/// **The complete obstruction lineage of one deed**: every occurrence that refused, in passage
/// order, each saying whether it originated the refusal or carried it and from which predecessor.
/// Empty when nothing refused. Equal across every legal schedule of the same diagram, because every
/// kernel reads only its declared lineage — that equality is the falsifier.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ObstructionLineage {
    pub refusals: Vec<OccurrenceRefusal>,
}

impl ObstructionLineage {
    pub fn is_empty(&self) -> bool {
        self.refusals.is_empty()
    }
    /// The occurrences where a refusal originated.
    pub fn origins(&self) -> impl Iterator<Item = &OccurrenceRefusal> {
        self.refusals.iter().filter(|r| r.origin)
    }
    /// Whether `index` stands: it neither originated nor carried a refusal.
    pub fn stands(&self, index: usize) -> bool {
        !self.refusals.iter().any(|r| r.index == index)
    }
    /// The union of every flag raised anywhere in the deed — the one scalar face, offered beside
    /// the lineage and never in place of it.
    pub fn joined_flags(&self) -> u32 {
        self.refusals.iter().fold(0, |acc, r| acc | r.flags)
    }
}

/// What one launch of a passage returned: the census of every occurrence, the complete obstruction
/// lineage read off it, and how the deed crossed. The terminal face is read separately, by the
/// receiver, from the section it names — and only with this reading in hand.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageReading {
    pub slots: Vec<SlotReading>,
    pub obstruction: ObstructionLineage,
    pub census_before: TransferCensus,
    pub census_after: TransferCensus,
}

impl PassageReading {
    /// The complete obstruction lineage of this deed.
    pub fn obstruction(&self) -> &ObstructionLineage {
        &self.obstruction
    }
}

impl<'chart> ResidentPassage<'chart> {
    /// The graph as the driver holds it, beside what the builder intended: the nodes and edges the
    /// apparatus actually bound.
    pub fn graph_census(&self) -> &GraphCensus {
        &self.graph_census
    }
    pub fn intended(&self) -> (usize, usize) {
        (self.intended_nodes, self.intended_edges)
    }
    pub fn occurrences(&self) -> usize {
        self.occurrences
    }
    pub fn schedule(&self) -> Schedule {
        self.schedule
    }
    /// The declared lineage every kernel inspects, as bound.
    pub fn declared_lineage(&self, index: usize) -> &[usize] {
        &self.declared[index]
    }
    /// The census array's whole range and its octets — receipt egress when read.
    pub fn census_octets(&self) -> u64 {
        (SLOT_WORDS * self.occurrences.max(1) * 4) as u64
    }
    /// The lineage array's octets, resident for the passage's life.
    pub fn lineage_octets(&self) -> u64 {
        (self.lineage_words.max(1) * 4) as u64
    }

    /// **The deed**: one graph launch, one synchronize, one census read. Nothing else crosses.
    pub fn launch(&self) -> Result<PassageReading, ResidentRefusal> {
        let census_before = self.surface.census();
        self.surface.context.make_current()?;
        self.exec.launch(&self.origin)?;
        self.surface.census.borrow_mut().deed_launches += 1;
        self.origin.synchronize()?;
        self.surface.census.borrow_mut().synchronizations += 1;
        self.read_census(census_before)
    }

    /// **Launch this passage onto a caller's stream and return immediately.**
    ///
    /// The deed is the same deed; what moves is where the terminal synchronization sits. A caller
    /// conducting many passages in succession orders them on one stream — the card carries the
    /// standing from one graph into the next without the apparatus waiting between them — and
    /// synchronizes once at the end, then reads every census with [`ResidentPassage::census`].
    ///
    /// The census array is zeroed by a memset node **inside** the graph, so a launch cannot read a
    /// previous launch's words, and the ordering of the zeroing against the kernels is the
    /// graph's own. Nothing here waits, and no census is readable until the caller has
    /// synchronized: reading before that returns the words of a deed that has not finished, which
    /// is why [`ResidentPassage::census`] is a separate call and not folded into this one.
    pub fn launch_on(&self, stream: &Stream) -> Result<TransferCensus, ResidentRefusal> {
        let census_before = self.surface.census();
        self.surface.context.make_current()?;
        self.exec.launch(stream)?;
        self.surface.census.borrow_mut().deed_launches += 1;
        Ok(census_before)
    }

    /// **Read this passage's census after the caller has synchronized.** The same reading
    /// [`ResidentPassage::launch`] returns, from the same words.
    pub fn census(&self, census_before: TransferCensus) -> Result<PassageReading, ResidentRefusal> {
        self.surface.context.make_current()?;
        self.read_census(census_before)
    }

    fn read_census(
        &self,
        census_before: TransferCensus,
    ) -> Result<PassageReading, ResidentRefusal> {
        let words_count = SLOT_WORDS * self.occurrences.max(1);
        let mut words = vec![0u32; words_count];
        self.census_buffer.copy_to_slice(&mut words)?;
        self.surface.census.borrow_mut().egress_receipt_octets += (words_count * 4) as u64;
        let slots: Vec<SlotReading> = (0..self.occurrences)
            .map(|i| SlotReading::of(&words[i * SLOT_WORDS..(i + 1) * SLOT_WORDS]))
            .collect();
        let refusals = slots
            .iter()
            .enumerate()
            .filter(|(_, slot)| slot.refused != 0)
            .map(|(index, slot)| OccurrenceRefusal {
                index,
                flags: slot.refused,
                origin: slot.originates_refusal(),
                upstream_flags: slot.upstream_flags,
                upstream_first: slot.upstream_first,
                upstream_count: slot.upstream_count,
            })
            .collect();
        Ok(PassageReading {
            slots,
            obstruction: ObstructionLineage { refusals },
            census_before,
            census_after: self.surface.census(),
        })
    }
}

impl Drop for ResidentPassage<'_> {
    fn drop(&mut self) {
        let _ = self.surface.context.make_current();
        self.surface
            .census
            .borrow_mut()
            .resident_shrank(self.census_octets() + self.lineage_octets());
    }
}

// ---------------------------------------------------------------------------------------------
// the source-scan gate: the production cone cannot reach the quarantined interpreter
// ---------------------------------------------------------------------------------------------

/// **The structural half of the first falsifier**: the production dependency cone cannot reach
/// the quarantined serial-reference realization or its host semantic dispatch. The behavioural
/// half is the census: between a graph launch and its terminal synchronize the surface issues no
/// launch, which a renamed loop cannot pass.
pub fn production_cone_reaches_the_reference(
    sources: &[(&str, &str)],
) -> Vec<(String, &'static str)> {
    const FORBIDDEN: [&str; 8] = [
        "ported_reference",
        "PortedOperationKind",
        "PortedCarrier",
        "PortedProgram",
        "ported_reference::realize",
        "fn enact(",
        "impl EnactsInOrder",
        "cuCtxSynchronize",
    ];
    let mut reached = Vec::new();
    for (name, text) in sources {
        for token in FORBIDDEN {
            if text.contains(token) {
                reached.push(((*name).to_owned(), token));
            }
        }
    }
    reached
}

#[cfg(test)]
#[path = "resident_section/tests_core.rs"]
mod tests_core;
#[cfg(test)]
#[path = "resident_section/tests_transport.rs"]
mod tests_transport;
