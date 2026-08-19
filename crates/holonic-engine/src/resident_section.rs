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
//! # One apparatus occurrence, through `soma/mount`
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
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::cuda_aperture::DerivedLaunch;
use crate::embedding_fiber::{MountedReadout, ResidentReadout};
use crate::exact_value::ExactInterval;
use crate::exact_work::ExactWork;
use crate::hardware_cover::{DeviceDeclaration, HardwareCover, ModeIdentity};
use mount::{BorrowedContext, Device, DeviceAttribute, DeviceBuffer, Dim3, Event, GraphCensus, GraphExec, MemoryInfo, Module, Stream};

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

/// The kernel symbols the module must carry. Loaded at [`ResidentSurface::on`]; a missing symbol
/// refuses there and never at a launch.
pub const KERNELS: [&str; 25] = [
    "section_from_bfloat16",
    "section_carry",
    "section_withdraw_rows",
    "section_permute_columns",
    "section_contract",
    "section_rms_rebase",
    "section_chronology",
    "section_contact",
    "section_gelu_tanh",
    "section_hadamard",
    "section_re_entry",
    "section_scale",
    "section_withdraw_columns",
    "section_collapse_control",
    "section_census",
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
    Driver { operation: String, code: i32, name: String, message: String },
    /// The mounted device (through `mount`) and the readout's device do not name one card.
    #[error("the readout mounted {readout:?} and the apparatus census names {mounted:?}")]
    DeviceDisagrees { readout: String, mounted: String },
    /// The measured or a-priori octaves plus the operation's own growth would leave the exact
    /// carrier. Decided before the launch; **nothing is truncated**.
    #[error("{operation}: the exact carrier admits {admitted} octaves and this material needs {needed}")]
    CarrierRange { operation: &'static str, needed: u32, admitted: u32 },
    /// The card raised the carrier flag during the deed at the named occurrence.
    #[error("{operation}: a coordinate left the exact carrier on the card")]
    CarrierLeft { operation: String },
    #[error("{operation}: malformed material — a non-finite codeword or a non-positive denominator")]
    Malformed { operation: String },
    /// A lawful step produced `lo > hi`. A soundness fault in the law itself, reported by name.
    #[error("{operation}: an enclosure inverted on the card")]
    Inverted { operation: String },
    /// A predecessor refused, so this occurrence wrote nothing; the first refusal names itself.
    #[error("{operation}: a predecessor refused upstream")]
    Upstream { operation: String },
    /// The a-priori octave bound this occurrence was admitted under was refuted by its own census.
    #[error("{operation}: admitted at {admitted} octaves and measured {measured}; the a-priori law is refuted here")]
    BoundRefuted { operation: String, admitted: u32, measured: u32 },
    #[error("{operation}: sections of width {left} and {right} do not meet")]
    WidthDisagrees { operation: &'static str, left: usize, right: usize },
    #[error("{operation}: sections of {left} and {right} rows do not meet")]
    RowsDisagree { operation: &'static str, left: usize, right: usize },
    #[error("{operation}: {rows} rows of {width} exceeds the resident chart's declared grid aperture")]
    GridAperture { operation: &'static str, rows: usize, width: usize },
    #[error("{operation}: {words} words is not {rows} rows of {width}")]
    Ragged { operation: &'static str, words: usize, rows: usize, width: usize },
    #[error("{operation}: sections at grains {left} and {right} do not meet; a grain is declared once per deed")]
    GrainsDisagree { operation: &'static str, left: u32, right: u32 },
    #[error("{operation}: {what}")]
    Declaration { operation: &'static str, what: String },
    /// The mode the caller declared for the launch is not the mode this surface stands in.
    #[error("the declared mode is not the surface's: expected {expected:?}, the surface is {actual:?}")]
    ModeMismatch { expected: Box<ModeIdentity>, actual: Box<ModeIdentity> },
    /// The deed's predicted resident octets exceed what the mounted device has free.
    #[error("the deed requires {required} resident octets and the device has {free} free")]
    MemoryAperture { required: u64, free: u64 },
}

impl From<mount::CudaError> for ResidentRefusal {
    fn from(error: mount::CudaError) -> Self {
        Self::Driver { operation: error.context.to_owned(), code: error.code, name: error.name, message: error.message }
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
    pub const ONE: Self = Self { significand: 1, exponent: 0 };

    pub fn octaves(&self) -> u32 {
        64 - self.significand.unsigned_abs().leading_zeros()
    }

    /// The exact dyadic of a `binary64` word, through the workspace's declared float mouth.
    pub fn of_binary64_bits(bits: u64) -> Result<Self, ResidentRefusal> {
        let datum = crate::exact_value::ieee754::decode_binary64_bits(bits).map_err(|error| ResidentRefusal::Declaration {
            operation: "dyadic",
            what: format!("{error:?}"),
        })?;
        let magnitude = i64::try_from(&datum.significand).map_err(|_| ResidentRefusal::Declaration {
            operation: "dyadic",
            what: "a binary64 significand exceeds the signed word".to_owned(),
        })?;
        Ok(Self { significand: if datum.negative { -magnitude } else { magnitude }, exponent: datum.ulp_exponent })
    }

    /// The exact dyadic of a `bfloat16` word.
    pub fn of_bfloat16_bits(word: u16) -> Result<Self, ResidentRefusal> {
        let datum = crate::exact_value::ieee754::decode_bfloat16_bits(word).map_err(|error| ResidentRefusal::Declaration {
            operation: "dyadic",
            what: format!("{error:?}"),
        })?;
        let magnitude = i64::try_from(&datum.significand).map_err(|_| ResidentRefusal::Declaration {
            operation: "dyadic",
            what: "a bfloat16 significand exceeds the signed word".to_owned(),
        })?;
        Ok(Self { significand: if datum.negative { -magnitude } else { magnitude }, exponent: datum.ulp_exponent })
    }

    /// The exact rational this dyadic is.
    pub fn value(&self) -> Rat {
        let significand = Rat::from_integer(BigInt::from(self.significand));
        if self.exponent >= 0 {
            significand * Rat::from_integer(BigInt::from(BigUint::from(1u8) << self.exponent as usize))
        } else {
            significand / Rat::from_integer(BigInt::from(BigUint::from(1u8) << (-self.exponent) as usize))
        }
    }
}

/// The exact rational a section word denotes at a grain: `word · 2^-F`.
pub fn word_value(word: i64, grain: ResidentGrain) -> Rat {
    Rat::new(BigInt::from(word), BigInt::from(BigUint::from(1u8) << grain.0 as usize))
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
        64 - self.lo.unsigned_abs().max(self.hi.unsigned_abs()).leading_zeros()
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
        Ok(Self { lo: i64::try_from(&floor).map_err(|_| refuse())?, hi: i64::try_from(&ceil).map_err(|_| refuse())?, grain })
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
#[derive(Clone, Debug, Default, PartialEq, Eq)]
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
    partials: RefCell<Vec<DeviceBuffer<i64>>>,
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
    pub fn resident_octets(&self) -> u64 {
        self.octets
    }
    fn count(&self) -> usize {
        self.rows * self.width
    }
    /// The address ranges this section occupies — its footprint as a realization coordinate.
    pub fn ranges(&self) -> [(u64, u64); 2] {
        let octets = (self.count() * std::mem::size_of::<i64>()) as u64;
        [(self.lo.device_ptr(), self.lo.device_ptr() + octets), (self.hi.device_ptr(), self.hi.device_ptr() + octets)]
    }
}

impl Drop for ResidentSection<'_> {
    fn drop(&mut self) {
        let _ = self.surface.context.make_current();
        self.surface.census.borrow_mut().resident_shrank(self.octets);
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
        [&self.cos_lo, &self.cos_hi, &self.sin_lo, &self.sin_hi].map(|b| (b.device_ptr(), b.device_ptr() + octets))
    }
}

impl Drop for BandElements<'_> {
    fn drop(&mut self) {
        let _ = self.surface.context.make_current();
        self.surface.census.borrow_mut().resident_shrank(self.octets);
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
        (self.buffer.device_ptr(), self.buffer.device_ptr() + (self.rows * 4) as u64)
    }
}

impl Drop for Positions<'_> {
    fn drop(&mut self) {
        let _ = self.surface.context.make_current();
        self.surface.census.borrow_mut().resident_shrank(self.octets);
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
        (self.buffer.device_ptr(), self.buffer.device_ptr() + self.octets)
    }
}

impl Drop for StagedWords<'_> {
    fn drop(&mut self) {
        let _ = self.surface.context.make_current();
        self.surface.census.borrow_mut().resident_shrank(self.octets);
    }
}

fn ceil_log2(n: usize) -> u32 {
    if n <= 1 {
        0
    } else {
        (n - 1).ilog2() + 1
    }
}

/// The parameter words of one launch, each in its own 64-bit slot so `cuLaunchKernel` reads every
/// argument from a stable address of its own size (little-endian: a 32-bit argument is the low
/// half of its slot).
struct Params {
    words: Vec<u64>,
}

impl Params {
    fn new() -> Self {
        Self { words: Vec::with_capacity(20) }
    }
    fn ptr(&mut self, pointer: u64) -> &mut Self {
        self.words.push(pointer);
        self
    }
    fn u32(&mut self, value: u32) -> &mut Self {
        self.words.push(u64::from(value));
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
        self.words.iter_mut().map(|word| (word as *mut u64).cast::<c_void>()).collect()
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
            upstream_first: if words[9] == 0 { None } else { Some(words[9] as usize - 1) },
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
            return Some(ResidentRefusal::BoundRefuted { operation: name, admitted, measured: self.max_octave });
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

impl<'chart> ResidentSurface<'chart> {
    /// **Mount the apparatus occurrence** on the readout's context. Refuses when no device answers,
    /// when the census names a device the readout did not mount, or when a kernel symbol is
    /// missing from the module.
    pub fn on(readout: &'chart ResidentReadout) -> Result<Self, ResidentRefusal> {
        mount::cuda::init()?;
        if Device::count()? == 0 {
            return Err(ResidentRefusal::NoResidentChart);
        }
        let device = Device::get(0)?;
        if device.name != readout.device_name() {
            return Err(ResidentRefusal::DeviceDisagrees { readout: readout.device_name().to_owned(), mounted: device.name.clone() });
        }
        let context = BorrowedContext::adopt(readout.raw_context())?;
        context.make_current()?;
        let module = Module::load_ptx(PTX)?;
        let attribute = |selector: i32| -> Result<u32, ResidentRefusal> {
            let value = device.attribute(DeviceAttribute::from_raw(selector))?;
            Ok(u32::try_from(value).unwrap_or(0))
        };
        let declaration = DeviceDeclaration {
            ordinal: 0,
            name: device.name.clone(),
            capability_major: attribute(ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR)?,
            capability_minor: attribute(ATTRIBUTE_COMPUTE_CAPABILITY_MINOR)?,
            multiprocessors: attribute(ATTRIBUTE_MULTIPROCESSOR_COUNT)?,
            warp_size: attribute(ATTRIBUTE_WARP_SIZE)?,
            max_threads_per_block: attribute(ATTRIBUTE_MAX_THREADS_PER_BLOCK)?,
            max_threads_per_multiprocessor: attribute(ATTRIBUTE_MAX_THREADS_PER_MULTIPROCESSOR)?,
            max_grid_x: attribute(ATTRIBUTE_MAX_GRID_DIM_X)?,
            max_sectiond_bytes: attribute(ATTRIBUTE_MAX_SHARED_MEMORY_PER_BLOCK)?,
            async_engines: attribute(ATTRIBUTE_ASYNC_ENGINE_COUNT)?,
            concurrent_kernels: attribute(ATTRIBUTE_CONCURRENT_KERNELS)? != 0,
            unified_addressing: attribute(ATTRIBUTE_UNIFIED_ADDRESSING)? != 0,
        };
        let mut kernel_block = declaration.max_threads_per_block.max(1);
        for symbol in KERNELS {
            let function = module.function(symbol)?;
            kernel_block = kernel_block.min(function.max_threads_per_block()?);
        }
        let launch = DerivedLaunch::from_admissions(
            declaration.max_threads_per_block.max(1),
            kernel_block,
            declaration.max_grid_x.max(1),
            declaration.warp_size.max(1),
        );
        let reduction_block = {
            let admitted = launch.block_x.max(1);
            let mut block = 1u32;
            while block * 2 <= admitted {
                block *= 2;
            }
            block.max(launch.warp.max(1))
        };
        let cover = HardwareCover::over(Some(declaration.clone()));
        let sm_limits = MultiprocessorLimits {
            max_blocks: attribute(ATTRIBUTE_MAX_BLOCKS_PER_MULTIPROCESSOR)?,
            max_threads: declaration.max_threads_per_multiprocessor,
            max_registers: attribute(ATTRIBUTE_MAX_REGISTERS_PER_MULTIPROCESSOR)?,
            max_shared_octets: attribute(ATTRIBUTE_MAX_SHARED_MEMORY_PER_MULTIPROCESSOR)?,
            warp: declaration.warp_size.max(1),
            multiprocessors: declaration.multiprocessors.max(1),
            register_grain: REGISTER_GRAIN_PER_WARP,
        };
        let allocation_grain = context.allocation_grain_bytes()? as u64;
        let memory_at_mount = context.memory_info()?;
        let ptx_sha256 = Sha256::digest(PTX).iter().map(|byte| format!("{byte:02x}")).collect();
        Ok(Self {
            readout,
            context,
            device,
            module,
            ptx_sha256,
            max_shared_octets: declaration.max_sectiond_bytes,
            declaration,
            cover,
            launch,
            reduction_block,
            memory_at_mount,
            allocation_grain,
            sm_limits,
            partials: RefCell::new(Vec::new()),
            census: RefCell::new(TransferCensus::default()),
        })
    }

    pub fn device_name(&self) -> &str {
        &self.device.name
    }
    pub fn readout(&self) -> &'chart ResidentReadout {
        self.readout
    }
    /// The device's own declaration, as the surface read it. A reading; the cover is built from it.
    pub fn declaration(&self) -> &DeviceDeclaration {
        &self.declaration
    }
    /// **The cover this surface stands under.** Built from the mounted device's own attributes;
    /// a passage reads it here and cannot be handed another.
    pub fn cover(&self) -> &HardwareCover {
        &self.cover
    }
    /// The PTX's content digest — the kernel identity as content, not as a name.
    pub fn ptx_sha256(&self) -> &str {
        &self.ptx_sha256
    }
    /// The mode this surface stands in: source law, boundary, kernel name and content, device,
    /// arithmetic tier and apparatus chart. Two surfaces with one kernel name and different PTX
    /// are two modes.
    pub fn mode(&self) -> ModeIdentity {
        ModeIdentity::of(&self.cover, "holonic_engine::resident_section", "exact-integer-interval-v2", "exact_resident_section")
            .with_kernel_content(self.ptx_sha256.clone())
    }
    /// The memory the device reported at mount, and now.
    pub fn memory_at_mount(&self) -> MemoryInfo {
        self.memory_at_mount
    }
    pub fn memory(&self) -> Result<MemoryInfo, ResidentRefusal> {
        Ok(self.context.memory_info()?)
    }
    /// The measured allocation grain, in octets. A deed's apparatus prediction rounds every
    /// allocation up to it; changing the grain changes the requirement lawfully and visibly.
    pub fn allocation_grain(&self) -> u64 {
        self.allocation_grain
    }
    /// The census so far. A reading, never a governor.
    pub fn census(&self) -> TransferCensus {
        self.census.borrow().clone()
    }
    /// The exact carrier's octave aperture: what an accumulation may occupy before the hand.
    pub const fn carrier_octaves() -> u32 {
        WIDE_OCTAVES - 1
    }
    /// The launch geometry derived from the device and the kernels: the block, the grid ceiling,
    /// the warp. Read by the passage to place cells on the cover's device chart.
    pub fn derived_launch(&self) -> (u32, u32, u32) {
        (self.launch.block_x, self.launch.max_grid_x, self.launch.warp)
    }

    // -----------------------------------------------------------------------------------------
    // allocation, staging, mounting — the material's arrival, counted
    // -----------------------------------------------------------------------------------------

    fn alloc<T: Copy>(&self, count: usize) -> Result<DeviceBuffer<T>, ResidentRefusal> {
        self.context.make_current()?;
        let buffer = DeviceBuffer::<T>::alloc(count.max(1))?;
        let mut census = self.census.borrow_mut();
        census.allocations += 1;
        census.resident_grew((count.max(1) * std::mem::size_of::<T>()) as u64);
        Ok(buffer)
    }

    /// A fresh section, allocated and unwritten. Allocation is counted; nothing launches.
    pub fn fresh_section(&'chart self, rows: usize, width: usize, grain: ResidentGrain) -> Result<ResidentSection<'chart>, ResidentRefusal> {
        let count = rows * width;
        let lo = self.alloc::<i64>(count)?;
        let hi = self.alloc::<i64>(count)?;
        Ok(ResidentSection { surface: self, lo, hi, rows, width, grain, octets: 2 * (count.max(1) * 8) as u64 })
    }

    /// Stage entering codewords: allocate once and upload (ingress). Refillable.
    pub fn stage_words(&'chart self, words: &[u16], rows: usize, width: usize) -> Result<StagedWords<'chart>, ResidentRefusal> {
        if words.len() != rows * width {
            return Err(ResidentRefusal::Ragged { operation: "stage", words: words.len(), rows, width });
        }
        let buffer = self.alloc::<u16>(words.len())?;
        let staged = StagedWords { surface: self, buffer, rows, width, octets: (words.len().max(1) * 2) as u64 };
        self.refill(&staged, words)?;
        Ok(staged)
    }

    /// Upload new entering codewords into a staged buffer of the same extent — a later deed's
    /// material crossing once.
    pub fn refill(&self, staged: &StagedWords<'chart>, words: &[u16]) -> Result<(), ResidentRefusal> {
        if words.len() != staged.rows * staged.width {
            return Err(ResidentRefusal::Ragged { operation: "refill", words: words.len(), rows: staged.rows, width: staged.width });
        }
        self.context.make_current()?;
        staged.buffer.copy_from_slice(words)?;
        self.census.borrow_mut().ingress_octets += (words.len() * 2) as u64;
        Ok(())
    }

    /// Lay the site's band group elements down once. `elements[b] = ((cos_lo, cos_hi), (sin_lo,
    /// sin_hi))` at `2^-grain`, founded on the serial chart from the exact algebraic angle.
    pub fn mount_bands(&'chart self, elements: &[((i64, i64), (i64, i64))], grain: u32) -> Result<BandElements<'chart>, ResidentRefusal> {
        let n = elements.len();
        let cos_lo = self.alloc::<i64>(n)?;
        let cos_hi = self.alloc::<i64>(n)?;
        let sin_lo = self.alloc::<i64>(n)?;
        let sin_hi = self.alloc::<i64>(n)?;
        let mut words = vec![0i64; n];
        for (buffer, pick) in [
            (&cos_lo, 0usize),
            (&cos_hi, 1),
            (&sin_lo, 2),
            (&sin_hi, 3),
        ] {
            for (slot, ((cl, ch), (sl, sh))) in words.iter_mut().zip(elements) {
                *slot = [*cl, *ch, *sl, *sh][pick];
            }
            buffer.copy_from_slice(&words)?;
        }
        self.census.borrow_mut().ingress_octets += (4 * n * 8) as u64;
        Ok(BandElements { surface: self, cos_lo, cos_hi, sin_lo, sin_hi, bands: n, grain, octets: (4 * n.max(1) * 8) as u64 })
    }

    /// The integer positions of a section's rows, laid down once.
    pub fn mount_positions(&'chart self, positions: &[u32]) -> Result<Positions<'chart>, ResidentRefusal> {
        let buffer = self.alloc::<u32>(positions.len())?;
        buffer.copy_from_slice(positions)?;
        self.census.borrow_mut().ingress_octets += (positions.len() * 4) as u64;
        Ok(Positions { surface: self, buffer, rows: positions.len(), octets: (positions.len().max(1) * 4) as u64 })
    }

    /// **The terminal receiver's copy.** The one place a section crosses to the serial chart, and it
    /// is counted as such. Returns `(lo, hi)` per coordinate at the section's grain, row-major.
    pub fn read_out(&self, section: &ResidentSection<'chart>) -> Result<Vec<(i64, i64)>, ResidentRefusal> {
        self.context.make_current()?;
        let count = section.count();
        let mut lo = vec![0i64; count];
        let mut hi = vec![0i64; count];
        section.lo.copy_to_slice(&mut lo)?;
        section.hi.copy_to_slice(&mut hi)?;
        {
            let mut census = self.census.borrow_mut();
            census.egress_section_octets += (2 * count * 8) as u64;
            census.section_read_outs += 1;
        }
        Ok(lo.into_iter().zip(hi).collect())
    }

    fn admit_octaves(operation: &'static str, needed: u32) -> Result<(), ResidentRefusal> {
        let admitted = Self::carrier_octaves();
        if needed > admitted {
            return Err(ResidentRefusal::CarrierRange { operation, needed, admitted });
        }
        Ok(())
    }

    // -----------------------------------------------------------------------------------------
    // the laws' shapes and prices — pure, before any launch
    // -----------------------------------------------------------------------------------------

    /// **The mouth**: entering codewords scaled by an exact dyadic and placed at the grain.
    pub fn shape_enter(&self, rows: usize, width: usize, scale: Dyadic, grain: ResidentGrain) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "enter";
        // A BF16 significand is eight octaves; the product with the scale must sit in the word
        // after the grain shift.
        let needed = 8 + scale.octaves() + grain.0 + 8;
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(count);
        work.entries_written = BigUint::from(2 * count);
        work.peak_bits = BigUint::from(u64::from(grain.0) + 16);
        work.cumulative_bits = BigUint::from(2 * count * (u64::from(grain.0) + 16));
        work.resident(2 * count);
        work.stepped();
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    fn flat_shape(&self, operation: &'static str, rows: usize, width: usize, needed: u32, predicted: ExactWork, couplings: Vec<CouplingPlan>) -> Result<LawShape, ResidentRefusal> {
        let count = rows * width;
        let count32 = u32::try_from(count).map_err(|_| ResidentRefusal::GridAperture { operation, rows, width })?;
        self.launch.grid_for(count32.max(1)).map_err(|_| ResidentRefusal::GridAperture { operation, rows, width })?;
        Ok(LawShape { operation, rows, width, needed, predicted, couplings, launches: 2, shared_octets: 0, block: self.launch.block_x })
    }

    /// The contraction through a mounted map: `out = section · mapᵀ`.
    pub fn shape_contract(&self, rows: usize, inner: usize, input_octaves: u32, map: &MountedReadout<'chart>) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "contract";
        if inner != map.dim() {
            return Err(ResidentRefusal::WidthDisagrees { operation: OPERATION, left: inner, right: map.dim() });
        }
        let needed = input_octaves + map.entry_octaves() + ceil_log2(inner) + 1;
        Self::admit_octaves(OPERATION, needed)?;
        let out_width = map.rows();
        let mut work = ExactWork::predicted_product(rows, inner, out_width, u64::from(input_octaves.max(map.entry_octaves())));
        work.entries_written = BigUint::from(2 * (rows * out_width) as u64);
        work.resident(2 * (rows * out_width) as u64);
        let peak = u64::from(input_octaves) + u64::from(map.entry_octaves()) + u64::from(ceil_log2(inner)) + 1;
        work.peak_bits = BigUint::from(peak);
        work.cumulative_bits = BigUint::from(2 * (rows * out_width) as u64 * peak);
        self.flat_shape(OPERATION, rows, out_width, needed, work, Vec::new())
    }

    /// The RMS rebase over runs of `group`: `x · (mean(x²) + eps)^{-1/2} · g`. The quadratic
    /// capacity is a named barrier realized as a resident block reduction.
    pub fn shape_rms_rebase(&self, rows: usize, width: usize, group: usize, input_octaves: u32, gain: Option<&MountedReadout<'chart>>) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "rms-rebase";
        if group == 0 || width % group != 0 {
            return Err(ResidentRefusal::Declaration { operation: OPERATION, what: format!("a group of {group} does not tile a width of {width}") });
        }
        if let Some(gain) = gain {
            if gain.rows() * gain.dim() != group {
                return Err(ResidentRefusal::WidthDisagrees { operation: OPERATION, left: group, right: gain.rows() * gain.dim() });
            }
        }
        let gain_octaves = gain.map(MountedReadout::entry_octaves).unwrap_or(0);
        let oct = input_octaves;
        // The squares are summed at 2^-2(F − s) with s the least shift that fits the wide carrier;
        // the kernel derives s from the group's own census, so here s is bounded from the a-priori
        // octaves and the product x·g must fit the wide carrier.
        let squares = 2 * oct + ceil_log2(group) + 1;
        let needed = squares.min(Self::carrier_octaves()).max(oct + gain_octaves + 1);
        Self::admit_octaves(OPERATION, needed)?;
        let block = self.reduction_block.min(group.next_power_of_two() as u32).max(self.launch.warp);
        let shared = 2 * block * 16 + block * 4;
        if shared > self.max_shared_octets {
            return Err(ResidentRefusal::Declaration { operation: OPERATION, what: format!("a block of {block} needs {shared} shared octets; the device admits {}", self.max_shared_octets) });
        }
        let blocks = rows * (width / group);
        if blocks > self.launch.max_grid_x as usize {
            return Err(ResidentRefusal::GridAperture { operation: OPERATION, rows, width });
        }
        let count = (rows * width) as u64;
        let groups = blocks as u64;
        let mut work = ExactWork::nothing();
        // the octave census, the squares, the reductions, the radical, the rebase, the gain
        work.multiplied(2 * count + 4 * count + count);
        work.added(2 * count + 2 * count + count);
        work.divided(groups * (64 + 2));
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        let peak = 2 * u64::from(oct) + u64::from(ceil_log2(group)) + 1;
        work.peak_bits = BigUint::from(peak.min(u64::from(Self::carrier_octaves())).max(u64::from(oct + gain_octaves + 10)));
        work.cumulative_bits = BigUint::from(2 * count * (u64::from(oct) + u64::from(gain_octaves)));
        work.dependency_span = BigUint::from(2 * u64::from(ceil_log2(group)) + 3);
        let mut reduction = ExactWork::nothing();
        reduction.added(2 * count);
        reduction.divided(groups * 66);
        reduction.dependency_span = BigUint::from(u64::from(ceil_log2(group)) + 2);
        let couplings = vec![CouplingPlan {
            coupling: "the quadratic capacity over the group, and the group's own octave census",
            kernel: "section_rms_rebase",
            extent: group as u64,
            block,
            predicted: reduction,
        }];
        Ok(LawShape { operation: OPERATION, rows, width, needed, predicted: work, couplings, launches: 2, shared_octets: shared, block })
    }

    /// The chronology: every head's pair `(x[b], x[b + D/2])` turned by the band element raised to
    /// the row's integer position.
    pub fn shape_chronology(&self, rows: usize, width: usize, heads: usize, head_width: usize, input_octaves: u32, bands: &BandElements<'chart>, positions: &Positions<'chart>, max_position: u32) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "chronology";
        if width != heads * head_width {
            return Err(ResidentRefusal::WidthDisagrees { operation: OPERATION, left: width, right: heads * head_width });
        }
        if bands.bands != head_width / 2 {
            return Err(ResidentRefusal::Declaration { operation: OPERATION, what: format!("{} band elements for a head width of {head_width}", bands.bands) });
        }
        if positions.rows != rows {
            return Err(ResidentRefusal::RowsDisagree { operation: OPERATION, left: rows, right: positions.rows });
        }
        let needed = (input_octaves + bands.grain + 1).max(2 * bands.grain + 2);
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * heads * (head_width / 2)) as u64;
        let powering = u64::from(ceil_log2(max_position as usize + 1)) * 2 * 16;
        let mut work = ExactWork::nothing();
        work.multiplied(count * (powering + 16));
        work.added(count * (powering / 2 + 6));
        work.entries_written = BigUint::from(2 * (rows * width) as u64);
        work.resident(2 * (rows * width) as u64);
        work.peak_bits = BigUint::from(u64::from(input_octaves + bands.grain + 1));
        work.cumulative_bits = BigUint::from(2 * (rows * width) as u64 * u64::from(input_octaves + 1));
        work.dependency_span = BigUint::from(u64::from(ceil_log2(max_position as usize + 1)) + 1);
        // The launch is flat over (row, head, band).
        let threads = rows * heads * (head_width / 2);
        let count32 = u32::try_from(threads).map_err(|_| ResidentRefusal::GridAperture { operation: OPERATION, rows, width })?;
        self.launch.grid_for(count32.max(1)).map_err(|_| ResidentRefusal::GridAperture { operation: OPERATION, rows, width })?;
        Ok(LawShape { operation: OPERATION, rows, width, needed, predicted: work, couplings: Vec::new(), launches: 2, shared_octets: 0, block: self.launch.block_x })
    }

    /// The contact and carried construction over `(q, k, v)`, sliding causal window.
    #[allow(clippy::too_many_arguments)]
    pub fn shape_contact(&self, rows: usize, q_width: usize, k_width: usize, v_width: usize, heads: usize, kv_heads: usize, head_width: usize, window: usize, terms: SeriesAperture, grain: ResidentGrain, q_octaves: u32, k_octaves: u32, v_octaves: u32) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "contact";
        if q_width != heads * head_width {
            return Err(ResidentRefusal::WidthDisagrees { operation: OPERATION, left: q_width, right: heads * head_width });
        }
        if k_width != kv_heads * head_width || v_width != kv_heads * head_width {
            return Err(ResidentRefusal::WidthDisagrees { operation: OPERATION, left: k_width.max(v_width), right: kv_heads * head_width });
        }
        if kv_heads == 0 || heads % kv_heads != 0 {
            return Err(ResidentRefusal::Declaration { operation: OPERATION, what: format!("{heads} heads over {kv_heads} families") });
        }
        let f = grain.0;
        let reach = rows.min(window.max(1));
        // The bracket sum is SELF-SCALED on the card from the block's own widest octave, so its
        // term is bounded by the carrier whatever the words; the carried construction and the
        // series are not, and decide the admission.
        let needed = (2 * q_octaves.max(k_octaves) + ceil_log2(head_width) + 1)
            .min(Self::carrier_octaves())
            .max(f + 1 + v_octaves + ceil_log2(reach) + 1)
            .max(2 * f + 4);
        Self::admit_octaves(OPERATION, needed)?;
        let block = self.reduction_block.min(head_width.max(reach).next_power_of_two() as u32).max(self.launch.warp);
        let shared = (4 * reach * 16) as u32;
        if shared > self.max_shared_octets {
            return Err(ResidentRefusal::Declaration { operation: OPERATION, what: format!("a reach of {reach} needs {shared} shared octets; the device admits {}", self.max_shared_octets) });
        }
        if rows * heads > self.launch.max_grid_x as usize {
            return Err(ResidentRefusal::GridAperture { operation: OPERATION, rows, width: q_width });
        }
        let reach_sum: u64 = (0..rows).map(|t| (t + 1).min(window.max(1)) as u64).sum();
        let brackets = reach_sum * heads as u64 * head_width as u64;
        let series = reach_sum * heads as u64 * 2 * (u64::from(terms.0) + 1);
        let carried = reach_sum * heads as u64 * head_width as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(4 * brackets + 2 * series + 4 * carried);
        work.added(2 * brackets + 2 * series + 2 * carried);
        work.divided(2 * series + 2 * (rows * heads * head_width) as u64);
        work.entries_written = BigUint::from(2 * (rows * heads * head_width) as u64);
        work.resident(2 * (rows * heads * head_width) as u64 + 4 * window.max(1) as u64);
        let peak = (2 * q_octaves.max(k_octaves) + ceil_log2(head_width) + 1).max(v_octaves + 40);
        work.peak_bits = BigUint::from(u64::from(peak));
        work.cumulative_bits = BigUint::from(2 * (rows * heads * head_width) as u64 * u64::from(v_octaves + 1));
        work.dependency_span = BigUint::from(5u64 + u64::from(terms.0));
        let coupling = |name: &'static str, extent: u64| {
            let mut reduction = ExactWork::nothing();
            reduction.added(reach_sum * heads as u64);
            reduction.dependency_span = BigUint::from(u64::from(ceil_log2(reach)) + 1);
            CouplingPlan { coupling: name, kernel: "section_contact", extent, block, predicted: reduction }
        };
        let couplings = vec![
            coupling("the null: greatest upper bracket over the reach", reach as u64),
            coupling("the partition function: sum of certified weights over the reach", reach as u64),
            coupling("the hull: least and greatest carried coordinate over the reach", reach as u64),
        ];
        Ok(LawShape { operation: OPERATION, rows, width: heads * head_width, needed, predicted: work, couplings, launches: 2, shared_octets: shared, block })
    }

    /// `½ x (1 + tanh(c1 (x + c2 x³)))` with the source's `binary64` constants as exact dyadics.
    pub fn shape_gelu_tanh(&self, rows: usize, width: usize, input_octaves: u32, grain: ResidentGrain, c1: Dyadic, c2: Dyadic, terms: SeriesAperture) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "gelu-tanh";
        let f = i64::from(grain.0);
        let oct = i64::from(input_octaves);
        // The cube and both dyadic products are SELF-SCALED on the card; the square (two words),
        // the final product with `1 + tanh`, and the series decide the admission.
        let _ = (c1, c2);
        let needed = (2 * oct).max(oct + f + 2).max(2 * f + 4);
        let needed = u32::try_from(needed.max(0)).unwrap_or(u32::MAX);
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let series = 2 * (u64::from(terms.0) + 1);
        let mut work = ExactWork::nothing();
        work.multiplied(count * (12 + 2 * series));
        work.added(count * (8 + series));
        work.divided(count * (4 + series));
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(3 * input_octaves + 53));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves));
        work.dependency_span = BigUint::from(6u64 + u64::from(terms.0));
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    /// The pointwise product of two standings.
    pub fn shape_hadamard(&self, rows: usize, width: usize, a_octaves: u32, b_octaves: u32) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "hadamard";
        // Two magnitudes below 2^a and 2^b multiply below 2^(a+b).
        let needed = a_octaves + b_octaves;
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(4 * count);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(a_octaves + b_octaves));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(a_octaves + b_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    /// The re-entry: a retained standing and a returned current, joined.
    pub fn shape_re_entry(&self, rows: usize, width: usize, a_octaves: u32, b_octaves: u32) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "re-entry";
        let needed = a_octaves.max(b_octaves) + 1;
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.added(2 * count);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(a_octaves.max(b_octaves) + 1));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(a_octaves.max(b_octaves) + 1));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    /// The product with an enclosed constant carried as its certified enclosure.
    pub fn shape_scale(&self, rows: usize, width: usize, input_octaves: u32, by: DyadicEnclosure) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "scale";
        let needed = input_octaves + by.octaves() + 1;
        Self::admit_octaves(OPERATION, needed)?;
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.multiplied(4 * count);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves + by.octaves()));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, needed, work, Vec::new())
    }

    /// The matched-sibling intervention: a declared span of columns withdrawn, out of place.
    pub fn shape_withdraw_columns(&self, rows: usize, width: usize, input_octaves: u32, from: usize, span: usize) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "withdraw-columns";
        if from + span > width {
            return Err(ResidentRefusal::WidthDisagrees { operation: OPERATION, left: from + span, right: width });
        }
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())
    }

    /// The intervention withdrawing rows `[from, from + span)`.
    pub fn shape_withdraw_rows(&self, rows: usize, width: usize, input_octaves: u32, from: usize, span: usize) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "withdraw-rows";
        if from + span > rows {
            return Err(ResidentRefusal::RowsDisagree { operation: OPERATION, left: from + span, right: rows });
        }
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())
    }

    /// The intervention permuting the column blocks of `block` by a declared permutation.
    pub fn shape_permute_columns(&self, rows: usize, width: usize, input_octaves: u32, block: usize, permutation: &[usize]) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "permute-columns";
        if block == 0 || width % block != 0 || permutation.len() != width / block {
            return Err(ResidentRefusal::WidthDisagrees { operation: OPERATION, left: permutation.len() * block, right: width });
        }
        let mut seen = vec![false; permutation.len()];
        for p in permutation {
            if *p >= permutation.len() || seen[*p] {
                return Err(ResidentRefusal::Declaration { operation: OPERATION, what: format!("{permutation:?} is not a permutation of {} blocks", permutation.len()) });
            }
            seen[*p] = true;
        }
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())
    }

    /// **A control, unsound by construction**: the enclosure collapsed to a midpoint at this site.
    pub fn shape_collapse_control(&self, rows: usize, width: usize, input_octaves: u32) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "collapse-control";
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.added(count);
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())
    }

    /// The carry of a resident standing into this passage: one read and one write per coordinate,
    /// no arithmetic, the octave bound unchanged.
    pub fn shape_carry(&self, rows: usize, width: usize, input_octaves: u32) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "carry";
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.cumulative_bits = BigUint::from(2 * count * u64::from(input_octaves.max(1)));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())
    }

    // -----------------------------------------------------------------------------------------
    // the passage: capture, launch once, read once
    // -----------------------------------------------------------------------------------------

    /// Begin binding a passage over a declared lineage: `lineage[i]` is the list of occurrences
    /// occurrence `i` reads (its predecessors in the diagram's bonds). The census array, one lane
    /// and one event per occurrence, and the **lineage array** — every occurrence's predecessor
    /// indices, sorted and deduplicated, uploaded before the capture opens — are allocated here;
    /// the capture opens with the memset that zeroes the census. Nothing launches until
    /// [`ResidentPassage::launch`].
    pub fn begin_passage(&'chart self, lineage: &[Vec<usize>]) -> Result<PassageBuilder<'chart>, ResidentRefusal> {
        self.begin_passage_scheduled(lineage, Schedule::CoPresent)
    }

    /// The same passage bound with every occurrence ALSO ordered after the one opened before it —
    /// a total order over the same kernels. A control: the co-present realization and this one
    /// must return one complete receipt, or the interchange claim is refuted physically.
    pub fn begin_passage_serialized(&'chart self, lineage: &[Vec<usize>]) -> Result<PassageBuilder<'chart>, ResidentRefusal> {
        self.begin_passage_scheduled(lineage, Schedule::Serialized)
    }

    /// Begin a passage under a declared [`Schedule`]. The schedule adds edges; it never removes
    /// the diagram's, and it never changes which slots a kernel reads.
    pub fn begin_passage_scheduled(&'chart self, lineage: &[Vec<usize>], schedule: Schedule) -> Result<PassageBuilder<'chart>, ResidentRefusal> {
        self.context.make_current()?;
        let occurrences = lineage.len();
        let mut declared: Vec<Vec<usize>> = Vec::with_capacity(occurrences);
        let mut flat: Vec<u32> = Vec::new();
        let mut offsets: Vec<(usize, usize)> = Vec::with_capacity(occurrences);
        for (index, producers) in lineage.iter().enumerate() {
            let mut sorted: Vec<usize> = producers.clone();
            sorted.sort_unstable();
            sorted.dedup();
            for producer in &sorted {
                if *producer >= index {
                    return Err(ResidentRefusal::Declaration { operation: "passage", what: format!("occurrence {index} declares predecessor {producer}, which is not earlier in the passage") });
                }
            }
            offsets.push((flat.len(), sorted.len()));
            flat.extend(sorted.iter().map(|p| *p as u32));
            declared.push(sorted);
        }
        let census_words = SLOT_WORDS * occurrences.max(1);
        let census_buffer = self.alloc::<u32>(census_words)?;
        let lineage_buffer = self.alloc::<u32>(flat.len().max(1))?;
        if !flat.is_empty() {
            lineage_buffer.copy_from_slice(&flat)?;
            self.census.borrow_mut().ingress_octets += (flat.len() * 4) as u64;
        }
        let origin = Stream::create()?;
        let mut lanes = Vec::with_capacity(occurrences);
        let mut events = Vec::with_capacity(occurrences);
        for _ in 0..occurrences {
            lanes.push(Stream::create()?);
            events.push(Event::create()?);
        }
        let memset_event = Event::create()?;
        origin.begin_capture()?;
        origin.memset_u32_async(census_buffer.device_ptr(), 0, census_words)?;
        memset_event.record(&origin)?;
        Ok(PassageBuilder {
            surface: self,
            origin,
            lanes,
            events,
            memset_event,
            census_buffer,
            lineage_buffer,
            lineage_words: flat.len(),
            declared,
            offsets,
            occurrences,
            nodes: 1,
            edges: 0,
            opened: vec![false; occurrences],
            closed: vec![false; occurrences],
            schedule,
            last_opened: None,
        })
    }

    fn function(&self, symbol: &str) -> Result<mount::Function<'_>, ResidentRefusal> {
        Ok(self.module.function(symbol)?)
    }

    fn flat_grid(&self, count: usize, operation: &'static str) -> Result<(Dim3, Dim3), ResidentRefusal> {
        let count32 = u32::try_from(count).map_err(|_| ResidentRefusal::GridAperture { operation, rows: count, width: 1 })?;
        let grid = self.launch.grid_for(count32.max(1)).map_err(|_| ResidentRefusal::GridAperture { operation, rows: count, width: 1 })?;
        Ok((Dim3::x(grid), Dim3::x(self.launch.block_x)))
    }

    /// Record one flat kernel onto a lane. Counted as a captured launch.
    fn record_flat(&self, lane: &Lane<'_, 'chart>, symbol: &str, count: usize, params: &mut Params, operation: &'static str) -> Result<(), ResidentRefusal> {
        let function = self.function(symbol)?;
        let (grid, block) = self.flat_grid(count, operation)?;
        let mut pointers = params.pointers();
        function.launch_on_shared(lane.stream, grid, block, 0, &mut pointers)?;
        self.census.borrow_mut().captured_launches += 1;
        Ok(())
    }

    fn record_blocks(&self, lane: &Lane<'_, 'chart>, symbol: &str, blocks: usize, block: u32, shared: u32, params: &mut Params, operation: &'static str) -> Result<(), ResidentRefusal> {
        let function = self.function(symbol)?;
        let blocks32 = u32::try_from(blocks).map_err(|_| ResidentRefusal::GridAperture { operation, rows: blocks, width: 1 })?;
        if blocks32 > self.launch.max_grid_x {
            return Err(ResidentRefusal::GridAperture { operation, rows: blocks, width: 1 });
        }
        let mut pointers = params.pointers();
        function.launch_on_shared(lane.stream, Dim3::x(blocks32.max(1)), Dim3::x(block), shared, &mut pointers)?;
        self.census.borrow_mut().captured_launches += 1;
        Ok(())
    }

    // Each `record_*` writes one occurrence's semantic kernel onto its lane. The parameter layout
    // is the kernel's signature, in order.

    pub fn record_enter(&self, lane: &Lane<'_, 'chart>, staged: &StagedWords<'chart>, scale: Dyadic, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let count = staged.rows * staged.width;
        if count != out.count() {
            return Err(ResidentRefusal::Ragged { operation: "enter", words: count, rows: out.rows, width: out.width });
        }
        let mut params = Params::new();
        params.ptr(staged.buffer.device_ptr()).u32(count as u32).i64(scale.significand).i32(scale.exponent).i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_from_bfloat16", count, &mut params, "enter")
    }

    pub fn record_contract(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, map: &MountedReadout<'chart>, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(input.rows as u32).u32(input.width as u32)
            .ptr(map.raw_resident()).i32(map.exponent()).u32(map.rows() as u32).i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_contract", input.rows * map.rows(), &mut params, "contract")
    }

    pub fn record_rms_rebase(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, group: usize, gain: Option<&MountedReadout<'chart>>, eps: Dyadic, shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(input.rows as u32).u32(input.width as u32).u32(group as u32)
            .ptr(gain.map(MountedReadout::raw_resident).unwrap_or(0)).i32(gain.map(MountedReadout::exponent).unwrap_or(0))
            .i64(eps.significand).i32(eps.exponent).i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        let blocks = input.rows * (input.width / group);
        self.record_blocks(lane, "section_rms_rebase", blocks, shape.block, shape.shared_octets, &mut params, "rms-rebase")
    }

    pub fn record_chronology(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, heads: usize, head_width: usize, bands: &BandElements<'chart>, positions: &Positions<'chart>, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(input.rows as u32).u32(heads as u32).u32(head_width as u32)
            .ptr(bands.cos_lo.device_ptr()).ptr(bands.cos_hi.device_ptr()).ptr(bands.sin_lo.device_ptr()).ptr(bands.sin_hi.device_ptr())
            .i32(bands.grain as i32).ptr(positions.buffer.device_ptr()).i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_chronology", input.rows * heads * (head_width / 2), &mut params, "chronology")
    }

    #[allow(clippy::too_many_arguments)]
    pub fn record_contact(&self, lane: &Lane<'_, 'chart>, q: &ResidentSection<'chart>, k: &ResidentSection<'chart>, v: &ResidentSection<'chart>, heads: usize, kv_heads: usize, head_width: usize, window: usize, terms: SeriesAperture, shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(q.lo.device_ptr()).ptr(q.hi.device_ptr()).ptr(k.lo.device_ptr()).ptr(k.hi.device_ptr()).ptr(v.lo.device_ptr()).ptr(v.hi.device_ptr())
            .u32(q.rows as u32).u32(heads as u32).u32(kv_heads as u32).u32(head_width as u32).u32(window.max(1) as u32)
            .i32(out.grain.0 as i32).u32(terms.0)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.slot + 4).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane, "section_contact", q.rows * heads, shape.block, shape.shared_octets, &mut params, "contact")
    }

    pub fn record_gelu_tanh(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, c1: Dyadic, c2: Dyadic, terms: SeriesAperture, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(input.count() as u32)
            .i64(c1.significand).i32(c1.exponent).i64(c2.significand).i32(c2.exponent).i32(out.grain.0 as i32).u32(terms.0)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_gelu_tanh", input.count(), &mut params, "gelu-tanh")
    }

    pub fn record_hadamard(&self, lane: &Lane<'_, 'chart>, a: &ResidentSection<'chart>, b: &ResidentSection<'chart>, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(a.lo.device_ptr()).ptr(a.hi.device_ptr()).ptr(b.lo.device_ptr()).ptr(b.hi.device_ptr()).u32(a.count() as u32).i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_hadamard", a.count(), &mut params, "hadamard")
    }

    pub fn record_re_entry(&self, lane: &Lane<'_, 'chart>, a: &ResidentSection<'chart>, b: &ResidentSection<'chart>, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(a.lo.device_ptr()).ptr(a.hi.device_ptr()).ptr(b.lo.device_ptr()).ptr(b.hi.device_ptr()).u32(a.count() as u32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_re_entry", a.count(), &mut params, "re-entry")
    }

    pub fn record_scale(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, by: DyadicEnclosure, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(input.count() as u32).i64(by.lo).i64(by.hi).i32(by.grain as i32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_scale", input.count(), &mut params, "scale")
    }

    pub fn record_withdraw_columns(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, from: usize, span: usize, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(input.rows as u32).u32(input.width as u32).u32(from as u32).u32(span as u32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_withdraw_columns", input.count(), &mut params, "withdraw-columns")
    }

    pub fn record_withdraw_rows(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, from: usize, span: usize, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(input.rows as u32).u32(input.width as u32).u32(from as u32).u32(span as u32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_withdraw_rows", input.count(), &mut params, "withdraw-rows")
    }

    /// Record the block-permutation intervention; `permutation` is a mounted positions-like array of
    /// block indices (see [`ResidentSurface::mount_positions`]).
    pub fn record_permute_columns(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, block: usize, permutation: &Positions<'chart>, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(input.rows as u32).u32(input.width as u32).u32(block as u32).ptr(permutation.device_ptr())
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_permute_columns", input.count(), &mut params, "permute-columns")
    }

    pub fn record_collapse_control(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(input.count() as u32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_collapse_control", input.count(), &mut params, "collapse-control")
    }

    /// Record the carry of a resident standing into `out`.
    pub fn record_carry(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        if input.rows() != out.rows() || input.width() != out.width() {
            return Err(ResidentRefusal::RowsDisagree { operation: "carry", left: input.rows() * input.width(), right: out.rows() * out.width() });
        }
        let mut params = Params::new();
        params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(out.count() as u32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_carry", out.count(), &mut params, "carry")
    }

    /// The census of one written section into the occurrence's slot, and the a-priori bound it was
    /// admitted under, which the census compares against.
    fn record_census(&self, lane: &Lane<'_, 'chart>, out: &ResidentSection<'chart>, admitted_octaves: u32) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params.ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).u32(out.count() as u32).u32(admitted_octaves).ptr(lane.slot);
        self.record_flat(lane, "section_census", out.count(), &mut params, "census")
    }

    // -----------------------------------------------------------------------------------------
    // the arithmetic control — a serial-chart reference can refute the helpers
    // -----------------------------------------------------------------------------------------

    /// Run the kernel's exact helpers on declared operands and return the wide results and the
    /// per-operand refusal words. A control, outside any passage; launched directly and
    /// synchronized, and counted as such.
    #[allow(clippy::type_complexity)]
    pub fn arithmetic_control(&self, a: &[i64], b: &[i64], s: &[i32], span: &[i64]) -> Result<(Vec<[i128; 10]>, Vec<u32>), ResidentRefusal> {
        let n = a.len();
        if b.len() != n || s.len() != n || span.len() != n {
            return Err(ResidentRefusal::Declaration { operation: "arithmetic-control", what: "operand arrays of unequal length".to_owned() });
        }
        self.context.make_current()?;
        let a_dev = self.alloc::<i64>(n)?;
        let b_dev = self.alloc::<i64>(n)?;
        let s_dev = self.alloc::<i32>(n)?;
        let span_dev = self.alloc::<i64>(n)?;
        let out = self.alloc::<i64>(n * 20)?;
        let refused = self.alloc::<u32>(n)?;
        a_dev.copy_from_slice(a)?;
        b_dev.copy_from_slice(b)?;
        s_dev.copy_from_slice(s)?;
        span_dev.copy_from_slice(span)?;
        refused.copy_from_slice(&vec![0u32; n.max(1)])?;
        let mut params = Params::new();
        params.ptr(a_dev.device_ptr()).ptr(b_dev.device_ptr()).ptr(s_dev.device_ptr()).ptr(span_dev.device_ptr()).u32(n as u32).ptr(out.device_ptr()).ptr(refused.device_ptr());
        let function = self.function("section_arithmetic_control")?;
        let (grid, block) = self.flat_grid(n, "arithmetic-control")?;
        let stream = Stream::create()?;
        let mut pointers = params.pointers();
        function.launch_on_shared(&stream, grid, block, 0, &mut pointers)?;
        stream.synchronize()?;
        {
            let mut census = self.census.borrow_mut();
            census.control_launches += 1;
            census.synchronizations += 1;
        }
        let mut words = vec![0i64; n * 20];
        out.copy_to_slice(&mut words)?;
        let mut flags = vec![0u32; n];
        refused.copy_to_slice(&mut flags)?;
        let results = (0..n)
            .map(|i| {
                let mut row = [0i128; 10];
                for (j, slot) in row.iter_mut().enumerate() {
                    let lo = words[(i * 10 + j) * 2] as u64;
                    let hi = words[(i * 10 + j) * 2 + 1] as u64;
                    *slot = ((u128::from(hi) << 64) | u128::from(lo)) as i128;
                }
                row
            })
            .collect();
        let shrink = (n.max(1) * (8 + 8 + 4 + 8 + 160 + 4)) as u64;
        self.census.borrow_mut().resident_shrank(shrink);
        Ok((results, flags))
    }

    // -----------------------------------------------------------------------------------------
    // the tiled contraction — one law, a second realization, and a caller-declared geometry
    // -----------------------------------------------------------------------------------------

    /// The multiprocessor's declared residency ceilings, as the device stated them at mount.
    pub fn multiprocessor_limits(&self) -> MultiprocessorLimits {
        self.sm_limits
    }

    /// **The registers per thread the loaded module actually carries for one entry**, read through
    /// `cuFuncGetAttribute(CU_FUNC_ATTRIBUTE_NUM_REGS)` after the driver lowered the PTX for this
    /// card. A measurement of the apparatus, never an estimate and never a governor.
    pub fn measured_registers(&self, symbol: &str) -> Result<u32, ResidentRefusal> {
        Ok(self.function(symbol)?.num_regs()?)
    }

    /// The statically declared shared octets of one entry — excluding the dynamic extent a launch
    /// declares, which the caller's tile decides.
    pub fn measured_static_shared(&self, symbol: &str) -> Result<u32, ResidentRefusal> {
        Ok(self.function(symbol)?.static_shared_bytes()?)
    }

    /// The per-thread local surface of one entry, in octets, as the driver reports it after
    /// lowering. Nonzero means the entry spilled or holds a stack frame; zero is lawful.
    pub fn measured_local_octets(&self, symbol: &str) -> Result<u32, ResidentRefusal> {
        Ok(u32::try_from(self.function(symbol)?.local_size_bytes()?).unwrap_or(u32::MAX))
    }

    /// The block extent one entry admits, as the driver reports it after lowering.
    pub fn measured_block_ceiling(&self, symbol: &str) -> Result<u32, ResidentRefusal> {
        Ok(self.function(symbol)?.max_threads_per_block()?)
    }

    /// The predicted shape of the tiled contraction. **The octave admission is the SAME as
    /// [`ResidentSurface::shape_contract`]'s**, deliberately and by derivation: the a-priori bound
    /// `input_octaves + entry_octaves + ceil_log2(inner) + 1` is subset-monotone, so no tree over
    /// any K-partition can widen it and no new admission law is needed. What the tile adds is
    /// apparatus: the block, the dynamic shared extent and the launch count.
    pub fn shape_contract_tiled(&self, rows: usize, inner: usize, input_octaves: u32, map: &MountedReadout<'chart>, tile: TileGeometry) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "contract-tiled";
        if inner != map.dim() {
            return Err(ResidentRefusal::WidthDisagrees { operation: OPERATION, left: inner, right: map.dim() });
        }
        let out_width = map.rows();
        tile.admit(OPERATION, self.launch.block_x, self.launch.warp, self.max_shared_octets)?;
        let needed = input_octaves + map.entry_octaves() + ceil_log2(inner) + 1;
        Self::admit_octaves(OPERATION, needed)?;
        let blocks = tile.blocks(rows, out_width);
        if blocks > u64::from(self.launch.max_grid_x) {
            return Err(ResidentRefusal::GridAperture { operation: OPERATION, rows, width: out_width });
        }
        let mut work = ExactWork::predicted_product(rows, inner, out_width, u64::from(input_octaves.max(map.entry_octaves())));
        work.entries_written = BigUint::from(2 * (rows * out_width) as u64);
        work.resident(2 * (rows * out_width) as u64);
        let peak = u64::from(input_octaves) + u64::from(map.entry_octaves()) + u64::from(ceil_log2(inner)) + 1;
        work.peak_bits = BigUint::from(peak);
        work.cumulative_bits = BigUint::from(2 * (rows * out_width) as u64 * peak);
        // The dependency span the geometry realizes: the serial K a lane walks, then the lane tree,
        // then (split-K only) the join tree. The scalar owner's span is `inner`.
        let lanes = u64::from(tile.lanes);
        let splits = u64::from(tile.splits.max(1));
        let serial = (inner as u64).div_ceil(lanes * splits);
        work.dependency_span = BigUint::from(serial + u64::from(ceil_log2(tile.lanes as usize)) + u64::from(ceil_log2(tile.splits.max(1) as usize)));
        let couplings = vec![CouplingPlan {
            coupling: "the inner contraction over K, folded by a fixed lane tree inside one block",
            kernel: tile.symbol(OPERATION)?,
            extent: inner as u64,
            block: tile.block(),
            predicted: {
                let mut reduction = ExactWork::nothing();
                reduction.added((rows * out_width) as u64 * (inner as u64));
                reduction.dependency_span = BigUint::from(serial + u64::from(ceil_log2(tile.lanes as usize)));
                reduction
            },
        }];
        // K-complete: the semantic kernel and its census. Split-K: the partial, the join, the census.
        let launches = if tile.splits > 1 { 3 } else { 2 };
        Ok(LawShape { operation: OPERATION, rows, width: out_width, needed, predicted: work, couplings, launches, shared_octets: tile.shared_octets(), block: tile.block() })
    }

    /// **Retain one split-K partial standing on the card.** `4` exact `i64` words per output
    /// coordinate per partial: the low and high halves of the lower accumulator, then of the upper.
    /// Nothing here is at the grain and nothing here is rounded.
    pub fn retain_partials(&self, rows: usize, out_width: usize, splits: u32) -> Result<PartialStanding, ResidentRefusal> {
        if splits == 0 || !splits.is_power_of_two() || splits > 16 {
            return Err(ResidentRefusal::Declaration { operation: "contract-split-k", what: format!("a split factor of {splits} is not a power of two in 1..=16") });
        }
        let words = 4 * rows * out_width * splits as usize;
        let buffer = self.alloc::<i64>(words)?;
        let pointer = buffer.device_ptr();
        let mut held = self.partials.borrow_mut();
        held.push(buffer);
        Ok(PartialStanding { index: held.len() - 1, pointer, rows, out_width, splits, words })
    }

    /// Read one retained partial standing back as its exact 128-bit accumulations, indexed
    /// `((a * rows) + row) * out_width + column`. The CPU-side replay of the declared join tree
    /// runs on exactly these words.
    pub fn read_partials(&self, standing: &PartialStanding) -> Result<Vec<(i128, i128)>, ResidentRefusal> {
        let held = self.partials.borrow();
        let buffer = held.get(standing.index).ok_or_else(|| ResidentRefusal::Declaration { operation: "contract-split-k", what: "a partial standing this surface does not hold".to_owned() })?;
        let mut words = vec![0i64; standing.words];
        buffer.copy_to_slice(&mut words)?;
        self.census.borrow_mut().egress_receipt_octets += (standing.words * 8) as u64;
        Ok((0..standing.words / 4)
            .map(|p| {
                let compose = |low: i64, high: i64| -> i128 { (((high as u64 as u128) << 64) | (low as u64 as u128)) as i128 };
                (compose(words[4 * p], words[4 * p + 1]), compose(words[4 * p + 2], words[4 * p + 3]))
            })
            .collect())
    }

    /// Record the K-complete tiled contraction: one block owns a disjoint output tile and the whole
    /// inner extent. `tree` selects which fixed word the lanes fold under; `Descending` is the
    /// declared word and `Ascending` is the reversed control.
    #[allow(clippy::too_many_arguments)]
    pub fn record_contract_tiled(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, map: &MountedReadout<'chart>, tile: TileGeometry, admitted_node_octaves: u32, tree: LaneTree, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        const OPERATION: &str = "contract-tiled";
        if tile.splits != 1 {
            return Err(ResidentRefusal::Declaration { operation: OPERATION, what: format!("a K-complete record with a split factor of {}", tile.splits) });
        }
        let mut params = Params::new();
        params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(input.rows as u32).u32(input.width as u32)
            .ptr(map.raw_resident()).i32(map.exponent()).u32(map.rows() as u32).i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr())
            .u32(tile.outs_per_block).u32(tile.k_tile).u32(admitted_node_octaves).u32(tree.word())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        let blocks = tile.blocks(input.rows, map.rows());
        self.record_blocks(lane, tile.symbol(OPERATION)?, blocks as usize, tile.block(), tile.shared_octets(), &mut params, OPERATION)
    }

    /// Record the split-K pair onto one lane: the exact 128-bit partial, then the join that folds
    /// the partials under the fixed balanced word and performs THE ONE OUTWARD ROUNDING. Both are
    /// one occurrence — one law, one output section, one census — recorded in order on one stream.
    #[allow(clippy::too_many_arguments)]
    pub fn record_contract_split_k(&self, lane: &Lane<'_, 'chart>, input: &ResidentSection<'chart>, map: &MountedReadout<'chart>, tile: TileGeometry, standing: &PartialStanding, admitted_node_octaves: u32, tree: LaneTree, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        const OPERATION: &str = "contract-split-k";
        if tile.splits <= 1 {
            return Err(ResidentRefusal::Declaration { operation: OPERATION, what: "a split-K record with no split".to_owned() });
        }
        if standing.rows != input.rows || standing.out_width != map.rows() || standing.splits != tile.splits {
            return Err(ResidentRefusal::Declaration { operation: OPERATION, what: format!("the partial standing is {}x{}x{} and the launch is {}x{}x{}", standing.splits, standing.rows, standing.out_width, tile.splits, input.rows, map.rows()) });
        }
        let mut partial_params = Params::new();
        partial_params.ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr()).u32(input.rows as u32).u32(input.width as u32)
            .ptr(map.raw_resident()).u32(map.rows() as u32).ptr(standing.pointer)
            .u32(tile.splits).u32(tile.outs_per_block).u32(tile.k_tile).u32(admitted_node_octaves).u32(tree.word())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        let blocks = tile.blocks(input.rows, map.rows());
        self.record_blocks(lane, tile.symbol(OPERATION)?, blocks as usize, tile.block(), tile.shared_octets(), &mut partial_params, OPERATION)?;
        let mut join_params = Params::new();
        join_params.ptr(standing.pointer).u32(tile.splits).u32(input.rows as u32).u32(map.rows() as u32)
            .i32(map.exponent()).i32(out.grain.0 as i32).u32(admitted_node_octaves).u32(tree.word())
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_flat(lane, "section_contract_join", input.rows * map.rows(), &mut join_params, OPERATION)
    }

    /// **The finite candidate family for one contraction shape, from the device's own attributes
    /// and the module's MEASURED registers.** Every member is admitted: it is a whole-warp block the
    /// module carries an entry for, whose dynamic shared extent the device admits and whose grid the
    /// device can cover. Nothing here is ordered and nothing here is called optimal — domination is
    /// the caller's declared axis set, and [`non_dominated`] takes it.
    pub fn contract_candidates(&self, rows: usize, inner: usize, out_width: usize) -> Result<Vec<LaunchCandidate>, ResidentRefusal> {
        let mut family = Vec::new();
        for tile in TileGeometry::enumerate() {
            if tile.admit("contract-tiled", self.launch.block_x, self.launch.warp, self.max_shared_octets).is_err() {
                continue;
            }
            let symbol = match tile.symbol(if tile.splits > 1 { "contract-split-k" } else { "contract-tiled" }) {
                Ok(symbol) => symbol,
                Err(_) => continue,
            };
            let blocks = tile.blocks(rows, out_width);
            if blocks == 0 || blocks > u64::from(self.launch.max_grid_x) {
                continue;
            }
            let registers = self.measured_registers(symbol)?;
            let shared = tile.shared_octets() + self.measured_static_shared(symbol)?;
            let block = tile.block();
            let limits = self.sm_limits;
            let warps = block.div_ceil(limits.warp.max(1)).max(1);
            let per_warp = (registers * limits.warp).div_ceil(limits.register_grain.max(1)) * limits.register_grain.max(1);
            let by_blocks = limits.max_blocks;
            let by_threads = limits.max_threads / block.max(1);
            let by_registers = if per_warp == 0 { u32::MAX } else { limits.max_registers / (per_warp * warps).max(1) };
            let by_shared = if shared == 0 { u32::MAX } else { limits.max_shared_octets / shared };
            let resident = by_blocks.min(by_threads).min(by_registers).min(by_shared);
            let bound_by = if resident == by_registers && by_registers <= by_shared && by_registers <= by_threads && by_registers <= by_blocks {
                "registers"
            } else if resident == by_shared && by_shared <= by_threads && by_shared <= by_blocks {
                "shared"
            } else if resident == by_threads && by_threads <= by_blocks {
                "threads"
            } else {
                "blocks"
            };
            let cover = u64::from(resident) * u64::from(limits.multiprocessors);
            family.push(LaunchCandidate {
                tile,
                symbol,
                block,
                shared_octets: shared,
                registers,
                local_octets: self.function(symbol)?.local_size_bytes()? as u32,
                resident_blocks: resident,
                occupancy: (resident * block, limits.max_threads.max(1)),
                blocks,
                residency_waves: (blocks, cover.max(1)),
                lane_waves: (blocks * u64::from(block), u64::from(limits.max_threads) * u64::from(limits.multiprocessors)),
                serial_k_per_lane: (inner as u64).div_ceil(u64::from(tile.lanes) * u64::from(tile.splits.max(1))),
                dependency_span: (inner as u64).div_ceil(u64::from(tile.lanes) * u64::from(tile.splits.max(1))) + u64::from(ceil_log2(tile.lanes as usize)) + u64::from(ceil_log2(tile.splits.max(1) as usize)),
                bound_by,
            });
        }
        Ok(family)
    }
}


// ---------------------------------------------------------------------------------------------
// the tiled contraction's apparatus geometry — a caller's declaration, never a semantic level
// ---------------------------------------------------------------------------------------------

/// **The launch geometry of one tiled contraction, declared by the caller.**
///
/// Every field here is an APPARATUS aperture and none of them is semantic: the returned words are
/// bit-identical under every admitted member of the family, which is what the equality control
/// asserts. The law's name in a receipt says so, and the geometry travels beside the law rather
/// than inside it.
///
/// * `tile_rows` — the token rows one block holds in registers, `T_t`;
/// * `lanes` — the lanes that cooperate over `K` for one output coordinate, `L`;
/// * `outs_per_block` — the output coordinates one block owns, `O_t`; the block is `O_t · L`;
/// * `k_tile` — the `x` staging depth in shared, `K_t`; `0` stages nothing and takes no barrier;
/// * `splits` — the `K` partition factor `S`; `1` is K-complete, and `S > 1` is the split-K pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TileGeometry {
    pub tile_rows: u32,
    pub lanes: u32,
    pub outs_per_block: u32,
    pub k_tile: u32,
    pub splits: u32,
}

impl TileGeometry {
    /// The block extent this geometry launches at: one lane group per output coordinate.
    pub fn block(&self) -> u32 {
        self.outs_per_block * self.lanes
    }
    /// The dynamic shared extent, in octets: the `[lo, hi]` pair of every staged `x` coordinate.
    pub fn shared_octets(&self) -> u32 {
        self.tile_rows * self.k_tile * 16
    }
    /// `ceil(out_width / O_t) · ceil(rows / T_t) · S`, linearized on x.
    pub fn blocks(&self, rows: usize, out_width: usize) -> u64 {
        let tiles_o = (out_width as u64).div_ceil(u64::from(self.outs_per_block).max(1));
        let tiles_t = (rows as u64).div_ceil(u64::from(self.tile_rows).max(1));
        tiles_o * tiles_t * u64::from(self.splits.max(1))
    }
    /// The unmangled entry this geometry resolves to, or the refusal naming the family it is not in.
    pub fn symbol(&self, operation: &'static str) -> Result<&'static str, ResidentRefusal> {
        let emitted = match (self.splits > 1, self.tile_rows, self.lanes) {
            (false, 1, 32) => Some("section_contract_tiled_r1_l32"),
            (false, 2, 32) => Some("section_contract_tiled_r2_l32"),
            (false, 4, 32) => Some("section_contract_tiled_r4_l32"),
            (false, 1, 16) => Some("section_contract_tiled_r1_l16"),
            (false, 4, 16) => Some("section_contract_tiled_r4_l16"),
            (false, 1, 8) => Some("section_contract_tiled_r1_l8"),
            (true, 1, 32) => Some("section_contract_partial_r1_l32"),
            (true, 4, 32) => Some("section_contract_partial_r4_l32"),
            _ => None,
        };
        emitted.ok_or(ResidentRefusal::Declaration { operation, what: format!("no entry is emitted for {self:?}; the family is the one the module carries") })
    }
    /// Refuse a geometry the device or the module cannot carry, naming which aperture refused.
    pub fn admit(&self, operation: &'static str, block_ceiling: u32, warp: u32, shared_ceiling: u32) -> Result<(), ResidentRefusal> {
        if self.lanes == 0 || !self.lanes.is_power_of_two() || self.lanes > warp.max(1) {
            return Err(ResidentRefusal::Declaration { operation, what: format!("{} lanes is not a power of two inside one warp of {warp}", self.lanes) });
        }
        if self.tile_rows == 0 || self.outs_per_block == 0 {
            return Err(ResidentRefusal::Declaration { operation, what: "a tile with no rows or no output coordinates".to_owned() });
        }
        if self.splits == 0 || !self.splits.is_power_of_two() || self.splits > 16 {
            return Err(ResidentRefusal::Declaration { operation, what: format!("a split factor of {} is not a power of two in 1..=16", self.splits) });
        }
        let block = self.block();
        if block == 0 || block % warp.max(1) != 0 {
            return Err(ResidentRefusal::Declaration { operation, what: format!("a block of {block} is not a whole number of warps of {warp}") });
        }
        if block > block_ceiling {
            return Err(ResidentRefusal::Declaration { operation, what: format!("a block of {block} exceeds the module's admitted {block_ceiling}") });
        }
        if self.shared_octets() > shared_ceiling {
            return Err(ResidentRefusal::Declaration { operation, what: format!("a staged tile of {} octets exceeds the device's {shared_ceiling} per block", self.shared_octets()) });
        }
        self.symbol(operation)?;
        Ok(())
    }
    /// **The finite population of geometries this module can realize at all.** The cross product of
    /// the emitted entries with the output-group and staging apertures; membership of the family a
    /// given shape admits is decided by [`ResidentSurface::contract_candidates`], which reads the
    /// device.
    pub fn enumerate() -> Vec<TileGeometry> {
        let mut family = Vec::new();
        for (tile_rows, lanes, splits) in [(1, 32, 1), (2, 32, 1), (4, 32, 1), (1, 16, 1), (4, 16, 1), (1, 8, 1), (1, 32, 2), (1, 32, 4), (1, 32, 8), (1, 32, 16), (4, 32, 2), (4, 32, 4), (4, 32, 8), (4, 32, 16)] {
            for outs_per_block in [1u32, 2, 4, 8, 16, 32, 64] {
                for k_tile in [0u32, 128, 256, 512, 1024] {
                    let tile = TileGeometry { tile_rows, lanes, outs_per_block, k_tile, splits };
                    if tile.block() > 512 || tile.block() % 32 != 0 || tile.shared_octets() > 49_152 {
                        continue;
                    }
                    family.push(tile);
                }
            }
        }
        family
    }
}

/// **Which fixed word the lanes fold under.** `Descending` is the declared word — halving offsets
/// `L/2 .. 1` — and `Ascending` is the reversed control, a different pairing of the same leaves.
/// Integer addition is exact and associative, so the two must return bit-identical values; the
/// per-node widths need not agree, and a value divergence is a defect of the realization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneTree {
    Descending,
    Ascending,
}

impl LaneTree {
    pub fn word(&self) -> u32 {
        match self {
            LaneTree::Descending => 0,
            LaneTree::Ascending => 1,
        }
    }
    pub fn written(&self) -> &'static str {
        match self {
            LaneTree::Descending => "descending halving offsets L/2 .. 1; join ascending in a",
            LaneTree::Ascending => "ascending doubling offsets 1 .. L/2; join descending in a",
        }
    }
}

/// **A retained split-K partial standing.** Not a section: it carries the exact `__int128`
/// accumulation of one `K` slice at grain `2^(map_e − F)` and never a coordinate at the grain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PartialStanding {
    index: usize,
    pointer: u64,
    pub rows: usize,
    pub out_width: usize,
    pub splits: u32,
    pub words: usize,
}

impl PartialStanding {
    /// **A partial standing declared without a card**, for a law whose entailment or shape is being
    /// read before any surface is mounted. It addresses nothing: `record` refuses it, because the
    /// surface it names holds no buffer at that index.
    pub fn declared(rows: usize, out_width: usize, splits: u32) -> Self {
        Self { index: usize::MAX, pointer: 0, rows, out_width, splits, words: 4 * rows * out_width * splits as usize }
    }
    /// The address range the partial occupies — a footprint coordinate, for a receipt.
    pub fn range(&self) -> (u64, u64) {
        (self.pointer, self.pointer + (self.words * 8) as u64)
    }
}

/// **One admitted launch geometry, with what the device and the module say about it.** Every
/// coordinate is measured or derived from a measurement; there is no combined coordinate, no score
/// and no ordering. Occupancy and the two wave faces are exact integer ratios — a float would put a
/// deleted tail into an apparatus reading.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaunchCandidate {
    pub tile: TileGeometry,
    pub symbol: &'static str,
    pub block: u32,
    /// Dynamic plus static shared octets per block.
    pub shared_octets: u32,
    /// **Measured** through `cuFuncGetAttribute(NUM_REGS)` on the loaded module.
    pub registers: u32,
    /// **Measured** per-thread local surface; nonzero means the entry spilled or holds a stack.
    pub local_octets: u32,
    pub resident_blocks: u32,
    /// `(resident lanes, the multiprocessor's ceiling)` — a ratio, never divided.
    pub occupancy: (u32, u32),
    pub blocks: u64,
    /// `(blocks, resident_blocks · multiprocessors)` — the residency wave face.
    pub residency_waves: (u64, u64),
    /// `(threads, the card's resident lanes)` — the lane wave face the profile classifies on.
    pub lane_waves: (u64, u64),
    pub serial_k_per_lane: u64,
    pub dependency_span: u64,
    /// Which term of the resource equation bound the residency.
    pub bound_by: &'static str,
}

/// One apparatus coordinate a receiver may declare, and the hand it reads it with.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CandidateAxis {
    ResidentBlocksUp,
    OccupancyUp,
    MapReuseUp,
    LanesUp,
    SharedDown,
    SerialKDown,
    DependencySpanDown,
    BlocksDown,
    RegistersDown,
}

impl CandidateAxis {
    /// The axis's coordinate as a ratio, oriented so that GREATER is better on the declared hand.
    fn read(&self, candidate: &LaunchCandidate) -> (u128, u128) {
        match self {
            CandidateAxis::ResidentBlocksUp => (u128::from(candidate.resident_blocks), 1),
            CandidateAxis::OccupancyUp => (u128::from(candidate.occupancy.0), u128::from(candidate.occupancy.1.max(1))),
            CandidateAxis::MapReuseUp => (u128::from(candidate.tile.tile_rows), 1),
            CandidateAxis::LanesUp => (u128::from(candidate.tile.lanes), 1),
            CandidateAxis::SharedDown => (1, u128::from(candidate.shared_octets) + 1),
            CandidateAxis::SerialKDown => (1, u128::from(candidate.serial_k_per_lane) + 1),
            CandidateAxis::DependencySpanDown => (1, u128::from(candidate.dependency_span) + 1),
            CandidateAxis::BlocksDown => (1, u128::from(candidate.blocks) + 1),
            CandidateAxis::RegistersDown => (1, u128::from(candidate.registers) + 1),
        }
    }
}

/// **The non-dominated members of a candidate family under a DECLARED axis set.**
///
/// A candidate is dominated when another is at least as good on every declared axis and strictly
/// better on one. No axis is summed with another — they are different species and a sum would be a
/// scalar governor over incomparable coordinates — so the returned set is a function of what the
/// receiver declared, exactly as a compression's remainder is. Changing the axis set changes the
/// set, which is the falsifier: a return that did not move under a changed declaration was ranking.
pub fn non_dominated(family: &[LaunchCandidate], axes: &[CandidateAxis]) -> Vec<usize> {
    let ratio_ge = |a: (u128, u128), b: (u128, u128)| a.0 * b.1 >= b.0 * a.1;
    let ratio_gt = |a: (u128, u128), b: (u128, u128)| a.0 * b.1 > b.0 * a.1;
    (0..family.len())
        .filter(|at| {
            !family.iter().enumerate().any(|(other, rival)| {
                other != *at
                    && axes.iter().all(|axis| ratio_ge(axis.read(rival), axis.read(&family[*at])))
                    && axes.iter().any(|axis| ratio_gt(axis.read(rival), axis.read(&family[*at])))
            })
        })
        .collect()
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
        (self.lineage_buffer.device_ptr() + (offset * 4) as u64, count as u32)
    }
    fn lane_of(&self, index: usize) -> Lane<'_, 'chart> {
        let (lineage, lineage_count) = self.lineage_of(index);
        Lane { stream: &self.lanes[index], slot: self.slot_of(index), census: self.census_buffer.device_ptr(), lineage, lineage_count, index, _surface: std::marker::PhantomData }
    }

    /// The address range of an occurrence's own slot — written by its kernels.
    pub fn slot_range(&self, index: usize) -> (u64, u64) {
        (self.slot_of(index), self.slot_of(index) + (SLOT_WORDS * 4) as u64)
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
    pub fn open(&mut self, index: usize, producers: &[usize]) -> Result<Lane<'_, 'chart>, ResidentRefusal> {
        if index >= self.occurrences || self.opened[index] {
            return Err(ResidentRefusal::Declaration { operation: "passage", what: format!("occurrence {index} opened twice or out of range") });
        }
        let mut given: Vec<usize> = producers.to_vec();
        given.sort_unstable();
        given.dedup();
        if given != self.declared[index] {
            return Err(ResidentRefusal::Declaration { operation: "passage", what: format!("occurrence {index} opens with producers {given:?} but declared lineage {:?}", self.declared[index]) });
        }
        let lane = &self.lanes[index];
        for producer in &self.declared[index] {
            if !self.closed[*producer] {
                return Err(ResidentRefusal::Declaration { operation: "passage", what: format!("occurrence {index} reads occurrence {producer}, which no earlier front wrote") });
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
                        return Err(ResidentRefusal::Declaration { operation: "passage", what: format!("serialized: occurrence {previous} was not closed before {index}") });
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
    pub fn close(&mut self, index: usize, out: &ResidentSection<'chart>, admitted_octaves: u32) -> Result<(), ResidentRefusal> {
        if !self.opened[index] || self.closed[index] {
            return Err(ResidentRefusal::Declaration { operation: "passage", what: format!("occurrence {index} closed before it was opened, or twice") });
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

    /// **Bind the passage**: join every lane back to the origin, end the capture, read the graph's
    /// own census, instantiate. What comes back is launchable and reads back once.
    pub fn finish(self) -> Result<ResidentPassage<'chart>, ResidentRefusal> {
        for index in 0..self.occurrences {
            if !self.closed[index] {
                return Err(ResidentRefusal::Declaration { operation: "passage", what: format!("occurrence {index} was never bound") });
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
        let words_count = SLOT_WORDS * self.occurrences.max(1);
        let mut words = vec![0u32; words_count];
        self.census_buffer.copy_to_slice(&mut words)?;
        self.surface.census.borrow_mut().egress_receipt_octets += (words_count * 4) as u64;
        let slots: Vec<SlotReading> = (0..self.occurrences).map(|i| SlotReading::of(&words[i * SLOT_WORDS..(i + 1) * SLOT_WORDS])).collect();
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
        Ok(PassageReading { slots, obstruction: ObstructionLineage { refusals }, census_before, census_after: self.surface.census() })
    }
}

impl Drop for ResidentPassage<'_> {
    fn drop(&mut self) {
        let _ = self.surface.context.make_current();
        self.surface.census.borrow_mut().resident_shrank(self.census_octets() + self.lineage_octets());
    }
}

// ---------------------------------------------------------------------------------------------
// the source-scan gate: the production cone cannot reach the quarantined interpreter
// ---------------------------------------------------------------------------------------------

/// **The structural half of the first falsifier**: the production dependency cone cannot reach
/// the quarantined serial-reference realization or its host semantic dispatch. The behavioural
/// half is the census: between a graph launch and its terminal synchronize the surface issues no
/// launch, which a renamed loop cannot pass.
pub fn production_cone_reaches_the_reference(sources: &[(&str, &str)]) -> Vec<(String, &'static str)> {
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
mod tests {
    use super::*;
    use num_traits::One;

    fn surface() -> Option<(&'static ResidentReadout, &'static ResidentSurface<'static>)> {
        let readout = match ResidentReadout::new() {
            Ok(readout) => Box::leak(Box::new(readout)),
            Err(_) => {
                eprintln!("no resident chart answered; the resident-section tests did not run");
                return None;
            }
        };
        let surface = Box::leak(Box::new(ResidentSurface::on(readout).ok()?));
        Some((readout, surface))
    }

    /// bf16 words for small dyadics: 1.0 = 0x3F80, 2.0 = 0x4000, -1.5 = 0xBFC0, 0.5 = 0x3F00
    const ONE: u16 = 0x3F80;
    const TWO: u16 = 0x4000;
    const HALF: u16 = 0x3F00;
    const MINUS_ONE_AND_HALF: u16 = 0xBFC0;
    const THREE: u16 = 0x4040;
    const FOUR: u16 = 0x4080;

    fn rat(n: i64, d: i64) -> Rat {
        Rat::new(BigInt::from(n), BigInt::from(d))
    }

    /// A one-occurrence passage entering `words` at `grain`, launched, and read out.
    fn enter_once(surface: &'static ResidentSurface<'static>, words: &[u16], rows: usize, width: usize, scale: Dyadic, grain: ResidentGrain) -> (Vec<(i64, i64)>, PassageReading) {
        let staged = surface.stage_words(words, rows, width).expect("stage");
        let shape = surface.shape_enter(rows, width, scale, grain).expect("shape");
        let out = surface.fresh_section(rows, width, grain).expect("section");
        let mut builder = surface.begin_passage(&[vec![]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface.record_enter(&lane, &staged, scale, &out).expect("record");
        builder.close(0, &out, shape.needed).expect("close");
        let passage = builder.finish().expect("finish");
        let reading = passage.launch().expect("launch");
        let read = surface.read_out(&out).expect("read");
        (read, reading)
    }

    #[test]
    fn the_production_cone_gate_names_what_it_finds_and_only_that() {
        let clean = [("resident", "use crate::exact_work::ExactWork;")];
        assert!(production_cone_reaches_the_reference(&clean).is_empty());
        let dirty = [("driver", "use holonic_engine::ported_reference::realize;")];
        assert!(production_cone_reaches_the_reference(&dirty).iter().any(|(_, token)| *token == "ported_reference"));
        let loop_shaped = [("owner", "impl EnactsInOrder for X {}")];
        assert!(production_cone_reaches_the_reference(&loop_shaped).iter().any(|(_, token)| *token == "impl EnactsInOrder"));
    }

    #[test]
    fn this_owner_does_not_reach_the_quarantined_interpreter() {
        let own = include_str!("resident_section.rs");
        let body: String = own
            .split("#[cfg(test)]")
            .next()
            .expect("the owner precedes its tests")
            .lines()
            .filter(|line| !line.trim_start().starts_with('"'))
            .collect::<Vec<_>>()
            .join("\n");
        let reached = production_cone_reaches_the_reference(&[("resident_section.rs", &body)]);
        assert!(reached.is_empty(), "{reached:?}");
    }

    #[test]
    fn a_binary64_word_is_an_exact_dyadic_and_its_value_is_the_word() {
        let scale = Dyadic::of_binary64_bits(0x3fe9884533d43651).expect("dyadic");
        assert_eq!(scale.octaves(), 53);
        assert_eq!(scale.exponent, -53);
        assert!(scale.value() < Rat::one() && scale.value() > rat(1, 2));
        assert_eq!(Dyadic::of_bfloat16_bits(HALF).expect("half").value(), rat(1, 2));
    }

    #[test]
    fn the_surface_binds_one_apparatus_occurrence_and_states_its_mode() {
        let Some((readout, surface)) = surface() else { return };
        assert_eq!(surface.device_name(), readout.device_name());
        assert_eq!(surface.cover().device().map(|d| d.name.as_str()), Some(surface.device_name()));
        let mode = surface.mode();
        assert_eq!(mode.kernel_content.as_deref(), Some(surface.ptx_sha256()));
        assert!(mode.device.is_some());
        assert_eq!(surface.declaration().warp_size, surface.derived_launch().2);
    }

    #[test]
    fn a_passage_of_one_occurrence_launches_once_synchronizes_once_and_reads_once() {
        let Some((_, surface)) = surface() else { return };
        let grain = ResidentGrain(20);
        let (words, reading) = enter_once(surface, &[ONE, TWO, HALF, MINUS_ONE_AND_HALF], 2, 2, Dyadic::ONE, grain);
        let unit = 1i64 << 20;
        assert_eq!(words, vec![(unit, unit), (2 * unit, 2 * unit), (unit / 2, unit / 2), (-3 * unit / 2, -3 * unit / 2)]);
        assert_eq!(reading.slots[0].max_octave, 22);
        assert_eq!(reading.slots[0].max_width, 0);
        assert!(reading.slots[0].written);
        assert!(reading.obstruction.is_empty());
        assert_eq!(reading.slots[0].lineage_inspected, 0, "an entering occurrence inspects no predecessor");
        let (before, after) = (&reading.census_before, &reading.census_after);
        assert_eq!(after.deed_launches, before.deed_launches + 1);
        assert_eq!(after.synchronizations, before.synchronizations + 1);
        assert_eq!(after.captured_launches, before.captured_launches, "no launch is issued during the deed");
        assert_eq!(after.egress_receipt_octets - before.egress_receipt_octets, (SLOT_WORDS * 4) as u64);
        assert_eq!(after.egress_section_octets, before.egress_section_octets, "the deed itself reads no section");
    }

    #[test]
    fn a_dyadic_scale_finer_than_the_grain_widens_by_one_grain_and_never_rounds_toward_a_value() {
        let Some((_, surface)) = surface() else { return };
        let (words, _) = enter_once(surface, &[HALF], 1, 1, Dyadic { significand: 3, exponent: -20 }, ResidentGrain(20));
        assert_eq!(words, vec![(1, 2)]);
    }

    /// A two-front passage: `enter x` then co-present `{scale x by 2, hadamard x·x, re-entry x+x}`,
    /// with the graph's own census read back beside what was intended.
    #[test]
    fn a_two_front_passage_binds_the_bonds_as_edges_and_the_co_present_members_share_no_edge() {
        let Some((_, surface)) = surface() else { return };
        let grain = ResidentGrain(20);
        let words = [ONE, TWO, HALF, MINUS_ONE_AND_HALF];
        let staged = surface.stage_words(&words, 1, 4).expect("stage");
        let enter = surface.shape_enter(1, 4, Dyadic::ONE, grain).expect("shape");
        let by = DyadicEnclosure { lo: 2, hi: 2, grain: 0 };
        let scale = surface.shape_scale(1, 4, 22, by).expect("shape");
        let hadamard = surface.shape_hadamard(1, 4, 22, 22).expect("shape");
        let re_entry = surface.shape_re_entry(1, 4, 22, 22).expect("shape");
        let x = surface.fresh_section(1, 4, grain).expect("x");
        let scaled = surface.fresh_section(1, 4, grain).expect("s");
        let squared = surface.fresh_section(1, 4, grain).expect("h");
        let doubled = surface.fresh_section(1, 4, grain).expect("r");
        let mut builder = surface.begin_passage(&[vec![], vec![0], vec![0, 0], vec![0, 0]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface.record_enter(&lane, &staged, Dyadic::ONE, &x).expect("enter");
        builder.close(0, &x, enter.needed).expect("close");
        let lane = builder.open(1, &[0]).expect("open");
        surface.record_scale(&lane, &x, by, &scaled).expect("scale");
        builder.close(1, &scaled, scale.needed).expect("close");
        let lane = builder.open(2, &[0, 0]).expect("open");
        surface.record_hadamard(&lane, &x, &x, &squared).expect("hadamard");
        builder.close(2, &squared, hadamard.needed).expect("close");
        let lane = builder.open(3, &[0, 0]).expect("open");
        surface.record_re_entry(&lane, &x, &x, &doubled).expect("re-entry");
        builder.close(3, &doubled, re_entry.needed).expect("close");
        let passage = builder.finish().expect("finish");
        // memset + 4 × (kernel + census) = 9 nodes; edges: memset→enter (1), enter.census→{scale,
        // hadamard, re-entry} (3), kernel→census (4) = 8.
        assert_eq!(passage.intended(), (9, 8));
        assert_eq!(passage.graph_census().nodes, 9, "{:?}", passage.graph_census());
        assert_eq!(passage.graph_census().edges, 8, "{:?}", passage.graph_census());
        assert_eq!(passage.graph_census().kernel_nodes, 8);
        assert_eq!(passage.graph_census().memset_nodes, 1);
        let reading = passage.launch().expect("launch");
        assert!(reading.obstruction.is_empty());
        assert_eq!(reading.slots[2].lineage_inspected, 1, "a doubled bond is one predecessor slot, read once");
        let unit = 1i64 << 20;
        assert_eq!(surface.read_out(&scaled).expect("read"), vec![(2 * unit, 2 * unit), (4 * unit, 4 * unit), (unit, unit), (-3 * unit, -3 * unit)]);
        let sq = surface.read_out(&squared).expect("read");
        assert_eq!(sq[3], (9 * unit / 4, 9 * unit / 4));
        assert_eq!(surface.read_out(&doubled).expect("read")[1], (4 * unit, 4 * unit));
        // Launching the same bound passage again returns the same faces: it is a graph, not a replay.
        let again = passage.launch().expect("launch again");
        assert_eq!(again.slots, reading.slots);
        assert_eq!(surface.read_out(&scaled).expect("read")[0], (2 * unit, 2 * unit));
    }

    #[test]
    fn a_refuted_a_priori_bound_refuses_downstream_on_the_card_and_names_the_occurrence() {
        let Some((_, surface)) = surface() else { return };
        let grain = ResidentGrain(20);
        let staged = surface.stage_words(&[TWO], 1, 1).expect("stage");
        let x = surface.fresh_section(1, 1, grain).expect("x");
        let y = surface.fresh_section(1, 1, grain).expect("y");
        let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface.record_enter(&lane, &staged, Dyadic::ONE, &x).expect("enter");
        // Admit the entry at 3 octaves; the word 2·2^20 occupies 22. The census must refute it.
        builder.close(0, &x, 3).expect("close");
        let lane = builder.open(1, &[0]).expect("open");
        surface.record_scale(&lane, &x, DyadicEnclosure { lo: 2, hi: 2, grain: 0 }, &y).expect("scale");
        builder.close(1, &y, 30).expect("close");
        let passage = builder.finish().expect("finish");
        let reading = passage.launch().expect("launch");
        assert!(reading.slots[0].bound_violated);
        assert!(matches!(reading.slots[0].refusal("enter", 3), Some(ResidentRefusal::BoundRefuted { admitted: 3, measured: 22, .. })));
        assert!(matches!(reading.slots[1].refusal("scale", 30), Some(ResidentRefusal::Upstream { .. })));
        assert_eq!(reading.slots[1].upstream_first, Some(0));
        assert_eq!(reading.slots[1].upstream_count, 1);
        assert_eq!(reading.slots[1].upstream_flags & REFUSED_BOUND, REFUSED_BOUND);
        let lineage = &reading.obstruction;
        assert_eq!(lineage.refusals.len(), 2);
        assert!(lineage.refusals[0].origin && lineage.refusals[0].index == 0);
        assert!(!lineage.refusals[1].origin && lineage.refusals[1].index == 1 && lineage.refusals[1].upstream_first == Some(0));
        assert!(lineage.joined_flags() & (REFUSED_BOUND | REFUSED_UPSTREAM) != 0);
        // The successor wrote nothing plausible: its section holds only what allocation left, and
        // its census marker still says the census ran.
        assert!(reading.slots[1].written);
    }

    #[test]
    fn the_rms_rebase_encloses_the_exact_value_and_a_finer_grain_nests() {
        let Some((_, surface)) = surface() else { return };
        let coarse = ResidentGrain(24);
        let fine = ResidentGrain(40);
        let eps = Dyadic { significand: 1, exponent: -30 };
        let radicand = rat(25, 2) + eps.value();
        let mut runs = Vec::new();
        for grain in [coarse, fine] {
            let staged = surface.stage_words(&[THREE, FOUR], 1, 2).expect("stage");
            let enter = surface.shape_enter(1, 2, Dyadic::ONE, grain).expect("shape");
            let rms = surface.shape_rms_rebase(1, 2, 2, grain.0 + 3, None).expect("shape");
            assert!(rms.couplings.iter().any(|c| c.coupling.contains("quadratic")));
            let x = surface.fresh_section(1, 2, grain).expect("x");
            let y = surface.fresh_section(1, 2, grain).expect("y");
            let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
            let lane = builder.open(0, &[]).expect("open");
            surface.record_enter(&lane, &staged, Dyadic::ONE, &x).expect("enter");
            builder.close(0, &x, enter.needed).expect("close");
            let lane = builder.open(1, &[0]).expect("open");
            surface.record_rms_rebase(&lane, &x, 2, None, eps, &rms, &y).expect("rms");
            builder.close(1, &y, rms.needed).expect("close");
            let passage = builder.finish().expect("finish");
            let reading = passage.launch().expect("launch");
            assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
            assert!(reading.slots[1].written);
            let out = surface.read_out(&y).expect("read");
            for (enclosure, x) in out.iter().zip([rat(3, 1), rat(4, 1)]) {
                let lo = word_value(enclosure.0, grain);
                let hi = word_value(enclosure.1, grain);
                assert!(lo >= Rat::from_integer(BigInt::from(0)));
                assert!(&lo * &lo * &radicand <= &x * &x, "lower bound below the value");
                assert!(&hi * &hi * &radicand >= &x * &x, "upper bound above the value");
            }
            runs.push(out.into_iter().map(|(l, h)| (word_value(l, grain), word_value(h, grain))).collect::<Vec<_>>());
        }
        for ((cl, ch), (fl, fh)) in runs[0].iter().zip(&runs[1]) {
            assert!(cl <= fl && fh <= ch, "finer grain must nest");
            assert!(fh - fl < ch - cl, "and be strictly narrower");
        }
    }


    fn candidate(tile: TileGeometry, registers: u32, resident_blocks: u32, shared: u32) -> LaunchCandidate {
        LaunchCandidate {
            tile,
            symbol: "section_contract_tiled_r1_l32",
            block: tile.block(),
            shared_octets: shared,
            registers,
            local_octets: 0,
            resident_blocks,
            occupancy: (resident_blocks * tile.block(), 1536),
            blocks: 512,
            residency_waves: (512, u64::from(resident_blocks) * 80),
            lane_waves: (512 * u64::from(tile.block()), 122_880),
            serial_k_per_lane: 2560 / u64::from(tile.lanes),
            dependency_span: 2560 / u64::from(tile.lanes) + 5,
            bound_by: "registers",
        }
    }

    #[test]
    fn a_contract_tiled_geometry_outside_the_emitted_family_refuses_by_name() {
        // the module carries an entry for (T_t, L) = (1, 32) and none for (3, 32)
        let admitted = TileGeometry { tile_rows: 1, lanes: 32, outs_per_block: 4, k_tile: 256, splits: 1 };
        assert_eq!(admitted.symbol("contract-tiled").expect("emitted"), "section_contract_tiled_r1_l32");
        assert_eq!(admitted.block(), 128);
        assert_eq!(admitted.shared_octets(), 1 * 256 * 16);
        let unemitted = TileGeometry { tile_rows: 3, lanes: 32, outs_per_block: 4, k_tile: 256, splits: 1 };
        assert!(matches!(unemitted.symbol("contract-tiled"), Err(ResidentRefusal::Declaration { .. })));
        // a partial block of lanes, a lane count past the warp, a split that is not a power of two,
        // a block past the module's ceiling and a staged tile past the device — each refuses, and
        // each names which aperture it left
        assert!(TileGeometry { tile_rows: 1, lanes: 8, outs_per_block: 3, k_tile: 0, splits: 1 }.admit("t", 512, 32, 49_152).is_err());
        assert!(TileGeometry { tile_rows: 1, lanes: 64, outs_per_block: 1, k_tile: 0, splits: 1 }.admit("t", 512, 32, 49_152).is_err());
        assert!(TileGeometry { tile_rows: 1, lanes: 32, outs_per_block: 4, k_tile: 0, splits: 3 }.admit("t", 512, 32, 49_152).is_err());
        assert!(TileGeometry { tile_rows: 1, lanes: 32, outs_per_block: 32, k_tile: 0, splits: 1 }.admit("t", 512, 32, 49_152).is_err());
        assert!(TileGeometry { tile_rows: 4, lanes: 32, outs_per_block: 4, k_tile: 1024, splits: 1 }.admit("t", 512, 32, 49_152).is_err());
        assert!(admitted.admit("t", 512, 32, 49_152).is_ok());
        // the blocks the geometry launches, including both tails
        assert_eq!(admitted.blocks(5, 2048), 512 * 5);
        assert_eq!(admitted.blocks(3, 2049), 513 * 3);
        let split = TileGeometry { tile_rows: 1, lanes: 32, outs_per_block: 4, k_tile: 256, splits: 8 };
        assert_eq!(split.blocks(1, 512), 128 * 8);
        assert_eq!(split.symbol("contract-split-k").expect("emitted"), "section_contract_partial_r1_l32");
    }

    #[test]
    fn the_contract_tiled_candidate_family_is_finite_and_the_retained_set_moves_with_the_declared_axes() {
        // every enumerated member is a whole-warp block the device could carry
        let family = TileGeometry::enumerate();
        assert!(!family.is_empty());
        for tile in &family {
            assert_eq!(tile.block() % 32, 0);
            assert!(tile.block() <= 512);
            assert!(tile.shared_octets() <= 49_152);
        }
        // domination is the receiver's declaration, and the retained set moves when it changes
        let candidates = vec![
            candidate(TileGeometry { tile_rows: 1, lanes: 32, outs_per_block: 4, k_tile: 0, splits: 1 }, 40, 10, 0),
            candidate(TileGeometry { tile_rows: 4, lanes: 32, outs_per_block: 4, k_tile: 256, splits: 1 }, 64, 6, 16_384),
            candidate(TileGeometry { tile_rows: 2, lanes: 32, outs_per_block: 4, k_tile: 0, splits: 1 }, 47, 9, 0),
        ];
        let coarse = non_dominated(&candidates, &[CandidateAxis::ResidentBlocksUp, CandidateAxis::SharedDown]);
        // the four-row tile is dominated on both coarse axes by the one-row tile
        assert_eq!(coarse, vec![0]);
        let with_reuse = non_dominated(&candidates, &[CandidateAxis::ResidentBlocksUp, CandidateAxis::SharedDown, CandidateAxis::MapReuseUp]);
        assert_eq!(with_reuse, vec![0, 1, 2]);
        // and a declaration that reads only one axis retains only its extremum
        assert_eq!(non_dominated(&candidates, &[CandidateAxis::MapReuseUp]), vec![1]);
    }

    #[test]
    fn the_contract_tiled_shape_admits_exactly_what_the_scalar_owner_admits_and_prices_the_tile_beside_it() {
        let Some((readout, surface)) = surface() else { return };
        let map = readout.mount_bfloat16(&[ONE, TWO, MINUS_ONE_AND_HALF, HALF], 2).expect("map");
        let scalar = surface.shape_contract(1, 2, 22, &map).expect("scalar shape");
        let tile = TileGeometry { tile_rows: 1, lanes: 32, outs_per_block: 4, k_tile: 256, splits: 1 };
        let tiled = surface.shape_contract_tiled(1, 2, 22, &map, tile).expect("tiled shape");
        // the same octave admission, by the subset-monotone argument, and the same output shape
        assert_eq!(tiled.needed, scalar.needed);
        assert_eq!((tiled.rows, tiled.width), (scalar.rows, scalar.width));
        // and the apparatus beside it: the tile's block, its staged extent, its launches
        assert_eq!(tiled.block, 128);
        assert_eq!(tiled.shared_octets, 4_096);
        assert_eq!(tiled.launches, 2);
        assert_eq!(tiled.couplings.len(), 1);
        // a split-K geometry records three launches, because the join is the third
        let split = TileGeometry { tile_rows: 1, lanes: 32, outs_per_block: 4, k_tile: 256, splits: 4 };
        assert_eq!(surface.shape_contract_tiled(1, 2, 22, &map, split).expect("split shape").launches, 3);
        // a geometry the module emits no entry for refuses at the shape, before any launch
        let unemitted = TileGeometry { tile_rows: 8, lanes: 32, outs_per_block: 4, k_tile: 256, splits: 1 };
        assert!(surface.shape_contract_tiled(1, 2, 22, &map, unemitted).is_err());
        // a width that disagrees with the map refuses by name
        assert!(surface.shape_contract_tiled(1, 3, 22, &map, tile).is_err());
    }

    #[test]
    fn the_contract_tiled_family_reads_its_registers_from_the_loaded_module() {
        let Some((_, surface)) = surface() else { return };
        // every emitted entry answers, and the scalar owner's own measured count stands beside them
        for symbol in ["section_contract", "section_contract_tiled_r1_l32", "section_contract_tiled_r4_l32", "section_contract_partial_r1_l32", "section_contract_join"] {
            let registers = surface.measured_registers(symbol).expect("registers");
            assert!(registers > 0 && registers <= 255, "{symbol} reported {registers} registers");
        }
        // the module-wide block derivation did not move when the family was added
        assert_eq!(surface.derived_launch().0, 512);
        for symbol in KERNELS {
            assert!(surface.measured_block_ceiling(symbol).expect("ceiling") >= 512, "{symbol} admits fewer than 512 threads");
        }
        let limits = surface.multiprocessor_limits();
        assert!(limits.max_blocks > 0 && limits.max_registers > 0 && limits.max_shared_octets > 0);
        let family = surface.contract_candidates(5, 2560, 2048).expect("family");
        assert!(!family.is_empty());
        for member in &family {
            assert!(member.resident_blocks >= 1, "{member:?} is resident nowhere");
            assert!(member.registers > 0);
        }
    }

    #[test]
    fn a_contract_tiled_return_is_bit_equal_to_the_scalar_owner_and_the_reversed_tree_agrees() {
        let Some((readout, surface)) = surface() else { return };
        let map = readout.mount_bfloat16(&[ONE, TWO, MINUS_ONE_AND_HALF, HALF], 2).expect("map");
        let grain = ResidentGrain(20);
        let staged = surface.stage_words(&[ONE, TWO], 1, 2).expect("stage");
        let enter = surface.shape_enter(1, 2, Dyadic::ONE, grain).expect("shape");
        let scalar_shape = surface.shape_contract(1, 2, enter.needed.min(22), &map).expect("shape");
        let tile = TileGeometry { tile_rows: 1, lanes: 32, outs_per_block: 2, k_tile: 128, splits: 1 };
        let tiled_shape = surface.shape_contract_tiled(1, 2, enter.needed.min(22), &map, tile).expect("shape");
        let x = surface.fresh_section(1, 2, grain).expect("x");
        let scalar_out = surface.fresh_section(1, 2, grain).expect("scalar");
        let descending = surface.fresh_section(1, 2, grain).expect("descending");
        let ascending = surface.fresh_section(1, 2, grain).expect("ascending");
        let mut builder = surface.begin_passage(&[vec![], vec![0], vec![0], vec![0]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface.record_enter(&lane, &staged, Dyadic::ONE, &x).expect("enter");
        builder.close(0, &x, enter.needed).expect("close");
        let lane = builder.open(1, &[0]).expect("open");
        surface.record_contract(&lane, &x, &map, &scalar_out).expect("scalar");
        builder.close(1, &scalar_out, scalar_shape.needed).expect("close");
        let lane = builder.open(2, &[0]).expect("open");
        surface.record_contract_tiled(&lane, &x, &map, tile, ResidentSurface::carrier_octaves(), LaneTree::Descending, &descending).expect("tiled");
        builder.close(2, &descending, tiled_shape.needed).expect("close");
        let lane = builder.open(3, &[0]).expect("open");
        surface.record_contract_tiled(&lane, &x, &map, tile, ResidentSurface::carrier_octaves(), LaneTree::Ascending, &ascending).expect("tiled");
        builder.close(3, &ascending, tiled_shape.needed).expect("close");
        let passage = builder.finish().expect("finish");
        let reading = passage.launch().expect("launch");
        assert!(reading.obstruction.is_empty(), "{:?}", reading.obstruction);
        let scalar_words = surface.read_out(&scalar_out).expect("read");
        assert_eq!(surface.read_out(&descending).expect("read"), scalar_words);
        assert_eq!(surface.read_out(&ascending).expect("read"), scalar_words);
        // the census words of the three occurrences agree, not only the sections
        for at in [2usize, 3] {
            assert_eq!(reading.slots[at].max_octave, reading.slots[1].max_octave);
            assert_eq!(reading.slots[at].max_width, reading.slots[1].max_width);
            assert_eq!(reading.slots[at].width_sum, reading.slots[1].width_sum);
            assert_eq!(reading.slots[at].nonzero_widths, reading.slots[1].nonzero_widths);
            assert_eq!(reading.slots[at].refused, reading.slots[1].refused);
        }
    }

    #[test]
    fn a_contract_tiled_node_aperture_refuses_where_the_scalar_owner_wraps_silently() {
        let Some((readout, surface)) = surface() else { return };
        // a one-octave node aperture is narrower than any real accumulation: the tiled kernel
        // refuses at the node and names REFUSED_CARRIER; the scalar owner has no per-step check
        // at all and returns the same words it always did. That is the behavioural difference.
        let map = readout.mount_bfloat16(&[ONE, TWO, MINUS_ONE_AND_HALF, HALF], 2).expect("map");
        let grain = ResidentGrain(20);
        let staged = surface.stage_words(&[ONE, TWO], 1, 2).expect("stage");
        let enter = surface.shape_enter(1, 2, Dyadic::ONE, grain).expect("shape");
        let tile = TileGeometry { tile_rows: 1, lanes: 32, outs_per_block: 2, k_tile: 128, splits: 1 };
        let tiled_shape = surface.shape_contract_tiled(1, 2, enter.needed.min(22), &map, tile).expect("shape");
        let x = surface.fresh_section(1, 2, grain).expect("x");
        let out = surface.fresh_section(1, 2, grain).expect("out");
        let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface.record_enter(&lane, &staged, Dyadic::ONE, &x).expect("enter");
        builder.close(0, &x, enter.needed).expect("close");
        let lane = builder.open(1, &[0]).expect("open");
        surface.record_contract_tiled(&lane, &x, &map, tile, 1, LaneTree::Descending, &out).expect("tiled");
        builder.close(1, &out, tiled_shape.needed).expect("close");
        let passage = builder.finish().expect("finish");
        let reading = passage.launch().expect("launch");
        assert_eq!(reading.slots[1].refused & REFUSED_CARRIER, REFUSED_CARRIER);
        assert!(reading.obstruction.origins().any(|refusal| refusal.index == 1));
    }

    #[test]
    fn a_split_k_partial_is_exact_and_the_join_rounds_once() {
        let Some((readout, surface)) = surface() else { return };
        // four inner coordinates, split two ways: each partial carries an exact 128-bit sum at the
        // product grain, and only the join places anything at the section's grain.
        let map_words = [ONE, TWO, THREE, FOUR, HALF, ONE, TWO, HALF];
        let map = readout.mount_bfloat16(&map_words, 4).expect("map");
        let grain = ResidentGrain(20);
        let staged = surface.stage_words(&[ONE, TWO, ONE, FOUR], 1, 4).expect("stage");
        let enter = surface.shape_enter(1, 4, Dyadic::ONE, grain).expect("shape");
        let scalar_shape = surface.shape_contract(1, 4, enter.needed.min(24), &map).expect("shape");
        let tile = TileGeometry { tile_rows: 1, lanes: 32, outs_per_block: 2, k_tile: 128, splits: 2 };
        let split_shape = surface.shape_contract_tiled(1, 4, enter.needed.min(24), &map, tile).expect("shape");
        let standing = surface.retain_partials(1, 2, 2).expect("partials");
        let x = surface.fresh_section(1, 4, grain).expect("x");
        let scalar_out = surface.fresh_section(1, 2, grain).expect("scalar");
        let split_out = surface.fresh_section(1, 2, grain).expect("split");
        let mut builder = surface.begin_passage(&[vec![], vec![0], vec![0]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface.record_enter(&lane, &staged, Dyadic::ONE, &x).expect("enter");
        builder.close(0, &x, enter.needed).expect("close");
        let lane = builder.open(1, &[0]).expect("open");
        surface.record_contract(&lane, &x, &map, &scalar_out).expect("scalar");
        builder.close(1, &scalar_out, scalar_shape.needed).expect("close");
        let lane = builder.open(2, &[0]).expect("open");
        surface.record_contract_split_k(&lane, &x, &map, tile, &standing, ResidentSurface::carrier_octaves(), LaneTree::Descending, &split_out).expect("split");
        builder.close(2, &split_out, split_shape.needed).expect("close");
        let passage = builder.finish().expect("finish");
        let reading = passage.launch().expect("launch");
        assert!(reading.obstruction.is_empty(), "{:?}", reading.obstruction);
        assert_eq!(surface.read_out(&split_out).expect("read"), surface.read_out(&scalar_out).expect("read"));
        // the partials themselves: two per output coordinate, and their exact sum is the whole
        let partials = surface.read_partials(&standing).expect("partials");
        assert_eq!(partials.len(), 2 * 1 * 2);
        for column in 0..2usize {
            let (a_lo, a_hi) = partials[column];
            let (b_lo, b_hi) = partials[2 + column];
            let whole_lo = a_lo + b_lo;
            let whole_hi = a_hi + b_hi;
            // the join's one rounding takes the exact sum at 2^(map_e − F) down to 2^-F
            let exponent = map.exponent();
            let floor = |value: i128| -> i128 { if exponent >= 0 { value << exponent } else { value >> (-exponent) } };
            let read = surface.read_out(&split_out).expect("read")[column];
            assert_eq!(floor(whole_lo), i128::from(read.0), "the lower word is the floor of the exact sum");
            assert!(i128::from(read.1) >= floor(whole_hi));
        }
    }

    #[test]
    fn a_contract_through_a_mounted_map_is_the_exact_product() {
        let Some((readout, surface)) = surface() else { return };
        let map = readout.mount_bfloat16(&[ONE, TWO, MINUS_ONE_AND_HALF, HALF], 2).expect("map");
        let grain = ResidentGrain(20);
        let staged = surface.stage_words(&[ONE, TWO], 1, 2).expect("stage");
        let enter = surface.shape_enter(1, 2, Dyadic::ONE, grain).expect("shape");
        let contract = surface.shape_contract(1, 2, enter.needed.min(22), &map).expect("shape");
        assert!(contract.needed <= ResidentSurface::carrier_octaves());
        let x = surface.fresh_section(1, 2, grain).expect("x");
        let y = surface.fresh_section(1, 2, grain).expect("y");
        let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface.record_enter(&lane, &staged, Dyadic::ONE, &x).expect("enter");
        builder.close(0, &x, enter.needed).expect("close");
        let lane = builder.open(1, &[0]).expect("open");
        surface.record_contract(&lane, &x, &map, &y).expect("contract");
        builder.close(1, &y, contract.needed).expect("close");
        let passage = builder.finish().expect("finish");
        let reading = passage.launch().expect("launch");
        assert!(reading.obstruction.is_empty());
        let unit = 1i64 << 20;
        assert_eq!(surface.read_out(&y).expect("read"), vec![(5 * unit, 5 * unit), (-unit / 2, -unit / 2)]);
    }

    #[test]
    fn the_contact_carries_a_convex_combination_inside_the_hull_and_the_negative_numerator_law_holds() {
        let Some((_, surface)) = surface() else { return };
        let grain = ResidentGrain(24);
        let q_words = [ONE, 0, ONE, 0];
        let v_words = [MINUS_ONE_AND_HALF, TWO, HALF, ONE];
        let sq = surface.stage_words(&q_words, 2, 2).expect("stage");
        let sk = surface.stage_words(&q_words, 2, 2).expect("stage");
        let sv = surface.stage_words(&v_words, 2, 2).expect("stage");
        let enter = surface.shape_enter(2, 2, Dyadic::ONE, grain).expect("shape");
        let contact = surface.shape_contact(2, 2, 2, 2, 1, 1, 2, 512, SeriesAperture(12), grain, 26, 26, 26).expect("shape");
        assert_eq!(contact.couplings.len(), 3);
        let q = surface.fresh_section(2, 2, grain).expect("q");
        let k = surface.fresh_section(2, 2, grain).expect("k");
        let v = surface.fresh_section(2, 2, grain).expect("v");
        let out = surface.fresh_section(2, 2, grain).expect("out");
        let mut builder = surface.begin_passage(&[vec![], vec![], vec![], vec![0, 1, 2]]).expect("begin");
        for (index, (staged, section)) in [(&sq, &q), (&sk, &k), (&sv, &v)].into_iter().enumerate() {
            let lane = builder.open(index, &[]).expect("open");
            surface.record_enter(&lane, staged, Dyadic::ONE, section).expect("enter");
            builder.close(index, section, enter.needed).expect("close");
        }
        let lane = builder.open(3, &[0, 1, 2]).expect("open");
        surface.record_contact(&lane, &q, &k, &v, 1, 1, 2, 512, SeriesAperture(12), &contact, &out).expect("contact");
        builder.close(3, &out, contact.needed).expect("close");
        let passage = builder.finish().expect("finish");
        let reading = passage.launch().expect("launch");
        assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
        assert_eq!(reading.slots[3].lineage_inspected, 3);
        assert_eq!(reading.slots[3].reach, 2);
        let words = surface.read_out(&out).expect("read");
        let contains = |enclosure: (i64, i64), value: &Rat| word_value(enclosure.0, grain) <= *value && *value <= word_value(enclosure.1, grain);
        assert!(contains(words[0], &rat(-3, 2)) && words[0].0 == words[0].1);
        assert!(contains(words[1], &rat(2, 1)) && words[1].0 == words[1].1);
        assert!(contains(words[2], &rat(-1, 2)), "{:?}", words[2]);
        assert!(word_value(words[2].0, grain) >= rat(-3, 2) && word_value(words[2].1, grain) <= rat(1, 2));
        assert!(contains(words[3], &rat(3, 2)), "{:?}", words[3]);
        assert!(words[2].1 - words[2].0 <= 1 && words[3].1 - words[3].0 <= 1, "{:?} {:?}", words[2], words[3]);
    }

    #[test]
    fn a_carrier_range_is_refused_before_any_launch_and_names_the_octaves() {
        let Some((_, surface)) = surface() else { return };
        // a product of sixty-four and sixty-three octaves would need one hundred and twenty-seven
        let launches = surface.census().captured_launches;
        let outcome = surface.shape_hadamard(1, 1, 64, 63);
        assert!(matches!(outcome, Err(ResidentRefusal::CarrierRange { operation: "hadamard", needed: 127, admitted: 126 })), "{outcome:?}");
        assert_eq!(surface.census().captured_launches, launches, "no launch on a refused budget");
        // and a word that leaves the signed carrier ON the card raises the carrier flag, typed
        let (words, reading) = enter_once(surface, &[TWO], 1, 1, Dyadic::ONE, ResidentGrain(62));
        assert_eq!(words, vec![(0, 0)]);
        assert!(matches!(reading.slots[0].refusal("enter", 80), Some(ResidentRefusal::CarrierLeft { .. })));
    }

    /// **The lineage falsifiers.** Two branches enter side by side; branch B's entering material
    /// carries a non-finite codeword at a NONZERO coordinate, so its kernel refuses `MALFORMED` at
    /// runtime. Every successor of B refuses `UPSTREAM` naming B; branch A and A's successor are
    /// bit-identical to the unpoisoned run; the join of A and B refuses upstream naming B alone;
    /// and the complete obstruction lineage is one reading under the co-present schedule, the
    /// serialized schedule, and the serialized schedule with the front opened in reverse.
    fn two_branch_passage(surface: &'static ResidentSurface<'static>, poison: bool, schedule: Schedule, reverse_front: bool) -> (PassageReading, Vec<(i64, i64)>, Vec<(i64, i64)>, Vec<(i64, i64)>, Vec<(i64, i64)>) {
        let grain = ResidentGrain(20);
        let a_words = [ONE, TWO, HALF, FOUR];
        // 0x7F80 is +inf in bfloat16: a non-finite stored codeword, at coordinate 2.
        let b_words = if poison { [ONE, TWO, 0x7F80, THREE] } else { [ONE, TWO, HALF, THREE] };
        let sa = surface.stage_words(&a_words, 1, 4).expect("stage");
        let sb = surface.stage_words(&b_words, 1, 4).expect("stage");
        let enter = surface.shape_enter(1, 4, Dyadic::ONE, grain).expect("shape");
        let by = DyadicEnclosure { lo: 2, hi: 2, grain: 0 };
        let scale = surface.shape_scale(1, 4, 23, by).expect("shape");
        let join = surface.shape_re_entry(1, 4, 24, 24).expect("shape");
        let a = surface.fresh_section(1, 4, grain).expect("a");
        let b = surface.fresh_section(1, 4, grain).expect("b");
        let a2 = surface.fresh_section(1, 4, grain).expect("a2");
        let b2 = surface.fresh_section(1, 4, grain).expect("b2");
        let joined = surface.fresh_section(1, 4, grain).expect("j");
        // occurrences: 0 enter A · 1 enter B · 2 scale A · 3 scale B · 4 re-entry(A2, B2)
        let lineage = vec![vec![], vec![], vec![0], vec![1], vec![2, 3]];
        let mut builder = surface.begin_passage_scheduled(&lineage, schedule).expect("begin");
        let front0: Vec<usize> = if reverse_front { vec![1, 0] } else { vec![0, 1] };
        for index in front0 {
            let (staged, out) = if index == 0 { (&sa, &a) } else { (&sb, &b) };
            let lane = builder.open(index, &[]).expect("open");
            surface.record_enter(&lane, staged, Dyadic::ONE, out).expect("enter");
            builder.close(index, out, enter.needed).expect("close");
        }
        let front1: Vec<usize> = if reverse_front { vec![3, 2] } else { vec![2, 3] };
        for index in front1 {
            let (input, out, producer) = if index == 2 { (&a, &a2, 0) } else { (&b, &b2, 1) };
            let lane = builder.open(index, &[producer]).expect("open");
            surface.record_scale(&lane, input, by, out).expect("scale");
            builder.close(index, out, scale.needed).expect("close");
        }
        let lane = builder.open(4, &[2, 3]).expect("open");
        surface.record_re_entry(&lane, &a2, &b2, &joined).expect("join");
        builder.close(4, &joined, join.needed).expect("close");
        let passage = builder.finish().expect("finish");
        let reading = passage.launch().expect("launch");
        let ra = surface.read_out(&a).expect("read");
        let ra2 = surface.read_out(&a2).expect("read");
        let rb2 = surface.read_out(&b2).expect("read");
        let rj = surface.read_out(&joined).expect("read");
        (reading, ra, ra2, rb2, rj)
    }

    #[test]
    fn a_runtime_refusal_at_a_nonzero_coordinate_travels_only_along_its_lineage_and_the_sibling_is_bit_identical() {
        let Some((_, surface)) = surface() else { return };
        let (clean, clean_a, clean_a2, clean_b2, clean_j) = two_branch_passage(surface, false, Schedule::CoPresent, false);
        assert!(clean.obstruction.is_empty(), "{:?}", clean.slots);
        let (poisoned, a, a2, b2, j) = two_branch_passage(surface, true, Schedule::CoPresent, false);
        // B refused at runtime, of its own: MALFORMED, originating.
        assert!(matches!(poisoned.slots[1].refusal("enter", 30), Some(ResidentRefusal::Malformed { .. })), "{:?}", poisoned.slots[1]);
        assert!(poisoned.slots[1].originates_refusal());
        // every successor of B refuses UPSTREAM, deterministically, naming B
        assert!(matches!(poisoned.slots[3].refusal("scale", 30), Some(ResidentRefusal::Upstream { .. })));
        assert_eq!(poisoned.slots[3].upstream_first, Some(1));
        assert_eq!(poisoned.slots[3].upstream_count, 1);
        assert_eq!(poisoned.slots[3].upstream_flags, REFUSED_MALFORMED);
        // the join of A and B refuses upstream naming B's successor alone (A's stood)
        assert!(matches!(poisoned.slots[4].refusal("re-entry", 30), Some(ResidentRefusal::Upstream { .. })));
        assert_eq!(poisoned.slots[4].upstream_first, Some(3));
        assert_eq!(poisoned.slots[4].upstream_count, 1, "A's successor did not refuse; only B's did");
        assert_eq!(poisoned.slots[4].lineage_inspected, 2);
        // the unrelated sibling and its successor are bit-identical to the clean run
        assert_eq!(a, clean_a);
        assert_eq!(a2, clean_a2);
        assert_eq!(poisoned.slots[0], clean.slots[0]);
        assert_eq!(poisoned.slots[2], clean.slots[2]);
        assert!(poisoned.obstruction.stands(0) && poisoned.obstruction.stands(2));
        // B's own section and the join are NOT standing: partially written words are refused by
        // the lineage, whatever they hold.
        assert!(!poisoned.obstruction.stands(1) && !poisoned.obstruction.stands(3) && !poisoned.obstruction.stands(4));
        let _ = (b2, j, clean_b2, clean_j);
        // the complete lineage, as a population: origins {1}, carried {3, 4}
        let origins: Vec<usize> = poisoned.obstruction.origins().map(|r| r.index).collect();
        assert_eq!(origins, vec![1]);
        assert_eq!(poisoned.obstruction.refusals.iter().map(|r| r.index).collect::<Vec<_>>(), vec![1, 3, 4]);
    }

    #[test]
    fn the_complete_obstruction_lineage_is_one_reading_under_every_legal_schedule() {
        let Some((_, surface)) = surface() else { return };
        let (co_present, ..) = two_branch_passage(surface, true, Schedule::CoPresent, false);
        let (serialized, ..) = two_branch_passage(surface, true, Schedule::Serialized, false);
        let (reversed, ..) = two_branch_passage(surface, true, Schedule::Serialized, true);
        assert_eq!(co_present.obstruction, serialized.obstruction);
        assert_eq!(co_present.obstruction, reversed.obstruction);
        assert_eq!(co_present.slots, serialized.slots);
        assert_eq!(co_present.slots, reversed.slots);
        // and the co-present deed launched again is the same reading
        let (again, ..) = two_branch_passage(surface, true, Schedule::CoPresent, false);
        assert_eq!(again.obstruction, co_present.obstruction);
    }

    #[test]
    fn a_lineage_that_disagrees_with_the_producers_opened_is_a_declaration_error_not_a_silent_read() {
        let Some((_, surface)) = surface() else { return };
        let grain = ResidentGrain(20);
        let staged = surface.stage_words(&[ONE], 1, 1).expect("stage");
        let x = surface.fresh_section(1, 1, grain).expect("x");
        let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface.record_enter(&lane, &staged, Dyadic::ONE, &x).expect("enter");
        builder.close(0, &x, 30).expect("close");
        assert!(matches!(builder.open(1, &[]), Err(ResidentRefusal::Declaration { .. })), "opening with an undeclared lineage must refuse");
        // a predecessor not earlier in the passage is refused at declaration
        assert!(matches!(surface.begin_passage(&[vec![1], vec![]]), Err(ResidentRefusal::Declaration { .. })));
    }

    /// The kernel's helpers against an independent exact reference: signed minimum, its negation,
    /// negative shifts both ways, shifts by the carrier width, zero, positive and negative interval
    /// products, denominators touching zero, and the negative quotient enclosure.
    #[test]
    fn the_arithmetic_helpers_agree_with_the_serial_exact_reference_on_the_signed_edge_cases() {
        let Some((_, surface)) = surface() else { return };
        let cases: Vec<(i64, i64, i32, i64)> = vec![
            (i64::MIN, 3, 0, 0),
            (i64::MIN, 3, -1, 0),
            (i64::MIN, 3, 40, 0),
            (i64::MIN + 1, 7, -3, 0),
            (-7, 2, -1, 0),
            (-7, 2, 1, 0),
            (7, 2, -1, 0),
            (-1, 1, -70, 0),
            (1, 1, -70, 0),
            (0, 5, 60, 0),
            (-2, 1, 1, 1),         // interval quotient N=[-2,-1], D=[1,2] lifted by 1
            (-2, 1, 0, 1),         // corners of [-2,-1]·[1,2]
            (3, 4, 0, 2),          // corners of [3,5]·[4,6]
            (-5, 3, 0, 4),         // corners of [-5,-1]·[3,7]
            (i64::MAX, i64::MAX, 0, 0),
            (-i64::MAX, i64::MAX, 3, 0),
            (5, 0, 0, 0),          // denominator zero: refused, not divided
            (5, 1, 126, 0),        // shift by the carrier width refuses
            (1, 1, 127, 0),
        ];
        let a: Vec<i64> = cases.iter().map(|c| c.0).collect();
        let b: Vec<i64> = cases.iter().map(|c| c.1).collect();
        let s: Vec<i32> = cases.iter().map(|c| c.2).collect();
        let span: Vec<i64> = cases.iter().map(|c| c.3).collect();
        let (results, flags) = surface.arithmetic_control(&a, &b, &s, &span).expect("control");
        let two = BigInt::from(2);
        let pow = |k: u32| BigInt::from(BigUint::from(1u8) << k as usize);
        let floor_div = |n: &BigInt, d: &BigInt| -> BigInt {
            let q = n / d;
            if (n % d) != BigInt::from(0) && ((n < &BigInt::from(0)) != (d < &BigInt::from(0))) { q - 1 } else { q }
        };
        let ceil_div = |n: &BigInt, d: &BigInt| -> BigInt {
            let q = n / d;
            if (n % d) != BigInt::from(0) && ((n < &BigInt::from(0)) == (d < &BigInt::from(0))) { q + 1 } else { q }
        };
        let carrier = pow(127);
        for (i, (av, bv, sv, sp)) in cases.iter().enumerate() {
            let a = BigInt::from(*av);
            let b = BigInt::from(*bv);
            let row = results[i];
            let flag = flags[i];
            // shift_floor / shift_ceil against the exact rational
            let (expected_floor, expected_ceil, overflow) = if *sv >= 0 {
                let value = &a * pow(*sv as u32);
                let overflow = value.magnitude() >= carrier.magnitude();
                (value.clone(), value, overflow)
            } else {
                let d = pow((-*sv) as u32);
                (floor_div(&a, &d), ceil_div(&a, &d), false)
            };
            if overflow {
                assert!(flag & REFUSED_CARRIER != 0, "case {i}: an overflowing shift must refuse");
            } else {
                assert_eq!(BigInt::from(row[0]), expected_floor, "case {i} floor");
                assert_eq!(BigInt::from(row[1]), expected_ceil, "case {i} ceil");
            }
            // product_shift(a, b, |s|): floor and ceil of a·b / 2^|s|
            let k = sv.unsigned_abs();
            let product = &a * &b;
            let d = pow(k);
            if product.magnitude() < pow(253).magnitude() {
                let pf = floor_div(&product, &d);
                let pc = ceil_div(&product, &d);
                if pf.magnitude() <= pow(126).magnitude() && pc.magnitude() <= pow(126).magnitude() {
                    assert_eq!(BigInt::from(row[2]), pf, "case {i} product floor");
                    assert_eq!(BigInt::from(row[3]), pc, "case {i} product ceil");
                }
            }
            // div_floor / div_ceil for b > 0
            if *bv > 0 {
                assert_eq!(BigInt::from(row[4]), floor_div(&a, &b), "case {i} div floor");
                assert_eq!(BigInt::from(row[5]), ceil_div(&a, &b), "case {i} div ceil");
                // the interval quotient of [a, a+span] / [b, b+span], lifted by one
                let n_lo = &a * &two;
                let n_hi = (&a + BigInt::from(*sp)) * &two;
                let d_lo = b.clone();
                let d_hi = &b + BigInt::from(*sp);
                let q_lo = floor_div(&n_lo, if n_lo < BigInt::from(0) { &d_lo } else { &d_hi });
                let q_hi = ceil_div(&n_hi, if n_hi < BigInt::from(0) { &d_hi } else { &d_lo });
                if n_lo.magnitude() < carrier.magnitude() && n_hi.magnitude() < carrier.magnitude() {
                    assert_eq!(BigInt::from(row[6]), q_lo, "case {i} quotient lo");
                    assert_eq!(BigInt::from(row[7]), q_hi, "case {i} quotient hi");
                }
            } else {
                assert!(flag & REFUSED_MALFORMED != 0, "case {i}: a non-positive denominator must refuse");
            }
            // corners of [a, a+span]·[b, b+span]
            let ends = [
                &a * &b,
                &a * (&b + BigInt::from(*sp)),
                (&a + BigInt::from(*sp)) * &b,
                (&a + BigInt::from(*sp)) * (&b + BigInt::from(*sp)),
            ];
            let c_lo = ends.iter().min().cloned().expect("four");
            let c_hi = ends.iter().max().cloned().expect("four");
            if c_lo.magnitude() < carrier.magnitude() && c_hi.magnitude() < carrier.magnitude() {
                assert_eq!(BigInt::from(row[8]), c_lo, "case {i} corners lo");
                assert_eq!(BigInt::from(row[9]), c_hi, "case {i} corners hi");
            }
        }
        // The named negative quotient: N=[-2,-1] over D=[1,2] is exactly [-2, -1/2].
        let named = cases.iter().position(|c| *c == (-2, 1, 1, 1)).expect("the named case");
        assert_eq!(results[named][6], -4, "lo = -2 at half-grain resolution");
        assert_eq!(results[named][7], -1, "hi = -1/2 at half-grain resolution");
        assert_eq!(flags[named], 0);
    }
}
