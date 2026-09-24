//! **The launch law.** D1 (`the launch is a passage and owes a receipt`) and D2 (`exclusive access
//! is a type`) of [`docs/plans/THE_EXACT_DEVICE_LAW_IS_CONSTRUCTED.md`], executable.
//!
//! The Lean owner is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/DeviceLaunchLaw.lean`
//! (`Soma.Holonics.Foundation.DeviceLaunchLaw`).  Every structure below has a formal counterpart
//! there and every theorem there appears here as an invariant or a test:
//!
//! | Rust | Lean |
//! |---|---|
//! | [`LaunchShape`], [`LaunchShape::threads`] | `LaunchShape`, `LaunchShape.threads` |
//! | [`LaunchRequirement::cover_with`] | `LaunchShape.cover`, `cover_covers`, `cover_tail` |
//! | [`LaunchClause::CoverageExact`] | `linear_thread_bijective` (and the weaker `exists_unique_thread`) |
//! | [`LaunchClause::CoverageGuarded`] | `linear_thread_injective_guarded`, `foldl_guarded_cover`, `guarded_of_le` |
//! | [`LaunchClause::ThreadProductRepresentable`] | `LaunchShape.threads_lt_wire` |
//! | [`DisjointPartition::uniform`] | `DisjointPartition.uniform` |
//! | [`DisjointPartition::from_offsets`] | `DisjointPartition.ofOffsets`, `offsets_mono` |
//! | [`DisjointPartition::verify_pairwise_disjoint`] | `DisjointPartition.region_disjoint`, `region_subset`, `offsets_mono` |
//! | [`PartitionedWrite`] | `DisjointPartition.raceFree`, `write_right_comm` |
//! | [`PartitionedWrite::scope`] | `DisjointPartition.raceFreeInterleaved`, `shuffleWrites_eq_sequential` |
//! | [`DisjointPartition::scatter`] | `scatter_perm`, `scatter_order_dependent` |
//! | [`ScatterLaw::Accumulated`] | `scatterAdd_perm` |
//!
//! ## What the law is for
//!
//! `cuLaunchKernel` accepts any grid, any block, any shared extent and any argument array, and
//! reports its objection — when it reports one at all — as a driver error after the fact.  A wrong
//! grid that still fits the device is not an error at all: it silently drops or double-covers work.
//! This module moves the whole of that decision to the call site.  A kernel declares a
//! [`LaunchRequirement`]; a caller offers a [`LaunchShape`] and its [`ArgumentSpan`]s; the
//! construction of a [`LawfulLaunch`] either returns a [`LaunchReceipt`] naming every clause it
//! proved, or a [`LaunchRefusal`] naming the one clause it could not.  There is no third outcome
//! and no path to the driver that skips it.
//!
//! **No device limit is ever authored here.**  [`LaunchLimits::read`] takes every bound from the
//! mounted card (`cuDeviceGetAttribute`) and the lowered entry (`cuFuncGetAttribute`), exactly as
//! `crates/holonic-engine/build.rs` reads its virtual architecture off the device rather than
//! pinning it.  A limit the caller's evidence does not carry is **deferred and said aloud** in the
//! receipt, never defaulted.  The literals `1024` and `65535` do not appear in this file outside
//! the synthetic test fixtures, which are compiled only under `cfg(test)`.

use core::ffi::c_void;
use core::fmt;
use core::marker::PhantomData;
use core::ops::Range;

use crate::cuda::{LaunchCensus, LinearLaunch};
use crate::{
    Context, CudaError, Device, DeviceAttribute, DeviceBuffer, Dim3, Function, PinnedHost, Result,
    Stream,
};

/// The result of a construction that either proves the launch law or names the clause it violated.
pub type Lawful<T> = core::result::Result<T, LaunchRefusal>;

/// The result of a construction that either proves the partition law or names the clause it
/// violated.
pub type Partitioned<T> = core::result::Result<T, PartitionRefusal>;

// ---------------------------------------------------------------------------------------------
// D1 — clauses and refusals
// ---------------------------------------------------------------------------------------------

/// One named clause of the launch law.  A [`LaunchReceipt`] lists the clauses it proved and the
/// clauses it deferred for want of evidence; a [`LaunchRefusal`] names the single clause that
/// failed.  Clauses are never scored, ranked or summed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LaunchClause {
    /// The declared element extent is positive.
    PositiveExtent,
    /// Every block dimension is positive.
    PositiveBlock,
    /// Every grid dimension is positive.
    PositiveGrid,
    /// The block equals the shape the kernel declared exactly.
    BlockExact,
    /// The block thread count is a multiple of the declared divisor.
    BlockMultiple,
    /// The block thread count is a multiple of the device's warp.
    BlockWarpMultiple,
    /// The block thread count is within the kernel's own declared cap.
    BlockWithinDeclared,
    /// The block thread count is within the lowered function's `MAX_THREADS_PER_BLOCK`.
    BlockWithinFunction,
    /// The block thread count is within the device's `MAX_THREADS_PER_BLOCK`.
    BlockWithinDevice,
    /// Each block dimension is within the device's per-dimension block extent.
    BlockDimensionWithinDevice,
    /// Each grid dimension is within the device's per-dimension grid extent.
    GridWithinDevice,
    /// `grid.x * grid.y * grid.z * block.x * block.y * block.z` is representable without wrapping.
    ThreadProductRepresentable,
    /// `grid.x * block.x` is representable in the kernel's `u32` stride wire.
    StrideRepresentable,
    /// The thread population equals the declared extent exactly.
    CoverageExact,
    /// The thread population reaches the declared extent and the guarded tail is below one block.
    CoverageGuarded,
    /// The stride wire covers the declared extent by repetition.
    CoverageStrided,
    /// The dynamic shared extent equals the kernel's declared function of the block shape.
    SharedBytesMatch,
    /// Static plus dynamic shared bytes are within the device's per-block shared extent.
    SharedWithinDevice,
    /// The presented argument population equals the declared population.
    ArgumentCount,
    /// Each presented argument carries the declared name, in declared order.
    ArgumentName,
    /// Each presented argument lives where the kernel declared it must.
    ArgumentResidency,
    /// Each presented argument's element width and count satisfy the declared extent.
    ArgumentExtent,
    /// Each device- or pinned-resident argument carries a non-null address.
    ArgumentAddress,
    /// Each presented argument's access is the access the kernel declared for it.  This is a
    /// *declaration* clause, distinct from [`LaunchClause::ArgumentAliasing`]: a caller presenting
    /// a read span where the entry declares `*mut` has misread the signature, which is a different
    /// fault from two spans overlapping.
    ArgumentAccess,
    /// No writable argument overlaps another argument of the same residency.
    ArgumentAliasing,
    /// Every declared scalar parameter is presented exactly once, in declared order, at its
    /// declared width.
    ScalarArguments,
    /// The offered stream matches the declared ordering.
    StreamOrdering,
}

impl LaunchClause {
    /// The clause's own name, for a receipt or a refusal message.
    pub const fn name(self) -> &'static str {
        match self {
            LaunchClause::PositiveExtent => "positive-extent",
            LaunchClause::PositiveBlock => "positive-block",
            LaunchClause::PositiveGrid => "positive-grid",
            LaunchClause::BlockExact => "block-exact",
            LaunchClause::BlockMultiple => "block-multiple",
            LaunchClause::BlockWarpMultiple => "block-warp-multiple",
            LaunchClause::BlockWithinDeclared => "block-within-declared",
            LaunchClause::BlockWithinFunction => "block-within-function",
            LaunchClause::BlockWithinDevice => "block-within-device",
            LaunchClause::BlockDimensionWithinDevice => "block-dimension-within-device",
            LaunchClause::GridWithinDevice => "grid-within-device",
            LaunchClause::ThreadProductRepresentable => "thread-product-representable",
            LaunchClause::StrideRepresentable => "stride-representable",
            LaunchClause::CoverageExact => "coverage-exact",
            LaunchClause::CoverageGuarded => "coverage-guarded",
            LaunchClause::CoverageStrided => "coverage-strided",
            LaunchClause::SharedBytesMatch => "shared-bytes-match",
            LaunchClause::SharedWithinDevice => "shared-within-device",
            LaunchClause::ArgumentCount => "argument-count",
            LaunchClause::ArgumentName => "argument-name",
            LaunchClause::ArgumentResidency => "argument-residency",
            LaunchClause::ArgumentExtent => "argument-extent",
            LaunchClause::ArgumentAddress => "argument-address",
            LaunchClause::ArgumentAccess => "argument-access",
            LaunchClause::ArgumentAliasing => "argument-aliasing",
            LaunchClause::ScalarArguments => "scalar-arguments",
            LaunchClause::StreamOrdering => "stream-ordering",
        }
    }
}

/// An unlawful launch: a typed **construction** refusal naming the violated clause.  It is raised
/// before any driver call, so an unlawful launch is never observed as a CUDA error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaunchRefusal {
    /// The kernel entry whose law was violated.
    pub kernel: &'static str,
    /// The single clause that failed.
    pub clause: LaunchClause,
    /// The exact quantities that failed it.
    pub detail: String,
}

impl LaunchRefusal {
    /// Name a violated clause.
    pub fn new(kernel: &'static str, clause: LaunchClause, detail: impl Into<String>) -> Self {
        Self {
            kernel,
            clause,
            detail: detail.into(),
        }
    }
}

impl fmt::Display for LaunchRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: launch law clause `{}` refused: {}",
            self.kernel,
            self.clause.name(),
            self.detail
        )
    }
}

impl std::error::Error for LaunchRefusal {}

/// A refusal crosses into the driver-shaped `Result` of this crate without becoming a driver
/// error: the name stays `LAUNCH_LAW_REFUSAL` and the context stays the violated clause, so a
/// caller reading a log can still tell a construction refusal from a card fault.
impl From<LaunchRefusal> for CudaError {
    fn from(refusal: LaunchRefusal) -> CudaError {
        CudaError {
            code: -1,
            name: String::from("LAUNCH_LAW_REFUSAL"),
            message: format!("{}: {}", refusal.kernel, refusal.detail),
            context: refusal.clause.name(),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// D1 — declared arguments
// ---------------------------------------------------------------------------------------------

/// Where an argument must live for the kernel to read it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Residency {
    /// A device allocation reachable by the kernel through its own address space.
    Device,
    /// Page-locked host standing a copy engine may read without a bounce buffer.
    Pinned,
    /// Ordinary pageable host memory.  A kernel never dereferences it; a transport may read it.
    Host,
}

impl Residency {
    /// The residency's own name.
    pub const fn name(self) -> &'static str {
        match self {
            Residency::Device => "device",
            Residency::Pinned => "pinned",
            Residency::Host => "host",
        }
    }
}

/// What the kernel does to an argument.  `Write` means *may be written* and is audited as
/// exclusive: an argument whose read-only character has not been verified in the kernel source is
/// declared `Write`, which is the conservative and truthful reading.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Access {
    /// Read only.  Read spans may alias one another.
    Read,
    /// Written.  A write span may alias nothing else of the same residency.
    Write,
}

/// The element population a declared argument must carry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Extent {
    /// Any population, including zero.  Used where the entry itself accepts an empty face.
    Any,
    /// Exactly this many elements.
    Exactly(usize),
    /// At least this many elements.
    AtLeast(usize),
    /// A positive whole number of rows of this width.
    Rows(usize),
}

impl Extent {
    fn admits(self, elements: usize) -> core::result::Result<(), String> {
        match self {
            Extent::Any => Ok(()),
            Extent::Exactly(n) if elements == n => Ok(()),
            Extent::Exactly(n) => Err(format!("declared exactly {n} elements, presented {elements}")),
            Extent::AtLeast(n) if elements >= n => Ok(()),
            Extent::AtLeast(n) => Err(format!("declared at least {n} elements, presented {elements}")),
            Extent::Rows(0) => Err(String::from("a row width of zero is not an extent")),
            Extent::Rows(width) if elements != 0 && elements.is_multiple_of(width) => Ok(()),
            Extent::Rows(width) => Err(format!(
                "declared a positive whole number of {width}-element rows, presented {elements}"
            )),
        }
    }
}

/// One argument as the kernel declares it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArgumentRequirement {
    /// The argument's name in the entry's signature, in declared order.
    pub name: &'static str,
    /// Where it must live.
    pub residency: Residency,
    /// What the kernel does to it.
    pub access: Access,
    /// The element width in octets.
    pub element_bytes: usize,
    /// The element population it must carry.
    pub extent: Extent,
}

impl ArgumentRequirement {
    /// Declare a device-resident argument.
    pub const fn device(
        name: &'static str,
        access: Access,
        element_bytes: usize,
        extent: Extent,
    ) -> Self {
        Self {
            name,
            residency: Residency::Device,
            access,
            element_bytes,
            extent,
        }
    }

    /// Declare a page-locked host argument (a transport source, never a kernel dereference).
    pub const fn pinned(name: &'static str, access: Access, extent: Extent) -> Self {
        Self {
            name,
            residency: Residency::Pinned,
            access,
            element_bytes: 1,
            extent,
        }
    }

    /// Declare an ordinary host argument.
    pub const fn host(name: &'static str, element_bytes: usize, extent: Extent) -> Self {
        Self {
            name,
            residency: Residency::Host,
            access: Access::Read,
            element_bytes,
            extent,
        }
    }
}

/// One argument as the call site actually presents it.
///
/// **The fields are private.**  A span is a claim that an address range of a stated width and
/// population exists and is reachable by the kernel; nothing outside this crate may author that
/// claim by writing the fields, and nothing may edit one after it was derived from an allocation.
/// The safe public constructors — [`ArgumentSpan::device`], [`ArgumentSpan::pinned`],
/// [`ArgumentSpan::host`], [`DeviceReadSpan::argument`], [`DeviceWriteSpan::argument`] — all take
/// the address and extent *from a live borrow* rather than from the caller's arithmetic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArgumentSpan {
    name: &'static str,
    residency: Residency,
    access: Access,
    address: u64,
    elements: usize,
    element_bytes: usize,
}

impl ArgumentSpan {
    /// The argument's name, matched against the declaration.
    pub const fn name(&self) -> &'static str {
        self.name
    }

    /// Where it actually lives.
    pub const fn residency(&self) -> Residency {
        self.residency
    }

    /// What the caller intends to do to it.
    pub const fn access(&self) -> Access {
        self.access
    }

    /// Its base address: a device pointer, a pinned host pointer, or a host pointer.
    pub const fn address(&self) -> u64 {
        self.address
    }

    /// Its element population.
    pub const fn elements(&self) -> usize {
        self.elements
    }

    /// Its element width in octets.
    pub const fn element_bytes(&self) -> usize {
        self.element_bytes
    }
}

impl ArgumentSpan {
    /// Present a whole typed device allocation.
    pub fn device<T: Copy>(name: &'static str, buffer: &DeviceBuffer<T>, access: Access) -> Self {
        Self {
            name,
            residency: Residency::Device,
            access,
            address: buffer.device_ptr(),
            elements: buffer.len(),
            element_bytes: core::mem::size_of::<T>(),
        }
    }

    /// Present a device span already carved and bounds-proved by another owner (a
    /// [`crate::RegisterSpan`], a [`crate::LiveEventSpan`], a [`DeviceReadSpan`]).
    ///
    /// **Crate-private.**  Its precondition — that `address .. address + elements *
    /// element_bytes` is a live, mapped device range the kernel may touch under `access` — is not
    /// checkable here and is discharged by the span owners in this crate, each of which derives
    /// the address and extent from a borrowed [`DeviceBuffer`].  It was formerly a safe `pub const
    /// fn` over public fields, which let any caller author an arbitrary device address and have
    /// the launch law certify it; that door is closed.
    pub(crate) const fn device_raw(
        name: &'static str,
        address: u64,
        elements: usize,
        element_bytes: usize,
        access: Access,
    ) -> Self {
        Self {
            name,
            residency: Residency::Device,
            access,
            address,
            elements,
            element_bytes,
        }
    }

    /// Present a page-locked host slot.
    pub fn pinned(name: &'static str, host: &PinnedHost, access: Access) -> Self {
        Self {
            name,
            residency: Residency::Pinned,
            access,
            address: host.as_ptr() as u64,
            elements: host.octets(),
            element_bytes: 1,
        }
    }

    /// Present an ordinary host slice.
    pub fn host<T>(name: &'static str, values: &[T]) -> Self {
        Self {
            name,
            residency: Residency::Host,
            access: Access::Read,
            address: values.as_ptr() as u64,
            elements: values.len(),
            element_bytes: core::mem::size_of::<T>(),
        }
    }

    /// The span's octet extent, or `None` when the declared element count and width do not
    /// multiply inside `usize`.
    pub fn bytes(&self) -> Option<usize> {
        self.elements.checked_mul(self.element_bytes)
    }
}

// ---------------------------------------------------------------------------------------------
// D1 — declared scalar parameters
// ---------------------------------------------------------------------------------------------

/// The width of a declared scalar parameter, in the entry's own wire.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarWidth {
    /// A 32-bit scalar: the driver reads four octets.
    U32,
    /// A 64-bit scalar: the driver reads eight octets.
    U64,
}

impl ScalarWidth {
    /// The scalar's own name.
    pub const fn name(self) -> &'static str {
        match self {
            ScalarWidth::U32 => "u32",
            ScalarWidth::U64 => "u64",
        }
    }

    /// The largest value the wire carries.
    const fn ceiling(self) -> u64 {
        match self {
            ScalarWidth::U32 => u32::MAX as u64,
            ScalarWidth::U64 => u64::MAX,
        }
    }
}

/// One scalar parameter as the kernel declares it.
///
/// [definition] A scalar is declared **at a position in the parameter block**, not appended by
/// convention: `after_arguments` is how many of the entry's `(pointer, extent)` buffer pairs
/// precede it.  `regional_contacts` interleaves its `standing_axis` after the first pair, and that
/// is a declaration here rather than a hand-built parameter array at the call site.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScalarRequirement {
    /// The parameter's name in the entry's signature.
    pub name: &'static str,
    /// Its width in the entry's wire.
    pub width: ScalarWidth,
    /// How many declared buffer arguments precede it in the parameter block.
    pub after_arguments: usize,
}

impl ScalarRequirement {
    /// Declare a scalar that follows `after_arguments` buffer pairs.
    pub const fn at(name: &'static str, width: ScalarWidth, after_arguments: usize) -> Self {
        Self {
            name,
            width,
            after_arguments,
        }
    }

    /// Declare a scalar appended after every buffer pair of an entry with `arguments` of them.
    pub const fn trailing(name: &'static str, width: ScalarWidth, arguments: usize) -> Self {
        Self::at(name, width, arguments)
    }
}

/// One scalar parameter as the call site presents it.  It is matched by name and width against the
/// declaration, so a caller cannot slide a value into the wrong slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScalarArgument {
    /// The parameter's name, matched against the declaration.
    pub name: &'static str,
    /// The value, widened to the largest wire.  A value past the declared width is a refusal.
    pub value: u64,
}

impl ScalarArgument {
    /// Present a scalar by name.
    pub const fn new(name: &'static str, value: u64) -> Self {
        Self { name, value }
    }
}

/// The scalar face recorded on a receipt.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScalarReceipt {
    /// The declared name.
    pub name: &'static str,
    /// The declared width.
    pub width: ScalarWidth,
    /// How many buffer pairs precede it.
    pub after_arguments: usize,
    /// The proved value.
    pub value: u64,
}

/// The argument face recorded on a receipt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgumentReceipt {
    /// The declared name.
    pub name: &'static str,
    /// The proved base address.
    pub address: u64,
    /// The proved residency.
    pub residency: Residency,
    /// The proved access.
    pub access: Access,
    /// The proved element population.
    pub elements: usize,
    /// The proved octet extent.
    pub bytes: usize,
}

// ---------------------------------------------------------------------------------------------
// D1 — block, shared, coverage, stream
// ---------------------------------------------------------------------------------------------

/// The block shape a kernel constrains.  Every field is a kernel declaration, never a device
/// reading; the device readings live in [`LaunchLimits`] and are compared against these.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockConstraint {
    /// The kernel requires exactly this block (a cooperative entry whose barrier width is fixed).
    pub exact: Option<Dim3>,
    /// The block thread count must be a multiple of this divisor.
    pub multiple_of: Option<u32>,
    /// The block thread count must be a whole number of warps, as the device reports the warp.
    pub warp_multiple: bool,
    /// The kernel's own cap on the block thread count, tighter than the device's.
    pub max_threads: Option<u32>,
}

impl BlockConstraint {
    /// No kernel-side block constraint; the device and the lowered function decide.
    pub const ANY: BlockConstraint = BlockConstraint {
        exact: None,
        multiple_of: None,
        warp_multiple: false,
        max_threads: None,
    };

    /// The kernel requires exactly this block.
    pub const fn exactly(block: Dim3) -> BlockConstraint {
        BlockConstraint {
            exact: Some(block),
            ..BlockConstraint::ANY
        }
    }

    /// The kernel requires a block thread count divisible by `divisor`.
    pub const fn multiple_of(divisor: u32) -> BlockConstraint {
        BlockConstraint {
            multiple_of: Some(divisor),
            ..BlockConstraint::ANY
        }
    }
}

/// The dynamic shared extent a kernel needs, **as a function of the block shape** rather than as a
/// number.  `bytes_for` evaluates it with checked arithmetic; a block whose shared need does not
/// fit `u32` is a refusal, not a truncation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SharedRequirement {
    /// Octets needed once per block.
    pub per_block_bytes: u32,
    /// Octets needed once per thread of the block.
    pub per_thread_bytes: u32,
}

impl SharedRequirement {
    /// An entry that declares no dynamic shared surface.
    pub const NONE: SharedRequirement = SharedRequirement {
        per_block_bytes: 0,
        per_thread_bytes: 0,
    };

    /// Evaluate the declared shared extent at a block shape.
    pub fn bytes_for(&self, block_threads: u32) -> core::result::Result<u32, String> {
        let per_thread = self.per_thread_bytes.checked_mul(block_threads).ok_or_else(|| {
            format!(
                "per-thread shared {} times block {block_threads} exceeds the u32 shared wire",
                self.per_thread_bytes
            )
        })?;
        per_thread.checked_add(self.per_block_bytes).ok_or_else(|| {
            format!(
                "per-block shared {} added to {per_thread} exceeds the u32 shared wire",
                self.per_block_bytes
            )
        })
    }
}

/// How the thread population relates to the declared element extent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Coverage {
    /// `threads == extent`.  Every element has exactly one thread and no thread is idle.  The Lean
    /// statement is `linear_thread_bijective`: under the launch's own linearization
    /// `blockIdx * blockDim + threadIdx` the thread-index-to-element map is a *bijection* onto
    /// `[0, extent)`.
    Exact,
    /// `threads >= extent`, with the surplus strictly below one block, and the kernel carrying the
    /// in-range guard.  The Lean statement is `foldl_guarded_cover`.
    Guarded,
    /// The kernel strides by `grid.x * block.x` until the extent is covered.  The stride must be
    /// positive and representable in the `u32` wire the kernel reads.
    Strided,
    /// **The mouth was handed a shape and no element extent.**  Every arithmetic, limit, residency
    /// and aliasing clause is still proved; the coverage clause is *deferred and named in the
    /// receipt* because there is no declared extent to relate the thread population to.  A caller
    /// that knows its extent uses one of the three forms above and gets a complete receipt.
    Undeclared,
}

/// The stream ordering a kernel declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamRequirement {
    /// The entry is launched on the context's default current.
    Default,
    /// The entry must be launched on a declared ordered current.
    Ordered,
}

/// The stream a lawful launch actually used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamIdentity {
    /// The context's default current.
    Default,
    /// A declared ordered current, with the non-blocking character it was created with.
    Ordered {
        /// Whether the stream was created `CU_STREAM_NON_BLOCKING`.
        nonblocking: bool,
    },
}

// ---------------------------------------------------------------------------------------------
// D1 — device limits, read and never authored
// ---------------------------------------------------------------------------------------------

/// `CU_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_X`.
const MAX_BLOCK_DIM_X: DeviceAttribute = DeviceAttribute::from_raw(2);
/// `CU_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_Y`.
const MAX_BLOCK_DIM_Y: DeviceAttribute = DeviceAttribute::from_raw(3);
/// `CU_DEVICE_ATTRIBUTE_MAX_BLOCK_DIM_Z`.
const MAX_BLOCK_DIM_Z: DeviceAttribute = DeviceAttribute::from_raw(4);
/// `CU_DEVICE_ATTRIBUTE_MAX_SHARED_MEMORY_PER_BLOCK`.
const MAX_SHARED_MEMORY_PER_BLOCK: DeviceAttribute = DeviceAttribute::from_raw(8);
/// `CU_DEVICE_ATTRIBUTE_WARP_SIZE`.
const WARP_SIZE: DeviceAttribute = DeviceAttribute::from_raw(10);

/// Every bound a launch is proved against.  Fields are private: outside `cfg(test)` the only way
/// to obtain one is to read the mounted device and the lowered entry.  A bound the caller's
/// evidence does not carry stays `None` and its clause is **deferred in the receipt**, which is
/// how this owner declines to invent `1024` or `65535`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LaunchLimits {
    function_max_threads_per_block: u32,
    function_static_shared_bytes: u32,
    device_max_threads_per_block: Option<u32>,
    max_grid: Option<Dim3>,
    max_block: Option<Dim3>,
    max_shared_bytes_per_block: Option<u32>,
    warp: Option<u32>,
    multiprocessors: Option<u32>,
}

fn positive_attribute(device: &Device, attribute: DeviceAttribute, field: &str) -> Result<u32> {
    let value = device.attribute(attribute)?;
    u32::try_from(value)
        .ok()
        .filter(|value| *value > 0)
        .ok_or_else(|| CudaError {
            code: -1,
            name: String::from("INVALID_DRIVER_VALUE"),
            message: format!("driver reported {field}={value}; expected a positive extent"),
            context: "LaunchLimits::read",
        })
}

impl LaunchLimits {
    /// **The complete path.**  Every bound is read from the mounted device and the lowered entry:
    /// per-dimension grid and block extents, the device and function thread caps, the per-block
    /// shared extent, the warp, and the multiprocessor population.  Nothing is deferred.
    pub fn read(device: &Device, function: &Function<'_>) -> Result<LaunchLimits> {
        Ok(LaunchLimits {
            function_max_threads_per_block: function.max_threads_per_block()?,
            function_static_shared_bytes: function.static_shared_bytes()?,
            device_max_threads_per_block: Some(positive_attribute(
                device,
                DeviceAttribute::MAX_THREADS_PER_BLOCK,
                "max threads per block",
            )?),
            max_grid: Some(Dim3 {
                x: positive_attribute(device, DeviceAttribute::MAX_GRID_DIM_X, "max grid X")?,
                y: positive_attribute(device, DeviceAttribute::MAX_GRID_DIM_Y, "max grid Y")?,
                z: positive_attribute(device, DeviceAttribute::MAX_GRID_DIM_Z, "max grid Z")?,
            }),
            max_block: Some(Dim3 {
                x: positive_attribute(device, MAX_BLOCK_DIM_X, "max block X")?,
                y: positive_attribute(device, MAX_BLOCK_DIM_Y, "max block Y")?,
                z: positive_attribute(device, MAX_BLOCK_DIM_Z, "max block Z")?,
            }),
            max_shared_bytes_per_block: Some(positive_attribute(
                device,
                MAX_SHARED_MEMORY_PER_BLOCK,
                "max shared memory per block",
            )?),
            warp: Some(positive_attribute(device, WARP_SIZE, "warp size")?),
            multiprocessors: Some(positive_attribute(
                device,
                DeviceAttribute::MULTIPROCESSOR_COUNT,
                "multiprocessor count",
            )?),
        })
    }

    /// **The census path.**  A caller already holding a [`LaunchCensus`] — itself read from the
    /// device by `Device::launch_census` — completes it with the lowered entry's own attributes.
    /// The per-dimension block extents, the per-block shared extent and the warp are not in a
    /// census, so their clauses are deferred rather than assumed.  For a one-dimensional block
    /// (`y == z == 1`) the per-dimension block clause is subsumed by the thread-count clause,
    /// which this path does prove.
    pub fn from_census(census: LaunchCensus, function: &Function<'_>) -> Result<LaunchLimits> {
        Ok(LaunchLimits {
            function_max_threads_per_block: function.max_threads_per_block()?,
            function_static_shared_bytes: function.static_shared_bytes()?,
            device_max_threads_per_block: Some(census.max_threads_per_block),
            max_grid: Some(census.max_grid),
            max_block: None,
            max_shared_bytes_per_block: None,
            warp: None,
            multiprocessors: Some(census.multiprocessor_count),
        })
    }

    /// **The function-only path.**  A launch mouth that was handed no device evidence at all can
    /// still prove the lowered entry's own caps and every arithmetic clause.  The device clauses
    /// are deferred and named in the receipt; this is testimony about the actual scope of the
    /// proof, not a silent default.
    pub fn from_function(function: &Function<'_>) -> Result<LaunchLimits> {
        Ok(LaunchLimits {
            function_max_threads_per_block: function.max_threads_per_block()?,
            function_static_shared_bytes: function.static_shared_bytes()?,
            device_max_threads_per_block: None,
            max_grid: None,
            max_block: None,
            max_shared_bytes_per_block: None,
            warp: None,
            multiprocessors: None,
        })
    }

    /// The lowered entry's own block cap.
    pub const fn function_max_threads_per_block(&self) -> u32 {
        self.function_max_threads_per_block
    }

    /// The lowered entry's static shared surface.
    pub const fn function_static_shared_bytes(&self) -> u32 {
        self.function_static_shared_bytes
    }

    /// The device's block cap, when the caller's evidence carries it.
    pub const fn device_max_threads_per_block(&self) -> Option<u32> {
        self.device_max_threads_per_block
    }

    /// The device's per-dimension grid extents, when the caller's evidence carries them.
    pub const fn max_grid(&self) -> Option<Dim3> {
        self.max_grid
    }

    /// The device's per-dimension block extents, when the caller's evidence carries them.
    pub const fn max_block(&self) -> Option<Dim3> {
        self.max_block
    }

    /// The device's per-block shared extent, when the caller's evidence carries it.
    pub const fn max_shared_bytes_per_block(&self) -> Option<u32> {
        self.max_shared_bytes_per_block
    }

    /// The device's warp, when the caller's evidence carries it.
    pub const fn warp(&self) -> Option<u32> {
        self.warp
    }

    /// The device's multiprocessor population, when the caller's evidence carries it.
    pub const fn multiprocessors(&self) -> Option<u32> {
        self.multiprocessors
    }

    /// The narrowest block cap the caller's evidence proves.
    fn block_cap(&self) -> u32 {
        match self.device_max_threads_per_block {
            Some(device) => self.function_max_threads_per_block.min(device),
            None => self.function_max_threads_per_block,
        }
    }

    /// Build the limits the caller's declared [`LaunchEvidence`] affords for one lowered entry.
    pub fn from_evidence(
        evidence: LaunchEvidence<'_>,
        function: &Function<'_>,
    ) -> Result<LaunchLimits> {
        match evidence {
            LaunchEvidence::Device(device) => LaunchLimits::read(device, function),
            LaunchEvidence::Census(census) => LaunchLimits::from_census(census, function),
            LaunchEvidence::FunctionOnly => LaunchLimits::from_function(function),
        }
    }

    /// A synthetic limits record for cpu tests.  It is compiled only under `cfg(test)` precisely
    /// so no production path can author a device bound.
    #[cfg(test)]
    pub(crate) const fn synthetic(
        function_max_threads_per_block: u32,
        device_max_threads_per_block: Option<u32>,
        max_grid: Option<Dim3>,
        max_block: Option<Dim3>,
        max_shared_bytes_per_block: Option<u32>,
        warp: Option<u32>,
    ) -> LaunchLimits {
        LaunchLimits {
            function_max_threads_per_block,
            function_static_shared_bytes: 0,
            device_max_threads_per_block,
            max_grid,
            max_block,
            max_shared_bytes_per_block,
            warp,
            multiprocessors: None,
        }
    }
}

/// **The device evidence a launch mouth was handed, said aloud by the caller.**
///
/// [definition] A mouth that silently fell back to the lowered function's own attributes deferred
/// the device clauses without the caller ever choosing to.  This enum makes that choice explicit:
/// every migrated launcher takes one, and [`LaunchEvidence::FunctionOnly`] is a caller's stated
/// declaration that it is offering no device reading, not a default the owner invented.
#[derive(Debug, Clone, Copy)]
pub enum LaunchEvidence<'d> {
    /// The mounted card itself.  Every bound is read; nothing is deferred.
    Device(&'d Device),
    /// A [`LaunchCensus`] the caller already took off the card.  The per-dimension block extents,
    /// the per-block shared extent and the warp are not in a census, so those clauses are deferred
    /// and named in the receipt.
    Census(LaunchCensus),
    /// No device evidence at all.  Every arithmetic, function-cap, residency, access and aliasing
    /// clause is still proved; every device clause is deferred and named.
    FunctionOnly,
}

impl LaunchEvidence<'_> {
    /// The evidence's own name, for a receipt line.
    pub const fn name(&self) -> &'static str {
        match self {
            LaunchEvidence::Device(_) => "device",
            LaunchEvidence::Census(_) => "census",
            LaunchEvidence::FunctionOnly => "function-only",
        }
    }
}

// ---------------------------------------------------------------------------------------------
// D1 — the shape and the requirement
// ---------------------------------------------------------------------------------------------

/// The shape a caller offers for proof.  The Lean counterpart flattens it to
/// `DeviceLaunchLaw.LaunchShape`; the flattening here is the same and is performed with checked
/// arithmetic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LaunchShape {
    /// The grid extent.
    pub grid: Dim3,
    /// The block extent.
    pub block: Dim3,
    /// The dynamic shared octets per block.
    pub shared_bytes: u32,
}

impl LaunchShape {
    /// A one-dimensional shape with no dynamic shared surface.
    pub const fn linear(grid_x: u32, block_x: u32) -> LaunchShape {
        LaunchShape {
            grid: Dim3 {
                x: grid_x,
                y: 1,
                z: 1,
            },
            block: Dim3 {
                x: block_x,
                y: 1,
                z: 1,
            },
            shared_bytes: 0,
        }
    }

    /// Adopt a shape already derived by `Function::linear_launch` / `Function::block_launch`.
    pub const fn from_linear(launch: LinearLaunch, shared_bytes: u32) -> LaunchShape {
        LaunchShape {
            grid: launch.grid,
            block: launch.block,
            shared_bytes,
        }
    }

    /// The block thread count, or `None` when the dimensions do not multiply inside `u32`.
    pub fn block_threads(&self) -> Option<u32> {
        self.block
            .x
            .checked_mul(self.block.y)?
            .checked_mul(self.block.z)
    }

    /// The block population, or `None` when the dimensions do not multiply inside `u64`.
    pub fn grid_blocks(&self) -> Option<u64> {
        (self.grid.x as u64)
            .checked_mul(self.grid.y as u64)?
            .checked_mul(self.grid.z as u64)
    }

    /// The total thread population, or `None` when it does not fit `u64`.
    pub fn threads(&self) -> Option<u64> {
        self.grid_blocks()?
            .checked_mul(self.block_threads()? as u64)
    }

    /// The X stride the kernel reads, or `None` when it does not fit the `u32` wire.
    pub fn x_stride(&self) -> Option<u32> {
        self.grid.x.checked_mul(self.block.x)
    }
}

/// What one kernel entry requires of every launch of it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaunchRequirement {
    /// The entry symbol.
    pub kernel: &'static str,
    /// The element population the launch must cover.
    pub extent: u64,
    /// How the thread population must relate to that extent.
    pub coverage: Coverage,
    /// The block shape the kernel constrains.
    pub block: BlockConstraint,
    /// The dynamic shared surface, as a function of the block shape.
    pub shared: SharedRequirement,
    /// The declared arguments, in signature order.
    pub arguments: Vec<ArgumentRequirement>,
    /// The declared scalar parameters, each at its position in the parameter block.
    pub scalars: Vec<ScalarRequirement>,
    /// The stream ordering.
    pub stream: StreamRequirement,
}

impl LaunchRequirement {
    /// Declare a guarded one-dimensional cover of `extent` elements with no dynamic shared
    /// surface, on the default current.
    pub fn guarded(
        kernel: &'static str,
        extent: u64,
        arguments: Vec<ArgumentRequirement>,
    ) -> LaunchRequirement {
        LaunchRequirement {
            kernel,
            extent,
            coverage: Coverage::Guarded,
            block: BlockConstraint::ANY,
            shared: SharedRequirement::NONE,
            arguments,
            scalars: Vec::new(),
            stream: StreamRequirement::Default,
        }
    }

    /// Declare the entry's scalar parameters, each at its position in the parameter block.
    pub fn with_scalars(mut self, scalars: Vec<ScalarRequirement>) -> LaunchRequirement {
        self.scalars = scalars;
        self
    }

    /// Declare a strided cover: the kernel repeats by `grid.x * block.x` until the extent is done.
    pub fn strided(
        kernel: &'static str,
        extent: u64,
        arguments: Vec<ArgumentRequirement>,
    ) -> LaunchRequirement {
        LaunchRequirement {
            coverage: Coverage::Strided,
            ..LaunchRequirement::guarded(kernel, extent, arguments)
        }
    }

    /// Declare an exact cover at a fixed block: one thread per element, no idle thread.
    pub fn exact(
        kernel: &'static str,
        extent: u64,
        block: Dim3,
        arguments: Vec<ArgumentRequirement>,
    ) -> LaunchRequirement {
        LaunchRequirement {
            coverage: Coverage::Exact,
            block: BlockConstraint::exactly(block),
            ..LaunchRequirement::guarded(kernel, extent, arguments)
        }
    }

    /// Declare a mouth that receives its shape from the caller and no element extent.  Every
    /// clause but coverage is still proved; the receipt names what was deferred.
    pub fn undeclared(
        kernel: &'static str,
        arguments: Vec<ArgumentRequirement>,
    ) -> LaunchRequirement {
        LaunchRequirement {
            coverage: Coverage::Undeclared,
            ..LaunchRequirement::guarded(kernel, 0, arguments)
        }
    }

    /// Require a declared ordered current rather than the context default.
    pub fn on_ordered_stream(mut self) -> LaunchRequirement {
        self.stream = StreamRequirement::Ordered;
        self
    }

    /// **Derive** the covering shape from the declared extent and the caller's device evidence.
    ///
    /// This is the executable form of `DeviceLaunchLaw.LaunchShape.cover`: ceiling division at the
    /// widest admissible block, folding X into Y when X saturates the device's grid extent or the
    /// `u32` stride wire.  A derived shape is **not** thereby lawful — it is submitted to
    /// [`LawfulLaunch::prove`] exactly like a caller-authored one.
    pub fn cover_with(&self, limits: &LaunchLimits) -> Lawful<LaunchShape> {
        let refuse = |clause: LaunchClause, detail: String| LaunchRefusal::new(self.kernel, clause, detail);
        if matches!(self.coverage, Coverage::Undeclared) {
            return Err(refuse(
                LaunchClause::PositiveExtent,
                String::from("a shape cannot be derived from an undeclared element extent"),
            ));
        }
        if self.extent == 0 {
            return Err(refuse(
                LaunchClause::PositiveExtent,
                String::from("a launch carries one positive element extent"),
            ));
        }
        let block = match self.block.exact {
            Some(block) => block,
            None => {
                if matches!(self.coverage, Coverage::Exact) {
                    return Err(refuse(
                        LaunchClause::BlockExact,
                        String::from("an exact cover declares its own block shape"),
                    ));
                }
                let mut threads = limits.block_cap();
                if let Some(cap) = self.block.max_threads {
                    threads = threads.min(cap);
                }
                if let Some(divisor) = self.block.multiple_of {
                    if divisor == 0 {
                        return Err(refuse(
                            LaunchClause::BlockMultiple,
                            String::from("a block divisor of zero is not a constraint"),
                        ));
                    }
                    threads = threads / divisor * divisor;
                }
                if self.block.warp_multiple {
                    match limits.warp {
                        Some(warp) => threads = threads / warp * warp,
                        None => {
                            return Err(refuse(
                                LaunchClause::BlockWarpMultiple,
                                String::from(
                                    "the entry declares a warp-multiple block and the caller's \
                                     evidence carries no device warp; read the device",
                                ),
                            ))
                        }
                    }
                }
                if threads == 0 {
                    return Err(refuse(
                        LaunchClause::PositiveBlock,
                        String::from("the declared block constraints admit no positive block"),
                    ));
                }
                Dim3::x(threads)
            }
        };
        let block_threads = LaunchShape {
            grid: Dim3::x(1),
            block,
            shared_bytes: 0,
        }
        .block_threads()
        .ok_or_else(|| {
            refuse(
                LaunchClause::ThreadProductRepresentable,
                format!("block {}x{}x{} overflows u32", block.x, block.y, block.z),
            )
        })?;
        if block_threads == 0 {
            return Err(refuse(
                LaunchClause::PositiveBlock,
                String::from("a block carries one positive thread population"),
            ));
        }
        let shared_bytes = self
            .shared
            .bytes_for(block_threads)
            .map_err(|detail| refuse(LaunchClause::SharedBytesMatch, detail))?;

        if matches!(self.coverage, Coverage::Exact) {
            if !self.extent.is_multiple_of(block_threads as u64) {
                return Err(refuse(
                    LaunchClause::CoverageExact,
                    format!(
                        "extent {} is not a whole number of {block_threads}-thread blocks",
                        self.extent
                    ),
                ));
            }
            let grid_x = u32::try_from(self.extent / block_threads as u64).map_err(|_| {
                refuse(
                    LaunchClause::GridWithinDevice,
                    format!("exact cover of {} needs a grid beyond the u32 wire", self.extent),
                )
            })?;
            return Ok(LaunchShape {
                grid: Dim3::x(grid_x),
                block,
                shared_bytes,
            });
        }

        let blocks = self.extent.div_ceil(block_threads as u64);
        // The kernel's X stride is a u32; a grid wider than this could not be addressed by it.
        let stride_blocks = (u32::MAX / block_threads) as u64;
        let grid_extent = match limits.max_grid {
            Some(grid) => (grid.x as u64).min(stride_blocks),
            None => stride_blocks,
        };
        let grid_x = u32::try_from(blocks.min(grid_extent)).map_err(|_| {
            refuse(
                LaunchClause::GridWithinDevice,
                String::from("the admissible X grid exceeds the u32 wire"),
            )
        })?;
        if grid_x == 0 {
            return Err(refuse(
                LaunchClause::PositiveGrid,
                String::from("the function and device afford no X block"),
            ));
        }
        let grid_y = blocks.div_ceil(grid_x as u64);
        let grid_y = u32::try_from(grid_y).map_err(|_| {
            refuse(
                LaunchClause::GridWithinDevice,
                format!("extent {} needs a Y grid beyond the u32 wire", self.extent),
            )
        })?;
        if let Some(grid) = limits.max_grid {
            if grid_y > grid.y {
                return Err(refuse(
                    LaunchClause::GridWithinDevice,
                    format!(
                        "extent {} exceeds the device X/Y launch aperture {}x{} at block {block_threads}",
                        self.extent, grid.x, grid.y
                    ),
                ));
            }
        }
        Ok(LaunchShape {
            grid: Dim3 {
                x: grid_x,
                y: grid_y,
                z: 1,
            },
            block,
            shared_bytes,
        })
    }
}

// ---------------------------------------------------------------------------------------------
// D1 — the receipt and the proof
// ---------------------------------------------------------------------------------------------

/// The receipt a lawful launch owes.  It names the kernel, the proved shape, the extents, the
/// stream, and **which clauses were proved and which were deferred** — so a reader can tell the
/// actual scope of the proof without re-deriving it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaunchReceipt {
    /// The entry symbol.
    pub kernel: &'static str,
    /// The proved grid.
    pub grid: Dim3,
    /// The proved block.
    pub block: Dim3,
    /// The proved thread population.
    pub threads: u64,
    /// The declared element extent.
    pub extent: u64,
    /// The threads the in-range guard must turn into no-ops.
    pub guard_threads: u64,
    /// The X stride the kernel reads.
    pub x_stride: u32,
    /// The proved dynamic shared octets per block.
    pub shared_bytes: u32,
    /// The stream the launch was ordered on.
    pub stream: StreamIdentity,
    /// The proved arguments, in signature order.
    pub arguments: Vec<ArgumentReceipt>,
    /// The proved scalar parameters, in parameter-block order.
    pub scalars: Vec<ScalarReceipt>,
    /// Every clause this launch proved.  **Private**, with [`LaunchReceipt::proved`] to read it:
    /// the clause lists are what [`LaunchReceipt::fully_proved`] decides on, so they may not be
    /// authored or edited from outside.  Their privacy also makes a struct-literal
    /// `LaunchReceipt { .. }` impossible outside this module, so a receipt is always one this
    /// owner issued.
    proved: Vec<LaunchClause>,
    /// Every clause deferred because the caller's evidence did not carry the bound.  A deferred
    /// clause is stated, never assumed.  Private, for the same reason.
    deferred: Vec<LaunchClause>,
}

impl LaunchReceipt {
    /// Every clause this launch proved, in clause order.
    pub fn proved(&self) -> &[LaunchClause] {
        &self.proved
    }

    /// Every clause deferred for want of evidence, in clause order.
    pub fn deferred(&self) -> &[LaunchClause] {
        &self.deferred
    }

    /// Whether a named clause was proved.
    pub fn proves(&self, clause: LaunchClause) -> bool {
        self.proved.contains(&clause)
    }

    /// Whether a named clause was deferred for want of evidence.
    pub fn defers(&self, clause: LaunchClause) -> bool {
        self.deferred.contains(&clause)
    }

    /// Whether this receipt deferred nothing.
    pub fn is_fully_proved(&self) -> bool {
        self.deferred.is_empty()
    }

    /// **Take the type-level witness that nothing was deferred, or `None`.**
    ///
    /// A receipt with deferred device clauses and a completely proved one were formerly the same
    /// type, so a consumer that needed the complete proof could not ask for it in its signature.
    /// [`FullyProvedReceipt`] is constructible only through this accessor and only when
    /// `deferred` is empty, so a function taking one cannot be handed a partial proof.
    pub fn fully_proved(self) -> Option<FullyProvedReceipt> {
        if self.deferred.is_empty() {
            Some(FullyProvedReceipt(self))
        } else {
            None
        }
    }

    /// The same distinction as a total split, for a caller that must handle both.
    pub fn proof_scope(self) -> ProofScope {
        if self.deferred.is_empty() {
            ProofScope::FullyProved(FullyProvedReceipt(self))
        } else {
            ProofScope::Deferred(DeferredReceipt(self))
        }
    }
}

/// **A receipt every clause of which was proved.**  Its only constructor is
/// [`LaunchReceipt::fully_proved`], which refuses a receipt carrying any deferred clause, so this
/// type *is* the statement "no bound in this launch was taken on trust".
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FullyProvedReceipt(LaunchReceipt);

impl FullyProvedReceipt {
    /// The receipt itself.
    pub const fn receipt(&self) -> &LaunchReceipt {
        &self.0
    }

    /// Give up the witness and keep the receipt.
    pub fn into_receipt(self) -> LaunchReceipt {
        self.0
    }
}

impl fmt::Display for FullyProvedReceipt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} fully-proved", self.0)
    }
}

/// **A receipt with one or more clauses deferred for want of evidence**, which it names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeferredReceipt(LaunchReceipt);

impl DeferredReceipt {
    /// The receipt itself.
    pub const fn receipt(&self) -> &LaunchReceipt {
        &self.0
    }

    /// The clauses this launch did not prove.  Never empty.
    pub fn deferred(&self) -> &[LaunchClause] {
        &self.0.deferred
    }

    /// Give up the receipt.
    pub fn into_receipt(self) -> LaunchReceipt {
        self.0
    }
}

impl fmt::Display for DeferredReceipt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let names: Vec<&'static str> = self.0.deferred.iter().map(|c| c.name()).collect();
        write!(f, "{} deferred[{}]", self.0, names.join(","))
    }
}

/// The total split of a receipt by the scope of its proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofScope {
    /// Nothing was deferred.
    FullyProved(FullyProvedReceipt),
    /// One or more clauses were deferred and are named.
    Deferred(DeferredReceipt),
}

impl fmt::Display for LaunchReceipt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} grid={}x{}x{} block={}x{}x{} threads={} extent={} guard={} stride={} shared={} proved={} deferred={}",
            self.kernel,
            self.grid.x,
            self.grid.y,
            self.grid.z,
            self.block.x,
            self.block.y,
            self.block.z,
            self.threads,
            self.extent,
            self.guard_threads,
            self.x_stride,
            self.shared_bytes,
            self.proved.len(),
            self.deferred.len(),
        )
    }
}

/// A launch whose shape, residency and arithmetic have been proved against its kernel's declared
/// [`LaunchRequirement`].  It is the only value in this crate that can reach `cuLaunchKernel`
/// through [`LawfulLaunch::enact`], and it cannot be constructed except by [`LawfulLaunch::prove`].
///
/// **It is deliberately not `Clone`.**  One proof is one enactment: [`LawfulLaunch::enact`]
/// consumes `self`, and a cloneable proof would let one proof issue two launches — including two
/// launches writing the same audited spans, which the aliasing audit proved disjoint *within one*
/// launch and says nothing about across two.
#[derive(Debug, PartialEq, Eq)]
#[must_use = "a proved launch that is never enacted issues no work; drop it explicitly if that is meant"]
pub struct LawfulLaunch {
    receipt: LaunchReceipt,
    scalars: Vec<ScalarRequirement>,
    stream: StreamRequirement,
}

impl LawfulLaunch {
    /// Prove the launch law, or refuse naming the single clause that failed.
    ///
    /// Every arithmetic step here is checked: block and grid products, the thread population, the
    /// `u32` stride wire, each argument's octet extent.  Nothing wraps and nothing saturates.
    pub fn prove(
        requirement: &LaunchRequirement,
        limits: &LaunchLimits,
        shape: LaunchShape,
        arguments: &[ArgumentSpan],
    ) -> Lawful<LawfulLaunch> {
        let kernel = requirement.kernel;
        let refuse =
            |clause: LaunchClause, detail: String| LaunchRefusal::new(kernel, clause, detail);
        let mut proved: Vec<LaunchClause> = Vec::new();
        let mut deferred: Vec<LaunchClause> = Vec::new();

        if matches!(requirement.coverage, Coverage::Undeclared) {
            deferred.push(LaunchClause::PositiveExtent);
        } else if requirement.extent == 0 {
            return Err(refuse(
                LaunchClause::PositiveExtent,
                String::from("a launch carries one positive element extent"),
            ));
        } else {
            proved.push(LaunchClause::PositiveExtent);
        }

        if shape.block.x == 0 || shape.block.y == 0 || shape.block.z == 0 {
            return Err(refuse(
                LaunchClause::PositiveBlock,
                format!(
                    "block {}x{}x{} carries a zero dimension",
                    shape.block.x, shape.block.y, shape.block.z
                ),
            ));
        }
        proved.push(LaunchClause::PositiveBlock);

        if shape.grid.x == 0 || shape.grid.y == 0 || shape.grid.z == 0 {
            return Err(refuse(
                LaunchClause::PositiveGrid,
                format!(
                    "grid {}x{}x{} carries a zero dimension",
                    shape.grid.x, shape.grid.y, shape.grid.z
                ),
            ));
        }
        proved.push(LaunchClause::PositiveGrid);

        let block_threads = shape.block_threads().ok_or_else(|| {
            refuse(
                LaunchClause::ThreadProductRepresentable,
                format!(
                    "block {}x{}x{} overflows the u32 thread product",
                    shape.block.x, shape.block.y, shape.block.z
                ),
            )
        })?;
        let grid_blocks = shape.grid_blocks().ok_or_else(|| {
            refuse(
                LaunchClause::ThreadProductRepresentable,
                format!(
                    "grid {}x{}x{} overflows the u64 block product",
                    shape.grid.x, shape.grid.y, shape.grid.z
                ),
            )
        })?;
        let threads = grid_blocks.checked_mul(block_threads as u64).ok_or_else(|| {
            refuse(
                LaunchClause::ThreadProductRepresentable,
                format!("grid {grid_blocks} blocks times block {block_threads} overflows u64"),
            )
        })?;
        proved.push(LaunchClause::ThreadProductRepresentable);

        let x_stride = shape.x_stride().ok_or_else(|| {
            refuse(
                LaunchClause::StrideRepresentable,
                format!(
                    "grid X {} times block X {} exceeds the u32 stride wire the kernel reads",
                    shape.grid.x, shape.block.x
                ),
            )
        })?;
        proved.push(LaunchClause::StrideRepresentable);

        // --- the kernel's own block constraints -------------------------------------------------
        if let Some(exact) = requirement.block.exact {
            if shape.block != exact {
                return Err(refuse(
                    LaunchClause::BlockExact,
                    format!(
                        "the entry declares block {}x{}x{}; the call site offered {}x{}x{}",
                        exact.x, exact.y, exact.z, shape.block.x, shape.block.y, shape.block.z
                    ),
                ));
            }
            proved.push(LaunchClause::BlockExact);
        }
        if let Some(divisor) = requirement.block.multiple_of {
            if divisor == 0 || block_threads % divisor != 0 {
                return Err(refuse(
                    LaunchClause::BlockMultiple,
                    format!("block {block_threads} is not a multiple of the declared {divisor}"),
                ));
            }
            proved.push(LaunchClause::BlockMultiple);
        }
        if requirement.block.warp_multiple {
            match limits.warp {
                Some(warp) if warp > 0 && block_threads % warp == 0 => {
                    proved.push(LaunchClause::BlockWarpMultiple)
                }
                Some(warp) => {
                    return Err(refuse(
                        LaunchClause::BlockWarpMultiple,
                        format!("block {block_threads} is not a whole number of {warp}-lane warps"),
                    ))
                }
                None => deferred.push(LaunchClause::BlockWarpMultiple),
            }
        }
        if let Some(cap) = requirement.block.max_threads {
            if block_threads > cap {
                return Err(refuse(
                    LaunchClause::BlockWithinDeclared,
                    format!("block {block_threads} exceeds the entry's own cap {cap}"),
                ));
            }
            proved.push(LaunchClause::BlockWithinDeclared);
        }

        // --- the device's and the lowered entry's limits ----------------------------------------
        if block_threads > limits.function_max_threads_per_block {
            return Err(refuse(
                LaunchClause::BlockWithinFunction,
                format!(
                    "block {block_threads} exceeds the lowered entry's driver-reported cap {}",
                    limits.function_max_threads_per_block
                ),
            ));
        }
        proved.push(LaunchClause::BlockWithinFunction);

        match limits.device_max_threads_per_block {
            Some(cap) if block_threads <= cap => proved.push(LaunchClause::BlockWithinDevice),
            Some(cap) => {
                return Err(refuse(
                    LaunchClause::BlockWithinDevice,
                    format!("block {block_threads} exceeds the device's reported cap {cap}"),
                ))
            }
            None => deferred.push(LaunchClause::BlockWithinDevice),
        }

        match limits.max_block {
            Some(max) => {
                if shape.block.x > max.x || shape.block.y > max.y || shape.block.z > max.z {
                    return Err(refuse(
                        LaunchClause::BlockDimensionWithinDevice,
                        format!(
                            "block {}x{}x{} exceeds the device block aperture {}x{}x{}",
                            shape.block.x, shape.block.y, shape.block.z, max.x, max.y, max.z
                        ),
                    ));
                }
                proved.push(LaunchClause::BlockDimensionWithinDevice);
            }
            None => deferred.push(LaunchClause::BlockDimensionWithinDevice),
        }

        match limits.max_grid {
            Some(max) => {
                if shape.grid.x > max.x || shape.grid.y > max.y || shape.grid.z > max.z {
                    return Err(refuse(
                        LaunchClause::GridWithinDevice,
                        format!(
                            "grid {}x{}x{} exceeds the device grid aperture {}x{}x{}",
                            shape.grid.x, shape.grid.y, shape.grid.z, max.x, max.y, max.z
                        ),
                    ));
                }
                proved.push(LaunchClause::GridWithinDevice);
            }
            None => deferred.push(LaunchClause::GridWithinDevice),
        }

        // --- coverage ---------------------------------------------------------------------------
        let guard_threads = match requirement.coverage {
            Coverage::Exact => {
                if threads != requirement.extent {
                    return Err(refuse(
                        LaunchClause::CoverageExact,
                        format!(
                            "an exact cover of {} elements needs exactly {} threads; the shape carries {threads}",
                            requirement.extent, requirement.extent
                        ),
                    ));
                }
                proved.push(LaunchClause::CoverageExact);
                0
            }
            Coverage::Guarded => {
                if threads < requirement.extent {
                    return Err(refuse(
                        LaunchClause::CoverageGuarded,
                        format!(
                            "{threads} threads do not reach the declared extent {}",
                            requirement.extent
                        ),
                    ));
                }
                let guard = threads - requirement.extent;
                if guard >= block_threads as u64 {
                    return Err(refuse(
                        LaunchClause::CoverageGuarded,
                        format!(
                            "the guarded tail {guard} is one whole {block_threads}-thread block or \
                             more; the shape over-covers extent {}",
                            requirement.extent
                        ),
                    ));
                }
                proved.push(LaunchClause::CoverageGuarded);
                guard
            }
            Coverage::Strided => {
                if x_stride == 0 {
                    return Err(refuse(
                        LaunchClause::CoverageStrided,
                        String::from("a strided cover carries a positive X stride"),
                    ));
                }
                proved.push(LaunchClause::CoverageStrided);
                0
            }
            Coverage::Undeclared => {
                deferred.push(LaunchClause::CoverageGuarded);
                0
            }
        };

        // --- shared memory ----------------------------------------------------------------------
        let declared_shared = requirement
            .shared
            .bytes_for(block_threads)
            .map_err(|detail| refuse(LaunchClause::SharedBytesMatch, detail))?;
        if declared_shared != shape.shared_bytes {
            return Err(refuse(
                LaunchClause::SharedBytesMatch,
                format!(
                    "the entry declares {declared_shared} dynamic shared octets at block \
                     {block_threads}; the call site offered {}",
                    shape.shared_bytes
                ),
            ));
        }
        proved.push(LaunchClause::SharedBytesMatch);

        match limits.max_shared_bytes_per_block {
            Some(max) => {
                let total = limits
                    .function_static_shared_bytes
                    .checked_add(shape.shared_bytes)
                    .ok_or_else(|| {
                        refuse(
                            LaunchClause::SharedWithinDevice,
                            format!(
                                "static shared {} plus dynamic shared {} overflows u32",
                                limits.function_static_shared_bytes, shape.shared_bytes
                            ),
                        )
                    })?;
                if total > max {
                    return Err(refuse(
                        LaunchClause::SharedWithinDevice,
                        format!(
                            "static {} plus dynamic {} shared octets exceed the device's per-block {max}",
                            limits.function_static_shared_bytes, shape.shared_bytes
                        ),
                    ));
                }
                proved.push(LaunchClause::SharedWithinDevice);
            }
            None => deferred.push(LaunchClause::SharedWithinDevice),
        }

        // --- arguments --------------------------------------------------------------------------
        if arguments.len() != requirement.arguments.len() {
            return Err(refuse(
                LaunchClause::ArgumentCount,
                format!(
                    "the entry declares {} arguments; the call site presented {}",
                    requirement.arguments.len(),
                    arguments.len()
                ),
            ));
        }
        proved.push(LaunchClause::ArgumentCount);

        let mut argument_receipts = Vec::with_capacity(arguments.len());
        for (declared, presented) in requirement.arguments.iter().zip(arguments) {
            if declared.name != presented.name {
                return Err(refuse(
                    LaunchClause::ArgumentName,
                    format!(
                        "argument position expects `{}`; the call site presented `{}`",
                        declared.name, presented.name
                    ),
                ));
            }
            if declared.residency != presented.residency {
                return Err(refuse(
                    LaunchClause::ArgumentResidency,
                    format!(
                        "`{}` must be {}-resident; the call site presented {}-resident standing",
                        declared.name,
                        declared.residency.name(),
                        presented.residency.name()
                    ),
                ));
            }
            if declared.access != presented.access {
                return Err(refuse(
                    LaunchClause::ArgumentAccess,
                    format!(
                        "`{}` is declared {:?} and presented {:?}",
                        declared.name, declared.access, presented.access
                    ),
                ));
            }
            if declared.element_bytes != presented.element_bytes {
                return Err(refuse(
                    LaunchClause::ArgumentExtent,
                    format!(
                        "`{}` carries {}-octet elements; the call site presented {}-octet elements",
                        declared.name, declared.element_bytes, presented.element_bytes
                    ),
                ));
            }
            declared.extent.admits(presented.elements).map_err(|detail| {
                refuse(
                    LaunchClause::ArgumentExtent,
                    format!("`{}`: {detail}", declared.name),
                )
            })?;
            let bytes = presented.bytes().ok_or_else(|| {
                refuse(
                    LaunchClause::ArgumentExtent,
                    format!(
                        "`{}`: {} elements of {} octets overflow usize",
                        declared.name, presented.elements, presented.element_bytes
                    ),
                )
            })?;
            if presented.residency != Residency::Host && presented.address == 0 && bytes != 0 {
                return Err(refuse(
                    LaunchClause::ArgumentAddress,
                    format!("`{}` presents a null {} address", declared.name, presented.residency.name()),
                ));
            }
            argument_receipts.push(ArgumentReceipt {
                name: declared.name,
                address: presented.address,
                residency: declared.residency,
                access: declared.access,
                elements: presented.elements,
                bytes,
            });
        }
        proved.push(LaunchClause::ArgumentName);
        proved.push(LaunchClause::ArgumentResidency);
        proved.push(LaunchClause::ArgumentExtent);
        proved.push(LaunchClause::ArgumentAddress);
        proved.push(LaunchClause::ArgumentAccess);

        // --- declared scalars -------------------------------------------------------------------
        // Their *values* arrive at enactment; what is proved here is that every declared scalar
        // sits after a buffer pair the entry actually has, so the parameter block the receipt
        // generates is the entry's own block and not a caller's arithmetic.
        for scalar in &requirement.scalars {
            if scalar.after_arguments > requirement.arguments.len() {
                return Err(refuse(
                    LaunchClause::ScalarArguments,
                    format!(
                        "scalar `{}` is declared after {} buffer pairs; the entry declares {}",
                        scalar.name,
                        scalar.after_arguments,
                        requirement.arguments.len()
                    ),
                ));
            }
        }

        AliasAudit::admit_all(arguments).map_err(|refusal| {
            refuse(
                LaunchClause::ArgumentAliasing,
                format!("{}: {}", refusal.clause.name(), refusal.detail),
            )
        })?;
        proved.push(LaunchClause::ArgumentAliasing);

        proved.sort_unstable();
        deferred.sort_unstable();
        Ok(LawfulLaunch {
            receipt: LaunchReceipt {
                kernel,
                grid: shape.grid,
                block: shape.block,
                threads,
                extent: requirement.extent,
                guard_threads,
                x_stride,
                shared_bytes: shape.shared_bytes,
                stream: StreamIdentity::Default,
                arguments: argument_receipts,
                scalars: Vec::new(),
                proved,
                deferred,
            },
            scalars: requirement.scalars.clone(),
            stream: requirement.stream,
        })
    }

    /// Derive the covering shape from the device evidence and prove it in one step.
    pub fn cover(
        requirement: &LaunchRequirement,
        limits: &LaunchLimits,
        arguments: &[ArgumentSpan],
    ) -> Lawful<LawfulLaunch> {
        let shape = requirement.cover_with(limits)?;
        LawfulLaunch::prove(requirement, limits, shape, arguments)
    }

    /// The receipt this proof earned, before the launch is enacted.
    pub fn receipt(&self) -> &LaunchReceipt {
        &self.receipt
    }

    /// The proved shape, for a caller that must hand the same grid/block to another mouth.
    pub fn shape(&self) -> LaunchShape {
        LaunchShape {
            grid: self.receipt.grid,
            block: self.receipt.block,
            shared_bytes: self.receipt.shared_bytes,
        }
    }

    /// The X stride the kernel reads from its parameter block.
    pub fn x_stride(&self) -> u32 {
        self.receipt.x_stride
    }

    /// **Enact the proved launch.**
    ///
    /// The CUDA parameter block is built **from the receipt itself**: for each proved argument, the
    /// proved address and the proved element extent, with each declared scalar emitted at the
    /// position its [`ScalarRequirement`] names.  The caller supplies only the scalar *values*, by
    /// name, and a name the entry did not declare, a missing one, a repeat, or a value past the
    /// declared width is a [`LaunchClause::ScalarArguments`] refusal.  There is no path here that
    /// takes a caller-built `params` array: the addresses and extents the driver receives are
    /// literally the ones that were proved, and no second derivation can drift from the proof.
    ///
    /// The declared stream ordering is checked here, so a kernel that requires an ordered current
    /// cannot be issued on the default one.
    pub fn enact(
        self,
        function: &Function<'_>,
        stream: Option<&Stream>,
        scalars: &[ScalarArgument],
    ) -> Result<LaunchReceipt> {
        let kernel = self.receipt.kernel;
        let refuse = |detail: String| {
            CudaError::from(LaunchRefusal::new(
                kernel,
                LaunchClause::ScalarArguments,
                detail,
            ))
        };
        if scalars.len() != self.scalars.len() {
            return Err(refuse(format!(
                "the entry declares {} scalar parameters; the call site presented {}",
                self.scalars.len(),
                scalars.len()
            )));
        }
        let mut scalar_receipts: Vec<ScalarReceipt> = Vec::with_capacity(self.scalars.len());
        for (declared, presented) in self.scalars.iter().zip(scalars) {
            if declared.name != presented.name {
                return Err(refuse(format!(
                    "scalar position expects `{}`; the call site presented `{}`",
                    declared.name, presented.name
                )));
            }
            if presented.value > declared.width.ceiling() {
                return Err(refuse(format!(
                    "scalar `{}` is declared {} and the call site presented {}",
                    declared.name,
                    declared.width.name(),
                    presented.value
                )));
            }
            scalar_receipts.push(ScalarReceipt {
                name: declared.name,
                width: declared.width,
                after_arguments: declared.after_arguments,
                value: presented.value,
            });
        }

        // The parameter block, in the entry's own order: each buffer pair, with every scalar
        // declared after that many pairs emitted immediately behind it.  Both arenas are filled
        // completely before a single pointer into them is taken.
        enum Slot {
            Word(usize),
            Half(usize),
        }
        let mut words: Vec<u64> = Vec::new();
        let mut halves: Vec<u32> = Vec::new();
        let mut order: Vec<Slot> = Vec::new();
        let emit_scalars_after = |pairs: usize,
                                      words: &mut Vec<u64>,
                                      halves: &mut Vec<u32>,
                                      order: &mut Vec<Slot>| {
            for scalar in scalar_receipts.iter().filter(|s| s.after_arguments == pairs) {
                match scalar.width {
                    ScalarWidth::U32 => {
                        halves.push(scalar.value as u32);
                        order.push(Slot::Half(halves.len() - 1));
                    }
                    ScalarWidth::U64 => {
                        words.push(scalar.value);
                        order.push(Slot::Word(words.len() - 1));
                    }
                }
            }
        };
        emit_scalars_after(0, &mut words, &mut halves, &mut order);
        for (pairs, argument) in self.receipt.arguments.iter().enumerate() {
            words.push(argument.address);
            order.push(Slot::Word(words.len() - 1));
            words.push(u64::try_from(argument.elements).map_err(|_| {
                CudaError::from(LaunchRefusal::new(
                    kernel,
                    LaunchClause::ArgumentExtent,
                    format!(
                        "`{}` extent {} exceeds its 64-bit ABI word",
                        argument.name, argument.elements
                    ),
                ))
            })?);
            order.push(Slot::Word(words.len() - 1));
            emit_scalars_after(pairs + 1, &mut words, &mut halves, &mut order);
        }

        let word_addresses: Vec<*mut c_void> = words
            .iter_mut()
            .map(|value| value as *mut u64 as *mut c_void)
            .collect();
        let half_addresses: Vec<*mut c_void> = halves
            .iter_mut()
            .map(|value| value as *mut u32 as *mut c_void)
            .collect();
        let mut params: Vec<*mut c_void> = order
            .iter()
            .map(|slot| match slot {
                Slot::Word(at) => word_addresses[*at],
                Slot::Half(at) => half_addresses[*at],
            })
            .collect();

        let mut receipt = self.receipt;
        receipt.scalars = scalar_receipts;
        receipt.proved.push(LaunchClause::ScalarArguments);
        receipt.proved.sort_unstable();
        let params = &mut params[..];
        match (self.stream, stream) {
            (StreamRequirement::Default, None) => {
                receipt.stream = StreamIdentity::Default;
                receipt.proved.push(LaunchClause::StreamOrdering);
                receipt.proved.sort_unstable();
                function.launch(receipt.grid, receipt.block, params)?;
            }
            (StreamRequirement::Ordered, Some(stream)) => {
                receipt.stream = StreamIdentity::Ordered {
                    nonblocking: stream.is_nonblocking(),
                };
                receipt.proved.push(LaunchClause::StreamOrdering);
                receipt.proved.sort_unstable();
                function.launch_on_shared(
                    stream,
                    receipt.grid,
                    receipt.block,
                    receipt.shared_bytes,
                    params,
                )?;
            }
            (StreamRequirement::Default, Some(_)) => {
                return Err(LaunchRefusal::new(
                    receipt.kernel,
                    LaunchClause::StreamOrdering,
                    "the entry declares the default current and the call site offered an ordered one",
                )
                .into())
            }
            (StreamRequirement::Ordered, None) => {
                return Err(LaunchRefusal::new(
                    receipt.kernel,
                    LaunchClause::StreamOrdering,
                    "the entry declares an ordered current and the call site offered none",
                )
                .into())
            }
        }
        Ok(receipt)
    }
}

// ---------------------------------------------------------------------------------------------
// D2 — exclusive access is a type
// ---------------------------------------------------------------------------------------------

/// One named clause of the partition law.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PartitionClause {
    /// The region population is positive.
    PositiveRegions,
    /// The stride is positive.
    PositiveStride,
    /// The write width does not exceed the stride, so consecutive regions cannot overlap.
    WidthWithinStride,
    /// The covered extent multiplies without overflow and stays inside the span.
    CoverWithinSpan,
    /// The offsets table carries a boundary for every region plus its end.
    OffsetsLength,
    /// The offsets table is monotone.
    OffsetsMonotone,
    /// The offsets table ends inside the span.
    OffsetsWithinSpan,
    /// Every scatter target is inside the span.
    ScatterWithinSpan,
    /// The scatter index map is injective, so scatter writes are disjoint.
    ScatterInjective,
    /// The partition's span and the borrowed span agree.
    SpanMismatch,
    /// A writable span overlaps another span of the same residency.
    Aliasing,
}

impl PartitionClause {
    /// The clause's own name.
    pub const fn name(self) -> &'static str {
        match self {
            PartitionClause::PositiveRegions => "positive-regions",
            PartitionClause::PositiveStride => "positive-stride",
            PartitionClause::WidthWithinStride => "width-within-stride",
            PartitionClause::CoverWithinSpan => "cover-within-span",
            PartitionClause::OffsetsLength => "offsets-length",
            PartitionClause::OffsetsMonotone => "offsets-monotone",
            PartitionClause::OffsetsWithinSpan => "offsets-within-span",
            PartitionClause::ScatterWithinSpan => "scatter-within-span",
            PartitionClause::ScatterInjective => "scatter-injective",
            PartitionClause::SpanMismatch => "span-mismatch",
            PartitionClause::Aliasing => "aliasing",
        }
    }
}

/// A typed construction refusal of the partition law.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartitionRefusal {
    /// The single clause that failed.
    pub clause: PartitionClause,
    /// The exact quantities that failed it.
    pub detail: String,
}

impl PartitionRefusal {
    /// Name a violated clause.
    pub fn new(clause: PartitionClause, detail: impl Into<String>) -> Self {
        Self {
            clause,
            detail: detail.into(),
        }
    }
}

impl fmt::Display for PartitionRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "partition law clause `{}` refused: {}",
            self.clause.name(),
            self.detail
        )
    }
}

impl std::error::Error for PartitionRefusal {}

impl From<PartitionRefusal> for CudaError {
    fn from(refusal: PartitionRefusal) -> CudaError {
        CudaError {
            code: -1,
            name: String::from("PARTITION_LAW_REFUSAL"),
            message: refusal.detail,
            context: refusal.clause.name(),
        }
    }
}

/// How a scatter through an incidence index map is made admissible.
///
/// This is the **D3 seam**.  With [`ScatterLaw::Injective`] the index map itself proves the writes
/// disjoint, and the final state is order-independent — the Lean statement is
/// `DeviceLaunchLaw.DisjointPartition.scatter_perm`.  With a colliding map the plain-store scatter
/// is order-dependent, which `scatter_order_dependent` demonstrates by counterexample; such a
/// scatter is admissible only under [`ScatterLaw::Accumulated`], where the colliding threads
/// combine through an associative-commutative accumulation and order-independence is restored
/// (`scatterAdd_perm`).  D3's general incidence owner inherits exactly this obligation: a declared
/// incidence generates a gather, a local application and a transposed scatter, and the scatter arm
/// must carry either an injectivity proof or an accumulation law.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScatterLaw {
    /// The index map is injective; plain stores are disjoint.
    Injective,
    /// Colliding targets combine through an associative-commutative accumulation declared by the
    /// caller (a device atomic add, an exact integer sum, a max).
    Accumulated,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum PartitionShape {
    Uniform { stride: usize, width: usize },
    Offsets(Vec<usize>),
    Scatter { targets: Vec<usize>, law: ScatterLaw },
}

/// **A proof-carrying partition of a mutable device span into per-thread write regions.**
///
/// Constructed only from a description that proves `region(i) ∩ region(j) = ∅` for `i ≠ j` and
/// `⋃ region(i) ⊆ span`.  The Lean owner is `DeviceLaunchLaw.DisjointPartition`, whose `separated`
/// field is the ordered form of the same statement and whose `region_disjoint` / `region_subset`
/// theorems are what [`DisjointPartition::verify_pairwise_disjoint`] witnesses executably.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DisjointPartition {
    elements: usize,
    regions: usize,
    shape: PartitionShape,
}

impl DisjointPartition {
    /// **The uniform stride form.**  `region(i) = [i * stride, i * stride + width)`.
    ///
    /// Clauses: `regions > 0`, `stride > 0`, `width > 0`, `width <= stride` (so consecutive
    /// regions cannot overlap), and `regions * stride <= elements` with checked multiplication.
    /// The Lean counterpart is `DisjointPartition.uniform`, whose two hypotheses are exactly
    /// `width ≤ stride` and `regions * stride ≤ span`.
    pub fn uniform(
        elements: usize,
        regions: usize,
        stride: usize,
        width: usize,
    ) -> Partitioned<DisjointPartition> {
        if regions == 0 {
            return Err(PartitionRefusal::new(
                PartitionClause::PositiveRegions,
                "a partition carries one or more regions",
            ));
        }
        if stride == 0 || width == 0 {
            return Err(PartitionRefusal::new(
                PartitionClause::PositiveStride,
                format!("stride {stride} and width {width} must both be positive"),
            ));
        }
        if width > stride {
            return Err(PartitionRefusal::new(
                PartitionClause::WidthWithinStride,
                format!("width {width} exceeds stride {stride}; consecutive regions would overlap"),
            ));
        }
        let covered = regions.checked_mul(stride).ok_or_else(|| {
            PartitionRefusal::new(
                PartitionClause::CoverWithinSpan,
                format!("{regions} regions of stride {stride} overflow usize"),
            )
        })?;
        if covered > elements {
            return Err(PartitionRefusal::new(
                PartitionClause::CoverWithinSpan,
                format!("{regions} regions of stride {stride} need {covered} elements, span has {elements}"),
            ));
        }
        Ok(DisjointPartition {
            elements,
            regions,
            shape: PartitionShape::Uniform { stride, width },
        })
    }

    /// **The explicit offsets form.**  `region(i) = [offsets[i], offsets[i + 1])`.
    ///
    /// Clauses: the table carries `regions + 1` boundaries, it is monotone (validated one adjacent
    /// pair at a time, which `DisjointPartition.offsets_mono` proves sufficient), and its last
    /// boundary is inside the span.  Empty regions are lawful and vacuously disjoint.
    pub fn from_offsets(elements: usize, offsets: Vec<usize>) -> Partitioned<DisjointPartition> {
        if offsets.len() < 2 {
            return Err(PartitionRefusal::new(
                PartitionClause::OffsetsLength,
                format!(
                    "an offsets table carries one boundary per region plus its end; got {}",
                    offsets.len()
                ),
            ));
        }
        for window in offsets.windows(2) {
            if window[0] > window[1] {
                return Err(PartitionRefusal::new(
                    PartitionClause::OffsetsMonotone,
                    format!("offsets {} then {} descend", window[0], window[1]),
                ));
            }
        }
        let end = *offsets.last().expect("the table carries two or more boundaries");
        if end > elements {
            return Err(PartitionRefusal::new(
                PartitionClause::OffsetsWithinSpan,
                format!("the offsets table ends at {end}, span has {elements}"),
            ));
        }
        let regions = offsets.len() - 1;
        Ok(DisjointPartition {
            elements,
            regions,
            shape: PartitionShape::Offsets(offsets),
        })
    }

    /// **The gather/scatter form.**  Thread `i` writes the single slot `targets[i]` named by an
    /// incidence relation.
    ///
    /// Under [`ScatterLaw::Injective`] every target must be in bounds *and* the map must be
    /// injective; the colliding pair is named in the refusal.  Under [`ScatterLaw::Accumulated`]
    /// only the bounds clause applies, and the caller has declared that colliding threads combine
    /// through an associative-commutative accumulation.
    pub fn scatter(
        elements: usize,
        targets: Vec<usize>,
        law: ScatterLaw,
    ) -> Partitioned<DisjointPartition> {
        if targets.is_empty() {
            return Err(PartitionRefusal::new(
                PartitionClause::PositiveRegions,
                "a scatter carries one or more incidence targets",
            ));
        }
        for (thread, target) in targets.iter().enumerate() {
            if *target >= elements {
                return Err(PartitionRefusal::new(
                    PartitionClause::ScatterWithinSpan,
                    format!("thread {thread} scatters to {target}, span has {elements}"),
                ));
            }
        }
        if law == ScatterLaw::Injective {
            let mut seen: std::collections::HashMap<usize, usize> =
                std::collections::HashMap::with_capacity(targets.len());
            for (thread, target) in targets.iter().enumerate() {
                if let Some(previous) = seen.insert(*target, thread) {
                    return Err(PartitionRefusal::new(
                        PartitionClause::ScatterInjective,
                        format!(
                            "threads {previous} and {thread} both scatter to slot {target}; a \
                             colliding index map is order-dependent under plain stores and is \
                             admissible only under a declared associative-commutative accumulation"
                        ),
                    ));
                }
            }
        }
        let regions = targets.len();
        Ok(DisjointPartition {
            elements,
            regions,
            shape: PartitionShape::Scatter { targets, law },
        })
    }

    /// The span extent this partition covers.
    pub const fn elements(&self) -> usize {
        self.elements
    }

    /// The region population: one per thread, or per block.
    pub const fn regions(&self) -> usize {
        self.regions
    }

    /// Whether this partition is a scatter, and under which law.
    pub fn scatter_law(&self) -> Option<ScatterLaw> {
        match &self.shape {
            PartitionShape::Scatter { law, .. } => Some(*law),
            _ => None,
        }
    }

    /// The exclusive write region of thread `index`, or `None` past the region population.
    pub fn region(&self, index: usize) -> Option<Range<usize>> {
        if index >= self.regions {
            return None;
        }
        match &self.shape {
            PartitionShape::Uniform { stride, width } => {
                let start = index.checked_mul(*stride)?;
                let end = start.checked_add(*width)?;
                Some(start..end)
            }
            PartitionShape::Offsets(offsets) => Some(offsets[index]..offsets[index + 1]),
            PartitionShape::Scatter { targets, .. } => {
                let target = targets[index];
                Some(target..target + 1)
            }
        }
    }

    /// The total element population the regions cover.
    pub fn covered(&self) -> usize {
        (0..self.regions)
            .filter_map(|index| self.region(index))
            .map(|region| region.end - region.start)
            .sum()
    }

    /// **Witness the Lean theorems executably**, without ever doing quadratic work.
    ///
    /// Every region is checked for containment (`DisjointPartition.region_subset`).  For
    /// disjointness (`DisjointPartition.region_disjoint`) the form decides the complete argument:
    ///
    /// * **Uniform and offsets forms** carry their regions in **address order**, which is exactly
    ///   the Lean `separated` field `i < j → hi i ≤ lo j`.  Checking each adjacent pair is
    ///   therefore already a *complete* proof of pairwise disjointness, not an approximation of
    ///   one — `DisjointPartition.offsets_mono` is the statement that adjacent validation implies
    ///   the general ordering, and `DisjointPartition.region_disjoint` derives symmetric
    ///   disjointness from it.  This arm is linear.
    /// * **An injective scatter** has one address per thread with no order, so the complete check
    ///   is that the address multiset has no repeat: sorting and scanning, `O(n log n)`.
    /// * **An accumulated scatter** is exempt from the disjointness half by declaration, and says
    ///   so; only the bounds are checked.
    ///
    /// The previous form compared every pair, which is `O(regions²)` over a caller-declared region
    /// population and so was a denial-of-service surface on a hostile declaration.  Nothing is
    /// weakened by the change: the adjacency argument proves strictly the same statement.
    pub fn verify_pairwise_disjoint(&self) -> Partitioned<()> {
        for index in 0..self.regions {
            let region = self.region(index).ok_or_else(|| {
                PartitionRefusal::new(
                    PartitionClause::CoverWithinSpan,
                    format!("region {index} overflows its own arithmetic"),
                )
            })?;
            if region.start > region.end || region.end > self.elements {
                return Err(PartitionRefusal::new(
                    PartitionClause::CoverWithinSpan,
                    format!(
                        "region {index} is {}..{} outside a span of {}",
                        region.start, region.end, self.elements
                    ),
                ));
            }
        }
        match &self.shape {
            PartitionShape::Scatter {
                law: ScatterLaw::Accumulated,
                ..
            } => Ok(()),
            PartitionShape::Scatter {
                targets,
                law: ScatterLaw::Injective,
            } => {
                let mut sorted = targets.clone();
                sorted.sort_unstable();
                for pair in sorted.windows(2) {
                    if pair[0] == pair[1] {
                        return Err(PartitionRefusal::new(
                            PartitionClause::Aliasing,
                            format!("two threads scatter to slot {}", pair[0]),
                        ));
                    }
                }
                Ok(())
            }
            PartitionShape::Uniform { .. } | PartitionShape::Offsets(_) => {
                // Address-ordered forms: adjacency is the whole of `separated`.
                let mut previous_end: Option<(usize, usize)> = None;
                for index in 0..self.regions {
                    let region = self.region(index).expect("regions were bounded above");
                    if region.start == region.end {
                        continue;
                    }
                    if let Some((at, end)) = previous_end {
                        if region.start < end {
                            return Err(PartitionRefusal::new(
                                PartitionClause::Aliasing,
                                format!(
                                    "regions {at} (ending at {end}) and {index} (starting at {}) overlap",
                                    region.start
                                ),
                            ));
                        }
                    }
                    previous_end = Some((index, region.end));
                }
                Ok(())
            }
        }
    }

    /// The quadratic reference: compares **every** pair.  `cfg(test)` only, and the tests assert
    /// it agrees with [`DisjointPartition::verify_pairwise_disjoint`] on every fixture, which is
    /// what licenses the linear argument above.
    #[cfg(test)]
    pub(crate) fn verify_pairwise_disjoint_quadratic(&self) -> Partitioned<()> {
        if self.scatter_law() == Some(ScatterLaw::Accumulated) {
            return Ok(());
        }
        for left in 0..self.regions {
            let first = self.region(left).expect("regions were bounded above");
            if first.start == first.end {
                continue;
            }
            for right in (left + 1)..self.regions {
                let second = self.region(right).expect("regions were bounded above");
                if second.start == second.end {
                    continue;
                }
                if first.start < second.end && second.start < first.end {
                    return Err(PartitionRefusal::new(
                        PartitionClause::Aliasing,
                        format!(
                            "regions {left} ({}..{}) and {right} ({}..{}) overlap",
                            first.start, first.end, second.start, second.end
                        ),
                    ));
                }
            }
        }
        Ok(())
    }
}

// --- spans whose exclusivity the borrow checker carries -----------------------------------------

/// A shared device span.  Read spans may alias one another freely; `PhantomData<&'a
/// DeviceBuffer<T>>` keeps the allocation borrowed for the span's whole life.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeviceReadSpan<'a, T> {
    address: u64,
    elements: usize,
    borrow: PhantomData<&'a DeviceBuffer<T>>,
}

impl<'a, T: Copy> DeviceReadSpan<'a, T> {
    /// Borrow a whole allocation for reading.
    pub fn whole(buffer: &'a DeviceBuffer<T>) -> Self {
        Self {
            address: buffer.device_ptr(),
            elements: buffer.len(),
            borrow: PhantomData,
        }
    }

    /// The span's base address.
    pub const fn address(&self) -> u64 {
        self.address
    }

    /// The span's element population.
    pub const fn elements(&self) -> usize {
        self.elements
    }

    /// Present this span as a launch argument.
    pub const fn argument(&self, name: &'static str) -> ArgumentSpan {
        ArgumentSpan::device_raw(
            name,
            self.address,
            self.elements,
            core::mem::size_of::<T>(),
            Access::Read,
        )
    }
}

/// **A uniquely borrowed mutable device span.**  It holds `PhantomData<&'a mut DeviceBuffer<T>>`,
/// so it is neither `Copy` nor `Clone` and the borrow checker refuses, *at compile time*, any
/// attempt to hold a [`DeviceReadSpan`] of the same allocation, or a second write span, while it
/// lives.  That is the compile-time half of "read-only spans may alias each other and never a
/// write span"; [`AliasAudit`] is the construction-time half, for spans carved from one backing
/// allocation where the borrow checker sees only the one backing borrow.
///
/// No accessor produces a `&mut` view from a `&` one.  `PinnedHost::as_mut_octets` in
/// `crates/holonics-cuda/src/cuda.rs` takes `&mut self` for the same reason, and
/// `crates/holonic-engine/src/streamed_standing.rs` takes that unique borrow **only after** the
/// copy that last read the slot has been synchronized.  Its sibling
/// `PinnedHost::as_octets_unchecked`, an `unsafe fn(&self) -> &mut [u8]` that pushed that proof
/// back onto a comment, was removed; nothing of that shape is reintroduced here.  The exclusivity
/// a launch needs is carried by this type and by [`PartitionedWrite::scope`], not by a safety
/// paragraph.
#[derive(Debug, PartialEq, Eq)]
pub struct DeviceWriteSpan<'a, T> {
    address: u64,
    elements: usize,
    borrow: PhantomData<&'a mut DeviceBuffer<T>>,
}

impl<'a, T: Copy> DeviceWriteSpan<'a, T> {
    /// Borrow a whole allocation exclusively for writing.
    pub fn whole(buffer: &'a mut DeviceBuffer<T>) -> Self {
        Self {
            address: buffer.device_ptr(),
            elements: buffer.len(),
            borrow: PhantomData,
        }
    }

    /// The span's base address.
    pub const fn address(&self) -> u64 {
        self.address
    }

    /// The span's element population.
    pub const fn elements(&self) -> usize {
        self.elements
    }

    /// Present this span as a launch argument.
    pub const fn argument(&self, name: &'static str) -> ArgumentSpan {
        ArgumentSpan::device_raw(
            name,
            self.address,
            self.elements,
            core::mem::size_of::<T>(),
            Access::Write,
        )
    }

    /// A synthetic exclusive span for the cpu tests: no allocation exists behind it, so it is
    /// compiled only under `cfg(test)` and can never reach a driver call from a production path.
    #[cfg(test)]
    pub(crate) const fn synthetic(address: u64, elements: usize) -> Self {
        Self {
            address,
            elements,
            borrow: PhantomData,
        }
    }
}

/// **What a launch scope synchronizes on.**  A sealed trait: outside `cfg(test)` its only
/// implementors are [`Stream`] and [`Context`], so a caller cannot supply a no-op "settle" and
/// hollow out [`PartitionedWrite::scope`]'s guarantee.
pub trait Settles: sealed::Settles {
    /// Block until the apparatus this names has finished the work ordered on it.
    fn synchronize_for_settle(&self) -> Result<()>;
}

mod sealed {
    /// Sealing supertrait.  Implemented in this module only.
    pub trait Settles {}
}

impl sealed::Settles for Stream {}
impl Settles for Stream {
    fn synchronize_for_settle(&self) -> Result<()> {
        Stream::synchronize(self)
    }
}

impl sealed::Settles for Context {}
impl Settles for Context {
    fn synchronize_for_settle(&self) -> Result<()> {
        Context::synchronize(self)
    }
}

// The cpu tests need a `Settles` they can count, and the trait is sealed precisely so no caller
// outside this module can supply one.  The seal is opened here for `cfg(test)` only.
#[cfg(test)]
impl sealed::Settles for tests::RecordedSettle {}
#[cfg(test)]
impl Settles for tests::RecordedSettle {
    fn synchronize_for_settle(&self) -> Result<()> {
        self.record()
    }
}

/// The handle a launch scope hands its closure.  It carries the proved address, the element
/// population and the bound partition, and **nothing that can outlive the scope**: the closure's
/// return type is fixed before the handle's lifetime is chosen, so no borrow of it can be returned.
#[derive(Debug)]
pub struct OpenWrite<'scope, 'a, T> {
    span: &'scope DeviceWriteSpan<'a, T>,
    partition: &'scope DisjointPartition,
}

impl<T: Copy> OpenWrite<'_, '_, T> {
    /// The base address the kernel will write through.
    pub const fn address(&self) -> u64 {
        self.span.address
    }

    /// The span's element population.
    pub const fn elements(&self) -> usize {
        self.span.elements
    }

    /// The bound partition.
    pub const fn partition(&self) -> &DisjointPartition {
        self.partition
    }

    /// Present the whole partitioned span as one launch argument.
    pub const fn argument(&self, name: &'static str) -> ArgumentSpan {
        self.span.argument(name)
    }
}

/// A mutable device span bound to a proof that its per-thread write regions are disjoint.
///
/// A second borrow of the same allocation is a compile error while the write span lives:
///
/// ```compile_fail,E0502
/// # use holonics_cuda::launch_law::{DeviceReadSpan, DeviceWriteSpan};
/// # use holonics_cuda::DeviceBuffer;
/// fn aliasing_is_a_compile_error(buffer: &mut DeviceBuffer<u32>) {
///     let write = DeviceWriteSpan::whole(buffer);
///     let read = DeviceReadSpan::whole(buffer); // second borrow while `write` lives
///     let _ = (write.address(), read.address());
/// }
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct PartitionedWrite<'a, T> {
    span: DeviceWriteSpan<'a, T>,
    partition: DisjointPartition,
}

impl<'a, T: Copy> PartitionedWrite<'a, T> {
    /// Bind a proved partition to an exclusively borrowed span.  The partition's span extent and
    /// the borrowed span's element population must agree exactly.
    pub fn bind(
        span: DeviceWriteSpan<'a, T>,
        partition: DisjointPartition,
    ) -> Partitioned<PartitionedWrite<'a, T>> {
        if partition.elements() != span.elements() {
            return Err(PartitionRefusal::new(
                PartitionClause::SpanMismatch,
                format!(
                    "the partition covers {} elements; the borrowed span carries {}",
                    partition.elements(),
                    span.elements()
                ),
            ));
        }
        Ok(PartitionedWrite { span, partition })
    }

    /// The bound partition.
    pub const fn partition(&self) -> &DisjointPartition {
        &self.partition
    }

    /// The exclusive span.
    pub const fn span(&self) -> &DeviceWriteSpan<'a, T> {
        &self.span
    }

    /// Present the whole partitioned span as one launch argument.
    pub const fn argument(&self, name: &'static str) -> ArgumentSpan {
        self.span.argument(name)
    }

    /// **Hand the span to the device for the duration of one closure.**
    ///
    /// This is the only shape in which the write borrow's release is a *type-level* guarantee, and
    /// it is the `std::thread::scope` shape for exactly the reason `std::thread::scope` has it.
    ///
    /// What is guaranteed, and by what mechanism:
    ///
    /// * The exclusive borrow of the backing allocation is the `&mut self` this method holds for
    ///   the whole of its own frame.  The allocation therefore cannot be re-spanned, read-spanned,
    ///   moved or dropped anywhere between the first enqueued launch and the return of `scope` —
    ///   the borrow checker refuses it, and the `compile_fail` doctests below are the receipts.
    /// * `scope` does not return until `on` has been synchronized.  On the ordinary path the
    ///   synchronization's own error is propagated; on an unwind it is performed by a guard living
    ///   **in this frame**, not in the caller's, so no `Drop` of any caller-held value is load
    ///   bearing.
    /// * There is consequently **no value the caller can `mem::forget`** to end the borrow early.
    ///   That is the defect the former `in_flight()` / `InFlightWrite` pair had: `drop(in_flight)`
    ///   — or forgetting it — released the exclusive borrow immediately while the kernel was still
    ///   running, and a `Drop` impl alone would not have fixed it, because `mem::forget` ends a
    ///   borrow statically without running `Drop`.
    ///
    /// The closure receives an [`OpenWrite`], from which it builds the launch argument; because
    /// the closure's return type `R` is fixed before the handle's lifetime is chosen, nothing
    /// borrowed from the handle can be carried out.
    ///
    /// **A note on these receipts.**  `rustdoc` does *not* enforce the error code written after
    /// `compile_fail` — a snippet that failed to compile for an unrelated reason, a stale import
    /// among them, would still pass.  So the first block below is a **positive control**: it uses
    /// the same imports and the same calls in a lawful order and must compile.  The three
    /// `compile_fail` blocks then differ from it only in the borrow they violate, and the codes
    /// recorded on them are the ones the compiler actually emits (`E0500`, `E0502`, `E0505`).
    ///
    /// The positive control — the same API, used lawfully, compiles:
    ///
    /// ```no_run
    /// # use holonics_cuda::launch_law::{DeviceReadSpan, DeviceWriteSpan, DisjointPartition, PartitionedWrite};
    /// # use holonics_cuda::{DeviceBuffer, Stream};
    /// fn a_lawful_scope(buffer: &mut DeviceBuffer<u32>, stream: &Stream) -> holonics_cuda::Result<()> {
    ///     let partition = DisjointPartition::uniform(buffer.len(), 4, 1, 1).unwrap();
    ///     let mut write =
    ///         PartitionedWrite::bind(DeviceWriteSpan::whole(&mut *buffer), partition).unwrap();
    ///     write.scope(stream, |open| {
    ///         let _argument = open.argument("cells");
    ///     })?;
    ///     // The borrow is over: the allocation may be read-spanned again.
    ///     let _read = DeviceReadSpan::whole(&*buffer);
    ///     Ok(())
    /// }
    /// ```
    ///
    /// The allocation cannot be re-spanned while a scope is open — the closure would need unique
    /// access to an allocation already uniquely borrowed by the open scope:
    ///
    /// ```compile_fail,E0500
    /// # use holonics_cuda::launch_law::{DeviceWriteSpan, DisjointPartition, PartitionedWrite};
    /// # use holonics_cuda::{DeviceBuffer, Stream};
    /// fn respanning_is_a_compile_error(buffer: &mut DeviceBuffer<u32>, stream: &Stream) {
    ///     let partition = DisjointPartition::uniform(buffer.len(), 4, 1, 1).unwrap();
    ///     let mut write =
    ///         PartitionedWrite::bind(DeviceWriteSpan::whole(&mut *buffer), partition).unwrap();
    ///     let _ = write.scope(stream, |_open| {
    ///         let _second = DeviceWriteSpan::whole(&mut *buffer); // a second exclusive span
    ///     });
    /// }
    /// ```
    ///
    /// Nor read-spanned while a scope is open:
    ///
    /// ```compile_fail,E0502
    /// # use holonics_cuda::launch_law::{DeviceReadSpan, DeviceWriteSpan, DisjointPartition, PartitionedWrite};
    /// # use holonics_cuda::{DeviceBuffer, Stream};
    /// fn read_spanning_is_a_compile_error(buffer: &mut DeviceBuffer<u32>, stream: &Stream) {
    ///     let partition = DisjointPartition::uniform(buffer.len(), 4, 1, 1).unwrap();
    ///     let mut write =
    ///         PartitionedWrite::bind(DeviceWriteSpan::whole(&mut *buffer), partition).unwrap();
    ///     let _ = write.scope(stream, |_open| {
    ///         let _read = DeviceReadSpan::whole(&*buffer); // a reader of the same allocation
    ///     });
    /// }
    /// ```
    ///
    /// Nor dropped while a scope is open:
    ///
    /// ```compile_fail,E0505
    /// # use holonics_cuda::launch_law::{DeviceWriteSpan, DisjointPartition, PartitionedWrite};
    /// # use holonics_cuda::{DeviceBuffer, Stream};
    /// fn freeing_is_a_compile_error(mut buffer: DeviceBuffer<u32>, stream: &Stream) {
    ///     let partition = DisjointPartition::uniform(buffer.len(), 4, 1, 1).unwrap();
    ///     let mut write =
    ///         PartitionedWrite::bind(DeviceWriteSpan::whole(&mut buffer), partition).unwrap();
    ///     let _ = write.scope(stream, |_open| {
    ///         drop(buffer); // freeing the allocation the kernel is writing
    ///     });
    /// }
    /// ```
    pub fn scope<S: Settles, R>(
        &mut self,
        on: &S,
        enqueue: impl FnOnce(&OpenWrite<'_, 'a, T>) -> R,
    ) -> Result<R> {
        /// Synchronizes on unwind, from *this* frame.  It never panics: a panic here would abort
        /// during an unwind, and the object of the guard is to wait, not to report.
        struct SettleOnUnwind<'s, S: Settles> {
            on: Option<&'s S>,
        }
        impl<S: Settles> Drop for SettleOnUnwind<'_, S> {
            fn drop(&mut self) {
                if let Some(on) = self.on {
                    let _ = on.synchronize_for_settle();
                }
            }
        }

        let mut guard = SettleOnUnwind { on: Some(on) };
        let value = {
            let open = OpenWrite {
                span: &self.span,
                partition: &self.partition,
            };
            enqueue(&open)
        };
        // The ordinary path synchronizes here so the driver's own error reaches the caller; the
        // guard is defused first so the wait is performed exactly once.
        guard.on = None;
        drop(guard);
        on.synchronize_for_settle()?;
        Ok(value)
    }

    /// **The escape hatch, for a caller that must interleave two mouths on one current.**
    ///
    /// Unlike [`PartitionedWrite::scope`] this hands back a caller-held value, and a caller-held
    /// value can be `mem::forget`-ed.  What it therefore guarantees is *weaker and is stated as
    /// such*: [`InFlightWrite`] is `#[must_use]`, and its `Drop` synchronizes (it never panics), so
    /// an in-flight write that is merely dropped still waits.  A `mem::forget` of it does not, and
    /// no type can make it, which is why `scope` exists and is the form the launchers use.
    pub fn in_flight<'s, S: Settles>(self, on: &'s S) -> InFlightWrite<'a, 's, T, S> {
        InFlightWrite {
            held: Some(self),
            on,
        }
    }
}

/// A partitioned write the device is still carrying.  The way back to the exclusive span is
/// [`InFlightWrite::settle`], which synchronizes and returns the driver's error; dropping it
/// synchronizes too, silently, as a second line.  **Forgetting it does neither** — see
/// [`PartitionedWrite::scope`], which has no such hole.
#[derive(Debug)]
#[must_use = "an in-flight write must be settled; dropping it silently synchronizes instead"]
pub struct InFlightWrite<'a, 's, T, S: Settles> {
    held: Option<PartitionedWrite<'a, T>>,
    on: &'s S,
}

impl<'a, T: Copy, S: Settles> InFlightWrite<'a, '_, T, S> {
    /// The base address, for a receipt or a second kernel ordered on the same current.
    pub fn address(&self) -> u64 {
        self.held
            .as_ref()
            .expect("an in-flight write holds its span until it settles")
            .span
            .address
    }

    /// The bound partition.
    pub fn partition(&self) -> &DisjointPartition {
        &self
            .held
            .as_ref()
            .expect("an in-flight write holds its span until it settles")
            .partition
    }

    /// Wait for the declared apparatus to reach this launch, then take the span back.
    pub fn settle(mut self) -> Result<PartitionedWrite<'a, T>> {
        let held = self
            .held
            .take()
            .expect("an in-flight write settles exactly once");
        self.on.synchronize_for_settle()?;
        Ok(held)
    }
}

impl<T, S: Settles> Drop for InFlightWrite<'_, '_, T, S> {
    fn drop(&mut self) {
        if self.held.is_some() {
            // Second line only, and deliberately silent: a panic in `Drop` during an unwind
            // aborts, and the point here is to wait rather than to report.
            let _ = self.on.synchronize_for_settle();
        }
    }
}

/// **The construction-time half of the aliasing law.**  Two spans carved out of one backing
/// allocation are, to the borrow checker, one borrow; their overlap is an arithmetic fact this
/// audit checks.  A writable span may overlap nothing else of the same residency; read spans may
/// overlap one another freely.  Zero-length spans are inert and are skipped.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AliasAudit {
    admitted: Vec<(Residency, u64, u64, Access, &'static str)>,
}

impl AliasAudit {
    /// An empty audit.
    pub fn new() -> AliasAudit {
        AliasAudit::default()
    }

    /// Admit one span, refusing if it aliases something already admitted unlawfully.
    pub fn admit(&mut self, span: &ArgumentSpan) -> Partitioned<()> {
        let bytes = span.bytes().ok_or_else(|| {
            PartitionRefusal::new(
                PartitionClause::CoverWithinSpan,
                format!(
                    "`{}`: {} elements of {} octets overflow usize",
                    span.name, span.elements, span.element_bytes
                ),
            )
        })?;
        if bytes == 0 {
            return Ok(());
        }
        let start = span.address;
        let end = start.checked_add(bytes as u64).ok_or_else(|| {
            PartitionRefusal::new(
                PartitionClause::CoverWithinSpan,
                format!("`{}`: the span end overflows the address wire", span.name),
            )
        })?;
        for (residency, other_start, other_end, other_access, other_name) in &self.admitted {
            if *residency != span.residency {
                continue;
            }
            let overlaps = start < *other_end && *other_start < end;
            if !overlaps {
                continue;
            }
            if span.access == Access::Write || *other_access == Access::Write {
                return Err(PartitionRefusal::new(
                    PartitionClause::Aliasing,
                    format!(
                        "`{}` ({start:#x}..{end:#x}) overlaps `{other_name}` \
                         ({other_start:#x}..{other_end:#x}) and one of them is written",
                        span.name
                    ),
                ));
            }
        }
        self.admitted
            .push((span.residency, start, end, span.access, span.name));
        Ok(())
    }

    /// Admit a whole argument population at once.
    pub fn admit_all(spans: &[ArgumentSpan]) -> Partitioned<AliasAudit> {
        let mut audit = AliasAudit::new();
        for span in spans {
            audit.admit(span)?;
        }
        Ok(audit)
    }

    /// The admitted span population.
    pub fn len(&self) -> usize {
        self.admitted.len()
    }

    /// Whether nothing has been admitted.
    pub fn is_empty(&self) -> bool {
        self.admitted.is_empty()
    }
}

#[cfg(test)]
mod tests;
