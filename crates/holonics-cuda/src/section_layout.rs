//! **The section layout.** D3 (`partition generates layout`) of
//! [`docs/plans/THE_EXACT_DEVICE_LAW_IS_CONSTRUCTED.md`], executable.
//!
//! The Lean owner is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/SectionLayout.lean`
//! (`Soma.Holonics.Foundation.SectionLayout`).  It continues
//! [`crate::launch_law`]'s `DeviceLaunchLaw` owner into the third law, and every structure below
//! has a formal counterpart there:
//!
//! | Rust | Lean |
//! |---|---|
//! | [`IncidenceDeclaration`] | `Incidence` (`addr`, `region`) |
//! | [`SectionLayout::gather_reference`] | `Incidence.gather` |
//! | [`SectionLayout::scatter_reference`] | `Incidence.scatterAdd` |
//! | [`SectionLayout::verify_adjoint`] | `Incidence.adjoint` |
//! | [`SectionLayout::apply_reference`] | `Incidence.assembled_apply` |
//! | [`SectionLayout::assemble_dense`] | `Incidence.assembled`, `Incidence.assembled_sum_regions` |
//! | [`LocalOperator::is_symmetric`] | `Incidence.assembled_symm` |
//! | [`ScatterReceipt::Injective`] | `Incidence.scatterAdd_of_injective`, `DisjointPartition.scatter_perm` |
//! | [`ScatterReceipt::Accumulated`] | `DisjointPartition.scatterAdd_perm` |
//! | [`RegionColouring`] | `Incidence.Colouring`, `Incidence.Proper` |
//! | [`RegionColouring::verify_proper`] | `Incidence.colour_fiber_single_region` |
//! | [`SectionKernels::enact`] (colour by colour) | `Incidence.colour_schedule` |
//!
//! ## What the law is for
//!
//! The shared-section work in `crates/holonic-engine/kernels/` performs, by hand and once per
//! kernel, a gather by region incidence into a local tile, a shared local material application, and
//! a transposed scatter.  That is a tile abstraction specialized to exact arithmetic, written out
//! each time.  Here it is **generated**: a caller declares an [`IncidenceDeclaration`] — for each
//! region, the ordered list of global addresses it is incident to — and
//! [`SectionLayout::generate`] derives from it
//!
//! * the gather index table and the local tile extents ([`TileExtents`]),
//! * the residency and launch requirement of each arm, with the dynamic shared surface **as a
//!   function of the declared tile width** rather than as an authored number,
//! * the transposed scatter table, and
//! * the scatter arm's **receipt, which is exactly one of two**: an injectivity proof over the
//!   incidence, or a named *exact* associative-commutative accumulation.
//!
//! A non-injective incidence with no declared accumulation is a construction refusal
//! ([`SectionClause::ScatterReceipt`]), because such a scatter has no well-defined result —
//! `DeviceLaunchLaw.DisjointPartition.scatter_order_dependent` is the counterexample.
//!
//! **A floating accumulation is refused by type.**  [`AccumulationLaw`] has no floating variant and
//! none can be added without breaking the Lean pairing, which states every law over a
//! `CommSemiring`; floating addition is not associative and `f64` is not one.  This is not a
//! runtime check that could be bypassed: there is no value of [`AccumulationLaw`] that names a
//! float.
//!
//! ## What is generated and what is declared
//!
//! Declared by the caller: the incidence table, the local operator's coefficients, and which of the
//! two scatter receipts is being claimed.  Generated here: the gather table, the tile extents, the
//! shared-memory extent, every [`crate::launch_law::LaunchRequirement`], every
//! [`crate::launch_law::DisjointPartition`], the transposed scatter table, and — for an
//! accumulating scatter — the region colouring that makes the device arm race-free without a single
//! atomic.

use std::collections::BTreeMap;
use std::fmt;

use holonics::ratio::ring::{AccumulationLaw, ExactRing, ModularWords};
use holonics_portable::section_layout_cuda as section_cuda;

use crate::launch_law::{
    Access, ArgumentRequirement, BlockConstraint, Coverage, DeviceReadSpan, DeviceWriteSpan,
    DisjointPartition, Extent, FullyProvedReceipt, LaunchEvidence, LaunchLimits, LaunchRequirement,
    LawfulLaunch, PartitionRefusal, PartitionedWrite, ScalarArgument, ScalarRequirement,
    ScalarWidth, ScatterLaw, SharedRequirement, StreamRequirement,
};
use crate::{Context, CudaError, Device, DeviceBuffer, Dim3, Function, Module, Result, Stream};

/// A named clause of the CUDA section-layout contract. A refusal identifies exactly one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SectionClause {
    /// The global field carries one positive address extent.
    PositiveGlobalExtent,
    /// The global address extent is representable in the `u32` index wire the device reads.
    GlobalExtentWire,
    /// The declaration carries one or more regions.
    PositiveRegions,
    /// The slot population is positive and representable in the `u32` index wire.
    SlotWire,
    /// The offsets table carries one boundary per region plus its end, and starts at zero.
    OffsetsLength,
    /// The offsets table is monotone and every region carries at least one slot.
    RegionWidth,
    /// The offsets table ends exactly at the address table's own length.
    OffsetsEnd,
    /// Every declared global address is below the declared global extent.
    AddressWithinExtent,
    /// A declared extent product does not fit its wire.
    ExtentProduct,
    /// The declared scatter receipt is not the one the incidence supports.
    ScatterReceipt,
    /// The declared accumulation is not an exact ring.
    AccumulationLaw,
    /// The declared accumulation has no device realization.
    AccumulationOnDevice,
    /// The local operator's width is not the declared tile width.
    LocalOperatorWidth,
    /// A presented field or tile does not carry the declared extent.
    SpanExtent,
    /// The exact arithmetic refused: a checked integer sum or product left its wire.
    ExactArithmetic,
    /// A word presented for the device is not the canonical residue of its class in the declared
    /// ring, i.e. it does not lie in `[0, modulus)`.
    CanonicalWord,
    /// A bounded derivation was asked for more work than the caller's declared ceiling admits.
    WorkCeiling,
    /// The generated launch shape could not be derived from the caller's device evidence.
    LaunchDerivation,
    /// A named colour class does not exist in this colouring.
    ColourClass,
    /// The colouring is not proper for this incidence.
    ColouringProper,
    /// The host descriptors used to stage the device tables do not match the descriptors supplied
    /// for enactment.
    TableProvenance,
}

impl SectionClause {
    /// The clause's own name.
    pub const fn name(self) -> &'static str {
        match self {
            SectionClause::PositiveGlobalExtent => "positive-global-extent",
            SectionClause::GlobalExtentWire => "global-extent-wire",
            SectionClause::PositiveRegions => "positive-regions",
            SectionClause::SlotWire => "slot-wire",
            SectionClause::OffsetsLength => "offsets-length",
            SectionClause::RegionWidth => "region-width",
            SectionClause::OffsetsEnd => "offsets-end",
            SectionClause::AddressWithinExtent => "address-within-extent",
            SectionClause::ExtentProduct => "extent-product",
            SectionClause::ScatterReceipt => "scatter-receipt",
            SectionClause::AccumulationLaw => "accumulation-law",
            SectionClause::AccumulationOnDevice => "accumulation-on-device",
            SectionClause::LocalOperatorWidth => "local-operator-width",
            SectionClause::SpanExtent => "span-extent",
            SectionClause::ExactArithmetic => "exact-arithmetic",
            SectionClause::CanonicalWord => "canonical-word",
            SectionClause::WorkCeiling => "work-ceiling",
            SectionClause::LaunchDerivation => "launch-derivation",
            SectionClause::ColourClass => "colour-class",
            SectionClause::ColouringProper => "colouring-proper",
            SectionClause::TableProvenance => "table-provenance",
        }
    }
}

/// A typed refusal of the section-layout declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SectionRefusal {
    /// The single clause that failed.
    pub clause: SectionClause,
    /// The exact quantities that failed it.
    pub detail: String,
}

impl SectionRefusal {
    /// Name a violated clause.
    pub fn new(clause: SectionClause, detail: impl Into<String>) -> Self {
        Self {
            clause,
            detail: detail.into(),
        }
    }
}

impl fmt::Display for SectionRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "section layout clause `{}` refused: {}",
            self.clause.name(),
            self.detail
        )
    }
}

impl std::error::Error for SectionRefusal {}

/// The section-layout operation's construction result.
pub type Sectioned<T> = core::result::Result<T, SectionRefusal>;

impl From<SectionRefusal> for CudaError {
    fn from(refusal: SectionRefusal) -> CudaError {
        CudaError {
            code: -1,
            name: String::from("SECTION_LAYOUT_REFUSAL"),
            message: refusal.detail,
            context: refusal.clause.name(),
        }
    }
}

fn refuse<T>(clause: SectionClause, detail: impl Into<String>) -> Sectioned<T> {
    Err(SectionRefusal::new(clause, detail))
}

/// Refuse a non-canonical word at the section boundary; ring arithmetic itself remains total.
fn verify_canonical_words(ring: &ModularWords, values: &[u64], table: &str) -> Sectioned<()> {
    for (at, value) in values.iter().enumerate() {
        if !ring.is_canonical(*value) {
            return refuse(
                SectionClause::CanonicalWord,
                format!(
                    "{table} entry {at} is {value}, which is not the canonical residue {} of its class in Z/{}; \
                     a word presented to the device is canonical or refused",
                    ring.canonical(*value),
                    ring.modulus()
                ),
            );
        }
    }
    Ok(())
}

fn from_partition(refusal: PartitionRefusal) -> SectionRefusal {
    SectionRefusal::new(
        SectionClause::ExtentProduct,
        format!("{}: {}", refusal.clause.name(), refusal.detail),
    )
}

// ---------------------------------------------------------------------------------------------
// The declaration
// ---------------------------------------------------------------------------------------------

/// **The incidence declaration: regions, each with an ordered list of global addresses.**
///
/// Carried in the compressed form the device reads directly: an `offsets` table with one boundary
/// per region plus its end, and a flat `addresses` table in region-major order.  Region `r` is
/// incident, in order, to `addresses[offsets[r] .. offsets[r + 1]]`.
///
/// **The fields are private and there is exactly one constructor**, so an `IncidenceDeclaration`
/// value is always one that passed every clause: there is no `Default`, no `Deserialize`, no public
/// field and no `Clone`-then-mutate path.  The validation is exact and complete:
///
/// * the global extent is positive and fits the `u32` index wire the device entries read;
/// * the offsets table starts at zero, carries `regions + 1` boundaries, is strictly increasing
///   (so no region is empty), and ends exactly at the address table's length;
/// * every declared address is strictly below the declared global extent;
/// * the region and slot populations fit their wires.
///
/// **Nothing is allocated from a declared number.**  The two tables arrive *by value*, so their
/// lengths are facts about allocations the caller already holds rather than declarations to be
/// trusted; the only derived allocations ([`SectionLayout::generate`]) are sized by
/// `addresses.len()` and `offsets.len()`, never by `global_extent`.  A hostile declaration naming a
/// global extent of `u32::MAX` therefore costs nothing until a field of that extent is actually
/// presented, and presenting one is an ordinary allocation the caller makes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IncidenceDeclaration {
    global_extent: usize,
    offsets: Vec<usize>,
    addresses: Vec<u32>,
}

impl IncidenceDeclaration {
    /// Declare an incidence from a validated offsets table and a flat address table.
    pub fn new(
        global_extent: usize,
        offsets: Vec<usize>,
        addresses: Vec<u32>,
    ) -> Sectioned<IncidenceDeclaration> {
        if global_extent == 0 {
            return refuse(
                SectionClause::PositiveGlobalExtent,
                "a section carries one positive global address extent",
            );
        }
        if global_extent > u32::MAX as usize {
            return refuse(
                SectionClause::GlobalExtentWire,
                format!(
                    "global extent {global_extent} exceeds the u32 index wire the device entries read"
                ),
            );
        }
        if offsets.len() < 2 {
            return refuse(
                SectionClause::OffsetsLength,
                format!(
                    "an offsets table carries one boundary per region plus its end; got {}",
                    offsets.len()
                ),
            );
        }
        if offsets[0] != 0 {
            return refuse(
                SectionClause::OffsetsLength,
                format!("the offsets table starts at {} rather than 0", offsets[0]),
            );
        }
        for (region, window) in offsets.windows(2).enumerate() {
            if window[1] <= window[0] {
                return refuse(
                    SectionClause::RegionWidth,
                    format!(
                        "region {region} spans {}..{}; every region carries at least one slot and \
                         the offsets table is strictly increasing",
                        window[0], window[1]
                    ),
                );
            }
        }
        let end = *offsets.last().expect("the table carries two or more boundaries");
        if end != addresses.len() {
            return refuse(
                SectionClause::OffsetsEnd,
                format!(
                    "the offsets table ends at {end}; the address table carries {} addresses",
                    addresses.len()
                ),
            );
        }
        if addresses.is_empty() {
            return refuse(
                SectionClause::SlotWire,
                "an incidence carries one or more slots",
            );
        }
        if addresses.len() > u32::MAX as usize {
            return refuse(
                SectionClause::SlotWire,
                format!(
                    "{} slots exceed the u32 slot wire the device entries read",
                    addresses.len()
                ),
            );
        }
        if offsets.len() - 1 > u32::MAX as usize {
            return refuse(
                SectionClause::PositiveRegions,
                format!(
                    "{} regions exceed the u32 region wire the device entries read",
                    offsets.len() - 1
                ),
            );
        }
        for (slot, address) in addresses.iter().enumerate() {
            if *address as usize >= global_extent {
                return refuse(
                    SectionClause::AddressWithinExtent,
                    format!(
                        "slot {slot} declares global address {address}; the declared extent is \
                         {global_extent}"
                    ),
                );
            }
        }
        Ok(IncidenceDeclaration {
            global_extent,
            offsets,
            addresses,
        })
    }

    /// Declare an incidence whose regions all carry the same width: the ordinary tile form.
    pub fn uniform(
        global_extent: usize,
        width: usize,
        addresses: Vec<u32>,
    ) -> Sectioned<IncidenceDeclaration> {
        if width == 0 {
            return refuse(
                SectionClause::RegionWidth,
                "a uniform incidence carries one positive region width",
            );
        }
        if !addresses.len().is_multiple_of(width) {
            return refuse(
                SectionClause::OffsetsEnd,
                format!(
                    "{} addresses are not a whole number of {width}-slot regions",
                    addresses.len()
                ),
            );
        }
        let regions = addresses.len() / width;
        // `regions + 1` is bounded by the address table's own length, an allocation the caller
        // already holds, so no declared number sizes this vector.
        let offsets: Vec<usize> = (0..=regions).map(|region| region * width).collect();
        IncidenceDeclaration::new(global_extent, offsets, addresses)
    }

    /// The declared global address extent.
    pub const fn global_extent(&self) -> usize {
        self.global_extent
    }

    /// The declared region population.
    pub fn regions(&self) -> usize {
        self.offsets.len() - 1
    }

    /// The declared slot population, `Σ_r width(r)`.
    pub fn slots(&self) -> usize {
        self.addresses.len()
    }

    /// The ordered global addresses of one region, or `None` past the region population.
    pub fn region(&self, region: usize) -> Option<&[u32]> {
        if region >= self.regions() {
            return None;
        }
        Some(&self.addresses[self.offsets[region]..self.offsets[region + 1]])
    }

    /// The width of one region, or `None` past the region population.
    pub fn width(&self, region: usize) -> Option<usize> {
        self.region(region).map(<[u32]>::len)
    }

    /// The offsets table.
    pub fn offsets(&self) -> &[usize] {
        &self.offsets
    }

    /// The flat address table, in region-major order.  **This is the gather index table**: the
    /// gather arm is the declaration read verbatim.
    pub fn addresses(&self) -> &[u32] {
        &self.addresses
    }
}

/// **The local tile extents, derived from the declaration.**
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TileExtents {
    regions: usize,
    slots: usize,
    max_width: usize,
    uniform_width: Option<usize>,
    tile_bytes: u32,
}

impl TileExtents {
    /// The region population: one tile per region.
    pub const fn regions(&self) -> usize {
        self.regions
    }

    /// The slot population: the local buffer's element extent.
    pub const fn slots(&self) -> usize {
        self.slots
    }

    /// The widest declared region.  The local operator is a dense `max_width × max_width` table and
    /// the dynamic shared surface is this many exact words.
    pub const fn max_width(&self) -> usize {
        self.max_width
    }

    /// The common region width when every region has one, otherwise `None`.  A uniform incidence
    /// generates a uniform-stride gather partition; a ragged one generates an offsets partition.
    pub const fn uniform_width(&self) -> Option<usize> {
        self.uniform_width
    }

    /// The dynamic shared octets one block needs: `max_width` exact 64-bit words.  **Generated**
    /// from the declaration with checked arithmetic, never typed in.
    pub const fn tile_bytes(&self) -> u32 {
        self.tile_bytes
    }
}

// ---------------------------------------------------------------------------------------------
// The scatter receipt
// ---------------------------------------------------------------------------------------------

/// Admit a declared accumulation: `holonics::ratio::ring::AccumulationLaw` names the ring law,
/// and the section layout refuses a degenerate modulus before any allocation.
fn admit(law: AccumulationLaw) -> Sectioned<AccumulationLaw> {
    match law {
        AccumulationLaw::IntegerAdd => Ok(law),
        AccumulationLaw::ModularAdd { modulus } if modulus >= 2 => Ok(law),
        AccumulationLaw::ModularAdd { modulus } => refuse(
            SectionClause::AccumulationLaw,
            format!("a modulus of {modulus} does not name a ring with two distinct elements"),
        ),
    }
}

/// **What the caller claims about the scatter arm.**  There are exactly two admissible claims and
/// no default: a declaration must say which one it is making.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScatterRequest {
    /// The incidence is injective: no global address is named by two slots.  Verified exactly
    /// during generation; a colliding pair is named in the refusal.
    Injective,
    /// Colliding slots combine through a named exact associative-commutative accumulation.
    Accumulated(AccumulationLaw),
}

/// **The scatter arm's receipt: exactly one of two.**
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScatterReceipt {
    /// Proved: each global address is named by at most one slot, so plain stores are disjoint and
    /// order-independent (`DeviceLaunchLaw.DisjointPartition.scatter_perm`).
    Injective,
    /// Declared: colliding slots combine through this exact accumulation, so the result is
    /// order-independent for any index map (`DisjointPartition.scatterAdd_perm`).
    Accumulated(AccumulationLaw),
}

impl ScatterReceipt {
    /// The receipt's own name.
    pub fn name(self) -> String {
        match self {
            ScatterReceipt::Injective => String::from("injective-incidence"),
            ScatterReceipt::Accumulated(law) => law.name(),
        }
    }

    /// The D2 scatter law this receipt presents to [`DisjointPartition::scatter`].
    pub const fn scatter_law(self) -> ScatterLaw {
        match self {
            ScatterReceipt::Injective => ScatterLaw::Injective,
            ScatterReceipt::Accumulated(_) => ScatterLaw::Accumulated,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The generated layout
// ---------------------------------------------------------------------------------------------

/// The generated transpose of the gather table: for each **touched** global address, the slots
/// incident to it.  This is `Pᵀ` as data.
///
/// It is built by sorting the `(address, slot)` pairs, so every allocation is sized by the slot
/// population — a fact about the caller's own table — and **nothing is sized by the declared global
/// extent**.  A counting sort indexed by the global extent would have been simpler and would have
/// been a hostile-declaration allocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransposeTable {
    touched: Vec<u32>,
    segment: Vec<u32>,
    slots: Vec<u32>,
}

impl TransposeTable {
    /// The distinct global addresses this incidence reaches, ascending.
    pub fn touched(&self) -> &[u32] {
        &self.touched
    }

    /// The slots incident to `touched()[at]`.
    pub fn fibre(&self, at: usize) -> Option<&[u32]> {
        if at >= self.touched.len() {
            return None;
        }
        Some(&self.slots[self.segment[at] as usize..self.segment[at + 1] as usize])
    }

    /// The largest fibre: how many slots reach one address.  One means the incidence is injective.
    pub fn max_multiplicity(&self) -> usize {
        (0..self.touched.len())
            .filter_map(|at| self.fibre(at))
            .map(<[u32]>::len)
            .max()
            .unwrap_or(0)
    }
}

/// **The generated section layout.**  Everything a section operator needs on either side, derived
/// from one [`IncidenceDeclaration`] and one [`ScatterRequest`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SectionLayout {
    incidence: IncidenceDeclaration,
    slot_region: Vec<u32>,
    transpose: TransposeTable,
    receipt: ScatterReceipt,
    tile: TileExtents,
    device_offsets: Vec<u32>,
}

impl SectionLayout {
    /// **Generate the layout.**  The gather table, the tile extents, the transposed scatter table
    /// and the scatter receipt all come out of the declaration; nothing here is authored.
    ///
    /// Work: `O(slots log slots)` for the transpose sort plus `O(slots + regions)` for everything
    /// else.  Every allocation is sized by `slots` or `regions`, both lengths of tables the caller
    /// already holds.
    pub fn generate(
        incidence: IncidenceDeclaration,
        request: ScatterRequest,
    ) -> Sectioned<SectionLayout> {
        let regions = incidence.regions();
        let slots = incidence.slots();

        // Slot -> region, read off the validated offsets table.
        let mut slot_region: Vec<u32> = Vec::with_capacity(slots);
        for region in 0..regions {
            let width = incidence.width(region).expect("region below the population");
            for _ in 0..width {
                slot_region.push(region as u32);
            }
        }

        // The transpose, by sorting `(address, slot)`.
        let mut pairs: Vec<(u32, u32)> = incidence
            .addresses()
            .iter()
            .enumerate()
            .map(|(slot, address)| (*address, slot as u32))
            .collect();
        pairs.sort_unstable();
        let mut touched: Vec<u32> = Vec::new();
        let mut segment: Vec<u32> = vec![0];
        let mut ordered: Vec<u32> = Vec::with_capacity(slots);
        for (address, slot) in &pairs {
            if touched.last() != Some(address) {
                touched.push(*address);
                segment.push(ordered.len() as u32);
            }
            ordered.push(*slot);
            let last = segment.len() - 1;
            segment[last] = ordered.len() as u32;
        }
        let transpose = TransposeTable {
            touched,
            segment,
            slots: ordered,
        };

        // The scatter receipt: exactly one of two, and never neither.
        let receipt = match request {
            ScatterRequest::Injective => {
                for at in 0..transpose.touched.len() {
                    let fibre = transpose.fibre(at).expect("a touched address has a fibre");
                    if fibre.len() > 1 {
                        return refuse(
                            SectionClause::ScatterReceipt,
                            format!(
                                "slots {} and {} are both incident to global address {}; an \
                                 injective receipt was claimed, and a colliding incidence is \
                                 order-dependent under plain stores — declare an exact \
                                 associative-commutative accumulation instead",
                                fibre[0], fibre[1], transpose.touched[at]
                            ),
                        );
                    }
                }
                ScatterReceipt::Injective
            }
            ScatterRequest::Accumulated(law) => ScatterReceipt::Accumulated(admit(law)?),
        };

        // The tile extents, with the shared surface a checked function of the widest region.
        let mut max_width = 0usize;
        let mut uniform = incidence.width(0);
        for region in 0..regions {
            let width = incidence.width(region).expect("region below the population");
            max_width = max_width.max(width);
            if uniform != Some(width) {
                uniform = None;
            }
        }
        let tile_bytes = max_width
            .checked_mul(core::mem::size_of::<u64>())
            .and_then(|bytes| u32::try_from(bytes).ok())
            .ok_or_else(|| {
                SectionRefusal::new(
                    SectionClause::ExtentProduct,
                    format!(
                        "a tile of {max_width} exact words exceeds the u32 dynamic shared wire"
                    ),
                )
            })?;
        let tile = TileExtents {
            regions,
            slots,
            max_width,
            uniform_width: uniform,
            tile_bytes,
        };

        let device_offsets: Vec<u32> = incidence
            .offsets()
            .iter()
            .map(|offset| *offset as u32)
            .collect();

        Ok(SectionLayout {
            incidence,
            slot_region,
            transpose,
            receipt,
            tile,
            device_offsets,
        })
    }

    /// The declaration this layout was generated from.
    pub const fn incidence(&self) -> &IncidenceDeclaration {
        &self.incidence
    }

    /// The derived tile extents.
    pub const fn tile(&self) -> TileExtents {
        self.tile
    }

    /// The scatter arm's receipt.
    pub const fn receipt(&self) -> ScatterReceipt {
        self.receipt
    }

    /// The generated transpose.
    pub const fn transpose(&self) -> &TransposeTable {
        &self.transpose
    }

    /// The declared global address extent.
    pub const fn global_extent(&self) -> usize {
        self.incidence.global_extent
    }

    /// The slot population.
    pub fn slots(&self) -> usize {
        self.incidence.slots()
    }

    /// The region population.
    pub fn regions(&self) -> usize {
        self.incidence.regions()
    }

    /// The region one slot belongs to, or `None` past the slot population.
    pub fn region_of_slot(&self, slot: usize) -> Option<usize> {
        self.slot_region.get(slot).map(|region| *region as usize)
    }

    /// The gather index table the device reads: slot to global address.
    pub fn gather_index(&self) -> &[u32] {
        self.incidence.addresses()
    }

    /// The region boundary table the device reads.
    pub fn device_offsets(&self) -> &[u32] {
        &self.device_offsets
    }

    // --- the generated partitions ------------------------------------------------------------

    /// **The gather arm's write partition**, generated from the incidence: region `r` writes
    /// exactly `local[offsets[r] .. offsets[r + 1])`.  Uniform widths generate the uniform-stride
    /// form; ragged widths generate the offsets form.  Both are
    /// `DeviceLaunchLaw.DisjointPartition`.
    pub fn gather_partition(&self) -> Sectioned<DisjointPartition> {
        match self.tile.uniform_width {
            Some(width) => {
                DisjointPartition::uniform(self.tile.slots, self.tile.regions, width, width)
                    .map_err(from_partition)
            }
            None => DisjointPartition::from_offsets(
                self.tile.slots,
                self.incidence.offsets().to_vec(),
            )
            .map_err(from_partition),
        }
    }

    /// **The scatter arm's write partition under an injective receipt**: one global address per
    /// slot, proved non-colliding.  Refused for an accumulating receipt, which is partitioned
    /// colour by colour instead ([`SectionLayout::colour_partition`]).
    pub fn scatter_partition(&self) -> Sectioned<DisjointPartition> {
        match self.receipt {
            ScatterReceipt::Injective => {
                let targets: Vec<usize> = self
                    .incidence
                    .addresses()
                    .iter()
                    .map(|address| *address as usize)
                    .collect();
                DisjointPartition::scatter(self.global_extent(), targets, ScatterLaw::Injective)
                    .map_err(from_partition)
            }
            ScatterReceipt::Accumulated(_) => refuse(
                SectionClause::ScatterReceipt,
                "an accumulating scatter is partitioned one colour class at a time; use \
                 `colour_partition`",
            ),
        }
    }

    /// **One colour class's write partition**: the distinct global addresses the regions of that
    /// colour reach, proved non-colliding *because the colouring is proper*.  Each colour launch is
    /// therefore an injective scatter, which is what makes the accumulating device arm race-free
    /// with no atomic (`SectionLayout.Incidence.colour_fiber_single_region`).
    pub fn colour_partition(
        &self,
        colouring: &RegionColouring,
        colour: usize,
    ) -> Sectioned<DisjointPartition> {
        let class = colouring.class(colour).ok_or_else(|| {
            SectionRefusal::new(
                SectionClause::ColourClass,
                format!(
                    "colour {colour} is not one of this colouring's {}",
                    colouring.colour_count()
                ),
            )
        })?;
        let mut targets: Vec<usize> = Vec::new();
        for region in class {
            let addresses = self.incidence.region(*region as usize).ok_or_else(|| {
                SectionRefusal::new(
                    SectionClause::ColourClass,
                    format!("colour {colour} names region {region}, past the population"),
                )
            })?;
            for address in addresses {
                targets.push(*address as usize);
            }
        }
        targets.sort_unstable();
        targets.dedup();
        DisjointPartition::scatter(self.global_extent(), targets, ScatterLaw::Injective)
            .map_err(from_partition)
    }

    // --- the generated launch requirements ----------------------------------------------------

    /// **The gather arm's launch requirement**, generated: one thread per declared slot, the three
    /// buffers with the residency, width and access the entry's own signature carries, and the slot
    /// population as a declared scalar.
    pub fn gather_requirement(&self) -> LaunchRequirement {
        LaunchRequirement {
            kernel: section_cuda::GATHER_ENTRY_SYMBOL,
            extent: self.slots() as u64,
            coverage: Coverage::Guarded,
            block: BlockConstraint::ANY,
            shared: SharedRequirement::NONE,
            arguments: vec![
                ArgumentRequirement::device(
                    "source",
                    Access::Read,
                    8,
                    Extent::Exactly(self.global_extent()),
                ),
                ArgumentRequirement::device("index", Access::Read, 4, Extent::Exactly(self.slots())),
                ArgumentRequirement::device("local", Access::Write, 8, Extent::Exactly(self.slots())),
            ],
            scalars: vec![ScalarRequirement::trailing("slots", ScalarWidth::U64, 3)],
            stream: StreamRequirement::Ordered,
        }
    }

    /// **The local-application arm's launch requirement**, generated from the tile and the card.
    ///
    /// One block per region — an *exact* cover of `regions × block` threads, with the block a whole
    /// number of the card's own warps, widened to the declared tile and capped by the entry's and
    /// the card's own limits.  The dynamic shared surface is
    /// [`TileExtents::tile_bytes`], a checked function of the declared tile width; not one of these
    /// numbers is authored here.
    pub fn apply_requirement(
        &self,
        limits: &LaunchLimits,
        operator_width: usize,
    ) -> Sectioned<LaunchRequirement> {
        if operator_width != self.tile.max_width {
            return refuse(
                SectionClause::LocalOperatorWidth,
                format!(
                    "the local operator is {operator_width} wide; the declared tile is {}",
                    self.tile.max_width
                ),
            );
        }
        let warp = limits.warp().ok_or_else(|| {
            SectionRefusal::new(
                SectionClause::LaunchDerivation,
                "the apply arm's block is a whole number of the card's warps and the caller's \
                 evidence carries no warp; present `LaunchEvidence::Device`",
            )
        })?;
        if warp == 0 {
            return refuse(
                SectionClause::LaunchDerivation,
                "the card reported a zero warp",
            );
        }
        let cap = limits
            .device_max_threads_per_block()
            .map_or(limits.function_max_threads_per_block(), |device| {
                limits.function_max_threads_per_block().min(device)
            });
        let wanted = u32::try_from(self.tile.max_width).map_err(|_| {
            SectionRefusal::new(
                SectionClause::ExtentProduct,
                format!("a tile of {} slots exceeds the u32 block wire", self.tile.max_width),
            )
        })?;
        let rounded = wanted.div_ceil(warp).checked_mul(warp).ok_or_else(|| {
            SectionRefusal::new(
                SectionClause::ExtentProduct,
                format!("rounding a {wanted}-slot tile up to a {warp}-lane warp overflows u32"),
            )
        })?;
        let block_x = if rounded <= cap { rounded } else { cap / warp * warp };
        if block_x == 0 {
            return refuse(
                SectionClause::LaunchDerivation,
                format!("a {warp}-lane warp does not fit the entry's {cap}-thread block cap"),
            );
        }
        let extent = (self.tile.regions as u64).checked_mul(block_x as u64).ok_or_else(|| {
            SectionRefusal::new(
                SectionClause::ExtentProduct,
                format!(
                    "{} regions of {block_x} threads overflow the u64 thread population",
                    self.tile.regions
                ),
            )
        })?;
        Ok(LaunchRequirement {
            kernel: section_cuda::APPLY_ENTRY_SYMBOL,
            extent,
            coverage: Coverage::Exact,
            block: BlockConstraint {
                exact: Some(Dim3::x(block_x)),
                multiple_of: None,
                warp_multiple: true,
                max_threads: None,
            },
            shared: SharedRequirement {
                per_block_bytes: self.tile.tile_bytes,
                per_thread_bytes: 0,
            },
            arguments: vec![
                ArgumentRequirement::device("local", Access::Write, 8, Extent::Exactly(self.slots())),
                ArgumentRequirement::device(
                    "offsets",
                    Access::Read,
                    4,
                    Extent::Exactly(self.regions() + 1),
                ),
                ArgumentRequirement::device(
                    "coefficients",
                    Access::Read,
                    8,
                    Extent::Exactly(operator_width.checked_mul(operator_width).ok_or_else(
                        || {
                            SectionRefusal::new(
                                SectionClause::ExtentProduct,
                                format!("a {operator_width}-wide dense operator overflows usize"),
                            )
                        },
                    )?),
                ),
            ],
            scalars: vec![
                ScalarRequirement::trailing("regions", ScalarWidth::U64, 3),
                ScalarRequirement::trailing("tile_width", ScalarWidth::U64, 3),
            ],
            stream: StreamRequirement::Ordered,
        })
    }

    /// **The injective scatter arm's launch requirement**: one thread per slot, plain stores.
    pub fn scatter_store_requirement(&self) -> Sectioned<LaunchRequirement> {
        if self.receipt != ScatterReceipt::Injective {
            return refuse(
                SectionClause::ScatterReceipt,
                "plain stores are admissible only under an injective receipt",
            );
        }
        Ok(LaunchRequirement {
            kernel: section_cuda::SCATTER_STORE_ENTRY_SYMBOL,
            extent: self.slots() as u64,
            coverage: Coverage::Guarded,
            block: BlockConstraint::ANY,
            shared: SharedRequirement::NONE,
            arguments: vec![
                ArgumentRequirement::device("local", Access::Read, 8, Extent::Exactly(self.slots())),
                ArgumentRequirement::device("index", Access::Read, 4, Extent::Exactly(self.slots())),
                ArgumentRequirement::device(
                    "target",
                    Access::Write,
                    8,
                    Extent::Exactly(self.global_extent()),
                ),
            ],
            scalars: vec![ScalarRequirement::trailing("slots", ScalarWidth::U64, 3)],
            stream: StreamRequirement::Ordered,
        })
    }

    /// **One colour class's accumulating scatter launch requirement**: one thread per region of the
    /// class, each walking its own region's slots in order.
    pub fn scatter_add_requirement(&self, class_regions: usize) -> Sectioned<LaunchRequirement> {
        match self.receipt {
            ScatterReceipt::Accumulated(_) => {}
            ScatterReceipt::Injective => {
                return refuse(
                    SectionClause::ScatterReceipt,
                    "an injective receipt scatters by plain store; use `scatter_store_requirement`",
                )
            }
        }
        if class_regions == 0 {
            return refuse(
                SectionClause::ColourClass,
                "a colour class carries one or more regions",
            );
        }
        Ok(LaunchRequirement {
            kernel: section_cuda::SCATTER_ADD_ENTRY_SYMBOL,
            extent: class_regions as u64,
            coverage: Coverage::Guarded,
            block: BlockConstraint::ANY,
            shared: SharedRequirement::NONE,
            arguments: vec![
                ArgumentRequirement::device("local", Access::Read, 8, Extent::Exactly(self.slots())),
                ArgumentRequirement::device("index", Access::Read, 4, Extent::Exactly(self.slots())),
                ArgumentRequirement::device(
                    "offsets",
                    Access::Read,
                    4,
                    Extent::Exactly(self.regions() + 1),
                ),
                ArgumentRequirement::device(
                    "colour_regions",
                    Access::Read,
                    4,
                    Extent::Exactly(class_regions),
                ),
                ArgumentRequirement::device(
                    "target",
                    Access::Write,
                    8,
                    Extent::Exactly(self.global_extent()),
                ),
            ],
            scalars: vec![ScalarRequirement::trailing("count", ScalarWidth::U64, 5)],
            stream: StreamRequirement::Ordered,
        })
    }

    // --- the colouring -------------------------------------------------------------------------

    /// **Compute the region colouring exactly**, by greedy colouring of the region conflict graph:
    /// two regions conflict when they are incident to a common global address.
    ///
    /// The conflict graph is never materialized.  Each region's forbidden colour set is read
    /// through the generated transpose, so the total work is `Σ_a deg(a)²` where `deg(a)` is the
    /// number of slots incident to address `a`.  **That number is computed first, with checked
    /// arithmetic, and compared against the caller's declared `work_ceiling`**; a hostile incidence
    /// concentrating every slot on one address is refused by
    /// [`SectionClause::WorkCeiling`] before the colouring loop runs, rather than being discovered
    /// by exhausting the machine.
    ///
    /// The greedy colouring uses at most `Δ + 1` colours, where `Δ` is the largest conflict degree.
    /// It is not claimed to be optimal; it is claimed to be *proper*, which is what the race-freedom
    /// argument needs, and [`RegionColouring::verify_proper`] witnesses that executably.
    pub fn colouring(&self, work_ceiling: usize) -> Sectioned<RegionColouring> {
        let mut conflict_work = 0usize;
        for at in 0..self.transpose.touched.len() {
            let degree = self.transpose.fibre(at).expect("a touched address has a fibre").len();
            let square = degree.checked_mul(degree).ok_or_else(|| {
                SectionRefusal::new(
                    SectionClause::ExtentProduct,
                    format!("a fibre of {degree} slots squared overflows usize"),
                )
            })?;
            conflict_work = conflict_work.checked_add(square).ok_or_else(|| {
                SectionRefusal::new(
                    SectionClause::ExtentProduct,
                    format!("the conflict work past address index {at} overflows usize"),
                )
            })?;
            if conflict_work > work_ceiling {
                return refuse(
                    SectionClause::WorkCeiling,
                    format!(
                        "colouring this incidence costs at least {conflict_work} conflict steps; \
                         the declared ceiling is {work_ceiling}"
                    ),
                );
            }
        }

        let regions = self.regions();
        // Both vectors are sized by the region population, the length of the caller's own offsets
        // table less one; no declared number sizes either.
        let mut colours: Vec<u32> = vec![u32::MAX; regions];
        let mut forbidden_stamp: Vec<u32> = vec![u32::MAX; regions];
        let mut colour_count = 0usize;

        // The address -> fibre lookup, over the sorted touched table.
        for region in 0..regions {
            let addresses = self.incidence.region(region).expect("region below the population");
            for address in addresses {
                let at = match self.transpose.touched.binary_search(address) {
                    Ok(at) => at,
                    Err(_) => {
                        return refuse(
                            SectionClause::AddressWithinExtent,
                            format!("address {address} is missing from its own transpose"),
                        )
                    }
                };
                for slot in self.transpose.fibre(at).expect("a touched address has a fibre") {
                    let other = self.slot_region[*slot as usize] as usize;
                    if other == region {
                        continue;
                    }
                    let colour = colours[other];
                    if colour != u32::MAX {
                        forbidden_stamp[colour as usize] = region as u32;
                    }
                }
            }
            let mut colour = 0usize;
            while colour < regions && forbidden_stamp[colour] == region as u32 {
                colour += 1;
            }
            if colour >= regions {
                return refuse(
                    SectionClause::ColouringProper,
                    format!("region {region} conflicts with every available colour"),
                );
            }
            colours[region] = colour as u32;
            colour_count = colour_count.max(colour + 1);
        }

        let mut classes: Vec<Vec<u32>> = vec![Vec::new(); colour_count];
        for (region, colour) in colours.iter().enumerate() {
            classes[*colour as usize].push(region as u32);
        }
        Ok(RegionColouring {
            colours,
            classes,
            conflict_work,
        })
    }
}

/// **A proper colouring of the declared regions.**
///
/// Its only constructor is [`SectionLayout::colouring`], which computes it exactly under a declared
/// work ceiling.  The Lean counterpart is `SectionLayout.Incidence.Colouring` with the `Proper`
/// predicate, and [`RegionColouring::verify_proper`] is the executable witness of that predicate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegionColouring {
    colours: Vec<u32>,
    classes: Vec<Vec<u32>>,
    conflict_work: usize,
}

impl RegionColouring {
    /// How many colours the greedy colouring used.
    pub fn colour_count(&self) -> usize {
        self.classes.len()
    }

    /// The regions of one colour class, in ascending order.
    pub fn class(&self, colour: usize) -> Option<&[u32]> {
        self.classes.get(colour).map(Vec::as_slice)
    }

    /// The colour of one region.
    pub fn colour_of(&self, region: usize) -> Option<u32> {
        self.colours.get(region).copied()
    }

    /// The exact conflict work this colouring cost, as counted against the declared ceiling.
    pub const fn conflict_work(&self) -> usize {
        self.conflict_work
    }

    /// **Witness the `Proper` predicate executably**: within one colour class, no two *distinct*
    /// regions are incident to a common global address.
    ///
    /// Done by sorting the `(colour, address, region)` triples and scanning adjacent pairs, which
    /// is `O(slots log slots)` — never a quadratic comparison over a declared region population.
    pub fn verify_proper(&self, layout: &SectionLayout) -> Sectioned<()> {
        if self.colours.len() != layout.regions() {
            return refuse(
                SectionClause::ColouringProper,
                format!(
                    "the colouring carries {} regions; the layout declares {}",
                    self.colours.len(),
                    layout.regions()
                ),
            );
        }
        let mut triples: Vec<(u32, u32, u32)> = Vec::with_capacity(layout.slots());
        for region in 0..layout.regions() {
            let colour = self.colours[region];
            for address in layout.incidence().region(region).expect("region below the population") {
                triples.push((colour, *address, region as u32));
            }
        }
        triples.sort_unstable();
        for pair in triples.windows(2) {
            if pair[0].0 == pair[1].0 && pair[0].1 == pair[1].1 && pair[0].2 != pair[1].2 {
                return refuse(
                    SectionClause::ColouringProper,
                    format!(
                        "regions {} and {} share colour {} and global address {}",
                        pair[0].2, pair[1].2, pair[0].0, pair[0].1
                    ),
                );
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------------------------
// The exact arithmetic and the exact CPU reference
// ---------------------------------------------------------------------------------------------
//
// `ExactRing`, `CheckedIntegers` and `ModularWords` are owned by `holonics::ratio::ring`; the
// operator and reference below compute in those exact rings.

/// **The declared local material operator**: a dense `width × width` table of exact ring elements,
/// shared by every region.  Region `r` uses its leading `width(r) × width(r)` block, which is the
/// `L_r` of the assembly identity `Σ_r P_rᵀ L_r P_r`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalOperator<V> {
    width: usize,
    entries: Vec<V>,
}

impl<V: Copy + PartialEq> LocalOperator<V> {
    /// Declare a dense local operator.  The entry table arrives by value and its length must be
    /// exactly `width * width`, checked; nothing is allocated from `width` alone.
    ///
    /// This constructor is generic in the ring's value type and therefore carries **no**
    /// representation clause: it does not know which ring `V` belongs to, so it cannot know what
    /// canonical means.  Canonicality is a clause of the *device* boundary and is held there — by
    /// [`LocalOperator::<u64>::dense_canonical`] at construction, and unconditionally by
    /// [`LocalOperator::<u64>::verify_canonical`], which [`SectionDeviceTables::stage`] runs before
    /// it allocates.
    pub fn dense(width: usize, entries: Vec<V>) -> Sectioned<LocalOperator<V>> {
        if width == 0 {
            return refuse(
                SectionClause::LocalOperatorWidth,
                "a local operator carries one positive width",
            );
        }
        let declared = width.checked_mul(width).ok_or_else(|| {
            SectionRefusal::new(
                SectionClause::ExtentProduct,
                format!("a {width}-wide dense operator overflows usize"),
            )
        })?;
        if entries.len() != declared {
            return refuse(
                SectionClause::LocalOperatorWidth,
                format!(
                    "a {width}-wide dense operator carries {declared} entries; {} were presented",
                    entries.len()
                ),
            );
        }
        Ok(LocalOperator { width, entries })
    }

    /// The operator's width.
    pub const fn width(&self) -> usize {
        self.width
    }

    /// The flat entry table, row-major.
    pub fn entries(&self) -> &[V] {
        &self.entries
    }

    /// One entry, or `None` outside the table.
    pub fn entry(&self, row: usize, column: usize) -> Option<V> {
        if row >= self.width || column >= self.width {
            return None;
        }
        self.entries.get(row * self.width + column).copied()
    }

    /// Whether the operator is symmetric.  `SectionLayout.Incidence.assembled_symm` is the theorem
    /// that a symmetric local operator assembles to a symmetric global one.
    pub fn is_symmetric(&self) -> bool {
        for row in 0..self.width {
            for column in (row + 1)..self.width {
                if self.entries[row * self.width + column] != self.entries[column * self.width + row]
                {
                    return false;
                }
            }
        }
        true
    }
}

impl LocalOperator<u64> {
    /// Declare a dense local operator **over a ring of modular words**, verifying in the same
    /// breath that every declared coefficient is the canonical residue of its class.  The width
    /// clause is [`LocalOperator::dense`]'s; the representation clause is checked at this section
    /// boundary, and a non-canonical coefficient is refused under
    /// [`SectionClause::CanonicalWord`] naming its own index.
    pub fn dense_canonical(
        width: usize,
        entries: Vec<u64>,
        ring: &ModularWords,
    ) -> Sectioned<LocalOperator<u64>> {
        let operator = LocalOperator::dense(width, entries)?;
        operator.verify_canonical(ring)?;
        Ok(operator)
    }

    /// Verify that every declared coefficient is canonical in `ring`, naming the first that is not.
    /// This is the clause [`SectionDeviceTables::stage`] discharges before it allocates anything on
    /// the card; this section boundary refuses rather than silently reducing a declaration.
    pub fn verify_canonical(&self, ring: &ModularWords) -> Sectioned<()> {
        verify_canonical_words(ring, &self.entries, "local operator coefficient")
    }
}

fn arithmetic_refusal<T>() -> Sectioned<T> {
    refuse(
        SectionClause::ExactArithmetic,
        "the exact sum or product left its representation; the exact result is refused rather \
         than wrapped",
    )
}

impl SectionLayout {
    /// **The gather arm, exactly.**  `(gather x)[s] = x[addr(s)]`.  The Lean owner is
    /// `SectionLayout.Incidence.gather`.
    pub fn gather_reference<R: ExactRing>(
        &self,
        x: &[R::Value],
    ) -> Sectioned<Vec<R::Value>> {
        if x.len() != self.global_extent() {
            return refuse(
                SectionClause::SpanExtent,
                format!(
                    "the global field carries {} values; the declared extent is {}",
                    x.len(),
                    self.global_extent()
                ),
            );
        }
        // Sized by the address table's own length, an allocation the caller already holds.
        let mut tile: Vec<R::Value> = Vec::with_capacity(self.slots());
        for address in self.incidence.addresses() {
            tile.push(x[*address as usize]);
        }
        Ok(tile)
    }

    /// **The local-application arm, exactly.**  Each region's tile is replaced by `L_r` applied to
    /// it.  The Lean owner is `SectionLayout.Incidence.applyLocal`.
    pub fn apply_local_reference<R: ExactRing>(
        &self,
        ring: &R,
        operator: &LocalOperator<R::Value>,
        tile: &mut [R::Value],
    ) -> Sectioned<()> {
        if operator.width() != self.tile.max_width {
            return refuse(
                SectionClause::LocalOperatorWidth,
                format!(
                    "the local operator is {} wide; the declared tile is {}",
                    operator.width(),
                    self.tile.max_width
                ),
            );
        }
        if tile.len() != self.slots() {
            return refuse(
                SectionClause::SpanExtent,
                format!(
                    "the tile carries {} slots; the declaration carries {}",
                    tile.len(),
                    self.slots()
                ),
            );
        }
        let mut row_values: Vec<R::Value> = Vec::with_capacity(self.tile.max_width);
        for region in 0..self.regions() {
            let lo = self.incidence.offsets()[region];
            let hi = self.incidence.offsets()[region + 1];
            let width = hi - lo;
            row_values.clear();
            for row in 0..width {
                let mut accumulator = ring.zero();
                for column in 0..width {
                    let coefficient = operator
                        .entry(row, column)
                        .expect("the operator covers the declared tile");
                    let product = match ring.mul(coefficient, tile[lo + column]) {
                        Some(product) => product,
                        None => return arithmetic_refusal(),
                    };
                    accumulator = match ring.add(accumulator, product) {
                        Some(sum) => sum,
                        None => return arithmetic_refusal(),
                    };
                }
                row_values.push(accumulator);
            }
            tile[lo..hi].copy_from_slice(&row_values);
        }
        Ok(())
    }

    /// **The scatter arm, exactly**, through the declared receipt: plain stores under an injective
    /// incidence, exact accumulation otherwise.  The Lean owner is
    /// `SectionLayout.Incidence.scatterAdd`, with `scatterAdd_of_injective` the theorem that the
    /// two agree when the incidence is injective.
    ///
    /// **The destination field is the caller's**, exactly as it is on the device: the accumulating
    /// arm adds into whatever the field already carries, which is the `σ +` of
    /// `SectionLayout.Incidence.colour_schedule`, and a caller wanting `Pᵀ L P x` alone presents a
    /// zero field.  Taking it rather than allocating it is also what keeps this owner from ever
    /// allocating from the *declared* global extent: the field's length is a fact about an
    /// allocation the caller already holds, and it is checked against the declaration.
    pub fn scatter_reference<R: ExactRing>(
        &self,
        ring: &R,
        tile: &[R::Value],
        field: &mut [R::Value],
    ) -> Sectioned<()> {
        if tile.len() != self.slots() {
            return refuse(
                SectionClause::SpanExtent,
                format!(
                    "the tile carries {} slots; the declaration carries {}",
                    tile.len(),
                    self.slots()
                ),
            );
        }
        if field.len() != self.global_extent() {
            return refuse(
                SectionClause::SpanExtent,
                format!(
                    "the global field carries {} values; the declared extent is {}",
                    field.len(),
                    self.global_extent()
                ),
            );
        }
        match self.receipt {
            ScatterReceipt::Injective => {
                for (slot, address) in self.incidence.addresses().iter().enumerate() {
                    field[*address as usize] = tile[slot];
                }
            }
            ScatterReceipt::Accumulated(_) => {
                self.scatter_add_reference(ring, tile, field)?;
            }
        }
        Ok(())
    }

    /// The accumulating scatter regardless of the receipt, which is what the adjoint identity is
    /// stated about.  Same discipline: the field is the caller's, checked against the declaration.
    fn scatter_add_reference<R: ExactRing>(
        &self,
        ring: &R,
        tile: &[R::Value],
        field: &mut [R::Value],
    ) -> Sectioned<()> {
        if tile.len() != self.slots() || field.len() != self.global_extent() {
            return refuse(
                SectionClause::SpanExtent,
                format!(
                    "the accumulating scatter takes {} slots into {} addresses; {} and {} were \
                     presented",
                    self.slots(),
                    self.global_extent(),
                    tile.len(),
                    field.len()
                ),
            );
        }
        for (slot, address) in self.incidence.addresses().iter().enumerate() {
            let at = *address as usize;
            field[at] = match ring.add(field[at], tile[slot]) {
                Some(sum) => sum,
                None => return arithmetic_refusal(),
            };
        }
        Ok(())
    }

    /// **The complete generated operator, exactly**: `scatterAdd ∘ applyLocal ∘ gather`.  This is
    /// the reference the device result is compared against bit for bit, and the Lean owner
    /// `SectionLayout.Incidence.assembled_apply` is the theorem that it equals the assembled global
    /// matrix.
    pub fn apply_reference<R: ExactRing>(
        &self,
        ring: &R,
        operator: &LocalOperator<R::Value>,
        x: &[R::Value],
    ) -> Sectioned<Vec<R::Value>> {
        // `gather_reference` refuses unless `x.len()` *is* the declared extent, so the field below
        // is sized by the caller's own allocation and never by the declaration.
        let mut tile = self.gather_reference::<R>(x)?;
        self.apply_local_reference(ring, operator, &mut tile)?;
        let mut field = vec![ring.zero(); x.len()];
        self.scatter_reference(ring, &tile, &mut field)?;
        Ok(field)
    }

    /// **The directly assembled global matrix** `Σ_r P_rᵀ L_r P_r`, as a dense `n × n` table.
    ///
    /// This is the independent construction the generated operator is tested against: it is built
    /// by the textbook finite-element assembly loop — for each region, for each local `(j, k)`, add
    /// `L[j][k]` at `(addr(lo+j), addr(lo+k))` — and never through the gather/scatter machinery.
    /// `entry_ceiling` bounds the `n²` allocation exactly: the product is checked and compared
    /// before a single element is allocated, so a large declared extent is a refusal rather than an
    /// exhausted machine.
    pub fn assemble_dense<R: ExactRing>(
        &self,
        ring: &R,
        operator: &LocalOperator<R::Value>,
        entry_ceiling: usize,
    ) -> Sectioned<Vec<R::Value>> {
        if operator.width() != self.tile.max_width {
            return refuse(
                SectionClause::LocalOperatorWidth,
                format!(
                    "the local operator is {} wide; the declared tile is {}",
                    operator.width(),
                    self.tile.max_width
                ),
            );
        }
        let extent = self.global_extent();
        let entries = extent.checked_mul(extent).ok_or_else(|| {
            SectionRefusal::new(
                SectionClause::ExtentProduct,
                format!("a dense {extent}x{extent} assembly overflows usize"),
            )
        })?;
        if entries > entry_ceiling {
            return refuse(
                SectionClause::WorkCeiling,
                format!(
                    "a dense {extent}x{extent} assembly is {entries} entries; the declared ceiling \
                     is {entry_ceiling}"
                ),
            );
        }
        let mut matrix = vec![ring.zero(); entries];
        for region in 0..self.regions() {
            let addresses = self.incidence.region(region).expect("region below the population");
            for (row, row_address) in addresses.iter().enumerate() {
                for (column, column_address) in addresses.iter().enumerate() {
                    let coefficient = operator
                        .entry(row, column)
                        .expect("the operator covers the declared tile");
                    let at = *row_address as usize * extent + *column_address as usize;
                    matrix[at] = match ring.add(matrix[at], coefficient) {
                        Some(sum) => sum,
                        None => return arithmetic_refusal(),
                    };
                }
            }
        }
        Ok(matrix)
    }

    /// Apply a dense global matrix exactly, for comparison against the generated operator.
    pub fn apply_assembled<R: ExactRing>(
        &self,
        ring: &R,
        matrix: &[R::Value],
        x: &[R::Value],
    ) -> Sectioned<Vec<R::Value>> {
        let extent = self.global_extent();
        if x.len() != extent || matrix.len() != extent.saturating_mul(extent) {
            return refuse(
                SectionClause::SpanExtent,
                format!(
                    "a dense application of a {extent}x{extent} matrix takes {extent} values; the \
                     matrix carries {} entries and the field {}",
                    matrix.len(),
                    x.len()
                ),
            );
        }
        let mut out = Vec::with_capacity(x.len());
        for row in 0..extent {
            let mut accumulator = ring.zero();
            for (column, value) in x.iter().enumerate() {
                let product = match ring.mul(matrix[row * extent + column], *value) {
                    Some(product) => product,
                    None => return arithmetic_refusal(),
                };
                accumulator = match ring.add(accumulator, product) {
                    Some(sum) => sum,
                    None => return arithmetic_refusal(),
                };
            }
            out.push(accumulator);
        }
        Ok(out)
    }

    /// **Witness the adjoint identity executably**: `⟨gather x, y⟩ = ⟨x, scatterAdd y⟩`.
    ///
    /// This is `SectionLayout.Incidence.adjoint`, and it is what makes the generated scatter table
    /// *the transpose of* the generated gather table rather than a second, independently authored
    /// map.  Returns the two inner products so a caller can report them, and they are equal exactly
    /// when the identity holds on this declaration.
    pub fn verify_adjoint<R: ExactRing>(
        &self,
        ring: &R,
        x: &[R::Value],
        y: &[R::Value],
    ) -> Sectioned<(R::Value, R::Value)> {
        if y.len() != self.slots() {
            return refuse(
                SectionClause::SpanExtent,
                format!(
                    "the local covector carries {} slots; the declaration carries {}",
                    y.len(),
                    self.slots()
                ),
            );
        }
        let gathered = self.gather_reference::<R>(x)?;
        let mut left = ring.zero();
        for (slot, value) in gathered.iter().enumerate() {
            let product = match ring.mul(*value, y[slot]) {
                Some(product) => product,
                None => return arithmetic_refusal(),
            };
            left = match ring.add(left, product) {
                Some(sum) => sum,
                None => return arithmetic_refusal(),
            };
        }
        // Same discipline: `x.len()` was proved to be the declared extent by the gather above.
        let mut scattered = vec![ring.zero(); x.len()];
        self.scatter_add_reference(ring, y, &mut scattered)?;
        let mut right = ring.zero();
        for (address, value) in scattered.iter().enumerate() {
            let product = match ring.mul(x[address], *value) {
                Some(product) => product,
                None => return arithmetic_refusal(),
            };
            right = match ring.add(right, product) {
                Some(sum) => sum,
                None => return arithmetic_refusal(),
            };
        }
        Ok((left, right))
    }
}

// ---------------------------------------------------------------------------------------------
// The device realization
// ---------------------------------------------------------------------------------------------

/// The four lowered entries of the generated triple.
pub struct SectionKernels<'m> {
    gather: Function<'m>,
    apply: Function<'m>,
    scatter_store: Function<'m>,
    scatter_add: Function<'m>,
}

/// The receipts one complete enactment earns.  Every one is a
/// [`crate::launch_law::FullyProvedReceipt`]: the enactment takes `LaunchEvidence::Device`, so no
/// clause is deferred, and a receipt that deferred anything is refused rather than reported.
#[derive(Debug)]
pub struct SectionReceipts {
    /// The gather arm.
    pub gather: FullyProvedReceipt,
    /// The local-application arm.
    pub apply: FullyProvedReceipt,
    /// The scatter arm: one receipt under an injective incidence, one per colour class under an
    /// accumulating one, in launch order.
    pub scatter: Vec<FullyProvedReceipt>,
}

/// The host descriptors from which the device tables were staged.  The generated triple accepts
/// the staged operator as its requested operator; there is no second operator at enactment to
/// compare.  Layout and colouring remain explicit enactment inputs for API compatibility, so their
/// contents are checked against this borrowed provenance before any driver call.
#[derive(Debug, Clone, Copy)]
struct SectionTableProvenance<'a> {
    layout: &'a SectionLayout,
    _operator: &'a LocalOperator<u64>,
    colouring: Option<&'a RegionColouring>,
}

impl SectionTableProvenance<'_> {
    fn verify(
        &self,
        layout: &SectionLayout,
        colouring: Option<&RegionColouring>,
    ) -> Sectioned<()> {
        if self.layout != layout {
            return Err(SectionRefusal::new(
                SectionClause::TableProvenance,
                "the enactment layout differs from the layout used to stage the device tables",
            ));
        }
        match (self.colouring, colouring) {
            (None, None) => Ok(()),
            (Some(staged), Some(presented)) if staged == presented => Ok(()),
            (None, Some(_)) => Err(SectionRefusal::new(
                SectionClause::TableProvenance,
                "enactment supplied a colouring but staging supplied none",
            )),
            (Some(_), None) => Err(SectionRefusal::new(
                SectionClause::TableProvenance,
                "staging supplied a colouring but enactment supplied none",
            )),
            (Some(_), Some(_)) => Err(SectionRefusal::new(
                SectionClause::TableProvenance,
                "the enactment colouring differs from the colouring used to stage the device tables",
            )),
        }
    }
}

/// The device-resident tables the generated triple reads: the gather index, the region boundaries,
/// the local operator's coefficients and, for an accumulating scatter, one region list per colour.
/// The borrowed provenance prevents a same-sized but different incidence or colouring from being
/// paired with these tables at enactment.
pub struct SectionDeviceTables<'a> {
    index: DeviceBuffer<u32>,
    offsets: DeviceBuffer<u32>,
    coefficients: DeviceBuffer<u64>,
    colour_regions: Vec<DeviceBuffer<u32>>,
    provenance: SectionTableProvenance<'a>,
}

impl SectionDeviceTables<'_> {
    /// Stage the generated tables onto the card.  Every extent comes from the layout, which
    /// generated it from the declaration.
    ///
    /// The declared coefficients cross into device memory verbatim, so their **representation** is
    /// a clause of this mouth and not a comment on the arithmetic: every coefficient is verified
    /// canonical in `Z/(2^61 - 1)` — the ring the four entries realize — before a single byte is
    /// allocated or copied.  A non-canonical coefficient is refused under
    /// [`SectionClause::CanonicalWord`], naming the first offending index; see
    /// [`ModularWords::verify_canonical`] for why refusal and not reduction.  The refusal is raised
    /// before any driver call, so a malformed declaration never reaches the card at all.
    pub fn stage<'a>(
        layout: &'a SectionLayout,
        operator: &'a LocalOperator<u64>,
        colouring: Option<&'a RegionColouring>,
    ) -> Result<SectionDeviceTables<'a>> {
        if operator.width() != layout.tile().max_width() {
            return Err(SectionRefusal::new(
                SectionClause::LocalOperatorWidth,
                format!(
                    "the local operator is {} wide; the declared tile is {}",
                    operator.width(),
                    layout.tile().max_width()
                ),
            )
            .into());
        }
        operator.verify_canonical(&ModularWords::MERSENNE61)?;
        if let Some(colouring) = colouring {
            colouring.verify_proper(layout)?;
        }
        let index = DeviceBuffer::<u32>::alloc(layout.slots())?;
        index.copy_from_slice(layout.gather_index())?;
        let offsets = DeviceBuffer::<u32>::alloc(layout.regions() + 1)?;
        offsets.copy_from_slice(layout.device_offsets())?;
        let coefficients = DeviceBuffer::<u64>::alloc(operator.entries().len())?;
        coefficients.copy_from_slice(operator.entries())?;
        let mut colour_regions = Vec::new();
        if let Some(colouring) = colouring {
            for colour in 0..colouring.colour_count() {
                let class = colouring.class(colour).expect("colour below the count");
                let buffer = DeviceBuffer::<u32>::alloc(class.len())?;
                buffer.copy_from_slice(class)?;
                colour_regions.push(buffer);
            }
        }
        Ok(SectionDeviceTables {
            index,
            offsets,
            coefficients,
            colour_regions,
            provenance: SectionTableProvenance {
                layout,
                _operator: operator,
                colouring,
            },
        })
    }

    /// How many colour classes were staged.
    pub fn colour_classes(&self) -> usize {
        self.colour_regions.len()
    }
}

impl<'m> SectionKernels<'m> {
    /// Resolve the four entries out of a loaded module.
    pub fn resolve(module: &'m Module) -> Result<SectionKernels<'m>> {
        Ok(SectionKernels {
            gather: module.function(section_cuda::GATHER_ENTRY_SYMBOL)?,
            apply: module.function(section_cuda::APPLY_ENTRY_SYMBOL)?,
            scatter_store: module.function(section_cuda::SCATTER_STORE_ENTRY_SYMBOL)?,
            scatter_add: module.function(section_cuda::SCATTER_ADD_ENTRY_SYMBOL)?,
        })
    }

    /// **Enact the generated triple on the card.**
    ///
    /// Every launch crosses [`crate::launch_law`] with `LaunchEvidence::Device`, so every device
    /// clause is proved and the receipts are [`FullyProvedReceipt`]s.  Every write span is opened
    /// through [`PartitionedWrite::scope`], bound to the partition **generated from the
    /// incidence**: a uniform-stride (or offsets) partition for the gather and apply arms, the
    /// injective-scatter partition for an injective scatter, and — for an accumulating scatter —
    /// one injective-scatter partition per colour class, launched colour by colour.
    ///
    /// `target` is *not* zeroed here: the accumulating arm adds into whatever the field already
    /// carries, which is the `σ +` of `SectionLayout.Incidence.colour_schedule`.  A caller wanting
    /// `Pᵀ L P x` alone zeroes it first.
    ///
    /// `AccumulationLaw::IntegerAdd` is refused: a device kernel cannot raise the overflow refusal
    /// that law owes, so it has no device arm rather than a wrapping one.
    ///
    /// `source` and `target` are buffers the caller already holds on the card, so this mouth cannot
    /// inspect their words — the host-side canonicality clause lives at
    /// [`SectionDeviceTables::stage`] and [`SectionApparatus::apply_once`], which are the two mouths
    /// that carry host words across.  Nothing exact is lost by that: `section_cuda::add` and
    /// `section_cuda::mul` are total over every pair of `u64` words, so a non-canonical resident
    /// word still folds to its exact residue rather than wrapping; the gather arm canonicalizes
    /// each word it reads, so the local tile is canonical whatever `source` held.
    #[allow(clippy::too_many_arguments)]
    pub fn enact(
        &self,
        device: &Device,
        stream: &Stream,
        layout: &SectionLayout,
        tables: &SectionDeviceTables<'_>,
        colouring: Option<&RegionColouring>,
        source: &DeviceBuffer<u64>,
        local: &mut DeviceBuffer<u64>,
        target: &mut DeviceBuffer<u64>,
    ) -> Result<SectionReceipts> {
        tables.provenance.verify(layout, colouring)?;
        if let Some(colouring) = colouring {
            colouring.verify_proper(layout)?;
        }
        if let ScatterReceipt::Accumulated(law) = layout.receipt() {
            match law {
                AccumulationLaw::ModularAdd { modulus } if modulus == section_cuda::MODULUS => {}
                other => {
                    return Err(SectionRefusal::new(
                        SectionClause::AccumulationOnDevice,
                        format!(
                            "the device arm realizes exactly `{}`; `{}` was declared",
                            AccumulationLaw::ModularAdd {
                                modulus: section_cuda::MODULUS
                            }
                            .name(),
                            other.name()
                        ),
                    )
                    .into())
                }
            }
        }
        let evidence = LaunchEvidence::Device(device);

        // --- the gather arm ------------------------------------------------------------------
        let gather_receipt = {
            let requirement = layout.gather_requirement();
            let limits = LaunchLimits::from_evidence(evidence, &self.gather)?;
            let partition = layout.gather_partition()?;
            let index = DeviceReadSpan::whole(&tables.index);
            let source_span = DeviceReadSpan::whole(source);
            let mut write = PartitionedWrite::bind(DeviceWriteSpan::whole(local), partition)?;
            write.scope(stream, |open| {
                let spans = [
                    source_span.argument("source"),
                    index.argument("index"),
                    open.argument("local"),
                ];
                LawfulLaunch::cover(&requirement, &limits, &spans)?.enact(
                    &self.gather,
                    Some(stream),
                    &[ScalarArgument::new("slots", layout.slots() as u64)],
                )
            })??
        };

        // --- the local-application arm --------------------------------------------------------
        let apply_receipt = {
            let limits = LaunchLimits::from_evidence(evidence, &self.apply)?;
            let width = layout.tile().max_width();
            let requirement = layout.apply_requirement(&limits, width)?;
            let partition = layout.gather_partition()?;
            let offsets = DeviceReadSpan::whole(&tables.offsets);
            let coefficients = DeviceReadSpan::whole(&tables.coefficients);
            let mut write = PartitionedWrite::bind(DeviceWriteSpan::whole(local), partition)?;
            write.scope(stream, |open| {
                let spans = [
                    open.argument("local"),
                    offsets.argument("offsets"),
                    coefficients.argument("coefficients"),
                ];
                LawfulLaunch::cover(&requirement, &limits, &spans)?.enact(
                    &self.apply,
                    Some(stream),
                    &[
                        ScalarArgument::new("regions", layout.regions() as u64),
                        ScalarArgument::new("tile_width", width as u64),
                    ],
                )
            })??
        };

        // --- the scatter arm ------------------------------------------------------------------
        let mut scatter_receipts = Vec::new();
        match layout.receipt() {
            ScatterReceipt::Injective => {
                let requirement = layout.scatter_store_requirement()?;
                let limits = LaunchLimits::from_evidence(evidence, &self.scatter_store)?;
                let partition = layout.scatter_partition()?;
                let index = DeviceReadSpan::whole(&tables.index);
                let tile = DeviceReadSpan::whole(&*local);
                let mut write = PartitionedWrite::bind(DeviceWriteSpan::whole(target), partition)?;
                let receipt = write.scope(stream, |open| {
                    let spans = [
                        tile.argument("local"),
                        index.argument("index"),
                        open.argument("target"),
                    ];
                    LawfulLaunch::cover(&requirement, &limits, &spans)?.enact(
                        &self.scatter_store,
                        Some(stream),
                        &[ScalarArgument::new("slots", layout.slots() as u64)],
                    )
                })??;
                scatter_receipts.push(fully_proved(receipt)?);
            }
            ScatterReceipt::Accumulated(_) => {
                let colouring = colouring.ok_or_else(|| {
                    CudaError::from(SectionRefusal::new(
                        SectionClause::ColouringProper,
                        "an accumulating scatter is launched colour by colour and no colouring was \
                         presented",
                    ))
                })?;
                colouring.verify_proper(layout)?;
                if tables.colour_regions.len() != colouring.colour_count() {
                    return Err(SectionRefusal::new(
                        SectionClause::ColourClass,
                        format!(
                            "{} colour classes were staged; the colouring carries {}",
                            tables.colour_regions.len(),
                            colouring.colour_count()
                        ),
                    )
                    .into());
                }
                let limits = LaunchLimits::from_evidence(evidence, &self.scatter_add)?;
                for colour in 0..colouring.colour_count() {
                    let class = colouring.class(colour).expect("colour below the count");
                    let requirement = layout.scatter_add_requirement(class.len())?;
                    let partition = layout.colour_partition(colouring, colour)?;
                    let index = DeviceReadSpan::whole(&tables.index);
                    let offsets = DeviceReadSpan::whole(&tables.offsets);
                    let regions = DeviceReadSpan::whole(&tables.colour_regions[colour]);
                    let tile = DeviceReadSpan::whole(&*local);
                    let mut write =
                        PartitionedWrite::bind(DeviceWriteSpan::whole(target), partition)?;
                    let receipt = write.scope(stream, |open| {
                        let spans = [
                            tile.argument("local"),
                            index.argument("index"),
                            offsets.argument("offsets"),
                            regions.argument("colour_regions"),
                            open.argument("target"),
                        ];
                        LawfulLaunch::cover(&requirement, &limits, &spans)?.enact(
                            &self.scatter_add,
                            Some(stream),
                            &[ScalarArgument::new("count", class.len() as u64)],
                        )
                    })??;
                    scatter_receipts.push(fully_proved(receipt)?);
                }
            }
        }

        Ok(SectionReceipts {
            gather: fully_proved(gather_receipt)?,
            apply: fully_proved(apply_receipt)?,
            scatter: scatter_receipts,
        })
    }
}

fn fully_proved(receipt: crate::launch_law::LaunchReceipt) -> Result<FullyProvedReceipt> {
    let kernel = receipt.kernel;
    let deferred: Vec<&'static str> = receipt.deferred().iter().map(|c| c.name()).collect();
    receipt.fully_proved().ok_or_else(|| CudaError {
        code: -1,
        name: String::from("SECTION_LAYOUT_DEFERRED_RECEIPT"),
        message: format!(
            "{kernel} deferred [{}]; the section triple is enacted with LaunchEvidence::Device and \
             owes a completely proved receipt",
            deferred.join(",")
        ),
        context: "SectionKernels::enact",
    })
}

/// A convenience mouth for a caller that has a context and a module and wants the whole exact
/// operator applied once: stage, enact, read back.  The costs are the caller's to measure — this
/// mouth names the clocks by separating the phases, and does no measurement of its own.
pub struct SectionApparatus<'m> {
    kernels: SectionKernels<'m>,
}

impl<'m> SectionApparatus<'m> {
    /// Resolve the four entries.
    pub fn resolve(module: &'m Module) -> Result<SectionApparatus<'m>> {
        Ok(SectionApparatus {
            kernels: SectionKernels::resolve(module)?,
        })
    }

    /// The resolved entries.
    pub const fn kernels(&self) -> &SectionKernels<'m> {
        &self.kernels
    }

    /// Apply the generated operator to one host field, returning the field the device produced and
    /// the receipts every launch earned.  The context is synchronized by each
    /// [`PartitionedWrite::scope`]; the final readback is an ordinary synchronous copy.
    ///
    /// `x` is uploaded verbatim, so — exactly as for the staged coefficients — every word of it is
    /// verified canonical in `Z/(2^61 - 1)` before anything is allocated, and a non-canonical word
    /// is refused under [`SectionClause::CanonicalWord`] naming the first offending index.
    #[allow(clippy::too_many_arguments)]
    pub fn apply_once(
        &self,
        device: &Device,
        context: &Context,
        stream: &Stream,
        layout: &SectionLayout,
        tables: &SectionDeviceTables<'_>,
        colouring: Option<&RegionColouring>,
        x: &[u64],
    ) -> Result<(Vec<u64>, SectionReceipts)> {
        if x.len() != layout.global_extent() {
            return Err(SectionRefusal::new(
                SectionClause::SpanExtent,
                format!(
                    "the global field carries {} values; the declared extent is {}",
                    x.len(),
                    layout.global_extent()
                ),
            )
            .into());
        }
        verify_canonical_words(&ModularWords::MERSENNE61, x, "global field")?;
        // This convenience owner explicitly receives a context. Select it before allocation,
        // not only at the final synchronization after work has already been submitted.
        context.make_current()?;
        let source = DeviceBuffer::<u64>::alloc(x.len())?;
        source.copy_from_slice(x)?;
        let mut local = DeviceBuffer::<u64>::alloc_zeroed(layout.slots())?;
        let mut target = DeviceBuffer::<u64>::alloc_zeroed(layout.global_extent())?;
        let receipts = self.kernels.enact(
            device,
            stream,
            layout,
            tables,
            colouring,
            &source,
            &mut local,
            &mut target,
        )?;
        context.synchronize()?;
        let mut out = vec![0u64; layout.global_extent()];
        target.copy_to_slice(&mut out)?;
        Ok((out, receipts))
    }
}

/// The entry population this owner launches, for the artifact assertion in `crate`'s own tests.
pub fn section_entry_symbols() -> BTreeMap<&'static str, usize> {
    section_cuda::Entry::ALL
        .iter()
        .map(|entry| (entry.symbol(), entry.cuda_parameter_words()))
        .collect()
}

#[cfg(test)]
mod tests;
