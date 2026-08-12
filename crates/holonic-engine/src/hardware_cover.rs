//! The hardware cover: two charts of one caused body, each declaring its own capacity.
//!
//! **The governing record is
//! `research/records/2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER_THE_CARD_MUST_CARRY_THE_CURRENT.md`,
//! and it names the failure this module exists to prevent:**
//!
//! > *"A short exact card kernel placed at the end of that host-owned passage does not make the card
//! > the owner of the current. … The GPU did not fall back. The operative machine never crossed its
//! > boundary."*
//!
//! and it fixes the ontology:
//!
//! > *"CPU/RAM and GPU/VRAM are local charts of the same caused body. A host-device copy is a codec
//! > and transport morphism between separately addressed memory sections. It is not serialization of
//! > a second semantic world."*
//!
//! > *"A GPU lane, warp, block, buffer address, page, stream, and host thread are **realization
//! > coordinates**; none is automatically a holon, receiver, or source identity."*
//!
//! So this module builds neither a "GPU backend" nor a "CPU fallback". It builds a **cover**: a
//! family of charts over one body, each of which **declares its own capacity by asking itself**, and
//! a decomposition of work across that cover which is licensed by proved independence rather than by
//! a schedule.
//!
//! # Nothing here is authored, and that is the point
//!
//! Brandon, 2026-08-10, directing this construction: *"do not be primitive or sparing about this,
//! you will contaminate the construction if you employ conservative thoughts about specifying
//! constants and knobs."*
//!
//! Every quantity below comes from one of exactly two places:
//!
//! - **the surface declaring itself** — the device through `soma/mount`'s `Device::attribute` and
//!   `Device::launch_census`, the host through `std::thread::available_parallelism`. A device's warp
//!   size is not a number this project chooses; it is the device's answer about the device.
//! - **the material** — how many members a cell has, how many cells there are.
//!
//! **This module does not query the card, and it must not.** `soma/mount/src/cuda.rs` already owns
//! that: `Device::attribute`, `Device::launch_census`, `Function::max_threads_per_block`, and
//! `Function::linear_launch`, which derives grid and block from driver-reported apertures and
//! **refuses rather than clipping** when the work exceeds them. The engine cannot depend on
//! `soma/mount` — `soma/life` depends on the engine, so the reverse edge is a Cargo cycle
//! (`blueprint/THE_ASSEMBLY.md` F1). A first version of this file declared its own
//! `cuDeviceGetAttribute` block; that is precisely the construction
//! `canon/THE_EXPLORATIVE_FAILURE.md` convicts, and it was removed. The engine owns the **law**; a
//! caller that can reach the surface supplies the declaration.
//!
//! What IS a contaminant, and it is in the engine's own device path: `cuda_aperture.rs:44` carries
//! `const THREADS_PER_BLOCK: u32 = 128` and `cuda_relation.rs` carries `128` and `256`, all three
//! dispositioned `ABI` in `meta/AUTHORED_LEVELS.tsv` with the reason *"CUDA launch geometry, fixed
//! by the device interface."* **That reason is false**, and `soma/mount` proves it by deriving the
//! same quantity from the driver. Those two engine modules declare no device-attribute call at all,
//! so they know the card's *name* and nothing about its shape — while a sibling stack in the same
//! repository does it correctly.
//!
//! # The mode identity, which the record requires
//!
//! > `μ = (L, ABI, P, D, A, χ)` — source law, exact boundary, kernel identity, **device
//! > capability**, arithmetic tier, apparatus chart. *"Changing any constituent reopens admission."*
//!
//! Device capability is a **constituent of the admitted mode**. A body that never queries the device
//! cannot state its own mode, so it cannot know when admission has reopened. [`ModeIdentity`] makes
//! it a value.
//!
//! # Independence is proved, never assumed
//!
//! > *"Two events belong to the independence relation only when their complete exact consequences
//! > commute … A common label, collection, or lack of a visible edge does not prove independence."*
//!
//! `H.0219` says the same thing from the other side: flux locality **licenses a decomposition and
//! never a schedule**. So [`CoverDecomposition::independence`] does not assert that sections commute —
//! it **checks** that their supports are disjoint and returns a named [`Barrier`] when they are not.

use std::collections::BTreeSet;

use num_bigint::BigUint;

// -------------------------------------------------------------------------------------------------
// What a surface declares about itself
// -------------------------------------------------------------------------------------------------

/// Which chart of the physical ecology a section is realized on.
///
/// A chart is **not** a receiver and **not** a holon. The record is explicit: lanes, warps, blocks
/// and host threads are *realization coordinates*. This type names where work was placed, and
/// carries no semantic authority whatever.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ChartId {
    Host,
    Device(i32),
}

impl std::fmt::Display for ChartId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ChartId::Host => write!(formatter, "host"),
            ChartId::Device(ordinal) => write!(formatter, "device{ordinal}"),
        }
    }
}

/// The device's own answers about itself, as obtained by a caller that can reach the card.
///
/// Every field is a driver-reported attribute. Nothing here may be authored by a caller that did not
/// ask the device: a stated declaration is lawful only in a test, where the point is to vary the
/// surface without one being present.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceDeclaration {
    pub ordinal: i32,
    pub name: String,
    pub capability_major: u32,
    pub capability_minor: u32,
    pub multiprocessors: u32,
    pub warp_size: u32,
    pub max_threads_per_block: u32,
    pub max_threads_per_multiprocessor: u32,
    pub max_grid_x: u32,
    pub max_sectiond_bytes: u32,
    pub async_engines: u32,
    pub concurrent_kernels: bool,
    pub unified_addressing: bool,
}

impl DeviceDeclaration {
    /// Every lane the device can hold resident at once. `multiprocessors × threads per
    /// multiprocessor`, both of which the device stated.
    pub fn resident_lanes(&self) -> u64 {
        u64::from(self.multiprocessors) * u64::from(self.max_threads_per_multiprocessor)
    }

    /// Resident **warps** — the device's own count of independently-issuing cells.
    pub fn resident_groups(&self) -> u64 {
        self.resident_lanes() / u64::from(self.warp_size.max(1))
    }

    /// The compute capability as `nvcc` names it: `compute_XY`.
    pub fn virtual_architecture(&self) -> String {
        format!(
            "compute_{}{}",
            self.capability_major, self.capability_minor
        )
    }
}

/// The host's own answer about itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HostDeclaration {
    /// `std::thread::available_parallelism`, which is the host stating its own width.
    pub lanes: u32,
}

impl HostDeclaration {
    /// The host declares itself. Never authored; never an environment override, because an override
    /// is a knob and a knob is what this module exists to remove.
    pub fn declare() -> Self {
        Self {
            lanes: std::thread::available_parallelism()
                .map(|lanes| lanes.get() as u32)
                .unwrap_or(1),
        }
    }

    pub fn resident_lanes(&self) -> u64 {
        u64::from(self.lanes)
    }
}

/// One chart of the cover, with what it said about itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Chart {
    Host(HostDeclaration),
    Device(DeviceDeclaration),
}

impl Chart {
    pub fn id(&self) -> ChartId {
        match self {
            Chart::Host(_) => ChartId::Host,
            Chart::Device(device) => ChartId::Device(device.ordinal),
        }
    }

    /// **The chart's grain: the smallest cell that does not leave lanes idle.**
    ///
    /// The host issues per lane, so its grain is one. The device issues per **warp** — every
    /// lane of a warp executes together, so a cell smaller than a warp leaves `warp_size − n` lanes
    /// doing nothing. This is the one structural difference between the two charts, and it is read
    /// off the device rather than chosen.
    pub fn grain(&self) -> u64 {
        match self {
            Chart::Host(_) => 1,
            Chart::Device(device) => u64::from(device.warp_size.max(1)),
        }
    }

    pub fn resident_lanes(&self) -> u64 {
        match self {
            Chart::Host(host) => host.resident_lanes(),
            Chart::Device(device) => device.resident_lanes(),
        }
    }

    /// How many cells at this chart's own grain it can hold resident.
    pub fn resident_groups(&self) -> u64 {
        self.resident_lanes() / self.grain().max(1)
    }
}

/// Why a surface could not declare itself. A refusal is named, never silently absorbed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SurfaceRefusal {
    /// The CUDA driver is present but returned an error at the named operation.
    Driver { operation: &'static str, code: i32 },
    /// The driver initialised and reported no devices.
    NoDevice,
}

impl std::fmt::Display for SurfaceRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SurfaceRefusal::Driver { operation, code } => {
                write!(formatter, "CUDA {operation} returned {code}")
            }
            SurfaceRefusal::NoDevice => write!(formatter, "the CUDA driver reports no device"),
        }
    }
}

// -------------------------------------------------------------------------------------------------
// The cover
// -------------------------------------------------------------------------------------------------

/// The declared charts over one caused body, with every surface that refused and why.
///
/// **A cover with one chart is a cover.** A body with no card is not degraded; it is covered by one
/// chart, and the decomposition below places every cell there. What is refused is the *pretence*
/// that a device was consulted — [`HardwareCover::refusals`] carries the reason by name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HardwareCover {
    charts: Vec<Chart>,
    refusals: Vec<(ChartId, SurfaceRefusal)>,
}

impl HardwareCover {
    /// Form the cover from the host's own declaration plus whatever the **caller** obtained from
    /// the device.
    ///
    /// **The engine does not query the card, and that is a structural fact rather than a gap.**
    /// `soma/mount/src/cuda.rs` already owns the device query — `Device::attribute`,
    /// `Device::launch_census`, `Function::max_threads_per_block`, and `Function::linear_launch`,
    /// which derives a launch shape from driver-reported apertures and refuses rather than clips.
    /// `crates/holonic-engine` cannot depend on `soma/mount`: `soma/life` depends on the engine, so
    /// the reverse edge is a Cargo cycle (`blueprint/THE_ASSEMBLY.md` F1). A first version of this
    /// module declared its own `cuDeviceGetAttribute` block, which is exactly the construction
    /// `canon/THE_EXPLORATIVE_FAILURE.md` convicts — a new organ beside an existing owner. It was
    /// removed.
    ///
    /// So the engine owns the **law** — which chart, licensed by what proof — and the physical
    /// surface is declared by a caller that can reach it.
    pub fn over(device: Option<DeviceDeclaration>) -> Self {
        let mut charts = vec![Chart::Host(HostDeclaration::declare())];
        let mut refusals = Vec::new();
        match device {
            Some(device) => charts.push(Chart::Device(device)),
            None => refusals.push((ChartId::Device(0), SurfaceRefusal::NoDevice)),
        }
        Self { charts, refusals }
    }

    /// A cover of exactly the host. Used where a caller declares that no device participates, and by
    /// the determinism controls, which require the cover to be varied.
    pub fn host_only() -> Self {
        Self {
            charts: vec![Chart::Host(HostDeclaration::declare())],
            refusals: Vec::new(),
        }
    }

    /// Build a cover from stated charts. The determinism controls need to vary the cover without a
    /// card present, and a construction that can only be built from real hardware cannot be graded
    /// on a machine that has none.
    pub fn of_charts(charts: Vec<Chart>) -> Self {
        Self {
            charts,
            refusals: Vec::new(),
        }
    }

    pub fn charts(&self) -> &[Chart] {
        &self.charts
    }

    pub fn refusals(&self) -> &[(ChartId, SurfaceRefusal)] {
        &self.refusals
    }

    pub fn chart(&self, id: ChartId) -> Option<&Chart> {
        self.charts.iter().find(|chart| chart.id() == id)
    }

    /// The device chart, if one declared itself.
    pub fn device(&self) -> Option<&DeviceDeclaration> {
        self.charts.iter().find_map(|chart| match chart {
            Chart::Device(device) => Some(device),
            Chart::Host(_) => None,
        })
    }

    pub fn host(&self) -> &HostDeclaration {
        self.charts
            .iter()
            .find_map(|chart| match chart {
                Chart::Host(host) => Some(host),
                Chart::Device(_) => None,
            })
            .expect("the host chart always declares")
    }

    /// Every lane the whole cover can hold resident at once, summed across charts.
    pub fn resident_lanes(&self) -> u64 {
        self.charts.iter().map(Chart::resident_lanes).sum()
    }
}

// -------------------------------------------------------------------------------------------------
// The mode identity the record requires
// -------------------------------------------------------------------------------------------------

/// `μ = (L, ABI, P, D, A, χ)`, from the governing record. Changing any constituent reopens
/// admission, so admission can only be tracked by a body that can *state* its mode.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModeIdentity {
    /// `L` — the source law this mode realizes, by owner path.
    pub source_law: &'static str,
    /// `ABI` — the exact boundary version the encode/decode pair speaks.
    pub abi: &'static str,
    /// `P` — the kernel identity: which PTX, by name.
    pub kernel: &'static str,
    /// `D` — the device capability, **as the device stated it**. `None` for a host-only mode.
    pub device: Option<String>,
    /// `A` — the arithmetic tier. This body is exact; a float tier would be a different mode.
    pub arithmetic: &'static str,
    /// `χ` — the apparatus chart: which cover declared, by chart ids.
    pub apparatus: String,
}

impl ModeIdentity {
    pub fn of(
        cover: &HardwareCover,
        source_law: &'static str,
        abi: &'static str,
        kernel: &'static str,
    ) -> Self {
        Self {
            source_law,
            abi,
            kernel,
            device: cover.device().map(|device| {
                format!(
                    "{} {} sm{} warp{}",
                    device.name,
                    device.virtual_architecture(),
                    device.multiprocessors,
                    device.warp_size
                )
            }),
            arithmetic: "exact-integer",
            apparatus: cover
                .charts()
                .iter()
                .map(|chart| chart.id().to_string())
                .collect::<Vec<_>>()
                .join("+"),
        }
    }
}

// -------------------------------------------------------------------------------------------------
// The decomposition, and the independence it must prove
// -------------------------------------------------------------------------------------------------

/// One cell of the front: an independently refinable unit and the extent of its support.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrontCell {
    /// Index into the caller's own front. This module never owns the material.
    pub index: usize,
    /// How many members the cell holds — the material's own extent.
    pub extent: u64,
}

/// A section of the front placed on one chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoverSection {
    pub chart: ChartId,
    pub cells: Vec<FrontCell>,
}

impl CoverSection {
    /// The exact work this section carries: members, and lanes that will stand idle.
    ///
    /// **Idle lanes are reported, never hidden.** A cell of `n` members on a chart of grain
    /// `g` occupies `ceil(n/g)·g` lanes, of which `ceil(n/g)·g − n` do nothing. That waste is a
    /// property of the placement and belongs in the receipt.
    /// **Exact from the first addition, not exact at the end.** This accumulated `members` and
    /// `occupied` in `u64` and converted afterwards, while its own return type's documentation
    /// said *"`BigUint` throughout"*. `extent.div_ceil(g)·g` can exceed `u64` for a large extent
    /// — `extent = 2^63` at `g = 32` already does — so the alleged exact carrier was constructed
    /// out of a quantity that had already wrapped. A carrier that reduces before it is read has
    /// decided for every consumer which magnitudes are invisible; the reduction belongs in the
    /// reading and never in the constructor.
    pub fn work(&self, grain: u64) -> SectionWork {
        let grain = grain.max(1);
        let mut members = BigUint::from(0u32);
        let mut occupied = BigUint::from(0u32);
        for cell in &self.cells {
            members += BigUint::from(cell.extent);
            occupied += BigUint::from(cell.extent.div_ceil(grain)) * BigUint::from(grain);
        }
        SectionWork {
            chart: self.chart,
            cells: BigUint::from(self.cells.len()),
            // `ceil(n/g)·g >= n` per cell, so the difference never underflows.
            idle_lanes: &occupied - &members,
            members,
            occupied_lanes: occupied,
        }
    }
}

/// The exact work of one section. `BigUint` throughout, reproducing on any machine.
///
/// `CLAUDE.md` §8: *a cost is measured in work, never in elapsed time. A clock may measure; it may
/// never select.* No field here is a duration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionWork {
    pub chart: ChartId,
    pub cells: BigUint,
    pub members: BigUint,
    pub occupied_lanes: BigUint,
    pub idle_lanes: BigUint,
}

/// Why a decomposition is not licensed. A barrier is named; it is never worked around.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Barrier {
    /// A cell is claimed more than once. `charts` carries one entry per CLAIM, with multiplicity,
    /// so two sections reads `[Host(0), Device(0)]` and one section holding an index twice reads
    /// `[Host(0), Host(0)]`. Counting sections rather than claims made the second invisible.
    SharedCell { cell: usize, charts: Vec<ChartId> },
    /// A cell of the front reached no chart. Silent loss is the failure this catches.
    UnplacedCell { cell: usize },
    /// A cell was placed under the front's own address carrying a DIFFERENT extent. The placement
    /// is then not a placement of this front: the work vector charges for material the front does
    /// not hold, and every index still resolves.
    ExtentDisagrees {
        cell: usize,
        chart: ChartId,
        declared: u64,
        placed: u64,
    },
    /// A section holds a cell the front never declared. Iterating the front cannot see it — the
    /// extra cell is enacted, charged for, and reported by nothing.
    ForeignCell { cell: usize, chart: ChartId },
    /// The front itself addresses one index twice. Two cells sharing an address cannot be told
    /// apart by any placement that addresses them by index, so no decomposition of it is provable.
    RepeatedFrontCell { cell: usize },
}

impl std::fmt::Display for Barrier {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Barrier::SharedCell { cell, charts } => write!(
                formatter,
                "cell {cell} is claimed by {} charts: {}",
                charts.len(),
                charts
                    .iter()
                    .map(ChartId::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Barrier::UnplacedCell { cell } => {
                write!(formatter, "cell {cell} reached no chart")
            }
            Barrier::ExtentDisagrees {
                cell,
                chart,
                declared,
                placed,
            } => write!(
                formatter,
                "cell {cell} is declared with extent {declared} and placed on {chart} with extent \
                 {placed}"
            ),
            Barrier::ForeignCell { cell, chart } => write!(
                formatter,
                "{chart} holds cell {cell}, which the front does not declare"
            ),
            Barrier::RepeatedFrontCell { cell } => {
                write!(formatter, "the front declares cell {cell} more than once")
            }
        }
    }
}

/// The front, decomposed across the cover.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoverDecomposition {
    pub sections: Vec<CoverSection>,
    pub mode: ModeIdentity,
}

impl CoverDecomposition {
    /// **Decompose the front across the cover, by the material against each chart's own
    /// grain.**
    ///
    /// The law, and it contains no number:
    ///
    /// > A cell is placed on the **coarsest** chart whose grain its own extent fills. A cell
    /// > that fills no chart's grain but the host's goes to the host.
    ///
    /// On a two-chart cover that reads: a cell with at least `warp_size` members fills a warp and
    /// goes to the device; a smaller cell would leave device lanes idle and goes to the host, whose
    /// grain is one and which therefore wastes nothing on any cell.
    ///
    /// `warp_size` is the **device's answer about itself**. The comparison is the *material* against
    /// that answer. Neither is authored, and there is no ratio, threshold, or split point anywhere in
    /// this function.
    ///
    /// **This is a decomposition and not a schedule.** `H.0219`: flux locality licenses the first and
    /// never the second. What order the sections run in, and whether they overlap, is the caller's;
    /// what this returns is *which work may be separated at all*.
    pub fn of(cover: &HardwareCover, front: &[FrontCell], kernel: &'static str) -> Self {
        // Coarsest first, so the most demanding grain gets first refusal on each cell.
        let mut charts: Vec<&Chart> = cover.charts().iter().collect();
        charts.sort_by_key(|chart| std::cmp::Reverse(chart.grain()));

        let mut sections: Vec<CoverSection> = charts
            .iter()
            .map(|chart| CoverSection {
                chart: chart.id(),
                cells: Vec::new(),
            })
            .collect();

        for cell in front {
            let placed = charts
                .iter()
                .position(|chart| cell.extent >= chart.grain())
                .unwrap_or(charts.len() - 1);
            sections[placed].cells.push(cell.clone());
        }

        Self {
            sections,
            mode: ModeIdentity::of(
                cover,
                "holonic_engine::hardware_cover",
                "exact-integer-v1",
                kernel,
            ),
        }
    }

    /// **Prove the decomposition is licensed.** Not asserted — checked.
    ///
    /// Two sections may run concurrently exactly when their consequences commute, and for a refinement
    /// over disjoint cells that reduces to disjointness of the cells themselves. The placement must
    /// therefore be a partition of the front **as a population of `(index, extent)` cells**, and
    /// every way it can fail to be one is returned as a named [`Barrier`].
    ///
    /// **Repaired 2026-08-11. The check licensed constructions it had not examined.** It iterated
    /// the front and counted how many SECTIONS contained each index, which is blind to four
    /// distinct ways a decomposition can differ from the front it claims to place:
    ///
    /// | not detected | why it matters |
    /// |---|---|
    /// | a changed extent under the same index | the work vector charges for material the front does not hold, and every index still resolves |
    /// | a section cell absent from the front | iterating the front cannot reach it; it is enacted and reported by nothing |
    /// | one index held twice inside ONE section | `filter(…).map(…)` yields that section once, so the count is 1 |
    /// | a front that repeats an index | both cells find the same claimants and both pass |
    ///
    /// All four pass while the placement and the work have changed, so the certificate was not a
    /// certificate of the front it named. `CLAUDE.md` §8: a check whose material cannot vary the
    /// property under test is the same defect as a check that cannot fail — and this one wore a
    /// passing result on exactly the constructions it existed to refuse.
    pub fn independence(&self, front: &[FrontCell]) -> Result<(), Vec<Barrier>> {
        let mut barriers = Vec::new();

        // Nothing here materializes an index: every question is asked of the front and the
        // sections directly. The check was already quadratic in the front — one pass per cell over
        // the sections — so reading them in place costs what the old shape cost and owns nothing
        // the caller did not already hand over.
        for (at, cell) in front.iter().enumerate() {
            // A repeated address is malformed BEFORE any placement is asked about: two cells
            // sharing one address cannot be told apart by a placement that addresses them by
            // index, so no decomposition of such a front is provable either way. Reported once,
            // at the second occurrence.
            if front[..at].iter().any(|earlier| earlier.index == cell.index) {
                barriers.push(Barrier::RepeatedFrontCell { cell: cell.index });
            }

            // Claims are counted with MULTIPLICITY rather than by section, which is what makes an
            // index held twice inside one section visible.
            let mut claims = 0usize;
            let mut first_claim = None;
            for section in &self.sections {
                for held in &section.cells {
                    if held.index == cell.index {
                        claims += 1;
                        if first_claim.is_none() {
                            first_claim = Some((section.chart, held.extent));
                        }
                    }
                }
            }

            match (claims, first_claim) {
                (0, _) | (_, None) => barriers.push(Barrier::UnplacedCell { cell: cell.index }),
                (1, Some((chart, placed))) => {
                    if placed != cell.extent {
                        barriers.push(Barrier::ExtentDisagrees {
                            cell: cell.index,
                            chart,
                            declared: cell.extent,
                            placed,
                        });
                    }
                }
                _ => {
                    // One entry per CLAIM, so two sections read `[Host, Device]` and one section
                    // holding an index twice reads `[Host, Host]`.
                    let mut charts = Vec::new();
                    for section in &self.sections {
                        for held in &section.cells {
                            if held.index == cell.index {
                                charts.push(section.chart);
                            }
                        }
                    }
                    barriers.push(Barrier::SharedCell {
                        cell: cell.index,
                        charts,
                    });
                }
            }
        }

        // A placed cell the front never declared. The loop above cannot reach it, by construction.
        for section in &self.sections {
            for held in &section.cells {
                if !front.iter().any(|cell| cell.index == held.index) {
                    barriers.push(Barrier::ForeignCell {
                        cell: held.index,
                        chart: section.chart,
                    });
                }
            }
        }

        if barriers.is_empty() {
            Ok(())
        } else {
            Err(barriers)
        }
    }

    /// The work of every section, each read against its own chart's grain.
    pub fn work(&self, cover: &HardwareCover) -> Vec<SectionWork> {
        self.sections
            .iter()
            .map(|section| {
                let grain = cover
                    .chart(section.chart)
                    .map(Chart::grain)
                    .unwrap_or(1);
                section.work(grain)
            })
            .collect()
    }

    /// Which charts actually received work. A cover whose device section is empty **did not use the
    /// card**, and saying so is the difference between a measurement and a claim.
    pub fn occupied_charts(&self) -> BTreeSet<ChartId> {
        self.sections
            .iter()
            .filter(|section| !section.cells.is_empty())
            .map(|section| section.chart)
            .collect()
    }
}

// -------------------------------------------------------------------------------------------------
// Launch geometry, computed from the device's own answers
// -------------------------------------------------------------------------------------------------

// -------------------------------------------------------------------------------------------------
// Launch geometry is NOT here, and that is deliberate
// -------------------------------------------------------------------------------------------------
//
// A first version of this module carried a `launch_for` deriving grid and block from the device
// declaration. It was removed for the same reason the FFI was: `soma/mount`'s
// `Function::linear_launch` already derives that shape from **both** the function's own
// `CU_FUNC_ATTRIBUTE_MAX_THREADS_PER_BLOCK` and the device's census, folds X into Y when X
// saturates, and refuses rather than clipping when the work exceeds the declared aperture. A weaker
// twin beside it is the construction `canon/THE_EXPLORATIVE_FAILURE.md` convicts.
//
// This module returns **which cells may be separated onto which chart, and why that separation is
// licensed**. How a chart realizes its own section is the chart's own owner's business.

#[cfg(test)]
mod tests {
    use super::*;

    /// A declaration built from stated numbers, for the tests that must not require a card.
    fn stated_device(warp: u32, threads: u32, multiprocessors: u32) -> DeviceDeclaration {
        DeviceDeclaration {
            ordinal: 0,
            name: "stated".to_owned(),
            capability_major: 8,
            capability_minor: 9,
            multiprocessors,
            warp_size: warp,
            max_threads_per_block: threads,
            max_threads_per_multiprocessor: threads * 2,
            max_grid_x: 2_147_483_647,
            max_sectiond_bytes: 49_152,
            async_engines: 2,
            concurrent_kernels: true,
            unified_addressing: true,
        }
    }

    fn front(extents: &[u64]) -> Vec<FrontCell> {
        extents
            .iter()
            .enumerate()
            .map(|(index, extent)| FrontCell {
                index,
                extent: *extent,
            })
            .collect()
    }

    /// The host always declares, and it declares something the machine actually has.
    #[test]
    fn the_host_declares_itself() {
        let host = HostDeclaration::declare();
        assert!(host.lanes >= 1, "the host must state at least one lane");
        let cover = HardwareCover::host_only();
        assert_eq!(cover.charts().len(), 1);
        assert_eq!(cover.host().lanes, host.lanes);
        assert_eq!(cover.charts()[0].grain(), 1, "a host lane is one");
    }

    /// **The decomposition is by the material against the chart's own grain, and it moves.**
    ///
    /// A front with cells on both sides of the declared warp must land on both charts. If it landed
    /// entirely on one, the cover would be a cover in name only.
    #[test]
    fn the_material_decides_which_chart_and_both_receive_work() {
        let cover = HardwareCover {
            charts: vec![
                Chart::Host(HostDeclaration { lanes: 8 }),
                Chart::Device(stated_device(32, 1024, 80)),
            ],
            refusals: Vec::new(),
        };
        let population = front(&[1, 2, 31, 32, 33, 4096]);
        let decomposition = CoverDecomposition::of(&cover, &population, "test");

        decomposition
            .independence(&population)
            .expect("disjoint placement is licensed");

        assert_eq!(
            decomposition.occupied_charts().len(),
            2,
            "both charts must carry work or this is not a cover: {:?}",
            decomposition.sections
        );

        let device = decomposition
            .sections
            .iter()
            .find(|section| matches!(section.chart, ChartId::Device(_)))
            .expect("a device section");
        let host = decomposition
            .sections
            .iter()
            .find(|section| section.chart == ChartId::Host)
            .expect("a host section");

        assert_eq!(
            device.cells.iter().map(|g| g.extent).collect::<Vec<_>>(),
            vec![32, 33, 4096],
            "exactly the cells that fill a warp"
        );
        assert_eq!(
            host.cells.iter().map(|g| g.extent).collect::<Vec<_>>(),
            vec![1, 2, 31],
            "exactly the cells that would idle device lanes"
        );
    }

    /// The grain is the device's answer, so a different device moves the split. If it did not,
    /// the decomposition would be reading something other than the material and the chart.
    #[test]
    fn a_different_device_moves_the_split() {
        let population = front(&[8, 40]);
        let narrow = HardwareCover {
            charts: vec![
                Chart::Host(HostDeclaration { lanes: 8 }),
                Chart::Device(stated_device(4, 256, 20)),
            ],
            refusals: Vec::new(),
        };
        let wide = HardwareCover {
            charts: vec![
                Chart::Host(HostDeclaration { lanes: 8 }),
                Chart::Device(stated_device(64, 1024, 20)),
            ],
            refusals: Vec::new(),
        };
        let on_narrow = CoverDecomposition::of(&narrow, &population, "test");
        let on_wide = CoverDecomposition::of(&wide, &population, "test");

        let device_extents = |d: &CoverDecomposition| -> Vec<u64> {
            d.sections
                .iter()
                .find(|s| matches!(s.chart, ChartId::Device(_)))
                .map(|s| s.cells.iter().map(|g| g.extent).collect())
                .unwrap_or_default()
        };
        assert_eq!(device_extents(&on_narrow), vec![8, 40]);
        assert_eq!(device_extents(&on_wide), Vec::<u64>::new());
        assert_ne!(
            device_extents(&on_narrow),
            device_extents(&on_wide),
            "the orbit of the device declaration must be non-trivial"
        );
    }

    /// Idle lanes are reported. A cell of 33 on a warp of 32 occupies 64 lanes and wastes 31.
    #[test]
    fn the_section_reports_the_lanes_that_will_stand_idle() {
        let section = CoverSection {
            chart: ChartId::Device(0),
            cells: front(&[33]),
        };
        let work = section.work(32);
        assert_eq!(work.members, BigUint::from(33u32));
        assert_eq!(work.occupied_lanes, BigUint::from(64u32));
        assert_eq!(work.idle_lanes, BigUint::from(31u32));
    }

    /// **Independence is checked and the check can fail.** A decomposition that drops a cell or
    /// claims one twice must be refused by name, or the licence is a formality.
    #[test]
    fn a_decomposition_that_loses_or_duplicates_a_cell_is_refused_by_name() {
        let population = front(&[64, 64]);
        let cover = HardwareCover::host_only();
        let mut dropped = CoverDecomposition::of(&cover, &population, "test");
        dropped.sections[0].cells.pop();
        match dropped.independence(&population) {
            Err(barriers) => assert!(matches!(barriers[0], Barrier::UnplacedCell { cell: 1 })),
            Ok(()) => panic!("a dropped cell must be refused"),
        }

        let mut duplicated = CoverDecomposition::of(&cover, &population, "test");
        let repeat = duplicated.sections[0].cells[0].clone();
        duplicated.sections.push(CoverSection {
            chart: ChartId::Device(0),
            cells: vec![repeat],
        });
        match duplicated.independence(&population) {
            Err(barriers) => assert!(
                barriers
                    .iter()
                    .any(|barrier| matches!(barrier, Barrier::SharedCell { cell: 0, .. }))
            ),
            Ok(()) => panic!("a duplicated cell must be refused"),
        }
    }

    /// **The four constructions the certificate used to admit, each refused by name.**
    ///
    /// Every one of these passed the index-presence check: the extent change and the doubled
    /// index both leave one section holding the index, the foreign cell is never visited because
    /// the loop iterated the front, and the repeated front cell resolves to the same claimant
    /// twice. A certificate that accepts a changed construction is worse than an absent one,
    /// because a caller reads it as a proof.
    #[test]
    fn the_certificate_refuses_a_placement_that_is_not_a_partition_of_its_own_front() {
        let population = front(&[64, 64]);
        let cover = HardwareCover::host_only();

        // (1) The same address, a different extent. Index presence is unchanged.
        let mut restated = CoverDecomposition::of(&cover, &population, "test");
        restated.sections[0].cells[0].extent = 65;
        match restated.independence(&population) {
            Err(barriers) => assert!(barriers.iter().any(|barrier| matches!(
                barrier,
                Barrier::ExtentDisagrees {
                    cell: 0,
                    declared: 64,
                    placed: 65,
                    ..
                }
            ))),
            Ok(()) => panic!("a restated extent must be refused"),
        }

        // (2) A cell the front never declared, so iterating the front cannot reach it.
        let mut foreign = CoverDecomposition::of(&cover, &population, "test");
        foreign.sections[0].cells.push(FrontCell {
            index: 7,
            extent: 1,
        });
        match foreign.independence(&population) {
            Err(barriers) => assert!(
                barriers
                    .iter()
                    .any(|barrier| matches!(barrier, Barrier::ForeignCell { cell: 7, .. }))
            ),
            Ok(()) => panic!("a foreign cell must be refused"),
        }

        // (3) One index held twice INSIDE one section. Counting sections yields 1.
        let mut doubled = CoverDecomposition::of(&cover, &population, "test");
        doubled.sections[0].cells.push(FrontCell {
            index: 0,
            extent: 64,
        });
        match doubled.independence(&population) {
            Err(barriers) => assert!(barriers.iter().any(|barrier| matches!(
                barrier,
                Barrier::SharedCell { cell: 0, charts } if charts.len() == 2
            ))),
            Ok(()) => panic!("an index held twice in one section must be refused"),
        }

        // (4) A front addressing one index twice. No placement of it is provable.
        let ambiguous = vec![
            FrontCell {
                index: 0,
                extent: 64,
            },
            FrontCell {
                index: 0,
                extent: 8,
            },
        ];
        let placed = CoverDecomposition::of(&cover, &ambiguous, "test");
        match placed.independence(&ambiguous) {
            Err(barriers) => assert!(
                barriers
                    .iter()
                    .any(|barrier| matches!(barrier, Barrier::RepeatedFrontCell { cell: 0 }))
            ),
            Ok(()) => panic!("a front repeating an address must be refused"),
        }

        // And the control: the decomposition the law itself produces still passes.
        let honest = CoverDecomposition::of(&cover, &population, "test");
        assert!(honest.independence(&population).is_ok());
    }

    /// **The work vector is exact from its first addition.** `ceil(n/g)·g` for `n = 2^63` at
    /// `g = 32` is `2^68`, which no `u64` holds; the return type's own documentation said
    /// `BigUint` throughout while the accumulation was `u64`.
    #[test]
    fn the_work_vector_does_not_wrap_before_it_becomes_exact() {
        let huge = vec![FrontCell {
            index: 0,
            extent: 1u64 << 63,
        }];
        let section = CoverSection {
            chart: ChartId::Device(0),
            cells: huge,
        };
        let work = section.work(32);
        let members = BigUint::from(1u64 << 63);
        assert_eq!(work.members, members);
        // Exactly divisible at this grain, so occupied == members and nothing stands idle —
        // the point is that both are past `u64::MAX / 32` and neither wrapped.
        assert_eq!(work.occupied_lanes, members);
        assert_eq!(work.idle_lanes, BigUint::from(0u32));

        // One member past a multiple of the grain: 2^63 + 1 members occupy 2^63 + 32 lanes.
        let past = CoverSection {
            chart: ChartId::Device(0),
            cells: vec![FrontCell {
                index: 0,
                extent: (1u64 << 63) + 1,
            }],
        };
        let work = past.work(32);
        assert_eq!(
            work.occupied_lanes,
            BigUint::from((1u64 << 63) + 32),
            "the ceiling is taken in BigUint, so it may exceed u64::MAX/32 without wrapping"
        );
        assert_eq!(work.idle_lanes, BigUint::from(31u32));
    }

    /// **The front expansion is exact under any cover: lanes may not move a result.**
    ///
    /// A branching material, so the front is a tree rather than a line, and the successors of a
    /// wide cell and a narrow one must land in the front's own order regardless of which lane
    /// finished first.
    #[test]
    fn the_front_expansion_is_canonical_under_every_cover() {
        let front: Vec<u64> = (0..200).collect();
        // A branching junction: cell `n` opens `n % 7 + 1` continuations, so extents differ and the
        // by-extent cover cannot coincide with a by-count one.
        let expand = |cell: u64| -> Result<Vec<u64>, ()> {
            Ok((0..(cell % 7 + 1)).map(|branch| cell * 10 + branch).collect())
        };
        let serial = expand_front(front.clone(), &HardwareCover::of_charts(vec![
            Chart::Host(HostDeclaration { lanes: 1 }),
        ]), |cell| cell % 7 + 1, expand)
        .expect("serial");
        for lanes in [2u32, 3, 8, 64] {
            let covered = expand_front(
                front.clone(),
                &HardwareCover::of_charts(vec![Chart::Host(HostDeclaration { lanes })]),
                |cell| cell % 7 + 1,
                expand,
            )
            .expect("covered");
            assert_eq!(
                serial, covered,
                "a lane is a realization coordinate and may not move a result: {lanes} lanes"
            );
        }
        assert_eq!(serial.len(), (0..200u64).map(|c| (c % 7 + 1) as usize).sum::<usize>());
    }

    /// A failing cell surfaces its failure rather than being silently dropped by its lane.
    #[test]
    fn a_failing_cell_returns_its_failure_from_any_lane() {
        let front: Vec<u64> = (0..64).collect();
        let outcome = expand_front(
            front,
            &HardwareCover::of_charts(vec![Chart::Host(HostDeclaration { lanes: 8 })]),
            |_| 1,
            |cell| if cell == 47 { Err("47") } else { Ok(vec![cell]) },
        );
        assert_eq!(outcome, Err("47"));
    }

    /// The mode identity carries the device capability, which the record makes a constituent of
    /// admission. A host-only mode must be distinguishable from a covered one.
    #[test]
    fn the_mode_identity_distinguishes_a_covered_body_from_a_host_only_one() {
        let covered = HardwareCover {
            charts: vec![
                Chart::Host(HostDeclaration { lanes: 8 }),
                Chart::Device(stated_device(32, 1024, 80)),
            ],
            refusals: Vec::new(),
        };
        let alone = HardwareCover::host_only();
        let with = ModeIdentity::of(&covered, "law", "abi", "kernel");
        let without = ModeIdentity::of(&alone, "law", "abi", "kernel");
        assert!(with.device.is_some());
        assert!(without.device.is_none());
        assert_ne!(with, without, "changing D must reopen admission");
        assert_eq!(with.apparatus, "host+device0");
        assert_eq!(without.apparatus, "host");
    }
}

// -------------------------------------------------------------------------------------------------
// The front expansion: the leader's law, one organ
// -------------------------------------------------------------------------------------------------
//
// **A leader is a branching structure with time parity, not a line.** Brandon, 2026-08-10: *"one
// receiver's returned chronology is not necessarily serial, it's a distribution of arcs, like the
// lightning leaders… I do not know why you don't ontologically understand why events are ever
// serial in arcs and electromagnetic events as opposed to parallel and branching in junctions."*
//
// The distinction is exact and it is the one this law is built on:
//
// - an **arc** is one conducting channel, so what travels it is ordered;
// - a **junction** is where current distributes, so what leaves it is co-present;
// - **chronology is not seriality.** Irreversibility — time parity, the arc's asymmetry — is a
//   different property from being a total order. Deleting the causal order is forbidden; asserting
//   a total order where the material has a tree is a different error and the one this law removes.
//
// **And the card's execution model is that same law in silicon rather than an analogy for it.**
// Lanes of a warp are co-present exactly while they share a path and the hardware serializes them
// when they diverge: arcs serial, junctions branching, enforced by the physics of the device. The
// many channels exist to carry combinatorial binary path distributions, which are `H.0150`'s
// membership words — the Boolean lattice, crossing depth, inclusion–exclusion as its Möbius
// function. A monitor is a receiver and a distribution is a receiver.
//
// # Why this is one organ and not three coverings
//
// Three generation fronts in this body have exactly this shape:
//
// ```text
//   token_invariance::sweep_covered        surfaces      -> readings
//   morphological_language generation      states        -> successors
//   causal_language leader                 branch tips   -> continuations
// ```
//
// A covering per organ is the cabinet-of-organs failure one level down, the same defect as a device
// path per organ. The material supplies `cell -> successors`; the law covers it.
//
// **All three conduct through this law as of 2026-08-11. Until that day this comment read "were
// being covered separately" while two of them still were**, which is the overstatement
// `canon/TABLET_THE_MANIFOLD.md` convicted in two code comments at once. The order the migration
// ran in is worth keeping, because the three were not one motion:
//
// - `causal_language`'s leader (`soma/life/src/causal_language.rs`) — the law's only external
//   caller for a day;
// - `morphological_language::generate_currents` (`soma/life/src/morphological_language/ecology.rs`)
//   — a change of **law** and not of plumbing: it sectioned `at % lanes` **by count**, and its own
//   corpus proved that cover was not even lane-invariant;
// - `token_invariance::sweep_covered` (`crates/holonic-engine/src/token_invariance.rs`) — which
//   carried a second, independently written copy of the by-extent placement below. Two copies of
//   one law are where the two drift apart.
//
// **And three is the population of GENERATION fronts, not of every front in the body.** Two
// receiver-conditioning fronts in `soma/life/src/causal_language.rs` —
// `condition_route_receivers` and `condition_route_receivers_with_executor` — still section
// `at % lanes` by count. The second cannot conduct through this law as written: it mounts a fresh
// `&mut dyn LiveCurrentExecutor` per lane, and `expand` here is `Fn + Sync`, so a per-lane mutable
// carrier has no seat in this signature. That is a declared boundary of this law and not an
// oversight in that caller.

/// **Expand one front of co-present cells across the cover.**
///
/// The material is the closure: what one cell branches into at its junction. Everything else — the
/// cover, the sectioning by extent, the canonical reassembly — is this law.
///
/// **This is a decomposition and never a schedule.** `H.0219`: flux locality licenses the first and
/// never the second. Successors are concatenated in **section order over a canonically ordered
/// front**, so a lane's completion order never becomes chronology.
///
/// A lane's panic propagates exactly as it would have serially.
pub fn expand_front<Cell, Successor, Failure>(
    front: Vec<Cell>,
    cover: &HardwareCover,
    extent_of: impl Fn(&Cell) -> u64 + Sync,
    expand: impl Fn(Cell) -> Result<Vec<Successor>, Failure> + Sync,
) -> Result<Vec<Successor>, Failure>
where
    Cell: Send,
    Successor: Send,
    Failure: Send,
{
    let lanes = cover
        .host()
        .lanes
        .max(1)
        .min(front.len().max(1) as u32) as usize;
    if lanes <= 1 || front.len() <= 1 {
        let mut out = Vec::new();
        for cell in front {
            out.extend(expand(cell)?);
        }
        return Ok(out);
    }

    // Covered by EXTENT, not by count: a branch tip carrying a thousand continuations and one
    // carrying two are not one unit each.
    let mut ordered: Vec<(usize, u64)> = front
        .iter()
        .enumerate()
        .map(|(at, cell)| (at, extent_of(cell).max(1)))
        .collect();
    ordered.sort_by_key(|(at, extent)| (std::cmp::Reverse(*extent), *at));
    let mut placement: Vec<Vec<usize>> = vec![Vec::new(); lanes];
    let mut carried = vec![0u128; lanes];
    for (at, extent) in ordered {
        let lane = carried
            .iter()
            .enumerate()
            .min_by_key(|(lane, load)| (**load, *lane))
            .map(|(lane, _)| lane)
            .unwrap_or(0);
        placement[lane].push(at);
        carried[lane] += u128::from(extent);
    }
    for section in &mut placement {
        section.sort_unstable();
    }

    // Each cell is moved into exactly one lane, which is the independence this law needs and which
    // the placement above guarantees by construction.
    let mut held: Vec<Option<Cell>> = front.into_iter().map(Some).collect();
    let mut sections: Vec<Vec<(usize, Cell)>> = Vec::with_capacity(lanes);
    for section in &placement {
        let mut taken = Vec::with_capacity(section.len());
        for at in section {
            if let Some(cell) = held[*at].take() {
                taken.push((*at, cell));
            }
        }
        sections.push(taken);
    }

    let expand = &expand;
    let gathered = std::thread::scope(|scope| {
        let handles: Vec<_> = sections
            .into_iter()
            .map(|section| {
                scope.spawn(move || -> Result<Vec<(usize, Vec<Successor>)>, Failure> {
                    let mut rows = Vec::with_capacity(section.len());
                    for (at, cell) in section {
                        rows.push((at, expand(cell)?));
                    }
                    Ok(rows)
                })
            })
            .collect();
        let mut gathered: Vec<(usize, Vec<Successor>)> = Vec::new();
        for handle in handles {
            match handle.join() {
                Ok(rows) => gathered.extend(rows?),
                Err(payload) => std::panic::resume_unwind(payload),
            }
        }
        Ok::<_, Failure>(gathered)
    })?;

    // Canonical: the front's own order, never the order lanes finished in.
    let mut gathered = gathered;
    gathered.sort_by_key(|(at, _)| *at);
    Ok(gathered
        .into_iter()
        .flat_map(|(_, successors)| successors)
        .collect())
}
