//! **A declared partition of one section into coordinate regions, certified by computation.**
//!
//! # What was attempted first, and exactly what it could not express
//!
//! Deed H1 begins with composition, and the composition was attempted before this module was
//! founded. It returns two things and neither is a preference:
//!
//! | owner | what it carries | what it cannot say |
//! |---|---|---|
//! | [`crate::hardware_cover::FrontCell`] | `index: usize`, `extent: u64` | **no coordinate.** Two cells of extent four on a `2 x 4` section are indistinguishable from two cells that both cover the same four coordinates. `CoverDecomposition::independence` proves the *index* population is a partition; there is no term in it that could be a *region*, so it cannot be asked whether the coordinates are one. |
//! | [`crate::interchange::MemberFootprint`] | flat half-open address ranges | **no completeness, and the region is deleted on refusal.** `certify_footprints` proves pairwise write-disjointness and returns one `address` where two ranges meet, not the region where they meet; and a partition with a *hole* is disjoint, so it certifies as `Interchangeable`. Completeness is the one property a footprint certificate cannot fail on, because absence never collides. |
//! | [`crate::hardware_cover::CoverSection::work`] | members, occupied lanes, idle lanes | a count of members with no coordinate attached to any of them. |
//! | [`crate::receiver_current`] | site capacity, co-present population, service rounds, chronology, deferred arrivals | **no resource-species axis** — a site carries one capacity — and **no port for a declared arriving population**: the population is minted as one per source by radiation and multiplied by the outgoing branch count. `found_site` takes a capacity and nothing else. |
//!
//! So the absent relation founded here is exactly one: **a coordinate region of a section, and the
//! partition of a section into such regions with its completeness and disjointness computed rather
//! than asserted.** The absent *type* is [`SectionRegion`]; the absent *consequence* is an
//! uncovered region returned by name ([`PartitionDefect::RegionUncovered`]), which no owner above
//! can produce because none of them holds a coordinate.
//!
//! # What is composed, and it is composed rather than restated
//!
//! - the cover, the placement and its barriers: [`CoverDecomposition::of`],
//!   [`CoverDecomposition::independence`], [`CoverDecomposition::work`],
//!   [`CoverDecomposition::occupied_charts`], [`ModeIdentity::of`] — every lane figure and every
//!   cover barrier in [`TilingReceipt`] comes from there and none is recomputed here;
//! - the independence certificate: this module derives each cell's address ranges from its region
//!   and hands them to [`certify_footprints`] unchanged. The verdict is the interchange owner's.
//!   What this module adds is the *region* the shared address lies in, recovered from the
//!   footprint's `address` by the section's own stride, so a refusal names a region and not a
//!   number;
//! - the pressure: [`ExactReceiverCurrentLaw`] is founded and radiated for real, per cell and per
//!   species, and its `service_rounds`, `co_present_branch_population`, `passage_delay`,
//!   `arrival_chronology` and `deferred_arrivals` are what [`SpeciesPressure`] returns. Where the
//!   declared demand exceeds the caller's declared enactment aperture the enacted half is
//!   [`EnactedCurrent::BeyondAperture`] — *unknown, never zero*.
//!
//! # The one equation this module writes down itself, and why
//!
//! `R = ceil(N / C)` is `receiver_current`'s own service dilation; its implementation there is
//! private and its `N` is a branch population, not a declared demand. A demand is enacted here as a
//! fan-out of `N` passages out of the cell's own species site, so `receiver_current` computes
//! `co_present_branch_population = N` and `service_rounds = ceil(N / C)` itself and the reading is
//! genuinely its return. Above the aperture the same ceiling is stated directly and marked as
//! stated. Wherever both are available they are compared and a disagreement is a defect.
//!
//! # No authored level
//!
//! Every number that enters a reading here is either read off the material (a region's bounds, a
//! cell's extent, the section's stride) or declared by the caller (a capacity, a unit, a
//! characteristic delay, the enactment aperture, the cover). This module contains no threshold, no
//! split point and no default aperture.

use std::collections::{BTreeMap, BTreeSet};

use holonic_structure::LocalSet;
use num_bigint::BigUint;
use num_traits::Zero;

use crate::hardware_cover::{
    ChartId, CoverBarrier, CoverDecomposition, FrontCell, HardwareCover, ModeIdentity, SectionWork,
};
use crate::interchange::{
    DistinguishingWord, FrontCertificate, MemberFootprint, certify_footprints,
};
use crate::receiver_current::{
    ExactReceiverCurrentLaw, ExactReceiverCurrentPassage, ReceiverCurrentPassageId,
    ReceiverCurrentSiteId,
};

// -------------------------------------------------------------------------------------------------
// the section, its coordinates, and its regions
// -------------------------------------------------------------------------------------------------

/// The shape and exact carrier of one section: `rows x width` entries, each an exact `i64` interval
/// at grain `2^-grain_exponent`. No float participates; the grain is an integer exponent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SectionShape {
    pub rows: usize,
    pub width: usize,
    /// `F` in `2^-F`. The carrier is exact integers; this says what they are integers *of*.
    pub grain_exponent: u32,
}

impl SectionShape {
    pub fn of(rows: usize, width: usize, grain_exponent: u32) -> Self {
        Self {
            rows,
            width,
            grain_exponent,
        }
    }

    /// How many entries the section holds. `u64` because a section's extent is a count.
    pub fn extent(&self) -> u64 {
        self.rows as u64 * self.width as u64
    }

    /// The section's own region — the whole of it.
    pub fn whole(&self) -> SectionRegion {
        SectionRegion {
            row_from: 0,
            row_to: self.rows,
            column_from: 0,
            column_to: self.width,
        }
    }
}

/// **A half-open coordinate region of a section**: rows `[row_from, row_to)` by columns
/// `[column_from, column_to)`.
///
/// This is the type the composition returned as absent. It is a *coordinate* object: an extent can
/// be read off it, and it cannot be read off an extent.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SectionRegion {
    pub row_from: usize,
    pub row_to: usize,
    pub column_from: usize,
    pub column_to: usize,
}

impl SectionRegion {
    /// A region, refusing an inverted or empty one by name. An empty region is refused because a
    /// partition of empty regions is complete on no material and would certify.
    pub fn new(
        row_from: usize,
        row_to: usize,
        column_from: usize,
        column_to: usize,
    ) -> Result<Self, PartitionDefect> {
        if row_from >= row_to || column_from >= column_to {
            return Err(PartitionDefect::EmptyRegion {
                row_from,
                row_to,
                column_from,
                column_to,
            });
        }
        Ok(Self {
            row_from,
            row_to,
            column_from,
            column_to,
        })
    }

    pub fn rows(&self) -> usize {
        self.row_to - self.row_from
    }

    pub fn columns(&self) -> usize {
        self.column_to - self.column_from
    }

    pub fn extent(&self) -> u64 {
        self.rows() as u64 * self.columns() as u64
    }

    /// The exact intersection, or `None` when the two regions do not meet. This is what names an
    /// overlap; a shared *address* cannot.
    pub fn meet(&self, other: &Self) -> Option<Self> {
        let row_from = self.row_from.max(other.row_from);
        let row_to = self.row_to.min(other.row_to);
        let column_from = self.column_from.max(other.column_from);
        let column_to = self.column_to.min(other.column_to);
        (row_from < row_to && column_from < column_to).then_some(Self {
            row_from,
            row_to,
            column_from,
            column_to,
        })
    }

    /// Whether this region lies inside a shape. A region that does not is foreign to the section.
    pub fn within(&self, shape: &SectionShape) -> bool {
        self.row_to <= shape.rows && self.column_to <= shape.width
    }

    pub fn contains(&self, row: usize, column: usize) -> bool {
        row >= self.row_from
            && row < self.row_to
            && column >= self.column_from
            && column < self.column_to
    }

    /// The half-open address ranges this region occupies in a row-major body of the given stride,
    /// offset by `base`. A region spanning the full stride is **one** range; otherwise it is one
    /// range per row. This is the bridge into [`MemberFootprint`], and it is the only place a
    /// coordinate becomes an address.
    pub fn address_ranges(&self, stride: usize, base: u64) -> Vec<(u64, u64)> {
        let stride = stride as u64;
        if self.column_from == 0 && self.column_to as u64 == stride {
            return vec![(
                base + self.row_from as u64 * stride,
                base + self.row_to as u64 * stride,
            )];
        }
        (self.row_from..self.row_to)
            .map(|row| {
                let start = base + row as u64 * stride;
                (
                    start + self.column_from as u64,
                    start + self.column_to as u64,
                )
            })
            .collect()
    }

    /// The coordinate an address lies at, in a body of the given stride offset by `base`. This is
    /// the inverse of [`SectionRegion::address_ranges`] at one point, and it is what turns
    /// `certify_footprints`' returned `address` back into a region.
    pub fn coordinate_of(address: u64, stride: usize, base: u64) -> Option<(usize, usize)> {
        let stride = stride as u64;
        if stride == 0 || address < base {
            return None;
        }
        let local = address - base;
        Some(((local / stride) as usize, (local % stride) as usize))
    }
}

impl std::fmt::Display for SectionRegion {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "[{}..{}) x [{}..{})",
            self.row_from, self.row_to, self.column_from, self.column_to
        )
    }
}

// -------------------------------------------------------------------------------------------------
// the cells, the junction outputs they feed, and the partition
// -------------------------------------------------------------------------------------------------

/// The body and source a section came from. Lineage, not identity: a path is a route and this
/// records the route, never a checksum standing in for the thing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionLineage {
    /// The source occurrence the material entered through.
    pub source: String,
    /// The population inside it whose region this section realizes.
    pub population: String,
    /// The body this section stands in.
    pub body: String,
}

/// A region a cell reads, in a named population. The population's own shape is declared on the
/// partition, so a read carries a coordinate and not an address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadRegion {
    pub population: String,
    pub region: SectionRegion,
}

/// Where a cell's write goes when the output is owned by a junction rather than by the cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PartialAddress {
    /// Which declared junction owns the output this cell contributes to.
    pub junction: usize,
    /// Which partial of that junction this cell is.
    pub partial: usize,
}

/// One cell of the partition: the coordinate region it writes, the regions it reads, and whether
/// its write is its own output or one partial of a junction's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionCell {
    pub index: usize,
    /// The region of the section this cell's write covers.
    pub write: SectionRegion,
    pub reads: Vec<ReadRegion>,
    /// `None` when the cell owns its output region outright. `Some` when several cells write one
    /// logical output and a junction owns it — then the write lands in that junction's partial
    /// standing and the cells remain independent.
    pub partial_of: Option<PartialAddress>,
}

/// The output half of a shared-output junction, as the partition needs to see it. The junction
/// itself is [`crate::reduction_junction::ReductionJunction`]; this is the face it presents to a
/// partition, so the partition owner does not depend on the reduction owner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JunctionOutput {
    pub owner: String,
    pub output: SectionRegion,
    pub partials: usize,
}

/// **A declared partition of one section.** Nothing is certified at construction; the certification
/// is [`SectionPartition::certify`] and it computes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionPartition {
    pub lineage: SectionLineage,
    pub shape: SectionShape,
    /// The shape of every population a cell may read, by name. A read naming a population absent
    /// from here is refused.
    pub populations: BTreeMap<String, SectionShape>,
    pub cells: Vec<SectionCell>,
}

// -------------------------------------------------------------------------------------------------
// the defects
// -------------------------------------------------------------------------------------------------

/// Why a declared partition is not a partition. Every variant carries the **region** at which it
/// failed, which is the whole reason this owner exists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PartitionDefect {
    /// A region with no coordinates in it. Refused at construction: a partition of empty regions
    /// covers nothing and would certify complete on no material.
    EmptyRegion {
        row_from: usize,
        row_to: usize,
        column_from: usize,
        column_to: usize,
    },
    /// A section with no coordinates in it at all. **A partition of nothing is not a partition**,
    /// and the row-band sweep returns early on a zero extent, so completeness would otherwise read
    /// `true` over no material. Refused at the shape, one level above [`PartitionDefect::EmptyRegion`].
    EmptySection { shape: SectionShape },
    /// A tile outside the section it claims to partition.
    RegionOutsideSection {
        cell: usize,
        region: SectionRegion,
        shape: SectionShape,
    },
    /// A junction's output runs outside the section it claims to cover. Checked the way a cell's
    /// write is: a foreign covering region would otherwise mask a real hole while covering material
    /// the section does not have.
    JunctionOutputOutsideSection {
        junction: usize,
        owner: String,
        output: SectionRegion,
        shape: SectionShape,
    },
    /// A junction's declared output is not covered by the cells that carry its partials. The
    /// junction would otherwise enter the covering population by **declaration**, and completeness
    /// would be satisfied by a region no cell writes.
    JunctionOutputUncovered {
        junction: usize,
        owner: String,
        region: SectionRegion,
    },
    /// Two cells write regions that meet, and neither is a declared partial of a junction. The
    /// meet is exhibited.
    RegionsOverlap {
        cells: (usize, usize),
        region: SectionRegion,
    },
    /// A region of the section no cell and no junction writes. The hole is exhibited. **No
    /// footprint certificate can return this**: absence never collides.
    RegionUncovered { region: SectionRegion },
    /// Two cells address the same index.
    RepeatedCellIndex { cell: usize },
    /// A cell declares itself a partial of a junction that was not declared.
    UnknownJunction { cell: usize, junction: usize },
    /// A cell declares a partial ordinal the junction does not hold.
    UnknownPartial {
        cell: usize,
        junction: usize,
        partial: usize,
        partials: usize,
    },
    /// A cell's write is declared a partial of a junction but does not lie inside that junction's
    /// output region.
    PartialOutsideOutput {
        cell: usize,
        region: SectionRegion,
        output: SectionRegion,
    },
    /// A junction's output region meets another junction's, or a non-partial cell's write.
    JunctionOutputOverlaps {
        junction: usize,
        against: JunctionCollision,
        region: SectionRegion,
    },
    /// A read names a population the partition never declared its shape for.
    UnknownReadPopulation { cell: usize, population: String },
    /// A read lies outside its population's declared shape.
    ReadOutsidePopulation {
        cell: usize,
        population: String,
        region: SectionRegion,
        shape: SectionShape,
    },
    /// A region several cells read is in a population some cell also writes. The shared standing is
    /// not immutable, so the cells are not independent.
    SharedReadIsWritten {
        population: String,
        region: SectionRegion,
        readers: Vec<usize>,
        writer: usize,
    },
    /// The cover refused the placement. Carried verbatim from `hardware_cover`.
    Cover { barrier: CoverBarrier },
    /// The footprint certificate refused, and the shared address is reported **as the region it
    /// lies in**. The distinguishing word is carried verbatim beside it.
    FootprintRefused {
        because: DistinguishingWord,
        region: Option<SectionRegion>,
    },
    /// The enacted current and the stated ceiling disagreed at a site. Either the composition or
    /// the equation is wrong; the reading refuses rather than choosing one.
    ServiceRoundsDisagree {
        cell: usize,
        species: String,
        enacted: BigUint,
        stated: BigUint,
    },
    /// A species was declared with a capacity or a unit of zero.
    DegenerateSpecies { species: String },
}

/// What a junction's output collided with.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JunctionCollision {
    Junction(usize),
    Cell(usize),
}

impl std::fmt::Display for PartitionDefect {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PartitionDefect::EmptyRegion {
                row_from,
                row_to,
                column_from,
                column_to,
            } => write!(
                formatter,
                "the region [{row_from}..{row_to}) x [{column_from}..{column_to}) holds no coordinate"
            ),
            PartitionDefect::EmptySection { shape } => write!(
                formatter,
                "the {} x {} section holds no coordinate, so no partition of it exists",
                shape.rows, shape.width
            ),
            PartitionDefect::RegionOutsideSection {
                cell,
                region,
                shape,
            } => write!(
                formatter,
                "cell {cell} writes {region}, which lies outside the {} x {} section",
                shape.rows, shape.width
            ),
            PartitionDefect::JunctionOutputOutsideSection {
                junction,
                owner,
                output,
                shape,
            } => write!(
                formatter,
                "junction {junction} ({owner}) owns {output}, which lies outside the {} x {} section",
                shape.rows, shape.width
            ),
            PartitionDefect::JunctionOutputUncovered {
                junction,
                owner,
                region,
            } => write!(
                formatter,
                "no partial of junction {junction} ({owner}) writes {region} of its own output"
            ),
            PartitionDefect::RegionsOverlap { cells, region } => write!(
                formatter,
                "cells {} and {} both write {region}",
                cells.0, cells.1
            ),
            PartitionDefect::RegionUncovered { region } => {
                write!(formatter, "no cell and no junction writes {region}")
            }
            PartitionDefect::RepeatedCellIndex { cell } => {
                write!(
                    formatter,
                    "the partition declares cell {cell} more than once"
                )
            }
            PartitionDefect::UnknownJunction { cell, junction } => write!(
                formatter,
                "cell {cell} is a partial of junction {junction}, which was not declared"
            ),
            PartitionDefect::UnknownPartial {
                cell,
                junction,
                partial,
                partials,
            } => write!(
                formatter,
                "cell {cell} is partial {partial} of junction {junction}, which holds {partials}"
            ),
            PartitionDefect::PartialOutsideOutput {
                cell,
                region,
                output,
            } => write!(
                formatter,
                "cell {cell} writes {region}, outside its junction's output {output}"
            ),
            PartitionDefect::JunctionOutputOverlaps {
                junction,
                against,
                region,
            } => match against {
                JunctionCollision::Junction(other) => write!(
                    formatter,
                    "junctions {junction} and {other} both own {region}"
                ),
                JunctionCollision::Cell(cell) => write!(
                    formatter,
                    "junction {junction} owns {region}, which cell {cell} also writes"
                ),
            },
            PartitionDefect::UnknownReadPopulation { cell, population } => write!(
                formatter,
                "cell {cell} reads {population}, whose shape the partition does not declare"
            ),
            PartitionDefect::ReadOutsidePopulation {
                cell,
                population,
                region,
                shape,
            } => write!(
                formatter,
                "cell {cell} reads {region} of {population}, which is {} x {}",
                shape.rows, shape.width
            ),
            PartitionDefect::SharedReadIsWritten {
                population,
                region,
                readers,
                writer,
            } => write!(
                formatter,
                "{region} of {population} is read by {readers:?} and written by cell {writer}"
            ),
            PartitionDefect::Cover { barrier } => write!(formatter, "{barrier}"),
            PartitionDefect::FootprintRefused { because, region } => match region {
                Some(region) => write!(formatter, "the front is ordered at {region}: {because:?}"),
                None => write!(formatter, "the front is ordered: {because:?}"),
            },
            PartitionDefect::ServiceRoundsDisagree {
                cell,
                species,
                enacted,
                stated,
            } => write!(
                formatter,
                "cell {cell} species {species}: the enacted current returned {enacted} rounds and \
                 the stated ceiling {stated}"
            ),
            PartitionDefect::DegenerateSpecies { species } => {
                write!(
                    formatter,
                    "species {species} declares a zero capacity or unit"
                )
            }
        }
    }
}

// -------------------------------------------------------------------------------------------------
// pressure: composed from receiver_current, one covector per species, never summed
// -------------------------------------------------------------------------------------------------

/// Which face of a cell's material a species' demand is read off. The caller declares the face and
/// the unit; the *quantity* is then read off the cell's own regions, so varying a region moves the
/// demand and no demand is authored.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DemandFace {
    /// Entries the cell writes.
    Written,
    /// Entries the cell reads, summed over its read regions.
    Read,
    /// Both.
    Touched,
}

/// One declared resource species. Capacity, unit and delay are the caller's declaration about the
/// apparatus; nothing here is authored inside the organ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclaredSpecies {
    pub name: String,
    /// What one unit of this species carries, in section entries. A lane that carries one entry
    /// declares `1`; a transfer sector that carries sixteen declares `16`.
    pub unit: u64,
    pub face: DemandFace,
    /// `C` — the co-present population one site serves in one round. **Caller-declared, per
    /// species.** It is not read off the cover and this module never consults a device: a driver
    /// that wants the cover's lane count here couples the two by hand, and that coupling is the
    /// driver's, not this owner's.
    pub capacity: BigUint,
    /// The positive chronology an uncongested passage of this species costs.
    pub characteristic_delay: u64,
    /// The capacity of the sink each branch of the enacted fan-out lands on. **Caller-declared,
    /// with no default**, because `receiver_current` requires a positive capacity at every founded
    /// site and this module may not invent one.
    ///
    /// It is carried honestly: in the enactment below the sinks are terminal — they have no
    /// outgoing passage — so no service dilation is taken at them and **this declaration does not
    /// move any returned coordinate today**. It is refused when zero, exactly as `capacity` is.
    pub sink_capacity: BigUint,
}

/// The species, and the aperture within which the current is actually enacted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResourceDeclaration {
    pub species: Vec<DeclaredSpecies>,
    /// The greatest demand this reading will enact through `receiver_current`. Above it the
    /// enacted half is [`EnactedCurrent::BeyondAperture`]; it never becomes zero.
    pub enactment_aperture: u64,
}

/// The half of a species reading that `receiver_current` actually conducted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EnactedCurrent {
    /// The law was founded and radiated. Every field is its return.
    Radiated {
        site: ReceiverCurrentSiteId,
        passage: ReceiverCurrentPassageId,
        co_present_branch_population: BigUint,
        site_capacity: BigUint,
        service_rounds: BigUint,
        characteristic_delay: u64,
        passage_delay: u64,
        arrival_chronology: u64,
        /// Populations that did not arrive within the declared horizon of one uncongested round.
        deferred: BigUint,
        deferred_arrivals: usize,
    },
    /// The demand exceeds the caller's enactment aperture. **Unknown, not zero.**
    BeyondAperture { demand: u64, aperture: u64 },
    /// **A genuine zero demand.** The cell's face carries no material for this species, so there is
    /// nothing to radiate and nothing is unknown. Named apart from
    /// [`EnactedCurrent::BeyondAperture`], whose whole purpose is to say *unknown, never zero*:
    /// returning the unknown variant on a real zero asserted the opposite of what happened.
    NoDemand { face: DemandFace },
}

/// One species' pressure at one site. A covector coordinate; it is never added to another species'.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpeciesPressure {
    pub species: String,
    pub unit: u64,
    pub face: DemandFace,
    /// `N` — the demand, read off the cell's regions in this species' unit.
    pub incoming: BigUint,
    /// `C` — the declared capacity.
    pub capacity: BigUint,
    /// `R = ceil(N / C)`, as `receiver_current` returned it where it was enacted, and as the same
    /// ceiling stated where the demand exceeded the aperture.
    pub service_rounds: BigUint,
    /// `R * C - N` — the capacity the last round does not fill. The idle-lane reading of a
    /// resource, exhibited rather than normalised away.
    pub boundary_residual: BigUint,
    /// The population refused within one uncongested round, which is the deferred current.
    pub reflected: BigUint,
    pub enacted: EnactedCurrent,
}

/// **The pressure at one cell**: one covector coordinate per species, and no coordinate that
/// combines them.
///
/// There is no `total`, no `sum`, no `utilization` and no `pressure` scalar on this type, and
/// [`PressureReceipt::coordinates`] returns exactly the declared species and nothing else.
///
/// **The absence of a combined coordinate is a fact about the TYPE, and the check that reads it is
/// a check on the type's own field names.** An earlier statement here offered a different falsifier
/// — that two declarations with equal cross-species sums and different splits return different
/// receipts — and that is weaker than it sounds: a receipt carrying an extra `total` field would
/// still return different receipts and would still pass it. The split comparison shows the
/// per-species coordinates are not collapsed INTO one; it cannot show that no combined coordinate
/// stands beside them. Both readings are kept, and the field-name reading is the one that decides.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PressureReceipt {
    pub cell: usize,
    pub species: Vec<SpeciesPressure>,
}

impl PressureReceipt {
    /// Every coordinate this receipt carries, by species name. The population of names is exactly
    /// the declared species.
    pub fn coordinates(&self) -> Vec<(&str, &SpeciesPressure)> {
        self.species
            .iter()
            .map(|species| (species.species.as_str(), species))
            .collect()
    }

    pub fn species_named(&self, name: &str) -> Option<&SpeciesPressure> {
        self.species.iter().find(|species| species.species == name)
    }
}

// -------------------------------------------------------------------------------------------------
// the receipt
// -------------------------------------------------------------------------------------------------

/// A region several cells read, and whether the standing it sits in is immutable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedRead {
    pub population: String,
    pub region: SectionRegion,
    pub readers: Vec<usize>,
    /// True when no cell writes this population, so the standing has one owner and is shared
    /// immutably. False is a defect and is returned as one.
    pub immutable: bool,
}

/// What the partition covers, computed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Completeness {
    pub section_extent: BigUint,
    pub covered_extent: BigUint,
    pub uncovered: Vec<SectionRegion>,
    pub complete: bool,
}

/// What the partition shares, computed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Disjointness {
    pub pairs_checked: usize,
    pub overlaps: Vec<(usize, usize, SectionRegion)>,
    pub disjoint: bool,
}

/// The cover's own reading of the placement, carried verbatim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TilingCover {
    pub occupied: BTreeSet<ChartId>,
    pub work: Vec<SectionWork>,
    pub barriers: Vec<CoverBarrier>,
}

/// **The tiling receipt.** Every field is either the material's own coordinate or a composed
/// owner's return.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TilingReceipt {
    pub schema: String,
    pub lineage: SectionLineage,
    pub shape: SectionShape,
    /// Per cell: its region, its extent, what it reads and where its write lands.
    pub cells: Vec<CellReceipt>,
    /// The junction outputs the partition was certified against.
    pub junctions: Vec<JunctionOutput>,
    pub completeness: Completeness,
    pub disjointness: Disjointness,
    pub shared_reads: Vec<SharedRead>,
    /// Per cell, per population: the part of its read region another cell also reads. The halo.
    pub halo: Vec<(usize, String, SectionRegion)>,
    pub cover: TilingCover,
    /// The interchange owner's verdict, derived from the cells' address ranges.
    pub certificate: FrontCertificate,
    pub pressure: Vec<PressureReceipt>,
    pub mode: ModeIdentity,
}

/// One cell's half of the receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellReceipt {
    pub index: usize,
    pub write: SectionRegion,
    pub write_extent: u64,
    pub reads: Vec<ReadRegion>,
    pub read_extent: u64,
    pub partial_of: Option<PartialAddress>,
    /// The address ranges the footprint certificate was derived from, in order.
    pub footprint: MemberFootprint,
}

impl TilingReceipt {
    pub fn is_partition(&self) -> bool {
        self.completeness.complete && self.disjointness.disjoint
    }

    pub fn is_interchangeable(&self) -> bool {
        self.certificate.is_interchangeable()
    }
}

// -------------------------------------------------------------------------------------------------
// the certification
// -------------------------------------------------------------------------------------------------

fn ceil_division(numerator: &BigUint, denominator: &BigUint) -> BigUint {
    if denominator.is_zero() {
        return BigUint::zero();
    }
    let one = BigUint::from(1u32);
    (numerator + denominator - &one) / denominator
}

impl SectionPartition {
    /// **Certify the partition.** Completeness and disjointness are computed; the cover, the
    /// independence certificate and the current are composed; every failure is returned as a
    /// [`PartitionDefect`] carrying the region it failed at.
    ///
    /// Nothing here classifies material by a field the caller set: the classes returned — covered,
    /// uncovered, overlapping, shared, immutable — are all decided by *interval arithmetic on the
    /// declared regions*, and moving any region's bound moves the class. That is the variation the
    /// perturbation controls exercise.
    pub fn certify(
        &self,
        cover: &HardwareCover,
        junctions: &[JunctionOutput],
        resources: &ResourceDeclaration,
        kernel: &'static str,
    ) -> Result<TilingReceipt, Vec<PartitionDefect>> {
        let mut defects: Vec<PartitionDefect> = Vec::new();

        // ---- the section itself must hold coordinates ------------------------------------------
        //
        // The sweep returns early on a zero extent, so without this a `0 x 8` section with no cells
        // reads back complete and disjoint — a partition of nothing. Refused here rather than in
        // the sweep, because the defect is the declared shape and not the covering population.
        if self.shape.extent() == 0 {
            defects.push(PartitionDefect::EmptySection { shape: self.shape });
        }

        // ---- the addresses each cell's region occupies, and the populations they live in -------
        let bases = self.address_bases(junctions);

        // ---- structural declarations: index, junction, population --------------------------------
        for (at, cell) in self.cells.iter().enumerate() {
            if self.cells[..at]
                .iter()
                .any(|earlier| earlier.index == cell.index)
            {
                defects.push(PartitionDefect::RepeatedCellIndex { cell: cell.index });
            }
            // `SectionRegion::new` refuses a degenerate region, and its fields are public, so a
            // caller reaches the state by a struct literal. The guard is re-taken HERE, at the
            // certifier, because that is where the doc's stated reason for it applies: a partition
            // of empty regions covers nothing and would otherwise certify.
            if cell.write.extent() == 0 {
                defects.push(PartitionDefect::EmptyRegion {
                    row_from: cell.write.row_from,
                    row_to: cell.write.row_to,
                    column_from: cell.write.column_from,
                    column_to: cell.write.column_to,
                });
            }
            for read in &cell.reads {
                if read.region.extent() == 0 {
                    defects.push(PartitionDefect::EmptyRegion {
                        row_from: read.region.row_from,
                        row_to: read.region.row_to,
                        column_from: read.region.column_from,
                        column_to: read.region.column_to,
                    });
                }
            }
            if !cell.write.within(&self.shape) {
                defects.push(PartitionDefect::RegionOutsideSection {
                    cell: cell.index,
                    region: cell.write,
                    shape: self.shape,
                });
            }
            match cell.partial_of {
                None => {}
                Some(address) => match junctions.get(address.junction) {
                    None => defects.push(PartitionDefect::UnknownJunction {
                        cell: cell.index,
                        junction: address.junction,
                    }),
                    Some(junction) => {
                        if address.partial >= junction.partials {
                            defects.push(PartitionDefect::UnknownPartial {
                                cell: cell.index,
                                junction: address.junction,
                                partial: address.partial,
                                partials: junction.partials,
                            });
                        }
                        if cell.write.meet(&junction.output) != Some(cell.write) {
                            defects.push(PartitionDefect::PartialOutsideOutput {
                                cell: cell.index,
                                region: cell.write,
                                output: junction.output,
                            });
                        }
                    }
                },
            }
            for read in &cell.reads {
                match self.populations.get(&read.population) {
                    None => defects.push(PartitionDefect::UnknownReadPopulation {
                        cell: cell.index,
                        population: read.population.clone(),
                    }),
                    Some(shape) => {
                        if !read.region.within(shape) {
                            defects.push(PartitionDefect::ReadOutsidePopulation {
                                cell: cell.index,
                                population: read.population.clone(),
                                region: read.region,
                                shape: *shape,
                            });
                        }
                    }
                }
            }
        }

        // ---- the junctions: their outputs are regions of THIS section, and their partials
        //      actually cover them ------------------------------------------------------------
        //
        // A junction output enters the covering population, so it is checked exactly as a cell's
        // write is: degenerate, foreign, and — the part no composed owner can do — **covered by the
        // cells that carry its partials**. Without the last check the junction covers by
        // declaration and completeness is satisfied by a region nothing writes.
        //
        // Overlap BETWEEN two partials of one junction is lawful and is deliberately not a defect:
        // two partials contract different inner regions into the same output coordinates, which is
        // what a junction is for. Their independence comes from the partial-slot address
        // separation, which `certify_footprints` sees; their coordinate regions are a union, not a
        // partition.
        for (at, junction) in junctions.iter().enumerate() {
            if junction.output.extent() == 0 {
                defects.push(PartitionDefect::EmptyRegion {
                    row_from: junction.output.row_from,
                    row_to: junction.output.row_to,
                    column_from: junction.output.column_from,
                    column_to: junction.output.column_to,
                });
                continue;
            }
            if !junction.output.within(&self.shape) {
                defects.push(PartitionDefect::JunctionOutputOutsideSection {
                    junction: at,
                    owner: junction.owner.clone(),
                    output: junction.output,
                    shape: self.shape,
                });
                continue;
            }
            let mut written: Vec<SectionRegion> = Vec::new();
            for cell in &self.cells {
                if cell
                    .partial_of
                    .is_some_and(|address| address.junction == at)
                {
                    written.push(cell.write);
                }
            }
            for region in uncovered_within(&junction.output, &written) {
                defects.push(PartitionDefect::JunctionOutputUncovered {
                    junction: at,
                    owner: junction.owner.clone(),
                    region,
                });
            }
        }

        // ---- the covering population: non-partial cell writes plus junction outputs -------------
        let covering = self.covering_regions(junctions);

        // ---- disjointness, computed by exact meets ---------------------------------------------
        let mut overlaps: Vec<(usize, usize, SectionRegion)> = Vec::new();
        let mut pairs_checked = 0usize;
        for (a, (a_owner, a_region)) in covering.iter().enumerate() {
            for (b_owner, b_region) in covering.iter().skip(a + 1) {
                pairs_checked += 1;
                if let Some(region) = a_region.meet(b_region) {
                    match (a_owner, b_owner) {
                        (CoveringOwner::Cell(left), CoveringOwner::Cell(right)) => {
                            overlaps.push((*left, *right, region));
                            defects.push(PartitionDefect::RegionsOverlap {
                                cells: (*left, *right),
                                region,
                            });
                        }
                        (CoveringOwner::Junction(junction), CoveringOwner::Cell(cell))
                        | (CoveringOwner::Cell(cell), CoveringOwner::Junction(junction)) => {
                            defects.push(PartitionDefect::JunctionOutputOverlaps {
                                junction: *junction,
                                against: JunctionCollision::Cell(*cell),
                                region,
                            });
                        }
                        (CoveringOwner::Junction(left), CoveringOwner::Junction(right)) => {
                            defects.push(PartitionDefect::JunctionOutputOverlaps {
                                junction: *left,
                                against: JunctionCollision::Junction(*right),
                                region,
                            });
                        }
                    }
                }
            }
        }

        // ---- completeness, computed by a row-band sweep with a column-interval complement -------
        let regions: Vec<SectionRegion> = covering.iter().map(|(_, region)| *region).collect();
        let uncovered = uncovered_regions(&self.shape, &regions);
        let covered_extent: BigUint = regions
            .iter()
            .map(|region| BigUint::from(region.extent()))
            .sum();
        let completeness = Completeness {
            section_extent: BigUint::from(self.shape.extent()),
            covered_extent,
            complete: uncovered.is_empty(),
            uncovered,
        };
        for region in &completeness.uncovered {
            defects.push(PartitionDefect::RegionUncovered { region: *region });
        }

        // ---- shared reads and the halo ----------------------------------------------------------
        let (shared_reads, halo) = self.shared_reads(&mut defects);

        // ---- the cover, composed ----------------------------------------------------------------
        let front: Vec<FrontCell> = self
            .cells
            .iter()
            .map(|cell| FrontCell {
                index: cell.index,
                extent: cell.write.extent(),
            })
            .collect();
        let decomposition = CoverDecomposition::of(cover, &front, kernel);
        let barriers = match decomposition.independence(&front) {
            Ok(()) => Vec::new(),
            Err(barriers) => barriers,
        };
        for barrier in &barriers {
            defects.push(PartitionDefect::Cover {
                barrier: barrier.clone(),
            });
        }
        let tiling_cover = TilingCover {
            occupied: decomposition.occupied_charts(),
            work: decomposition.work(cover),
            barriers,
        };

        // ---- the footprints and the interchange certificate, composed ---------------------------
        let footprints: Vec<MemberFootprint> = self
            .cells
            .iter()
            .map(|cell| self.footprint_of(cell, &bases))
            .collect();
        let certificate = certify_footprints(&footprints);
        if let Some(because) = certificate.because() {
            let region = self.region_of_shared_address(because, &bases);
            defects.push(PartitionDefect::FootprintRefused {
                because: because.clone(),
                region,
            });
        }

        // ---- the pressure, composed from receiver_current ----------------------------------------
        let pressure = self.pressure(resources, &mut defects);

        if !defects.is_empty() {
            return Err(defects);
        }

        let cells: Vec<CellReceipt> = self
            .cells
            .iter()
            .zip(footprints)
            .map(|(cell, footprint)| CellReceipt {
                index: cell.index,
                write: cell.write,
                write_extent: cell.write.extent(),
                reads: cell.reads.clone(),
                read_extent: cell.reads.iter().map(|read| read.region.extent()).sum(),
                partial_of: cell.partial_of,
                footprint,
            })
            .collect();

        Ok(TilingReceipt {
            schema: "holonic-engine.tiling-receipt.v1".to_owned(),
            lineage: self.lineage.clone(),
            shape: self.shape,
            cells,
            junctions: junctions.to_vec(),
            completeness,
            disjointness: Disjointness {
                pairs_checked,
                disjoint: overlaps.is_empty(),
                overlaps,
            },
            shared_reads,
            halo,
            cover: tiling_cover,
            certificate,
            pressure,
            mode: ModeIdentity::of(
                cover,
                "holonic_engine::section_partition",
                "exact-integer-v1",
                kernel,
            ),
        })
    }

    /// The regions that must cover the section: every cell that owns its output, plus every
    /// junction's output. A partial's write is *not* a covering region — the junction's output is.
    fn covering_regions(
        &self,
        junctions: &[JunctionOutput],
    ) -> Vec<(CoveringOwner, SectionRegion)> {
        let mut covering: Vec<(CoveringOwner, SectionRegion)> = self
            .cells
            .iter()
            .filter(|cell| cell.partial_of.is_none())
            .map(|cell| (CoveringOwner::Cell(cell.index), cell.write))
            .collect();
        for (at, junction) in junctions.iter().enumerate() {
            covering.push((CoveringOwner::Junction(at), junction.output));
        }
        covering
    }

    /// Which cell writes a region, when the region belongs to the population the cells write.
    ///
    /// A cell writes **the section**, and only the section. So a read is a read of a written
    /// standing exactly when it names the section's own population and its region meets some
    /// cell's write. That is a computed relation, not a declared flag: moving either region moves
    /// the answer.
    fn writer_of(&self, population: &str, region: &SectionRegion) -> Option<usize> {
        if population != self.lineage.population {
            return None;
        }
        self.cells
            .iter()
            .find(|cell| cell.write.meet(region).is_some())
            .map(|cell| cell.index)
    }

    /// Regions read by more than one cell, and the halo they form.
    fn shared_reads(
        &self,
        defects: &mut Vec<PartitionDefect>,
    ) -> (Vec<SharedRead>, Vec<(usize, String, SectionRegion)>) {
        let mut shared: Vec<SharedRead> = Vec::new();
        let mut halo: Vec<(usize, String, SectionRegion)> = Vec::new();
        for (a, left) in self.cells.iter().enumerate() {
            for right in self.cells.iter().skip(a + 1) {
                for left_read in &left.reads {
                    for right_read in &right.reads {
                        if left_read.population != right_read.population {
                            continue;
                        }
                        let Some(region) = left_read.region.meet(&right_read.region) else {
                            continue;
                        };
                        let writer = self.writer_of(&left_read.population, &region);
                        let immutable = writer.is_none();
                        if let Some(writer) = writer {
                            defects.push(PartitionDefect::SharedReadIsWritten {
                                population: left_read.population.clone(),
                                region,
                                readers: vec![left.index, right.index],
                                writer,
                            });
                        }
                        shared.push(SharedRead {
                            population: left_read.population.clone(),
                            region,
                            readers: vec![left.index, right.index],
                            immutable,
                        });
                        halo.push((left.index, left_read.population.clone(), region));
                        halo.push((right.index, right_read.population.clone(), region));
                    }
                }
            }
        }
        (shared, halo)
    }

    /// Where each address space begins: the section at zero, then one slot per declared junction
    /// partial, then the read populations in name order. Every base is a prefix sum over declared
    /// extents; nothing is authored.
    fn address_bases(&self, junctions: &[JunctionOutput]) -> AddressBases {
        let mut cursor = self.shape.extent();
        let mut partials: Vec<Vec<u64>> = Vec::with_capacity(junctions.len());
        for junction in junctions {
            let mut slots = Vec::with_capacity(junction.partials);
            for _ in 0..junction.partials {
                slots.push(cursor);
                cursor += self.shape.extent();
            }
            partials.push(slots);
        }
        let mut populations: BTreeMap<String, u64> = BTreeMap::new();
        for (name, shape) in &self.populations {
            // The section's own population is the address space the cells write. A read of it is a
            // read of what the cells write and must land on the same addresses — giving it a slot
            // of its own would have hidden exactly the write/read hazard the certificate exists to
            // find.
            if *name == self.lineage.population {
                populations.insert(name.clone(), 0);
                continue;
            }
            populations.insert(name.clone(), cursor);
            cursor += shape.extent();
        }
        AddressBases {
            section: 0,
            partials,
            populations,
        }
    }

    /// One cell's footprint: its reads in their populations' address spaces, its write in the
    /// section's or in its junction's partial slot.
    fn footprint_of(&self, cell: &SectionCell, bases: &AddressBases) -> MemberFootprint {
        let mut reads: Vec<(u64, u64)> = Vec::new();
        for read in &cell.reads {
            let (Some(shape), Some(base)) = (
                self.populations.get(&read.population),
                bases.populations.get(&read.population),
            ) else {
                continue;
            };
            reads.extend(read.region.address_ranges(shape.width, *base));
        }
        let base = match cell.partial_of {
            None => bases.section,
            Some(address) => bases
                .partials
                .get(address.junction)
                .and_then(|slots| slots.get(address.partial))
                .copied()
                .unwrap_or(bases.section),
        };
        let writes = cell.write.address_ranges(self.shape.width, base);
        MemberFootprint { reads, writes }
    }

    /// Turn the footprint certificate's shared **address** back into the **region** it lies in.
    /// This is the one thing `certify_footprints` deletes, and recovering it is why a coordinate
    /// owner had to exist.
    fn region_of_shared_address(
        &self,
        because: &DistinguishingWord,
        bases: &AddressBases,
    ) -> Option<SectionRegion> {
        let DistinguishingWord::FootprintShared { address, .. } = because else {
            return None;
        };
        let section_extent = self.shape.extent();
        // The section itself and every partial slot share the section's stride.
        let mut candidates: Vec<u64> = vec![bases.section];
        for slots in &bases.partials {
            candidates.extend(slots.iter().copied());
        }
        for base in candidates {
            if *address >= base && *address < base + section_extent {
                let (row, column) = SectionRegion::coordinate_of(*address, self.shape.width, base)?;
                return SectionRegion::new(row, row + 1, column, column + 1).ok();
            }
        }
        for (name, base) in &bases.populations {
            let shape = self.populations.get(name)?;
            if *address >= *base && *address < *base + shape.extent() {
                let (row, column) = SectionRegion::coordinate_of(*address, shape.width, *base)?;
                return SectionRegion::new(row, row + 1, column, column + 1).ok();
            }
        }
        None
    }

    /// **The pressure population, one covector coordinate per species per cell.**
    ///
    /// The demand is read off the cell's own regions in the species' declared unit. Where the
    /// demand is within the caller's enactment aperture, an `ExactReceiverCurrentLaw` is founded
    /// with the cell's species site at the declared capacity and a fan-out of `N` passages, and
    /// **`receiver_current` computes the service rounds**; the horizon is one uncongested round, so
    /// a demand needing more than one round arrives late and is returned as deferred current.
    fn pressure(
        &self,
        resources: &ResourceDeclaration,
        defects: &mut Vec<PartitionDefect>,
    ) -> Vec<PressureReceipt> {
        let mut population: Vec<PressureReceipt> = Vec::with_capacity(self.cells.len());
        for cell in &self.cells {
            let written = cell.write.extent();
            let read: u64 = cell.reads.iter().map(|read| read.region.extent()).sum();
            let mut species_population: Vec<SpeciesPressure> =
                Vec::with_capacity(resources.species.len());
            for species in &resources.species {
                if species.unit == 0
                    || species.capacity.is_zero()
                    || species.sink_capacity.is_zero()
                    || species.characteristic_delay == 0
                {
                    defects.push(PartitionDefect::DegenerateSpecies {
                        species: species.name.clone(),
                    });
                    continue;
                }
                let entries = match species.face {
                    DemandFace::Written => written,
                    DemandFace::Read => read,
                    DemandFace::Touched => written + read,
                };
                let demand = entries.div_ceil(species.unit);
                let incoming = BigUint::from(demand);
                let stated_rounds = ceil_division(&incoming, &species.capacity);
                let enacted = enact_current(demand, species, resources.enactment_aperture);
                let service_rounds = match &enacted {
                    EnactedCurrent::Radiated { service_rounds, .. } => {
                        if service_rounds != &stated_rounds {
                            defects.push(PartitionDefect::ServiceRoundsDisagree {
                                cell: cell.index,
                                species: species.name.clone(),
                                enacted: service_rounds.clone(),
                                stated: stated_rounds.clone(),
                            });
                        }
                        service_rounds.clone()
                    }
                    EnactedCurrent::BeyondAperture { .. } | EnactedCurrent::NoDemand { .. } => {
                        stated_rounds
                    }
                };
                let reflected = match &enacted {
                    EnactedCurrent::Radiated { deferred, .. } => deferred.clone(),
                    EnactedCurrent::BeyondAperture { .. } | EnactedCurrent::NoDemand { .. } => {
                        BigUint::zero()
                    }
                };
                let boundary_residual = &service_rounds * &species.capacity - &incoming;
                species_population.push(SpeciesPressure {
                    species: species.name.clone(),
                    unit: species.unit,
                    face: species.face,
                    incoming,
                    capacity: species.capacity.clone(),
                    service_rounds,
                    boundary_residual,
                    reflected,
                    enacted,
                });
            }
            population.push(PressureReceipt {
                cell: cell.index,
                species: species_population,
            });
        }
        population
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CoveringOwner {
    Cell(usize),
    Junction(usize),
}

struct AddressBases {
    section: u64,
    partials: Vec<Vec<u64>>,
    populations: BTreeMap<String, u64>,
}

/// **Enact one cell's demand for one species through `receiver_current`.**
///
/// The law is founded with the cell's species site at the declared capacity and `N` outgoing
/// passages into sinks, so the owner's own `co_present_branch_population` is `N`, its own
/// `service_rounds` is `ceil(N / C)` and its own `service_dilation` is `R - 1`. The horizon is one
/// uncongested round, so everything that needs a second round returns as deferred current.
fn enact_current(demand: u64, species: &DeclaredSpecies, aperture: u64) -> EnactedCurrent {
    if demand == 0 {
        return EnactedCurrent::NoDemand { face: species.face };
    }
    if demand > aperture {
        return EnactedCurrent::BeyondAperture { demand, aperture };
    }
    let mut law = ExactReceiverCurrentLaw::new();
    let site = ReceiverCurrentSiteId(0);
    if law.found_site(site, species.capacity.clone()).is_err() {
        return EnactedCurrent::BeyondAperture { demand, aperture };
    }
    for index in 0..demand {
        let sink = ReceiverCurrentSiteId(index + 1);
        if law.found_site(sink, species.sink_capacity.clone()).is_err() {
            return EnactedCurrent::BeyondAperture { demand, aperture };
        }
        if law
            .found_passage(ExactReceiverCurrentPassage {
                id: ReceiverCurrentPassageId(index),
                from: site,
                to: sink,
                characteristic_delay: species.characteristic_delay,
            })
            .is_err()
        {
            return EnactedCurrent::BeyondAperture { demand, aperture };
        }
    }
    let mut sources = LocalSet::new();
    sources.insert(site);
    let horizon = species.characteristic_delay;
    let Ok(radiation) = law.radiate_to_horizon(sources, horizon) else {
        return EnactedCurrent::BeyondAperture { demand, aperture };
    };
    let Some(receipt) = radiation.passage_receipts.first() else {
        return EnactedCurrent::BeyondAperture { demand, aperture };
    };
    let deferred: BigUint = radiation
        .deferred_arrivals
        .iter()
        .map(|arrival| arrival.population.clone())
        .sum();
    EnactedCurrent::Radiated {
        site,
        passage: receipt.passage,
        co_present_branch_population: receipt.co_present_branch_population.clone(),
        site_capacity: receipt.site_capacity.clone(),
        service_rounds: receipt.service_rounds.clone(),
        characteristic_delay: receipt.characteristic_delay,
        passage_delay: receipt.passage_delay,
        arrival_chronology: receipt.arrival_chronology,
        deferred,
        deferred_arrivals: radiation.deferred_arrivals.len(),
    }
}

/// **Every maximal region of the shape that no declared region covers.**
///
/// A row-band sweep: the regions' row bounds break the section into bands in which every region
/// either covers the whole band or misses it entirely, so the uncovered part of a band is the
/// complement of a merged column-interval population. Vertically adjacent bands with identical
/// gaps are merged, so a missing tile returns as one region and not as a stack of rows.
///
/// **This is the computation no composed owner can perform**, because it needs the section's own
/// extent and every region's coordinates at once.
pub fn uncovered_regions(shape: &SectionShape, regions: &[SectionRegion]) -> Vec<SectionRegion> {
    if shape.rows == 0 || shape.width == 0 {
        return Vec::new();
    }
    let mut breaks: BTreeSet<usize> = BTreeSet::new();
    breaks.insert(0);
    breaks.insert(shape.rows);
    for region in regions {
        if region.row_from < shape.rows {
            breaks.insert(region.row_from);
        }
        if region.row_to < shape.rows {
            breaks.insert(region.row_to);
        }
    }
    let bounds: Vec<usize> = breaks.into_iter().collect();
    let mut bands: Vec<(usize, usize, Vec<(usize, usize)>)> = Vec::new();
    for window in bounds.windows(2) {
        let (from, to) = (window[0], window[1]);
        let mut covered: Vec<(usize, usize)> = regions
            .iter()
            .filter(|region| region.row_from <= from && region.row_to >= to)
            .map(|region| (region.column_from, region.column_to))
            .collect();
        covered.sort_unstable();
        let mut gaps: Vec<(usize, usize)> = Vec::new();
        let mut cursor = 0usize;
        for (start, end) in covered {
            if start > cursor {
                gaps.push((cursor, start));
            }
            cursor = cursor.max(end);
        }
        if cursor < shape.width {
            gaps.push((cursor, shape.width));
        }
        if !gaps.is_empty() {
            bands.push((from, to, gaps));
        }
    }
    // Merge vertically adjacent bands with identical gaps.
    let mut merged: Vec<(usize, usize, Vec<(usize, usize)>)> = Vec::new();
    for band in bands {
        match merged.last_mut() {
            Some(last) if last.1 == band.0 && last.2 == band.2 => last.1 = band.1,
            _ => merged.push(band),
        }
    }
    let mut uncovered: Vec<SectionRegion> = Vec::new();
    for (from, to, gaps) in merged {
        for (column_from, column_to) in gaps {
            uncovered.push(SectionRegion {
                row_from: from,
                row_to: to,
                column_from,
                column_to,
            });
        }
    }
    uncovered
}

/// **Every maximal part of one REGION that the declared covering regions do not reach.**
///
/// [`uncovered_regions`] answers the question for a whole section, whose origin is `(0, 0)`. A
/// junction owns a *region*, so the same sweep is taken in that region's own frame: the covering
/// regions are met with it, shifted to its origin, swept, and the holes shifted back. No second
/// algorithm exists here — the sweep is the one above.
pub fn uncovered_within(region: &SectionRegion, covering: &[SectionRegion]) -> Vec<SectionRegion> {
    let frame = SectionShape::of(region.rows(), region.columns(), 0);
    let mut local: Vec<SectionRegion> = Vec::new();
    for candidate in covering {
        if let Some(met) = region.meet(candidate) {
            local.push(SectionRegion {
                row_from: met.row_from - region.row_from,
                row_to: met.row_to - region.row_from,
                column_from: met.column_from - region.column_from,
                column_to: met.column_to - region.column_from,
            });
        }
    }
    uncovered_regions(&frame, &local)
        .into_iter()
        .map(|hole| SectionRegion {
            row_from: hole.row_from + region.row_from,
            row_to: hole.row_to + region.row_from,
            column_from: hole.column_from + region.column_from,
            column_to: hole.column_to + region.column_from,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shape() -> SectionShape {
        SectionShape::of(4, 8, 12)
    }

    fn lineage() -> SectionLineage {
        SectionLineage {
            source: "fixture".to_owned(),
            population: "section".to_owned(),
            body: "test".to_owned(),
        }
    }

    fn region(r0: usize, r1: usize, c0: usize, c1: usize) -> SectionRegion {
        SectionRegion::new(r0, r1, c0, c1).expect("well-formed")
    }

    fn map_population() -> BTreeMap<String, SectionShape> {
        let mut populations = BTreeMap::new();
        populations.insert("map".to_owned(), SectionShape::of(8, 8, 12));
        populations
    }

    fn resources() -> ResourceDeclaration {
        ResourceDeclaration {
            species: vec![
                DeclaredSpecies {
                    name: "resident-lanes".to_owned(),
                    unit: 1,
                    face: DemandFace::Written,
                    capacity: BigUint::from(8u32),
                    characteristic_delay: 1,
                    sink_capacity: BigUint::from(1u32),
                },
                DeclaredSpecies {
                    name: "map-traffic".to_owned(),
                    unit: 4,
                    face: DemandFace::Read,
                    capacity: BigUint::from(2u32),
                    characteristic_delay: 2,
                    sink_capacity: BigUint::from(1u32),
                },
            ],
            enactment_aperture: 1024,
        }
    }

    /// Two cells whose writes cover the section in halves, each reading the whole map.
    fn two_cells(reads_map: bool) -> Vec<SectionCell> {
        let reads = |region: SectionRegion| {
            if reads_map {
                vec![ReadRegion {
                    population: "map".to_owned(),
                    region,
                }]
            } else {
                Vec::new()
            }
        };
        vec![
            SectionCell {
                index: 0,
                write: region(0, 2, 0, 8),
                reads: reads(region(0, 4, 0, 8)),
                partial_of: None,
            },
            SectionCell {
                index: 1,
                write: region(2, 4, 0, 8),
                reads: reads(region(4, 8, 0, 8)),
                partial_of: None,
            },
        ]
    }

    fn partition(cells: Vec<SectionCell>) -> SectionPartition {
        SectionPartition {
            lineage: lineage(),
            shape: shape(),
            populations: map_population(),
            cells,
        }
    }

    // ---------------------------------------------------------------------------------------
    // CONTROL 1 — disjoint outputs certify
    // ---------------------------------------------------------------------------------------

    #[test]
    fn control_one_disjoint_outputs_certify() {
        let cover = HardwareCover::cpu_only();
        let receipt = partition(two_cells(true))
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect("a partition of disjoint writes certifies");
        assert!(receipt.is_partition());
        assert!(receipt.is_interchangeable());
        assert!(receipt.completeness.uncovered.is_empty());
        assert_eq!(receipt.disjointness.overlaps.len(), 0);
    }

    /// **Perturbation: cell zero reads a region cell one writes** — the read moves from the `map`
    /// population into the section itself. The write/read hazard is a shared address and the
    /// front stays ordered.
    #[test]
    fn control_one_perturbed_a_read_of_another_cells_write_refuses() {
        let cover = HardwareCover::cpu_only();
        let mut cells = two_cells(true);
        let mut populations = map_population();
        populations.insert("section".to_owned(), shape());
        cells[0].reads.push(ReadRegion {
            population: "section".to_owned(),
            region: region(2, 4, 0, 8),
        });
        let perturbed = SectionPartition {
            lineage: lineage(),
            shape: shape(),
            populations,
            cells,
        };
        let defects = perturbed
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect_err("a read of another cell's write is not independent");
        assert!(
            defects
                .iter()
                .any(|defect| matches!(defect, PartitionDefect::FootprintRefused { .. }))
        );
    }

    // ---------------------------------------------------------------------------------------
    // CONTROL 2 — shared immutable input certifies
    // ---------------------------------------------------------------------------------------

    #[test]
    fn control_two_shared_immutable_input_certifies() {
        let cover = HardwareCover::cpu_only();
        let mut cells = two_cells(true);
        // Both cells read the SAME map rows — one shared immutable standing.
        cells[0].reads = vec![ReadRegion {
            population: "map".to_owned(),
            region: region(0, 8, 0, 8),
        }];
        cells[1].reads = vec![ReadRegion {
            population: "map".to_owned(),
            region: region(0, 8, 0, 8),
        }];
        let receipt = partition(cells)
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect("a shared immutable read certifies");
        assert!(receipt.is_interchangeable());
        assert_eq!(receipt.shared_reads.len(), 1);
        assert!(receipt.shared_reads[0].immutable);
        assert_eq!(receipt.shared_reads[0].region, region(0, 8, 0, 8));
        assert_eq!(receipt.halo.len(), 2);
    }

    /// **Perturbation: the shared standing stops being immutable** — the shared region is declared
    /// in the section's own population, which the cells write. The reading refuses and names the
    /// region.
    #[test]
    fn control_two_perturbed_a_shared_read_that_is_written_refuses() {
        let cover = HardwareCover::cpu_only();
        let mut populations = map_population();
        populations.insert("section".to_owned(), shape());
        let mut cells = two_cells(false);
        cells[0].reads = vec![ReadRegion {
            population: "section".to_owned(),
            region: region(0, 4, 0, 8),
        }];
        cells[1].reads = vec![ReadRegion {
            population: "section".to_owned(),
            region: region(0, 4, 0, 8),
        }];
        let perturbed = SectionPartition {
            lineage: lineage(),
            shape: shape(),
            populations,
            cells,
        };
        let defects = perturbed
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect_err("a shared read in a written population is not an immutable standing");
        let named = defects.iter().find_map(|defect| match defect {
            PartitionDefect::SharedReadIsWritten { region, .. } => Some(*region),
            _ => None,
        });
        assert_eq!(named, Some(region(0, 4, 0, 8)));
    }

    // ---------------------------------------------------------------------------------------
    // CONTROL 3 — a shared output refuses without a junction and certifies with one
    // ---------------------------------------------------------------------------------------

    #[test]
    fn control_three_a_shared_output_refuses_without_a_junction() {
        let cover = HardwareCover::cpu_only();
        let cells = vec![
            SectionCell {
                index: 0,
                write: shape().whole(),
                reads: Vec::new(),
                partial_of: None,
            },
            SectionCell {
                index: 1,
                write: shape().whole(),
                reads: Vec::new(),
                partial_of: None,
            },
        ];
        let defects = partition(cells)
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect_err("two cells writing one output are not independent");
        let named = defects.iter().find_map(|defect| match defect {
            PartitionDefect::RegionsOverlap { region, .. } => Some(*region),
            _ => None,
        });
        assert_eq!(named, Some(shape().whole()));
        assert!(defects.iter().any(|defect| matches!(
            defect,
            PartitionDefect::FootprintRefused {
                region: Some(_),
                ..
            }
        )));
    }

    #[test]
    fn control_three_the_same_shared_output_certifies_with_a_junction() {
        let cover = HardwareCover::cpu_only();
        let junction = JunctionOutput {
            owner: "reduction".to_owned(),
            output: shape().whole(),
            partials: 2,
        };
        let cells = vec![
            SectionCell {
                index: 0,
                write: shape().whole(),
                reads: Vec::new(),
                partial_of: Some(PartialAddress {
                    junction: 0,
                    partial: 0,
                }),
            },
            SectionCell {
                index: 1,
                write: shape().whole(),
                reads: Vec::new(),
                partial_of: Some(PartialAddress {
                    junction: 0,
                    partial: 1,
                }),
            },
        ];
        let receipt = partition(cells)
            .certify(
                &cover,
                std::slice::from_ref(&junction),
                &resources(),
                "section_partition_control",
            )
            .expect("the junction owns the output and the partials are independent");
        assert!(receipt.is_partition());
        assert!(receipt.is_interchangeable());
        assert_eq!(receipt.junctions.len(), 1);
    }

    // ---------------------------------------------------------------------------------------
    // CONTROL 4 — incomplete, overlapping and foreign tiles each refuse by name
    // ---------------------------------------------------------------------------------------

    #[test]
    fn control_four_an_exact_partition_certifies() {
        let cover = HardwareCover::cpu_only();
        let cells = vec![
            SectionCell {
                index: 0,
                write: region(0, 4, 0, 4),
                reads: Vec::new(),
                partial_of: None,
            },
            SectionCell {
                index: 1,
                write: region(0, 4, 4, 8),
                reads: Vec::new(),
                partial_of: None,
            },
        ];
        let receipt = partition(cells)
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect("an exact partition certifies");
        assert!(receipt.is_partition());
        assert_eq!(
            receipt.completeness.covered_extent,
            receipt.completeness.section_extent
        );
    }

    /// **Perturbation A: a region is missing.** The hole is returned by name.
    #[test]
    fn control_four_perturbed_incomplete_names_the_missing_region() {
        let cover = HardwareCover::cpu_only();
        let cells = vec![SectionCell {
            index: 0,
            write: region(0, 4, 0, 4),
            reads: Vec::new(),
            partial_of: None,
        }];
        let defects = partition(cells)
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect_err("half a section is not a partition of it");
        let named = defects.iter().find_map(|defect| match defect {
            PartitionDefect::RegionUncovered { region } => Some(*region),
            _ => None,
        });
        assert_eq!(named, Some(region(0, 4, 4, 8)));
    }

    /// **Perturbation B: two regions overlap.** The meet is returned.
    #[test]
    fn control_four_perturbed_overlapping_names_the_meet() {
        let cover = HardwareCover::cpu_only();
        let cells = vec![
            SectionCell {
                index: 0,
                write: region(0, 4, 0, 5),
                reads: Vec::new(),
                partial_of: None,
            },
            SectionCell {
                index: 1,
                write: region(0, 4, 4, 8),
                reads: Vec::new(),
                partial_of: None,
            },
        ];
        let defects = partition(cells)
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect_err("overlapping writes are not a partition");
        let named = defects.iter().find_map(|defect| match defect {
            PartitionDefect::RegionsOverlap { region, .. } => Some(*region),
            _ => None,
        });
        assert_eq!(named, Some(region(0, 4, 4, 5)));
    }

    /// **Perturbation C: a foreign tile, outside the section.**
    #[test]
    fn control_four_perturbed_a_foreign_tile_refuses() {
        let cover = HardwareCover::cpu_only();
        let cells = vec![
            SectionCell {
                index: 0,
                write: region(0, 4, 0, 8),
                reads: Vec::new(),
                partial_of: None,
            },
            SectionCell {
                index: 1,
                write: region(4, 6, 0, 8),
                reads: Vec::new(),
                partial_of: None,
            },
        ];
        let defects = partition(cells)
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect_err("a tile outside the section is foreign");
        assert!(defects.iter().any(|defect| matches!(
            defect,
            PartitionDefect::RegionOutsideSection { cell: 1, .. }
        )));
    }

    // ---------------------------------------------------------------------------------------
    // CONTROL 7 — pressure stays a local product, per cell and per species
    // ---------------------------------------------------------------------------------------

    #[test]
    fn control_seven_pressure_is_one_covector_per_species_and_nothing_combines_them() {
        let cover = HardwareCover::cpu_only();
        let receipt = partition(two_cells(true))
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect("certifies");
        assert_eq!(receipt.pressure.len(), 2);
        for cell in &receipt.pressure {
            let names: Vec<&str> = cell.coordinates().iter().map(|(name, _)| *name).collect();
            // Exactly the declared species, in the declared order, and nothing else. No `total`,
            // no `combined`, no scalar.
            assert_eq!(names, vec!["resident-lanes", "map-traffic"]);
            let lanes = cell.species_named("resident-lanes").expect("declared");
            // `receiver_current` conducted it, and its own service rounds are what is carried.
            assert!(matches!(lanes.enacted, EnactedCurrent::Radiated { .. }));
            assert_eq!(lanes.incoming, BigUint::from(16u32));
            assert_eq!(lanes.service_rounds, BigUint::from(2u32));
        }
    }

    /// **Perturbation: the units are moved so the two declarations have the SAME cross-species sum
    /// and a different per-species split** — `(16, 8)` against `(8, 16)`, both summing to `24`.
    ///
    /// Anything in the receipt that combined the species would identify these two declarations.
    /// The returned coordinates differ, so nothing in it combines them. This is the falsifier for
    /// a hidden scalar, and it fails the moment a combined coordinate is added.
    #[test]
    fn control_seven_perturbed_equal_sums_with_a_different_split_are_not_identified() {
        let cover = HardwareCover::cpu_only();
        let declared = resources();
        let moved = ResourceDeclaration {
            species: vec![
                DeclaredSpecies {
                    unit: 2,
                    ..declared.species[0].clone()
                },
                DeclaredSpecies {
                    unit: 2,
                    ..declared.species[1].clone()
                },
            ],
            enactment_aperture: declared.enactment_aperture,
        };
        let material = partition(two_cells(true));
        let left = material
            .certify(&cover, &[], &declared, "section_partition_control")
            .expect("certifies");
        let right = material
            .certify(&cover, &[], &moved, "section_partition_control")
            .expect("certifies");
        let sum = |receipt: &TilingReceipt| -> BigUint {
            receipt
                .pressure
                .iter()
                .flat_map(|cell| cell.species.iter())
                .map(|species| species.incoming.clone())
                .sum()
        };
        // The cross-species sums agree exactly — the quantity a combining receipt would return.
        assert_eq!(sum(&left), sum(&right));
        // And the receipts do not, because no coordinate in them is that sum.
        assert_ne!(left.pressure, right.pressure);
        let left_split: Vec<BigUint> = left.pressure[0]
            .species
            .iter()
            .map(|species| species.incoming.clone())
            .collect();
        let right_split: Vec<BigUint> = right.pressure[0]
            .species
            .iter()
            .map(|species| species.incoming.clone())
            .collect();
        assert_eq!(left_split, vec![BigUint::from(16u32), BigUint::from(8u32)]);
        assert_eq!(right_split, vec![BigUint::from(8u32), BigUint::from(16u32)]);
    }

    /// **The absence of a combined coordinate, read off the type's own field names.**
    ///
    /// The split comparison above shows the species are not collapsed into one; it does NOT show
    /// that no combined coordinate stands beside them, because a receipt carrying an extra `total`
    /// would pass it too. This reads the rendered receipt for any cross-species name and fails the
    /// moment one is added.
    #[test]
    fn control_seven_the_receipt_names_no_combined_coordinate() {
        let cover = HardwareCover::cpu_only();
        let receipt = partition(two_cells(true))
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect("certifies");
        let rendered = format!("{:?}", receipt.pressure[0]);
        for forbidden in [
            "total",
            "sum",
            "combined",
            "utilization",
            "utilisation",
            "overall",
            "aggregate",
            "score",
            "pressure:",
        ] {
            assert!(
                !rendered.to_lowercase().contains(forbidden),
                "the pressure receipt names a combined coordinate `{forbidden}`: {rendered}"
            );
        }
        // And the only plural it carries is the declared species population itself.
        assert_eq!(
            receipt.pressure[0].coordinates().len(),
            resources().species.len()
        );
    }

    /// A genuine zero demand is a zero, not an unknown.
    #[test]
    fn a_zero_demand_is_a_named_zero_and_never_the_unknown_variant() {
        let cover = HardwareCover::cpu_only();
        // `two_cells(false)` declares no reads, so the READ face is a true zero.
        let receipt = partition(two_cells(false))
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect("certifies");
        let traffic = receipt.pressure[0]
            .species_named("map-traffic")
            .expect("declared");
        assert!(traffic.incoming.is_zero());
        assert!(matches!(
            traffic.enacted,
            EnactedCurrent::NoDemand {
                face: DemandFace::Read
            }
        ));
    }

    /// A degenerate cell and an empty section are both refused at the certifier, not only in the
    /// region constructor whose fields are public.
    #[test]
    fn a_degenerate_region_and_an_empty_section_are_refused_at_the_certifier() {
        let cover = HardwareCover::cpu_only();
        let degenerate = SectionRegion {
            row_from: 2,
            row_to: 2,
            column_from: 0,
            column_to: 8,
        };
        let mut cells = two_cells(false);
        cells.push(SectionCell {
            index: 2,
            write: degenerate,
            reads: Vec::new(),
            partial_of: None,
        });
        let defects = partition(cells)
            .certify(&cover, &[], &resources(), "section_partition_control")
            .expect_err("a zero-extent cell is refused");
        assert!(
            defects
                .iter()
                .any(|defect| matches!(defect, PartitionDefect::EmptyRegion { .. }))
        );

        let empty = SectionPartition {
            lineage: lineage(),
            shape: SectionShape::of(0, 8, 12),
            populations: BTreeMap::new(),
            cells: Vec::new(),
        }
        .certify(&cover, &[], &resources(), "section_partition_control")
        .expect_err("a partition of nothing is not a partition");
        assert!(
            empty
                .iter()
                .any(|defect| matches!(defect, PartitionDefect::EmptySection { .. }))
        );
    }

    /// A junction covers by computation, never by declaration.
    #[test]
    fn a_junction_owes_the_coverage_of_its_own_output() {
        let cover = HardwareCover::cpu_only();
        let junction = JunctionOutput {
            owner: "reduction".to_owned(),
            output: shape().whole(),
            partials: 2,
        };
        // Both partials write one corner of an output that covers the section.
        let corner = region(0, 1, 0, 1);
        let cells = vec![
            SectionCell {
                index: 0,
                write: corner,
                reads: Vec::new(),
                partial_of: Some(PartialAddress {
                    junction: 0,
                    partial: 0,
                }),
            },
            SectionCell {
                index: 1,
                write: corner,
                reads: Vec::new(),
                partial_of: Some(PartialAddress {
                    junction: 0,
                    partial: 1,
                }),
            },
        ];
        let defects = partition(cells)
            .certify(
                &cover,
                std::slice::from_ref(&junction),
                &resources(),
                "section_partition_control",
            )
            .expect_err("the partials do not cover the output");
        assert!(
            defects
                .iter()
                .any(|defect| matches!(defect, PartitionDefect::JunctionOutputUncovered { .. }))
        );

        // And a junction output outside the section refuses the way a foreign cell does.
        let foreign = JunctionOutput {
            owner: "foreign".to_owned(),
            output: SectionRegion::new(0, 4, 0, 16).expect("a region"),
            partials: 1,
        };
        let defects = partition(vec![SectionCell {
            index: 0,
            write: region(0, 4, 0, 4),
            reads: Vec::new(),
            partial_of: Some(PartialAddress {
                junction: 0,
                partial: 0,
            }),
        }])
        .certify(
            &cover,
            std::slice::from_ref(&foreign),
            &resources(),
            "section_partition_control",
        )
        .expect_err("a foreign junction output refuses");
        assert!(
            defects.iter().any(|defect| matches!(
                defect,
                PartitionDefect::JunctionOutputOutsideSection { .. }
            ))
        );
    }

    // ---------------------------------------------------------------------------------------
    // the sweep itself
    // ---------------------------------------------------------------------------------------

    #[test]
    fn the_uncovered_sweep_returns_one_region_for_one_missing_tile() {
        let shape = SectionShape::of(4, 4, 0);
        let covering = vec![region(0, 2, 0, 4), region(2, 4, 0, 2)];
        let uncovered = uncovered_regions(&shape, &covering);
        assert_eq!(uncovered, vec![region(2, 4, 2, 4)]);
    }

    #[test]
    fn a_region_addresses_one_range_when_it_spans_the_stride_and_one_per_row_otherwise() {
        assert_eq!(region(1, 3, 0, 8).address_ranges(8, 0), vec![(8, 24)]);
        assert_eq!(
            region(1, 3, 2, 5).address_ranges(8, 100),
            vec![(110, 113), (118, 121)]
        );
    }
}
