//! The complete contextual predecessor fiber of one presented token occurrence.
//!
//! **Record:**
//! `research/records/2026-08-12_THE_RECONSTRUCTION_REMAINS_A_FIBER_THE_CONTEXT_RETURNS_BY_DIFFUSION_AND_THE_CIRCUIT_GROWS_IN_HIGHER_CELLS.md`.
//!
//! This is the first bounded textual instance of that record's carrier-neutral definition. A caller
//! supplies a situated focus, a complete finite candidate surface population, a receiver family,
//! and a causal horizon. Every actual candidate occurrence is presented with the same immediate
//! exposed face; left/right conduct then reaches its actual corpus context. The stable quotient from
//! `receiver_exact_compression` returns the focus fiber. Nothing chooses a surface.
//!
//! Local edit paths are a second face. They are returned as a compact DAG containing every minimal
//! route under the declared Unicode-scalar operation family, but their grade never admits, ranks, or
//! removes a candidate. Whitespace is not in `CorpusCensus`'s stream, so split/merge remains an
//! explicit open delivery boundary rather than an invented edit.
//!
//! An optional exact diffusion passage is enacted beside the fiber. It cannot enter the observed
//! system and therefore cannot change candidate identity or the quotient.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::corpus_census::{CorpusCensus, SurfaceId};
use holonic_engine::diffusion::{
    DiffusionError, DiffusionEvent, DiffusionReceipt, DiffusionStanding, ExactDiffusionLaw,
};
use holonic_engine::receiver_exact_compression::{
    compress, CollapsedPair, InputId, ItemId, Observation, ObservedSystem, Partition,
    ReceiverExactCompression, ReceiverId,
};
use holonic_engine::token_invariance::{reading, ConductAtlas, ReceiverAxis, ReceiverFamily, Step};
use num_bigint::BigUint;

mod edit;

pub use edit::{edit_complex, EditComplex, EditEdge, EditNode, EditOperation};

/// One situated token occurrence. Surface identity is checked against the named stream position.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OccurrenceAddress {
    pub whole: u32,
    pub position: u32,
    pub surface: SurfaceId,
}

/// The candidate carrier is always explicit. `EveryStandingSurface` still means every surface in
/// this census, not an assertion that the exterior has been exhausted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CandidatePopulation {
    Declared(BTreeSet<SurfaceId>),
    EveryStandingSurface,
}

/// The semantic declaration. Work capacity is separate because it may refuse presentation of the
/// complete object but may never change this population.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReconstructionDeclaration {
    pub candidates: CandidatePopulation,
    pub family: ReceiverFamily,
    pub horizon: usize,
}

/// Work demanded before the event starts. The pair chart is the complete `C(items, 2)` cover; the
/// compression may inspect fewer pairs, but can never inspect more.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReconstructionWorkDemand {
    pub candidates: usize,
    pub roots: usize,
    pub system_items: usize,
    pub pair_chart: BigUint,
    pub edit_cells: BigUint,
}

/// A caller's physical cover. Exceeding it refuses the whole event; no prefix is returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReconstructionWorkCover {
    pub system_items: usize,
    pub pair_chart: BigUint,
    pub edit_cells: BigUint,
}

impl ReconstructionWorkCover {
    /// A cover with no authored slack: exactly the demand the material returned.
    pub fn exactly(demand: &ReconstructionWorkDemand) -> Self {
        Self {
            system_items: demand.system_items,
            pair_chart: demand.pair_chart.clone(),
            edit_cells: demand.edit_cells.clone(),
        }
    }

    fn holds(&self, demand: &ReconstructionWorkDemand) -> bool {
        demand.system_items <= self.system_items
            && demand.pair_chart <= self.pair_chart
            && demand.edit_cells <= self.edit_cells
    }
}

/// The contextual preimage population returned by one completed pass.
#[derive(Debug, PartialEq, Eq)]
pub struct ReconstructionFiber {
    pub schema: String,
    pub focus: OccurrenceAddress,
    pub family: ReceiverFamily,
    pub horizon: usize,
    pub admitted_candidates: BTreeSet<SurfaceId>,
    pub roots: Vec<OccurrenceAddress>,
    pub focus_root: usize,
    pub root_one_shot_blocks: Vec<BTreeSet<usize>>,
    pub root_conduct_blocks: Vec<BTreeSet<usize>>,
    pub focus_candidates: BTreeSet<SurfaceId>,
    pub focus_support: Vec<OccurrenceAddress>,
    pub focus_collapsed: Vec<CollapsedPair>,
    pub edits: BTreeMap<SurfaceId, EditComplex>,
    pub outside_declared_population_open: bool,
    pub outside_corpus_open: bool,
    pub delivery_boundary_open: bool,
    pub compression: ReceiverExactCompression,
    pub work: ReconstructionWorkDemand,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReconstructionDiffusionReturn {
    pub standing_after: DiffusionStanding,
    pub receipt: DiffusionReceipt,
}

/// One returned passage. Diffusion is carried beside the fiber and has no route into it.
#[derive(Debug, PartialEq, Eq)]
pub struct ReconstructionPassage {
    pub fiber: ReconstructionFiber,
    pub diffusion: Option<ReconstructionDiffusionReturn>,
}

/// A caller-declared exact physical passage. Edit edges never supply these conductances.
pub struct DeclaredDiffusionPassage<'a> {
    pub law: &'a ExactDiffusionLaw,
    pub standing: &'a DiffusionStanding,
    pub event: &'a DiffusionEvent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReconstructionPassageId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReconstructionReflectionReceipt {
    pub predecessor: ReconstructionPassageId,
    pub successor: ReconstructionPassageId,
    pub retained: BTreeSet<SurfaceId>,
    pub departed: BTreeSet<SurfaceId>,
    pub separating_witnesses: Vec<CollapsedPair>,
    pub predecessor_family: ReceiverFamily,
    pub successor_family: ReceiverFamily,
    pub predecessor_horizon: usize,
    pub successor_horizon: usize,
}

/// A lineage holder for completed passages. It is intentionally not `Clone`: rereading deposits a
/// later passage over the prior one rather than copying a world and revising the copy.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct ReconstructionBody {
    passages: Vec<ReconstructionPassage>,
}

impl ReconstructionBody {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn found(
        &mut self,
        passage: ReconstructionPassage,
    ) -> Result<ReconstructionPassageId, ReconstructionError> {
        let id = u64::try_from(self.passages.len())
            .map(ReconstructionPassageId)
            .map_err(|_| ReconstructionError::PassageExtent)?;
        self.passages.push(passage);
        Ok(id)
    }

    pub fn passage(&self, id: ReconstructionPassageId) -> Option<&ReconstructionPassage> {
        usize::try_from(id.0)
            .ok()
            .and_then(|index| self.passages.get(index))
    }

    /// Deposit a richer rereading of the same fixed standing. The later family/aperture must only
    /// refine; an arriving candidate is a typed disagreement rather than a silently accepted pass.
    pub fn reflect(
        &mut self,
        predecessor: ReconstructionPassageId,
        successor: ReconstructionPassage,
    ) -> Result<ReconstructionReflectionReceipt, ReconstructionError> {
        let prior = self
            .passage(predecessor)
            .ok_or(ReconstructionError::UnknownPassage(predecessor))?;
        let before = &prior.fiber;
        let after = &successor.fiber;
        if before.focus != after.focus
            || before.admitted_candidates != after.admitted_candidates
            || !before.family.is_subset_of(after.family)
            || before.horizon > after.horizon
        {
            return Err(ReconstructionError::IncomparableReflection);
        }
        if !after.focus_candidates.is_subset(&before.focus_candidates) {
            return Err(ReconstructionError::ReflectionDidNotRefine);
        }
        let retained = after.focus_candidates.clone();
        let departed = before
            .focus_candidates
            .difference(&after.focus_candidates)
            .copied()
            .collect::<BTreeSet<_>>();
        let separating_witnesses = after
            .focus_collapsed
            .iter()
            .filter(|witness| {
                other_root_surface(after, witness)
                    .is_some_and(|surface| departed.contains(&surface))
            })
            .cloned()
            .collect();
        let successor_id = u64::try_from(self.passages.len())
            .map(ReconstructionPassageId)
            .map_err(|_| ReconstructionError::PassageExtent)?;
        let receipt = ReconstructionReflectionReceipt {
            predecessor,
            successor: successor_id,
            retained,
            departed,
            separating_witnesses,
            predecessor_family: before.family,
            successor_family: after.family,
            predecessor_horizon: before.horizon,
            successor_horizon: after.horizon,
        };
        self.passages.push(successor);
        Ok(receipt)
    }
}

#[derive(Debug)]
pub enum ReconstructionError {
    EmptyReceiverFamily,
    UnknownSurface(SurfaceId),
    UnknownWhole(u32),
    UnknownPosition {
        whole: u32,
        position: u32,
    },
    FocusSurfaceDisagrees {
        declared: SurfaceId,
        standing: SurfaceId,
    },
    WorkCoverInsufficient {
        demand: ReconstructionWorkDemand,
        cover: ReconstructionWorkCover,
    },
    Diffusion(DiffusionError),
    UnknownPassage(ReconstructionPassageId),
    IncomparableReflection,
    ReflectionDidNotRefine,
    PassageExtent,
    HorizonExtent,
    WorkExtent,
}

impl std::fmt::Display for ReconstructionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyReceiverFamily => write!(formatter, "the reconstruction receiver family is empty"),
            Self::UnknownSurface(surface) => write!(formatter, "unknown surface {}", surface.0),
            Self::UnknownWhole(whole) => write!(formatter, "unknown whole {whole}"),
            Self::UnknownPosition { whole, position } => {
                write!(formatter, "unknown position {position} in whole {whole}")
            }
            Self::FocusSurfaceDisagrees { declared, standing } => write!(
                formatter,
                "focus declared surface {} but the occurrence carries {}",
                declared.0, standing.0
            ),
            Self::WorkCoverInsufficient { demand, cover } => write!(
                formatter,
                "reconstruction requires {} items, pair chart {}, edit cells {}; cover holds {} / {} / {}",
                demand.system_items,
                demand.pair_chart,
                demand.edit_cells,
                cover.system_items,
                cover.pair_chart,
                cover.edit_cells
            ),
            Self::Diffusion(error) => write!(formatter, "declared diffusion passage refused: {error}"),
            Self::UnknownPassage(id) => write!(formatter, "unknown reconstruction passage {}", id.0),
            Self::IncomparableReflection => write!(formatter, "the later passage is not a richer reading of the same standing"),
            Self::ReflectionDidNotRefine => write!(formatter, "the later reconstruction fiber introduced a candidate"),
            Self::PassageExtent => write!(formatter, "reconstruction passage identity exceeded its carrier"),
            Self::HorizonExtent => write!(formatter, "the declared reconstruction horizon cannot be represented by the item carrier"),
            Self::WorkExtent => write!(formatter, "the complete reconstruction work demand exceeded its exact counter carrier"),
        }
    }
}

impl std::error::Error for ReconstructionError {}

impl From<DiffusionError> for ReconstructionError {
    fn from(error: DiffusionError) -> Self {
        Self::Diffusion(error)
    }
}

struct Prepared {
    candidates: BTreeSet<SurfaceId>,
    roots: Vec<OccurrenceAddress>,
    focus_root: usize,
    demand: ReconstructionWorkDemand,
    outside_declared_population_open: bool,
}

/// Compute the complete demand without running compression or edit reconstruction.
pub fn reconstruction_demand(
    census: &CorpusCensus,
    focus: OccurrenceAddress,
    declaration: &ReconstructionDeclaration,
) -> Result<ReconstructionWorkDemand, ReconstructionError> {
    Ok(prepare(census, focus, declaration)?.demand)
}

/// Return the complete declared fiber or refuse before execution. No capacity participates in the
/// quotient; it only decides whether the caller can hold the whole requested chart.
pub fn reconstruct(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
    focus: OccurrenceAddress,
    declaration: &ReconstructionDeclaration,
    cover: &ReconstructionWorkCover,
    diffusion: Option<DeclaredDiffusionPassage<'_>>,
) -> Result<ReconstructionPassage, ReconstructionError> {
    let prepared = prepare(census, focus, declaration)?;
    if !cover.holds(&prepared.demand) {
        return Err(ReconstructionError::WorkCoverInsufficient {
            demand: prepared.demand,
            cover: cover.clone(),
        });
    }

    let system = ReconstructionSystem::new(
        census,
        atlas,
        prepared.roots.clone(),
        declaration.horizon,
        declaration.family,
    );
    let compression = compress(&system);
    let root_one_shot_blocks = root_partition(&system, &compression.one_shot);
    let root_conduct_blocks = root_partition(&system, &compression.conduct);
    let focus_item = system.root_item(prepared.focus_root);
    let focus_block = compression
        .conduct
        .block_of(focus_item)
        .expect("a presented focus root belongs to the compression");
    let focus_root_indices = compression.conduct.blocks[focus_block]
        .iter()
        .filter_map(|item| system.root_index(*item))
        .collect::<BTreeSet<_>>();
    let focus_support = focus_root_indices
        .iter()
        .map(|root| prepared.roots[*root])
        .collect::<Vec<_>>();
    let focus_candidates = focus_support
        .iter()
        .map(|site| site.surface)
        .collect::<BTreeSet<_>>();
    let focus_collapsed = compression
        .collapsed
        .iter()
        .filter(|pair| {
            (pair.left == focus_item && system.root_index(pair.right).is_some())
                || (pair.right == focus_item && system.root_index(pair.left).is_some())
        })
        .cloned()
        .collect();

    let observed = census.surface(focus.surface).to_owned();
    let edits = prepared
        .candidates
        .iter()
        .map(|candidate| {
            (
                *candidate,
                edit_complex(census.surface(*candidate), &observed),
            )
        })
        .collect();

    let fiber = ReconstructionFiber {
        schema: "life.reconstruction-fiber.v1".to_owned(),
        focus,
        family: declaration.family,
        horizon: declaration.horizon,
        admitted_candidates: prepared.candidates,
        roots: prepared.roots,
        focus_root: prepared.focus_root,
        root_one_shot_blocks,
        root_conduct_blocks,
        focus_candidates,
        focus_support,
        focus_collapsed,
        edits,
        outside_declared_population_open: prepared.outside_declared_population_open,
        outside_corpus_open: true,
        delivery_boundary_open: true,
        compression,
        work: prepared.demand,
    };

    let diffusion = diffusion
        .map(|passage| {
            passage
                .law
                .enact(passage.standing, passage.event)
                .map(|(standing_after, receipt)| ReconstructionDiffusionReturn {
                    standing_after,
                    receipt,
                })
        })
        .transpose()?;

    Ok(ReconstructionPassage { fiber, diffusion })
}

fn prepare(
    census: &CorpusCensus,
    focus: OccurrenceAddress,
    declaration: &ReconstructionDeclaration,
) -> Result<Prepared, ReconstructionError> {
    if declaration.family.is_empty() {
        return Err(ReconstructionError::EmptyReceiverFamily);
    }
    let stride = declaration
        .horizon
        .checked_mul(2)
        .and_then(|extent| extent.checked_add(1))
        .ok_or(ReconstructionError::HorizonExtent)?;
    let stride_u64 = u64::try_from(stride).map_err(|_| ReconstructionError::HorizonExtent)?;
    let whole = census
        .wholes()
        .get(focus.whole as usize)
        .ok_or(ReconstructionError::UnknownWhole(focus.whole))?;
    let standing =
        *whole
            .stream
            .get(focus.position as usize)
            .ok_or(ReconstructionError::UnknownPosition {
                whole: focus.whole,
                position: focus.position,
            })?;
    if standing != focus.surface {
        return Err(ReconstructionError::FocusSurfaceDisagrees {
            declared: focus.surface,
            standing,
        });
    }
    let population = census.all_surfaces().count();
    let mut candidates = match &declaration.candidates {
        CandidatePopulation::Declared(candidates) => candidates.clone(),
        CandidatePopulation::EveryStandingSurface => census.all_surfaces().collect(),
    };
    candidates.insert(focus.surface);
    if let Some(surface) = candidates
        .iter()
        .find(|surface| surface.0 as usize >= population)
    {
        return Err(ReconstructionError::UnknownSurface(*surface));
    }

    let mut roots = Vec::new();
    for (whole_index, record) in census.wholes().iter().enumerate() {
        for (position, surface) in record.stream.iter().enumerate() {
            if candidates.contains(surface) {
                roots.push(OccurrenceAddress {
                    whole: whole_index as u32,
                    position: position as u32,
                    surface: *surface,
                });
            }
        }
    }
    let focus_root = roots
        .iter()
        .position(|root| *root == focus)
        .expect("the validated focus is among its surface's roots");
    let root_extent = u64::try_from(roots.len()).map_err(|_| ReconstructionError::WorkExtent)?;
    root_extent
        .checked_mul(stride_u64)
        .ok_or(ReconstructionError::WorkExtent)?;
    let system_items = roots.iter().try_fold(0usize, |total, root| {
        let extent = census.wholes()[root.whole as usize].stream.len();
        let position = root.position as usize;
        let local = 1
            + declaration.horizon.min(position)
            + declaration.horizon.min(extent.saturating_sub(position + 1));
        total
            .checked_add(local)
            .ok_or(ReconstructionError::WorkExtent)
    })?;
    let pair_chart = choose_two(BigUint::from(system_items));
    let observed_scalars = census.surface(focus.surface).chars().count() + 1;
    let edit_cells = candidates
        .iter()
        .map(|candidate| {
            BigUint::from(census.surface(*candidate).chars().count() + 1)
                * BigUint::from(observed_scalars)
        })
        .sum();
    let demand = ReconstructionWorkDemand {
        candidates: candidates.len(),
        roots: roots.len(),
        system_items,
        pair_chart,
        edit_cells,
    };
    Ok(Prepared {
        candidates,
        roots,
        focus_root,
        demand,
        outside_declared_population_open: matches!(
            declaration.candidates,
            CandidatePopulation::Declared(_)
        ),
    })
}

fn choose_two(population: BigUint) -> BigUint {
    if population < BigUint::from(2u8) {
        BigUint::from(0u8)
    } else {
        let prior = &population - BigUint::from(1u8);
        population * prior / BigUint::from(2u8)
    }
}

/// The candidate-root system. Offset zero is the common exposed presentation being reconstructed;
/// nonzero offsets are the actual contextual surfaces reached by conduct.
struct ReconstructionSystem<'a> {
    census: &'a CorpusCensus,
    atlas: &'a ConductAtlas,
    roots: Vec<OccurrenceAddress>,
    horizon: usize,
    axes: Vec<ReceiverAxis>,
}

impl<'a> ReconstructionSystem<'a> {
    fn new(
        census: &'a CorpusCensus,
        atlas: &'a ConductAtlas,
        roots: Vec<OccurrenceAddress>,
        horizon: usize,
        family: ReceiverFamily,
    ) -> Self {
        Self {
            census,
            atlas,
            roots,
            horizon,
            axes: family.axes(),
        }
    }

    fn stride(&self) -> u64 {
        (2 * self.horizon + 1) as u64
    }

    fn root_item(&self, root: usize) -> ItemId {
        ItemId(root as u64 * self.stride() + self.horizon as u64)
    }

    fn root_index(&self, item: ItemId) -> Option<usize> {
        let stride = self.stride();
        ((item.0 % stride) == self.horizon as u64)
            .then_some((item.0 / stride) as usize)
            .filter(|root| *root < self.roots.len())
    }

    fn site(&self, item: ItemId) -> Option<(u32, u32)> {
        let root = (item.0 / self.stride()) as usize;
        let slot = (item.0 % self.stride()) as i64;
        let offset = slot - self.horizon as i64;
        let address = *self.roots.get(root)?;
        let position = address.position as i64 + offset;
        let stream = &self.census.wholes()[address.whole as usize].stream;
        (position >= 0 && position < stream.len() as i64)
            .then_some((address.whole, position as u32))
    }
}

impl ObservedSystem for ReconstructionSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        (0..self.roots.len())
            .flat_map(|root| {
                (0..self.stride()).filter_map(move |slot| {
                    let item = ItemId(root as u64 * self.stride() + slot);
                    self.site(item).map(|_| item)
                })
            })
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        self.axes.iter().map(|axis| axis.id()).collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        vec![Step::Left.input(), Step::Right.input()]
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        if self.root_index(item).is_some() {
            return Observation(0);
        }
        let Some((whole, position)) = self.site(item) else {
            return Observation(u64::MAX);
        };
        let surface = self.census.wholes()[whole as usize].stream[position as usize];
        let values = reading(self.census, self.atlas, surface);
        Observation(
            ReceiverAxis::from_id(receiver)
                .map(|axis| axis.read(values))
                .unwrap_or(u64::MAX),
        )
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let step = Step::from_input(input)?;
        let root = item.0 / self.stride();
        let slot = (item.0 % self.stride()) as i64;
        let next_slot = slot + step.offset();
        if next_slot < 0 || next_slot >= self.stride() as i64 {
            return None;
        }
        let next = ItemId(root * self.stride() + next_slot as u64);
        self.site(next).map(|_| next)
    }
}

fn root_partition(
    system: &ReconstructionSystem<'_>,
    partition: &Partition,
) -> Vec<BTreeSet<usize>> {
    partition
        .blocks
        .iter()
        .map(|block| {
            block
                .iter()
                .filter_map(|item| system.root_index(*item))
                .collect::<BTreeSet<_>>()
        })
        .filter(|block| !block.is_empty())
        .collect()
}

fn other_root_surface(fiber: &ReconstructionFiber, pair: &CollapsedPair) -> Option<SurfaceId> {
    let stride = (2 * fiber.horizon + 1) as u64;
    let focus_item = ItemId(fiber.focus_root as u64 * stride + fiber.horizon as u64);
    let other = if pair.left == focus_item {
        pair.right
    } else if pair.right == focus_item {
        pair.left
    } else {
        return None;
    };
    if other.0 % stride != fiber.horizon as u64 {
        return None;
    }
    fiber
        .roots
        .get((other.0 / stride) as usize)
        .map(|root| root.surface)
}

#[cfg(test)]
mod tests;
