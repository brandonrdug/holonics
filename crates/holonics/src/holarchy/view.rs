//! **A Holarchy's quantities belong to the receiver: view, count and refine.**
//!
//! [definition] Object 11, second half ([§11](../../../../docs/ELEMENTARY_OBJECTS.md#11-holarchy)).
//! A Holarchy has no fixed count, mass or category. A [`Grain`] groups the regions of the glued
//! complex (its top-degree cells) into blocks; a [`RegionReceiver`] reads a block at an
//! occurrence; the receiver's clock is an aeon read at the receiver's section (Lean
//! `Aeon/Clock/Epoch.CutClock`): the receiver ticks where the aeon crosses its section, forward or
//! back, and each tick reads the occurrence the crossing reaches and opens an epoch. At every tick
//! [`Holarchy::view`] returns that occurrence and epoch, the receiver's face of each block, each
//! block's flux through its own boundary under the current at that occurrence, and the blocks the
//! receiver does not separate from each block.
//!
//! [definition] **`count` is decided, never asserted.** [`Holarchy::count`] returns a number only
//! when the receiver certifies the partition by computation: **finite** (the grain is an
//! enumerated list of blocks, so its carrier certifies finiteness), **exhaustive** (every region
//! lies in a block and every block is occupied), **disjoint** and **distinguishing** (the receiver
//! returns different faces on different blocks). Otherwise it returns [`Count::Unresolved`] with
//! the first failed hypothesis and its witness, never a number. [`Holarchy::refine`] passes from a
//! fine grain to a coarse one through a [`GrainRestriction`] and returns the core descent
//! ([`crate::holon::restriction::FactorDescent`]): the commuting scale square with the induced
//! coarse reading, or the defect retaining every merged fibre and the pairs the fine reading
//! separates.
//!
//! | Lean `Holarchy/View` | Rust |
//! |---|---|
//! | `Grain`, `Certified`, `count`, `count_eq_counted_iff`, `certified_count_eq_faces` | [`Grain`], [`Holarchy::count`], [`Count`] |
//! | `blockChain`, `blockFlux`, `sum_blockFlux`, `total_flux_grain_independent` | [`Holarchy::block_boundaries`], [`Holarchy::interface_flux`] |
//! | `shared_face_cancels`, `interior_face_silent` | [`Holarchy::block_boundaries`] |
//! | `GrainRestriction`, `refine_flux` | [`GrainRestriction`], [`Holarchy::refine`] |
//! | `RegionReceiver`, `ViewReturn`, `view`, `view_ticks`, `view_unresolved_singleton_iff`, `view_flux_total`, `holarchy_view_flux` | [`RegionReceiver`], [`TickView`], [`Holarchy::view`] |
//!
//! [open] Lean states the refinement as the flux square (`refine_flux`) and the defect witness
//! (`refine_defect_witness`); the computed descent with its induced coarse reading or its merged
//! fibres is Rust's, through `Holon/Restriction.descent_defect_refutes_factoring`.

use std::collections::BTreeSet;
use std::fmt::Debug;

use num_traits::Zero;

use crate::aeon::{Aeon, ParametricComplex, epochs};
use crate::holarchy::Holarchy;
use crate::holon::HolonError;
use crate::holon::restriction::tower::Transition;
use crate::holon::restriction::{DescentRefusal, FactorDescent, factor_descent_over};
use crate::ratio::Rat;
use crate::ratio::linear::vector::dot;

/// A block: a set of regions (top-degree cells of the glued complex).
pub type Block = BTreeSet<usize>;

/// [definition] **A grain**: the blocks into which a receiver groups the regions (Lean `Grain`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Grain {
    blocks: Vec<Block>,
}

impl Grain {
    pub fn new(blocks: Vec<Block>) -> Self {
        Self { blocks }
    }

    pub fn blocks(&self) -> &[Block] {
        &self.blocks
    }
}

/// [definition] **A receiver of regions**: its face of a block in a state (Lean
/// `Holarchy/View.RegionReceiver`, whose state is an occurrence).
pub trait RegionReceiver {
    type State;
    type Face: Clone + Eq + Debug;

    fn read(&self, state: &Self::State, block: &Block) -> Self::Face;
}

/// [definition] **What the view returns at one tick** (Lean `Holarchy/View.ViewReturn`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TickView<F, O> {
    /// The occurrence the tick reads: the one its crossing reaches.
    pub occurrence: O,
    /// The epoch the tick opens: [`crate::aeon::Epochs::epoch_of`] at the occurrence it reaches,
    /// the number of crossings up to and including it (Lean `epochOf` over
    /// `Aeon/Clock/Epoch.aeonSection`).
    pub epoch: usize,
    /// The receiver's face of each block.
    pub faces: Vec<F>,
    /// Each block's flux through its own boundary.
    pub interface_flux: Vec<Rat>,
    /// For each block, the blocks the receiver does not separate from it (itself included).
    pub unresolved: Vec<Vec<usize>>,
}

/// [definition] **Why a partition is not certified**, first failed hypothesis in the order
/// exhaustive, disjoint, distinguishing, with its witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Unresolved {
    /// A region in no block.
    Uncovered { cell: usize },
    /// A block with no region.
    Unoccupied { block: usize },
    /// A region in two blocks.
    Overlapping { cell: usize, blocks: (usize, usize) },
    /// Two blocks the receiver reads alike.
    Indistinct { blocks: (usize, usize) },
}

/// [definition] **What `count` returns** (Lean `CountReturn`): a number of blocks under a
/// certified partition, or the unresolved hypothesis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Count {
    Counted(usize),
    Unresolved(Unresolved),
}

/// [definition] **A restriction of grains** (Lean `Holarchy/View.GrainRestriction`): each fine block goes to one
/// coarse block that contains it. As a core [`Transition`] it transports a fine block to its
/// coarse block and retains the fine block as its residual.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrainRestriction {
    map: Vec<usize>,
}

impl GrainRestriction {
    /// Refuses a map of the wrong length, a coarse block outside the coarse grain, or a fine block
    /// not inside its coarse block.
    pub fn new(fine: &Grain, coarse: &Grain, map: Vec<usize>) -> Result<Self, HolonError> {
        if map.len() != fine.blocks.len() {
            return Err(HolonError::Shape {
                what: "grain restriction (one coarse block per fine block)",
                expected: fine.blocks.len(),
                found: map.len(),
            });
        }
        for (block, target) in map.iter().enumerate() {
            let Some(coarse_block) = coarse.blocks.get(*target) else {
                return Err(HolonError::BlockOutside { block });
            };
            if !fine.blocks[block].is_subset(coarse_block) {
                return Err(HolonError::BlockOutside { block });
            }
        }
        Ok(Self { map })
    }

    pub fn map(&self) -> &[usize] {
        &self.map
    }
}

impl Transition for GrainRestriction {
    type Source = usize;
    type Target = usize;
    type Residual = usize;

    fn apply(&self, block: &usize) -> usize {
        self.map[*block]
    }

    fn residual(&self, block: &usize) -> usize {
        *block
    }

    fn reopen(&self, _coarse: &usize, block: &usize) -> usize {
        *block
    }
}

impl Holarchy {
    /// Refuse a grain naming a region outside the glued complex.
    fn check_grain(&self, grain: &Grain) -> Result<usize, HolonError> {
        let (cells, d) = self.regions()?;
        let regions = cells.glued().cells(d);
        for block in &grain.blocks {
            if let Some(cell) = block.iter().find(|cell| **cell >= regions) {
                return Err(HolonError::CellOutside {
                    cell: *cell,
                    cells: regions,
                });
            }
        }
        Ok(regions)
    }

    /// [definition] **Each block's boundary on the glued faces** (Lean `blockChain`, then `∂`):
    /// the whole's interior restricted to the block, pushed through the glued boundary. Over a
    /// partition these sum to the whole's boundary face by face (`sum_blockBoundary_apply`); a
    /// face inside the whole touched by exactly two blocks enters them with opposite coefficients
    /// (`shared_face_cancels`), and a face inside one block is silent in its boundary
    /// (`interior_face_silent`).
    pub fn block_boundaries(&self, grain: &Grain) -> Result<Vec<Vec<Rat>>, HolonError> {
        self.check_grain(grain)?;
        let (cells, d) = self.regions()?;
        let orient = self.whole_interior()?;
        let boundary = cells.glued_boundary(d)?;
        grain
            .blocks
            .iter()
            .map(|block| {
                let chain: Vec<Rat> = orient
                    .iter()
                    .enumerate()
                    .map(|(cell, value)| {
                        if block.contains(&cell) {
                            value.clone()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect();
                Ok(boundary.apply(&chain)?)
            })
            .collect()
    }

    /// [definition] **Each block's interface flux** (Lean `blockFlux`): the current paired with the
    /// block's boundary. Over a partition they total the whole's flux at every grain
    /// (`sum_blockFlux`, `total_flux_grain_independent`).
    pub fn interface_flux(&self, grain: &Grain, current: &[Rat]) -> Result<Vec<Rat>, HolonError> {
        let (cells, d) = self.regions()?;
        let faces = cells.glued().cells(d - 1);
        if current.len() != faces {
            return Err(HolonError::Shape {
                what: "current on the glued faces",
                expected: faces,
                found: current.len(),
            });
        }
        Ok(self
            .block_boundaries(grain)?
            .iter()
            .map(|boundary| dot(current, boundary))
            .collect())
    }

    /// [proved-derived; implemented-exact] **`view receiver grain aeon section`** (Lean
    /// `Holarchy/View.view`): the receiver ticks at the aeon's crossings of its section, forward
    /// and back (`view_ticks`: their signed count is the section's reading, and they cut the aeon
    /// into one more epoch, the [`crate::aeon::Epochs`] of the aeon at the section). The
    /// Holarchy's own aeons are those of its parametric orientation [`Holarchy::parametric`]. At
    /// each tick it reads the occurrence reached, opens its epoch, and
    /// returns the faces, the interface fluxes of the current at that occurrence and the unresolved
    /// classes. The classes are all singletons exactly when the receiver distinguishes the grain at
    /// every tick (`view_unresolved_singleton_iff`), and the fluxes total the constituents' own
    /// fluxes (`view_flux_total`, `holarchy_view_flux`).
    pub fn view<K, R>(
        &self,
        receiver: &R,
        grain: &Grain,
        aeon: &Aeon<K>,
        section: impl Fn(&K::Passage) -> bool,
        current: impl Fn(&K::Occurrence) -> Vec<Rat>,
    ) -> Result<Vec<TickView<R::Face, K::Occurrence>>, HolonError>
    where
        K: ParametricComplex,
        R: RegionReceiver<State = K::Occurrence>,
    {
        self.check_grain(grain)?;
        let at = epochs(aeon, section);
        at.ticks()
            .iter()
            .map(|tick| {
                let occurrence = aeon.occurrences()[tick.step + 1].clone();
                let faces: Vec<R::Face> = grain
                    .blocks
                    .iter()
                    .map(|block| receiver.read(&occurrence, block))
                    .collect();
                let unresolved = faces
                    .iter()
                    .map(|face| {
                        (0..faces.len())
                            .filter(|other| faces[*other] == *face)
                            .collect()
                    })
                    .collect();
                Ok(TickView {
                    interface_flux: self.interface_flux(grain, &current(&occurrence))?,
                    occurrence,
                    epoch: at
                        .epoch_of(tick.step + 1)
                        .expect("a tick reaches a micro-state of the aeon it was read on"),
                    faces,
                    unresolved,
                })
            })
            .collect()
    }

    /// [proved-derived; implemented-exact] **`count`** (Lean `count`, `count_eq_counted_iff`,
    /// `certified_count_eq_faces`): the number of blocks exactly when the receiver certifies the
    /// partition in `state`, which is then the number of distinct faces it returns; otherwise the
    /// first failed hypothesis.
    pub fn count<R: RegionReceiver>(
        &self,
        receiver: &R,
        grain: &Grain,
        state: &R::State,
    ) -> Result<Count, HolonError> {
        let regions = self.check_grain(grain)?;
        let blocks = &grain.blocks;
        for cell in 0..regions {
            if !blocks.iter().any(|block| block.contains(&cell)) {
                return Ok(Count::Unresolved(Unresolved::Uncovered { cell }));
            }
        }
        if let Some(block) = blocks.iter().position(BTreeSet::is_empty) {
            return Ok(Count::Unresolved(Unresolved::Unoccupied { block }));
        }
        for left in 0..blocks.len() {
            for right in left + 1..blocks.len() {
                if let Some(cell) = blocks[left].intersection(&blocks[right]).next() {
                    return Ok(Count::Unresolved(Unresolved::Overlapping {
                        cell: *cell,
                        blocks: (left, right),
                    }));
                }
            }
        }
        let faces: Vec<R::Face> = blocks
            .iter()
            .map(|block| receiver.read(state, block))
            .collect();
        for left in 0..faces.len() {
            for right in left + 1..faces.len() {
                if faces[left] == faces[right] {
                    return Ok(Count::Unresolved(Unresolved::Indistinct {
                        blocks: (left, right),
                    }));
                }
            }
        }
        Ok(Count::Counted(blocks.len()))
    }

    /// [proved-derived; implemented-exact] **`refine`**: the receiver's reading of the fine blocks
    /// either descends through the restriction to the coarse grain (the witness carries the
    /// induced coarse reading) or exhibits two fine blocks the restriction merges and the reading
    /// separates (Lean `Holarchy/View.refine_defect_witness`). The flux reading always descends: a
    /// coarse block's flux is the sum of its fine blocks' (`refine_flux`).
    pub fn refine<R: RegionReceiver>(
        &self,
        receiver: &R,
        state: &R::State,
        fine: &Grain,
        restriction: &GrainRestriction,
    ) -> Result<FactorDescent<usize, usize, R::Face>, HolonError> {
        self.check_grain(fine)?;
        if restriction.map.len() != fine.blocks.len() {
            return Err(HolonError::Shape {
                what: "grain restriction (one coarse block per fine block)",
                expected: fine.blocks.len(),
                found: restriction.map.len(),
            });
        }
        let sources: Vec<usize> = (0..fine.blocks.len()).collect();
        let readings: Vec<R::Face> = fine
            .blocks
            .iter()
            .map(|block| receiver.read(state, block))
            .collect();
        factor_descent_over(restriction, &sources, &readings).map_err(|refusal| match refusal {
            DescentRefusal::SourcesAboveCeiling { declared, ceiling } => HolonError::Shape {
                what: "fine blocks (descent ceiling)",
                expected: ceiling,
                found: declared,
            },
            DescentRefusal::ReadingsMismatch { sources, readings } => HolonError::Shape {
                what: "fine readings",
                expected: sources,
                found: readings,
            },
        })
    }
}
