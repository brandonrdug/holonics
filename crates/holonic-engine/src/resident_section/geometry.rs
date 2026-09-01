use super::*;

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
        emitted.ok_or(ResidentRefusal::Declaration {
            operation,
            what: format!(
                "no entry is emitted for {self:?}; the family is the one the module carries"
            ),
        })
    }
    /// Refuse a geometry the device or the module cannot carry, naming which aperture refused.
    pub fn admit(
        &self,
        operation: &'static str,
        block_ceiling: u32,
        warp: u32,
        shared_ceiling: u32,
    ) -> Result<(), ResidentRefusal> {
        if self.lanes == 0 || !self.lanes.is_power_of_two() || self.lanes > warp.max(1) {
            return Err(ResidentRefusal::Declaration {
                operation,
                what: format!(
                    "{} lanes is not a power of two inside one warp of {warp}",
                    self.lanes
                ),
            });
        }
        if self.tile_rows == 0 || self.outs_per_block == 0 {
            return Err(ResidentRefusal::Declaration {
                operation,
                what: "a tile with no rows or no output coordinates".to_owned(),
            });
        }
        if self.splits == 0 || !self.splits.is_power_of_two() || self.splits > 16 {
            return Err(ResidentRefusal::Declaration {
                operation,
                what: format!(
                    "a split factor of {} is not a power of two in 1..=16",
                    self.splits
                ),
            });
        }
        let block = self.block();
        if block == 0 || block % warp.max(1) != 0 {
            return Err(ResidentRefusal::Declaration {
                operation,
                what: format!("a block of {block} is not a whole number of warps of {warp}"),
            });
        }
        if block > block_ceiling {
            return Err(ResidentRefusal::Declaration {
                operation,
                what: format!("a block of {block} exceeds the module's admitted {block_ceiling}"),
            });
        }
        if self.shared_octets() > shared_ceiling {
            return Err(ResidentRefusal::Declaration {
                operation,
                what: format!(
                    "a staged tile of {} octets exceeds the device's {shared_ceiling} per block",
                    self.shared_octets()
                ),
            });
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
        for (tile_rows, lanes, splits) in [
            (1, 32, 1),
            (2, 32, 1),
            (4, 32, 1),
            (1, 16, 1),
            (4, 16, 1),
            (1, 8, 1),
            (1, 32, 2),
            (1, 32, 4),
            (1, 32, 8),
            (1, 32, 16),
            (4, 32, 2),
            (4, 32, 4),
            (4, 32, 8),
            (4, 32, 16),
        ] {
            for outs_per_block in [1u32, 2, 4, 8, 16, 32, 64] {
                for k_tile in [0u32, 128, 256, 512, 1024] {
                    let tile = TileGeometry {
                        tile_rows,
                        lanes,
                        outs_per_block,
                        k_tile,
                        splits,
                    };
                    if tile.block() > 512 || tile.block() % 32 != 0 || tile.shared_octets() > 49_152
                    {
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
    pub(super) index: usize,
    pub(super) pointer: u64,
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
        Self {
            index: usize::MAX,
            pointer: 0,
            rows,
            out_width,
            splits,
            words: 4 * rows * out_width * splits as usize,
        }
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
            CandidateAxis::OccupancyUp => (
                u128::from(candidate.occupancy.0),
                u128::from(candidate.occupancy.1.max(1)),
            ),
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
    let axes: Vec<Box<dyn Fn(&LaunchCandidate) -> (u128, u128)>> = axes
        .iter()
        .map(|axis| {
            let axis = *axis;
            Box::new(move |candidate: &LaunchCandidate| axis.read(candidate))
                as Box<dyn Fn(&LaunchCandidate) -> (u128, u128)>
        })
        .collect();
    non_dominated_by(family, &axes)
}

/// **The domination rule itself, over any candidate species and any declared axis set.**
///
/// Lifted out of [`non_dominated`] 2026-08-20 when the native atlas's launch family arrived: its
/// geometry has no inner extent, no map and no split, so the contraction's axes do not read it —
/// but the *rule* is the same rule and a second spelling of a Pareto front is how a pre-check and
/// a guard drift apart. Each axis is a ratio oriented so that GREATER is better; no axis is summed
/// with another, and changing the declared set changes the returned set.
pub fn non_dominated_by<C>(
    family: &[C],
    axes: &[Box<dyn Fn(&C) -> (u128, u128) + '_>],
) -> Vec<usize> {
    let ratio_ge = |a: (u128, u128), b: (u128, u128)| a.0 * b.1 >= b.0 * a.1;
    let ratio_gt = |a: (u128, u128), b: (u128, u128)| a.0 * b.1 > b.0 * a.1;
    (0..family.len())
        .filter(|at| {
            !family.iter().enumerate().any(|(other, rival)| {
                other != *at
                    && axes
                        .iter()
                        .all(|axis| ratio_ge(axis(rival), axis(&family[*at])))
                    && axes
                        .iter()
                        .any(|axis| ratio_gt(axis(rival), axis(&family[*at])))
            })
        })
        .collect()
}
