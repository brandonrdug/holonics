//! Ceiling-free replay of already-enacted Soma deeds.
//!
//! This is the carried current-span surface used by the active membrane. It applies the same
//! body-owned ranked OWN law as live conduct, without re-running source action or interpreting the
//! organ which produced the deeds.

use body::manifold::{FeltEmission, RankedFeltDeposit, RankedOwnState};

use crate::{GrowingRankedOwn, RankedOwnCell};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RankedSurfaceError {
    DeedExtent,
    InvalidEmission,
    Topology,
}

pub struct RankedFeltSurface {
    state: RankedOwnState,
    storage: GrowingRankedOwn,
    deed_extent: usize,
    deeds_seen: usize,
}

impl RankedFeltSurface {
    pub fn preflight(deed_extent: usize) -> Result<Self, RankedSurfaceError> {
        let mut storage = GrowingRankedOwn::new();
        let state =
            RankedOwnState::preflight(&mut storage).map_err(|_| RankedSurfaceError::Topology)?;
        Ok(Self {
            state,
            storage,
            deed_extent,
            deeds_seen: 0,
        })
    }

    pub fn deposit(
        &mut self,
        emission: FeltEmission,
    ) -> Result<RankedFeltDeposit, RankedSurfaceError> {
        if self.deeds_seen >= self.deed_extent {
            return Err(RankedSurfaceError::DeedExtent);
        }
        if !emission.hand_is_exact() {
            return Err(RankedSurfaceError::InvalidEmission);
        }
        let receipt = self
            .state
            .deposit_term(&mut self.storage, emission.position, emission.term)
            .map_err(|_| RankedSurfaceError::Topology)?;
        self.deeds_seen += 1;
        Ok(receipt)
    }

    pub fn rank(&self) -> u64 {
        self.state.rank()
    }

    pub fn occupancy_words(&self) -> &[u64] {
        self.storage.occupancy_words()
    }

    pub fn breath(&self) -> (u64, u64) {
        self.state.breath()
    }

    pub fn cells(&self) -> &[RankedOwnCell] {
        self.storage.cells()
    }

    pub fn deeds_seen(&self) -> usize {
        self.deeds_seen
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::channel::WindingQuantum;
    use body::manifold::{FeltDeed, FeltEmission};
    use body::medium::FeltTerm;
    use body::num::Cog;
    use body::place::Place;
    use body::soul::Chi;

    use crate::SparseFeltSurface;

    fn ride(position: Place, same: i64, other: i64) -> FeltEmission {
        FeltEmission {
            position,
            term: FeltTerm {
                chi: Chi {
                    same: Cog::lit(same),
                    other: Cog::lit(other),
                },
                winding: WindingQuantum::None,
            },
            deed: FeltDeed::Ride,
            standing_read: None,
        }
    }

    fn occupancy_u64(words: &[u64]) -> Option<u64> {
        match words {
            [] => Some(0),
            [word] => Some(*word),
            _ => None,
        }
    }

    #[test]
    fn ranked_production_is_the_flat_sparse_law_at_every_lived_event() {
        let p0 = (Cog::lit(0), Cog::lit(0));
        let p1 = (Cog::lit(1), Cog::lit(0));
        let p2 = (Cog::lit(0), Cog::lit(1));
        let p3 = (Cog::lit(1), Cog::lit(1));
        let deeds = [
            ride(p0, 3, 5),
            ride(p1, 7, 11),
            ride(p2, 13, 17),
            ride(p3, 19, 23),
            ride(p0, -3, -5),
            ride(p1, -7, -11),
            ride(p2, -13, -17),
            ride(p3, -19, -23),
            ride(p3, 29, 31),
        ];
        let mut ranked = RankedFeltSurface::preflight(deeds.len()).unwrap();
        let mut flat = SparseFeltSurface::preflight(deeds.len()).unwrap();
        for deed in deeds {
            ranked.deposit(deed).unwrap();
            flat.deposit(deed).unwrap();
            assert_eq!(1u32 << ranked.rank(), flat.axis());
            assert_eq!(
                occupancy_u64(ranked.occupancy_words()),
                Some(flat.occupancy())
            );
            assert_eq!(ranked.breath(), flat.breath());
            let ranked_cells: Vec<_> = ranked
                .cells()
                .iter()
                .map(|cell| {
                    (
                        cell.address().try_flat_grip().unwrap(),
                        cell.founder(),
                        cell.form(),
                    )
                })
                .collect();
            let flat_cells: Vec<_> = flat
                .cells()
                .iter()
                .map(|cell| (cell.grip(), cell.position(), cell.form()))
                .collect();
            assert_eq!(ranked_cells, flat_cells);
        }
    }
}
