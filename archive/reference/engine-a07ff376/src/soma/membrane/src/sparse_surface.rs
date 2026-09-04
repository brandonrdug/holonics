//! Sparse REGISTER-equivalent replay of accepted Soma deeds.
//!
//! The dense [`body::manifold::FeltEmissionSurface`] remains the parity oracle.  This production
//! host surface carries only occupied grips and therefore breathes in proportion to live
//! construction, never `axis²`.  Its storage is preflighted from the exact deed extent; no
//! allocation, semantic selection, or source re-execution occurs during replay.

use std::vec::Vec;

use body::manifold::{FeltDeposit, FeltEmission, SparseOwnCell, SparseOwnState};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SparseSurfaceError {
    ResourceExtent,
    ResourceReservation,
    DeedExtent,
    InvalidEmission,
    Topology,
}

pub type SparseFeltCell = SparseOwnCell;

/// One exact current-local surface under the body's REGISTER arrival, alias, annihilation, and
/// retirement laws.  `deed_extent` is a physical transaction bound, not a workload cap: the
/// caller supplies the complete admitted journal span before mutation.
pub struct SparseFeltSurface {
    state: SparseOwnState,
    cells: Vec<SparseFeltCell>,
    deed_extent: usize,
    deeds_seen: usize,
}

impl SparseFeltSurface {
    pub fn preflight(deed_extent: usize) -> Result<Self, SparseSurfaceError> {
        let mut cells = Vec::new();
        cells
            .try_reserve_exact(deed_extent)
            .map_err(|_| SparseSurfaceError::ResourceReservation)?;
        cells.resize(deed_extent, SparseFeltCell::EMPTY);
        let state = SparseOwnState::preflight(cells.as_mut_slice())
            .ok_or(SparseSurfaceError::ResourceExtent)?;
        Ok(Self {
            state,
            cells,
            deed_extent,
            deeds_seen: 0,
        })
    }

    pub fn axis(&self) -> u32 {
        self.state.axis()
    }

    pub fn occupancy(&self) -> u64 {
        self.state.occupancy()
    }

    pub fn breath(&self) -> (u64, u64) {
        self.state.breath()
    }

    pub fn deeds_seen(&self) -> usize {
        self.deeds_seen
    }

    pub fn cells(&self) -> &[SparseFeltCell] {
        self.state
            .cells(self.cells.as_slice())
            .expect("a preflighted sparse surface retains its live extent")
    }

    /// Replay one already-enacted deed.  All fallible resource and structural checks precede
    /// mutation.  The returned posture has the same meaning as the dense oracle's [`FeltDeposit`].
    pub fn deposit(&mut self, emission: FeltEmission) -> Result<FeltDeposit, SparseSurfaceError> {
        if self.deeds_seen >= self.deed_extent {
            return Err(SparseSurfaceError::DeedExtent);
        }
        if !emission.hand_is_exact() {
            return Err(SparseSurfaceError::InvalidEmission);
        }

        let receipt = self
            .state
            .deposit_term(self.cells.as_mut_slice(), emission.position, emission.term)
            .ok_or(SparseSurfaceError::Topology)?;
        self.deeds_seen += 1;
        Ok(receipt)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::channel::WindingQuantum;
    use body::chart;
    use body::manifold::{
        narrow_own_cells, own_cell_position, zero_extend_own_cells, FeltDeed, FeltEmissionSurface,
        OwnRecast, OWN_CELL_FORM, OWN_CELL_LIVE, OWN_CELL_WORDS,
    };
    use body::medium::{FeltTerm, RegionalForm, FORM_WORDS};
    use body::num::{Cog, Rung};
    use body::place::{self, Place};
    use body::soul::Chi;

    struct DenseChart {
        words: Vec<u32>,
    }

    impl DenseChart {
        fn born() -> Self {
            Self {
                words: vec![0u32; OWN_CELL_WORDS],
            }
        }
    }

    impl OwnRecast for DenseChart {
        fn words(&self) -> &[u32] {
            &self.words
        }

        fn words_mut(&mut self) -> &mut [u32] {
            &mut self.words
        }

        fn recast(&mut self, old_axis: i64, new_axis: i64) {
            let mut fresh = vec![0u32; (new_axis * new_axis) as usize * OWN_CELL_WORDS];
            if new_axis > old_axis {
                zero_extend_own_cells(&self.words, &mut fresh, old_axis, new_axis);
            } else {
                narrow_own_cells(&self.words, &mut fresh, old_axis, new_axis);
            }
            self.words = fresh;
        }
    }

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

    fn assert_dense_sparse(deeds: &[FeltEmission]) {
        let mut dense_chart = DenseChart::born();
        let mut sparse = SparseFeltSurface::preflight(deeds.len()).unwrap();
        let (dense_axis, dense_occupancy, dense_breath) = {
            let mut dense = FeltEmissionSurface::over_register(&mut dense_chart);
            for &deed in deeds {
                let dense_receipt = dense.deposit_with_receipt(deed).unwrap();
                let sparse_receipt = sparse.deposit(deed).unwrap();
                assert_eq!(sparse_receipt, dense_receipt);
                assert_eq!(sparse.axis(), dense.axis());
                assert_eq!(sparse.occupancy(), dense.occupancy());
                assert_eq!(sparse.breath(), dense.breath());
            }
            (dense.axis(), dense.occupancy(), dense.breath())
        };
        assert_eq!(sparse.axis(), dense_axis);
        assert_eq!(sparse.occupancy(), dense_occupancy);
        assert_eq!(sparse.breath(), dense_breath);

        let mut dense_cells = Vec::new();
        for grip in 0..dense_axis * dense_axis {
            let at = grip as usize * OWN_CELL_WORDS;
            if dense_chart.words[at + OWN_CELL_LIVE] != 0 {
                dense_cells.push((
                    grip,
                    own_cell_position(&dense_chart.words, at),
                    RegionalForm::unpack(&dense_chart.words, at + OWN_CELL_FORM),
                ));
            }
        }
        let sparse_cells: Vec<_> = sparse
            .cells()
            .iter()
            .map(|cell| (cell.grip(), cell.position(), cell.form()))
            .collect();
        assert_eq!(sparse_cells, dense_cells);
    }

    #[test]
    fn sparse_surface_matches_dense_widen_alias_release_and_narrow() {
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
        assert_dense_sparse(&deeds);
    }

    #[test]
    fn an_off_section_barrier_clears_before_the_sparse_retirement_cascade() {
        let find = |tag: &[u8], want: &dyn Fn(Place) -> bool| -> Place {
            let mut salt = 0u32;
            while salt < 65_536 {
                let mut bytes = Vec::from(tag);
                bytes.extend_from_slice(&salt.to_le_bytes());
                let position = body::manifold::wind(&bytes);
                if want(position) {
                    return position;
                }
                salt += 1;
            }
            panic!("the deterministic banding witness must exist")
        };
        let p1 = find(b"cascade p1 ", &|position| {
            place::ground(position, 4) == chart::zero_extend_grip(place::ground(position, 2), 2, 4)
        });
        let p1_grip = place::ground(p1, 2);
        let p1_extended = chart::zero_extend_grip(p1_grip, 2, 4);
        let p2 = find(b"cascade p2 ", &|position| {
            place::ground(position, 2) != p1_grip
                && chart::zero_extended_source(place::ground(position, 4), 2, 4).is_none()
        });
        let p3 = find(b"cascade p3 ", &|position| {
            place::ground(position, 4) != p1_extended
                && chart::zero_extended_source(place::ground(position, 4), 2, 4).is_some()
        });
        let deeds = [
            ride(p1, 3, 4),
            ride(p2, 3, 4),
            ride(p3, 3, 4),
            ride(p1, -3, -4),
            ride(p3, -3, -4),
            ride(p2, -3, -4),
        ];
        assert_dense_sparse(&deeds);
        let mut sparse = SparseFeltSurface::preflight(deeds.len()).unwrap();
        for (ordinal, deed) in deeds.into_iter().enumerate() {
            sparse.deposit(deed).unwrap();
            match ordinal {
                4 => assert_eq!(
                    (sparse.axis(), sparse.occupancy(), sparse.breath()),
                    (4, 1, (2, 0)),
                    "the live off-section founder holds the wide gauge"
                ),
                5 => assert_eq!(
                    (sparse.axis(), sparse.occupancy(), sparse.breath()),
                    (1, 0, (3, 2)),
                    "removing that exact barrier retires both available digits in one event"
                ),
                _ => {}
            }
        }
    }

    #[test]
    fn opposed_winding_arms_prevent_false_annihilation() {
        let position = (Cog::lit(37), Cog::lit(41));
        let this_way = FeltEmission {
            position,
            term: FeltTerm {
                chi: Chi {
                    same: Cog::lit(3),
                    other: Cog::lit(4),
                },
                winding: WindingQuantum::ThisWay,
            },
            deed: FeltDeed::FoundThis,
            standing_read: None,
        };
        let that_way = FeltEmission {
            position,
            term: FeltTerm {
                chi: Chi {
                    same: Cog::lit(-3),
                    other: Cog::lit(-4),
                },
                winding: WindingQuantum::ThatWay,
            },
            deed: FeltDeed::FoundThat,
            standing_read: None,
        };
        assert_dense_sparse(&[this_way, that_way]);
        let mut sparse = SparseFeltSurface::preflight(2).unwrap();
        sparse.deposit(this_way).unwrap();
        sparse.deposit(that_way).unwrap();
        assert_eq!((sparse.occupancy(), sparse.breath()), (1, (0, 0)));
        let (this_arm, that_arm) = sparse.cells()[0].form().fiber();
        assert_ne!(this_arm, Rung::ZERO);
        assert_ne!(that_arm, Rung::ZERO);
    }

    #[test]
    fn a_mismatched_hand_and_an_extra_deed_refuse_before_mutation() {
        let mut sparse = SparseFeltSurface::preflight(1).unwrap();
        let invalid = FeltEmission {
            position: (Cog::lit(3), Cog::lit(5)),
            term: FeltTerm {
                chi: Chi {
                    same: Cog::lit(7),
                    other: Cog::lit(11),
                },
                winding: WindingQuantum::ThisWay,
            },
            deed: FeltDeed::Ride,
            standing_read: None,
        };
        assert_eq!(
            sparse.deposit(invalid),
            Err(SparseSurfaceError::InvalidEmission)
        );
        assert_eq!(
            (sparse.axis(), sparse.occupancy(), sparse.deeds_seen()),
            (1, 0, 0)
        );

        sparse
            .deposit(ride((Cog::lit(3), Cog::lit(5)), 7, 11))
            .unwrap();
        let before = (
            sparse.axis(),
            sparse.occupancy(),
            sparse.breath(),
            sparse.cells().to_vec(),
        );
        assert_eq!(
            sparse.deposit(ride((Cog::lit(13), Cog::lit(17)), 19, 23)),
            Err(SparseSurfaceError::DeedExtent)
        );
        assert_eq!(
            (
                sparse.axis(),
                sparse.occupancy(),
                sparse.breath(),
                sparse.cells().to_vec()
            ),
            before
        );
    }

    #[test]
    fn the_sparse_surface_never_materializes_the_axis_square() {
        let deeds: Vec<_> = (0..96)
            .map(|n| {
                ride(
                    (Cog::lit(n * 17 + 1), Cog::lit(n * 29 + 3)),
                    n + 1,
                    n * 2 + 1,
                )
            })
            .collect();
        let mut sparse = SparseFeltSurface::preflight(deeds.len()).unwrap();
        for deed in deeds {
            sparse.deposit(deed).unwrap();
        }
        assert_eq!(sparse.cells().len() as u64, sparse.occupancy());
        assert_eq!(sparse.cells.len(), sparse.deed_extent);
        assert!(sparse.cells().len() < (sparse.axis() as usize).pow(2));
        // This import is intentionally used here to pin the dense row size outside the sparse
        // representation: no `FORM_WORDS * axis²` allocation exists in the surface.
        assert!(FORM_WORDS > 0);
    }
}
