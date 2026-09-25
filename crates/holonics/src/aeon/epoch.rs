//! **Epochs: an aeon divided at a receiver's section, and the refinement tower.**
//!
//! [definition] Lean `Aeon/Clock/Epoch` and the aeon record ("epoch"). A receiver's section `Σ_R`
//! is given by the passages that cross it: traversing such a passage along its orientation is a
//! tick `+1`, against it a tick `−1`. The section is the cut cochain (Lean `CutClock`), and its
//! reading of an aeon is the **flux**, forward crossings minus backward crossings
//! (`reading_eq_crossings`); it adds under concatenation and changes sign under reversal as every
//! reading does (`crossings_concat`). The aeon's crossings, forward or back, are its ticks
//! (`crossingTicks`), a certified section of its micro-states (`aeonSection`). The **epoch** of a
//! micro-state is the number of ticks before it (`epochOf`), so the epochs partition the aeon into
//! intervals, the epoch advances by one at every tick, and there are `#ticks + 1` of them
//! (`epoch_contiguous`, `epochOf_succ`, `aeon_epochs_attained`). The **sheet** of a micro-state is
//! the flux up to it, the sheet of the section's cover it lies on. On a monotone aeon the sheet is
//! the epoch; on an aeon that crosses back the sheet returns to an earlier value where the epoch
//! opens a new interval.
//!
//! **Coarsening** passes to a sub-section `Σ′ ⊂ Σ` at a coarser grain, whose ticks are among the
//! finer ones (the first return to `Σ′`). The coarse epoch is then a function of the fine epoch,
//! which [`EpochTower::coarsen`] returns, and the functions compose along the tower
//! (`epochOf_coarse`, `coarsen_tower`). On the lift of the clock torus the section of navigator `i`
//! at grain `g` is the lattice hyperplanes `xᵢ ≡ 0 (mod g)` ([`ClockLift::ring_section`]); its flux
//! over an aeon is the difference of the whole windings of its endpoints (`signed_count_is_flux`),
//! and on a forward aeon it is the parametron ring's crossing count
//! [`crate::holon::parametron::ring_crossings`] (`monotone_count_is_flux`, `ring_count_is_flux`).
//!
//! [open] The sheets have no Lean owner, and they do not coarsen: along an aeon that crosses a
//! sub-cut against its orientation, one fine sheet meets two coarse sheets (the test
//! `the_sheets_of_a_sub_cut_crossed_back_do_not_coarsen`). The oriented (sheet) coarsening law is
//! owed in #62 (#72).

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use crate::aeon::AeonError;
use crate::aeon::groupoid::{Aeon, ClockLift, LiftPassage, ParametricComplex};

/// [definition] **A tick**: step `step` of the aeon crosses the section, forward (`+1`) or back
/// (`−1`). It reaches micro-state `step + 1`, Lean's tick in `crossingTicks`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tick {
    pub step: usize,
    pub forward: bool,
}

/// [definition] **The epochs of an aeon at a receiver's section**: the ticks and, for each
/// micro-state, its epoch (the number of ticks before it, Lean `epochOf` over `aeonSection`) and
/// its sheet (the flux up to it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Epochs {
    epochs: Vec<usize>,
    sheets: Vec<BigInt>,
    ticks: Vec<Tick>,
}

/// [definition] **The epochs of an aeon** at the section whose crossing passages `section` names.
pub fn epochs<K: ParametricComplex>(
    aeon: &Aeon<K>,
    section: impl Fn(&K::Passage) -> bool,
) -> Epochs {
    let micro_states = aeon.occurrences().len();
    let mut epochs = Vec::with_capacity(micro_states);
    let mut sheets = Vec::with_capacity(micro_states);
    let mut ticks = Vec::new();
    let mut sheet = BigInt::zero();
    epochs.push(0);
    sheets.push(sheet.clone());
    for (index, step) in aeon.steps().iter().enumerate() {
        if section(&step.passage) {
            ticks.push(Tick {
                step: index,
                forward: step.forward,
            });
            if step.forward {
                sheet += BigInt::one();
            } else {
                sheet -= BigInt::one();
            }
        }
        epochs.push(ticks.len());
        sheets.push(sheet.clone());
    }
    Epochs {
        epochs,
        sheets,
        ticks,
    }
}

impl Epochs {
    /// The aeon's micro-states: its occurrences, one more than its steps.
    pub fn micro_states(&self) -> usize {
        self.epochs.len()
    }

    pub fn ticks(&self) -> &[Tick] {
        &self.ticks
    }

    /// **The flux**: the oriented count of crossings, the section's reading of the aeon.
    pub fn flux(&self) -> BigInt {
        self.sheets[self.sheets.len() - 1].clone()
    }

    /// **The epoch of a micro-state**: the number of ticks at steps before it, the interval of the
    /// aeon between two crossings that it lies in. Lean `epochOf` over `crossingTicks`.
    pub fn epoch_of(&self, micro_state: usize) -> Option<usize> {
        self.epochs.get(micro_state).copied()
    }

    /// **The sheet of a micro-state**: the flux up to it, the oriented count of the ticks before
    /// it. It is the epoch on a monotone aeon and not otherwise.
    pub fn sheet_of(&self, micro_state: usize) -> Option<&BigInt> {
        self.sheets.get(micro_state)
    }

    /// Epoch `label`: the micro-states whose epoch it is. Lean `epoch`.
    pub fn epoch(&self, label: usize) -> Vec<usize> {
        (0..self.epochs.len())
            .filter(|micro_state| self.epochs[*micro_state] == label)
            .collect()
    }

    /// The epochs the aeon attains, lowest first.
    pub fn attained(&self) -> Vec<usize> {
        let mut attained = self.epochs.clone();
        attained.dedup();
        attained
    }

    /// Whether every tick crosses forward: the motion never returns through the section.
    pub fn is_monotone(&self) -> bool {
        self.ticks.iter().all(|tick| tick.forward)
    }
}

/// [definition] **An epoch tower**: the epochs of one aeon at a sequence of grains, fine to
/// coarse, each coarser section ticking only among the finer ticks. Lean `coarsen_tower`
/// (`Σ'' ⊆ Σ' ⊆ Σ`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochTower {
    grains: Vec<Epochs>,
}

impl EpochTower {
    /// Validate the grains: one aeon (one micro-state count), and every tick of a coarser grain a
    /// tick of the finer grain below it — the first return to a sub-section.
    pub fn new(grains: Vec<Epochs>) -> Result<Self, AeonError> {
        for (grain, pair) in grains.windows(2).enumerate() {
            let (fine, coarse) = (&pair[0], &pair[1]);
            if fine.micro_states() != coarse.micro_states() {
                return Err(AeonError::MicroStateMismatch);
            }
            if let Some(tick) = coarse.ticks.iter().find(|tick| !fine.ticks.contains(tick)) {
                return Err(AeonError::NotASubsection {
                    grain: grain + 1,
                    tick: tick.step,
                });
            }
        }
        Ok(Self { grains })
    }

    /// **The epochs of the aeon at grain `grain`.**
    pub fn epochs(&self, grain: usize) -> Result<&Epochs, AeonError> {
        self.grains
            .get(grain)
            .ok_or(AeonError::GrainOutside { grain })
    }

    /// **Coarsening** from grain `fine` to grain `coarse ≥ fine`: the coarse epoch of each fine
    /// epoch `k`, the number of coarse ticks whose fine epoch is at most `k` (Lean `coarsen`). It is
    /// total: [`Self::new`] certified the coarse ticks among the fine ones (every intermediate
    /// grain's, so the inclusion composes), so the coarse epoch of every micro-state is its image
    /// (`epochOf_coarse`), and the maps compose along the tower (`coarsen_tower`).
    pub fn coarsen(&self, fine: usize, coarse: usize) -> Result<BTreeMap<usize, usize>, AeonError> {
        if fine > coarse {
            return Err(AeonError::NotFinerGrain { fine, coarse });
        }
        let (fine_epochs, coarse_epochs) = (self.epochs(fine)?, self.epochs(coarse)?);
        Ok((0..=fine_epochs.ticks.len())
            .map(|k| {
                let image = coarse_epochs
                    .ticks
                    .iter()
                    .filter(|tick| fine_epochs.epochs[tick.step + 1] <= k)
                    .count();
                (k, image)
            })
            .collect())
    }
}

impl ClockLift {
    /// [definition] **The ring section of navigator `navigator` at grain `grain`**: the lattice
    /// hyperplanes `xᵢ ≡ 0 (mod grain)` (Lean `sectionForm`). A passage of that navigator crosses
    /// it when it arrives on it. At the navigator's period it is the parametron ring's section; at
    /// a multiple of the period it is a sub-section, the Odometer's next digit. Grain `0` is
    /// refused with [`AeonError::ZeroPeriod`]: a section has at least one micro-step per circle.
    pub fn ring_section(
        &self,
        navigator: usize,
        grain: BigUint,
    ) -> Result<impl Fn(&LiftPassage) -> bool + use<>, AeonError> {
        if grain.is_zero() {
            return Err(AeonError::ZeroPeriod);
        }
        let grain = BigInt::from(grain);
        Ok(move |passage: &LiftPassage| {
            passage.navigator == navigator
                && passage
                    .from
                    .get(navigator)
                    .is_some_and(|coordinate| ((coordinate + BigInt::one()) % &grain).is_zero())
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aeon::reading::{Reading, TorusClock, reading};
    use crate::geometry::winding::{Odometer, winding};
    use crate::holon::parametron::ring_crossings;
    use crate::navigator::Clock as NavigatorClock;
    use crate::ratio::{Rat, integer};

    fn lattice(values: &[i64]) -> Vec<BigInt> {
        values.iter().map(|value| BigInt::from(*value)).collect()
    }

    fn line(period: u32) -> ClockLift {
        ClockLift::new(vec![BigUint::from(period)]).unwrap()
    }

    /// A walk of the one-navigator lift from `start` by the signed moves.
    fn walk(lift: &ClockLift, start: i64, moves: &[bool]) -> Aeon<ClockLift> {
        let moves: Vec<(usize, bool)> = moves.iter().map(|forward| (0, *forward)).collect();
        lift.walk(lattice(&[start]), &moves).unwrap()
    }

    /// **Epochs partition the aeon into intervals and the flux is a reading.** The epoch advances
    /// by one at every tick, forward or back, and the sheet by the tick's sign; every epoch is an
    /// interval and there are `#ticks + 1` of them on any aeon; the flux adds under concatenation
    /// and changes sign under reversal; and the sheet is the epoch exactly on a monotone aeon. Lean
    /// `Epoch.epochOf_succ`, `epoch_contiguous`, `aeon_epochs_attained`, `crossings_concat`.
    #[test]
    fn epochs_partition_the_aeon_and_the_flux_is_a_reading() {
        let lift = line(3);
        let section = || lift.ring_section(0, BigUint::from(3u32)).unwrap();
        let gamma = walk(
            &lift,
            1,
            &[true, true, false, true, true, true, false, false],
        );
        let delta = lift.walk(gamma.end().clone(), &[(0, true); 5]).unwrap();
        let (at, forward) = (epochs(&gamma, section()), epochs(&delta, section()));
        for epochs in [&at, &forward] {
            for step in 0..epochs.micro_states() - 1 {
                let moved = epochs.epoch_of(step + 1).unwrap() - epochs.epoch_of(step).unwrap();
                let turned = epochs.sheet_of(step + 1).unwrap() - epochs.sheet_of(step).unwrap();
                match epochs.ticks().iter().find(|tick| tick.step == step) {
                    Some(tick) => {
                        assert_eq!(moved, 1);
                        assert_eq!(turned, BigInt::from(if tick.forward { 1 } else { -1 }));
                    }
                    None => assert!(moved == 0 && turned.is_zero()),
                }
            }
            assert_eq!(
                epochs.attained(),
                (0..=epochs.ticks().len()).collect::<Vec<_>>()
            );
            for label in epochs.attained() {
                let epoch = epochs.epoch(label);
                assert_eq!(epoch.len(), epoch[epoch.len() - 1] - epoch[0] + 1);
            }
        }
        let joined = epochs(&gamma.concat(&delta).unwrap(), section());
        assert_eq!(joined.flux(), at.flux() + forward.flux());
        assert_eq!(epochs(&gamma.reverse(), section()).flux(), -at.flux());
        assert!(forward.is_monotone());
        for micro_state in 0..forward.micro_states() {
            assert_eq!(
                &BigInt::from(forward.epoch_of(micro_state).unwrap()),
                forward.sheet_of(micro_state).unwrap()
            );
        }
        // `1 → 2 → 3 → 2`: crossing back into the first sheet opens the third epoch.
        assert!(!at.is_monotone());
        assert_eq!(at.sheet_of(3), at.sheet_of(0));
        assert_eq!((at.epoch_of(0), at.epoch_of(3)), (Some(0), Some(2)));
    }

    /// **Count is flux.** Over any `±1` aeon of the ring lift, the oriented crossings of the ring
    /// section are the difference of the endpoints' whole windings; over a forward aeon from
    /// residue `r` they are the parametron ring's crossing count and the navigator clock's jumps;
    /// the unsigned count of a walk that turns back is not the flux. Lean
    /// `Epoch.signed_count_is_flux`, `monotone_count_is_flux`, `ring_count_is_flux`,
    /// `unsigned_count_is_not_flux`.
    #[test]
    fn the_oriented_crossings_are_the_flux() {
        for period in 2u32..6 {
            let lift = line(period);
            let clock = TorusClock::navigator(&lift, 0).unwrap();
            let grain = BigUint::from(period);
            for start in -4i64..4 {
                let moves: Vec<bool> = (0..11).map(|index| (index * 7 + start) % 3 != 0).collect();
                let gamma = walk(&lift, start, &moves);
                let at = epochs(&gamma, lift.ring_section(0, grain.clone()).unwrap());
                let windings = |point: &BigInt| {
                    Reading::of_turns(&Rat::new(point.clone(), BigInt::from(period)))
                        .windings()
                        .clone()
                };
                assert_eq!(
                    at.flux(),
                    windings(&gamma.end()[0]) - windings(&gamma.start()[0])
                );
                assert_eq!(
                    reading(&clock, &gamma).unwrap().turns(),
                    Rat::new(&gamma.end()[0] - &gamma.start()[0], BigInt::from(period))
                );
            }
            for residue in 0..period {
                for count in 0..13usize {
                    let gamma = walk(&lift, residue as i64, &vec![true; count]);
                    let at = epochs(&gamma, lift.ring_section(0, grain.clone()).unwrap());
                    let crossings =
                        ring_crossings(&grain, &BigUint::from(residue), &BigUint::from(count))
                            .unwrap();
                    assert_eq!(at.flux(), BigInt::from(crossings.clone()));
                    let mut navigator =
                        NavigatorClock::ring(integer(1), u64::from(period)).unwrap();
                    navigator.advance(&BigUint::from(residue));
                    assert_eq!(navigator.advance(&BigUint::from(count)), crossings);
                }
            }
        }
        let lift = line(2);
        let back = walk(&lift, 0, &[true, true, false, true]);
        let at = epochs(&back, lift.ring_section(0, BigUint::from(2u32)).unwrap());
        assert_eq!((at.ticks().len(), at.flux()), (3, BigInt::one()));
    }

    /// [counterexample] **At grain one the ring's crossing record is not the flux.** Every lattice
    /// point lies on the section, so the parametron ring records no crossing, while the flux over
    /// `N` micro-steps is `N` whole windings. Lean `Epoch.nontransversal_count_is_not_flux`.
    #[test]
    fn at_grain_one_the_crossing_record_is_not_the_flux() {
        let lift = line(1);
        let gamma = walk(&lift, 0, &[true; 7]);
        let at = epochs(&gamma, lift.ring_section(0, BigUint::one()).unwrap());
        assert_eq!(
            ring_crossings(&BigUint::one(), &BigUint::zero(), &BigUint::from(7u32)).unwrap(),
            BigUint::zero()
        );
        assert_eq!(at.flux(), BigInt::from(7));
        assert_eq!(Reading::of_turns(&integer(7)).windings(), &at.flux());
    }

    /// **Coarsening composes along the tower.** Three ring grains `d | d·m | d·m·n` along a `±1`
    /// aeon: the coarse epoch of every micro-state is the image of its fine epoch, the maps compose
    /// (the scale square commutes), and a coarse epoch is the union of the fine epochs it receives.
    /// Lean `Epoch.epochOf_coarse`, `coarsen_tower`, `coarse_epoch_is_union_of_fine`.
    #[test]
    fn coarsening_composes_along_the_tower() {
        let lift = line(2);
        let moves: Vec<bool> = (0..40).map(|index| index % 5 != 3).collect();
        let gamma = walk(&lift, -3, &moves);
        let grains = [2u32, 6, 12]
            .map(|grain| epochs(&gamma, lift.ring_section(0, BigUint::from(grain)).unwrap()));
        let tower = EpochTower::new(grains.to_vec()).unwrap();
        let (fine_mid, mid_coarse, fine_coarse) = (
            tower.coarsen(0, 1).unwrap(),
            tower.coarsen(1, 2).unwrap(),
            tower.coarsen(0, 2).unwrap(),
        );
        let (fine, coarse) = (tower.epochs(0).unwrap(), tower.epochs(2).unwrap());
        assert!(!fine.is_monotone() && !coarse.ticks().is_empty());
        for micro_state in 0..fine.micro_states() {
            let label = fine.epoch_of(micro_state).unwrap();
            assert_eq!(fine_coarse[&label], coarse.epoch_of(micro_state).unwrap());
        }
        for (fine, coarse) in &fine_coarse {
            assert_eq!(&mid_coarse[&fine_mid[fine]], coarse);
        }
        for label in coarse.attained() {
            let mut union: Vec<usize> = fine_coarse
                .iter()
                .filter(|(_, image)| **image == label)
                .flat_map(|(source, _)| fine.epoch(*source))
                .collect();
            union.sort();
            assert_eq!(union, coarse.epoch(label));
        }
    }

    /// **The Odometer is a tower of epochs.** On a forward aeon from rest, the epoch at grain `n`
    /// is the Odometer's upper count, the epoch at grain `n·m` is its overflow, the lower digit is
    /// the place inside the epoch, and coarsening is the carry `winding m`. Lean
    /// `Epoch.odometer_counts_epochs`, `odometer_tower`, `epochOf_digitTicks`.
    #[test]
    fn the_odometer_is_a_tower_of_epochs() {
        let (n, m) = (3u32, 4u32);
        let lift = line(n);
        let gamma = walk(&lift, 0, &[true; 50]);
        let tower = EpochTower::new(vec![
            epochs(&gamma, lift.ring_section(0, BigUint::from(n)).unwrap()),
            epochs(&gamma, lift.ring_section(0, BigUint::from(n * m)).unwrap()),
        ])
        .unwrap();
        let coarsen = tower.coarsen(0, 1).unwrap();
        for j in 0..gamma.occurrences().len() {
            let mut odometer = Odometer::new(vec![BigUint::from(n), BigUint::from(m)]).unwrap();
            odometer.advance(&BigUint::from(j));
            let fine = tower.epochs(0).unwrap().epoch_of(j).unwrap();
            let coarse = tower.epochs(1).unwrap().epoch_of(j).unwrap();
            assert_eq!(&BigUint::from(coarse), odometer.overflow_winding());
            assert_eq!(
                BigUint::from(fine),
                &odometer.digits()[1] + BigUint::from(m) * odometer.overflow_winding()
            );
            assert_eq!(odometer.digits()[0], BigUint::from(j) % BigUint::from(n));
            assert_eq!(
                BigUint::from(coarsen[&fine]),
                winding(&BigUint::from(m), &BigUint::from(fine)).unwrap()
            );
        }
    }

    /// [counterexample] **The sheets of a sub-cut crossed against its orientation do not
    /// coarsen.** The finer section is crossed forward through one passage and back through the
    /// other, returning to its first sheet, while the coarser section, cutting only the second
    /// passage, has moved to sheet `−1`: one fine sheet meets two coarse sheets. The epochs, which
    /// count every crossing, still coarsen along the same aeon. The Lean counterpart for arrival
    /// sections is `Epoch.nontransversal_subsection_does_not_coarsen`; the oriented (sheet) form is
    /// owed in #62 (#72).
    #[test]
    fn the_sheets_of_a_sub_cut_crossed_back_do_not_coarsen() {
        let lift = ClockLift::new(vec![BigUint::one(), BigUint::one()]).unwrap();
        let first = LiftPassage {
            from: lattice(&[0, 0]),
            navigator: 0,
        };
        let second = LiftPassage {
            from: lattice(&[1, -1]),
            navigator: 1,
        };
        let gamma = lift
            .walk(lattice(&[0, 0]), &[(0, true), (1, false)])
            .unwrap();
        let fine = epochs(&gamma, |passage: &LiftPassage| {
            *passage == first || *passage == second
        });
        let coarse = epochs(&gamma, |passage: &LiftPassage| *passage == second);
        assert_eq!(fine.sheet_of(0), fine.sheet_of(2));
        assert_eq!(
            (coarse.sheet_of(0), coarse.sheet_of(2)),
            (Some(&BigInt::zero()), Some(&-BigInt::one()))
        );
        let tower = EpochTower::new(vec![fine, coarse]).unwrap();
        assert_eq!(
            tower.coarsen(0, 1).unwrap(),
            BTreeMap::from([(0, 0), (1, 0), (2, 1)])
        );
    }

    /// A ring section at grain `0` is refused: Lean's `sectionForm i 0` ticks at `xᵢ + 1 = 0`, not
    /// on a ring.
    #[test]
    fn a_ring_section_at_grain_zero_is_refused() {
        assert!(matches!(
            line(2).ring_section(0, BigUint::zero()),
            Err(AeonError::ZeroPeriod)
        ));
    }
}
