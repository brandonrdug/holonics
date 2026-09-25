//! **Resonating and emanating: the split of a drive against a constitution's modes.**
//!
//! [definition] A constitution `(K, C)` ([`Parametron`]: `K = Bᵀ W_K B`, `C = Bᵀ W_C B`) has at each
//! eigenvalue `λ` its **mode space** `E_λ = ker(K − λC)`, whose nonzero members are the generalized
//! modes `K v = λ C v`. A drive profile `d` at `λ = ω²` splits as (Lean
//! `Compression/Core/Resonance`, [objects](../../../../docs/ELEMENTARY_OBJECTS.md#emanation-and-resonance))
//!
//! ```text
//! d = r + e       r ∈ E_λ        resonating: rides the existing modes (RIDE)
//!                 e ⟂_C E_λ      emanating: off-resonance or founding (FOUND)
//! (K − λC) d = (K − λC) e                                   the holding-effort amplitude
//! W = λ S_C(e) − S_K(e) = λ S_C(d) − S_K(d)                 the work form, exact over ℚ
//! ⟨d, (K − λC) d⟩ = −2 W                                    the effort's pairing with the motion
//! ```
//!
//! with `S_W(v) = ½ Σ_b W_b (B v)_b²` the owner's storage ([`Parametron::storage`]).
//!
//! [proved-derived; implemented-exact] [`resonance_split`] returns the unique `C`-orthogonal split
//! (`split_exists_unique`, `split_orthogonal`). The effort of the drive is the effort of its
//! emanating part (`effort_split`), zero exactly when that part is (`emanating_effort_eq_zero_iff`),
//! and the reactive form sees only the emanating part (`reactive_split`). The resonating part
//! needs no effort and keeps the exchange law (`resonant_drive_rides`,
//! `Parametron.modeEnergy_conserved`); the emanating part always needs effort
//! (`emanating_drive_needs_effort`), but its work form can be zero: a clamp holds without
//! exchanging energy (`clamp_witness`), so no fixed price of emanation is asserted.
//!
//! [definition; agent-inferred] **The work is a form, not a function of time.** Holding
//! `x = cos(ωt) d` needs the effort `f = cos(ωt)(K − λC) d`, and the energy exchanged with the port
//! over `[0, t]` is `sin²(ωt) · W` (Lean `work_ledger`), with power
//! `⟨f, ẋ⟩ = 2ω sin(ωt) cos(ωt) · W`. Every one of these is the exact form `W` times a face of the
//! clock phase, so this owner returns `W` and the effort amplitude and evaluates no phase; the
//! tests read the clock at rational points of the Cayley chart, as the parametron owner does.
//!
//! [definition; agent-inferred] **A singular capacity is refused.** The split is unique when the
//! capacity form is anisotropic (Lean's hypothesis). For the parametron `C = Bᵀ W_C B` with
//! `W_C ⪰ 0`, so `C` is positive semidefinite and anisotropic exactly when it is nonsingular. A node
//! with no capacitance makes `C` singular, and the split is refused rather than pseudo-inverted.

use num_traits::Zero;

use crate::compression::CompressionError;
use crate::holon::parametron::Parametron;
use crate::ratio::Rat;
use crate::ratio::linear::vector::{add, dot, matrix, scale, sub, zeros};

/// [definition] **The split of a drive** against a constitution at one eigenvalue: the mode space,
/// the resonating and emanating parts, the holding-effort amplitude and the work form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonanceSplit {
    eigenvalue: Rat,
    drive: Vec<Rat>,
    modes: Vec<Vec<Rat>>,
    resonating: Vec<Rat>,
    emanating: Vec<Rat>,
    effort: Vec<Rat>,
    work: Rat,
}

/// **The resonating/emanating split** of a drive at eigenvalue `λ = ω²` (Lean
/// `Compression/Core/Resonance.split_exists_unique`, `split_orthogonal`).
///
/// The resonating part is the `C`-orthogonal projection onto `E_λ = ker(K − λC)`: with `E_λ`
/// spanned by `v_i`, `r = Σ a_i v_i` where `Σ_j ⟨v_i, C v_j⟩ a_j = ⟨v_i, C d⟩`. Refused when the
/// capacity is singular.
pub fn resonance_split(
    constitution: &Parametron,
    drive: &[Rat],
    eigenvalue: &Rat,
) -> Result<ResonanceSplit, CompressionError> {
    let nodes = constitution.nodes();
    if drive.len() != nodes {
        return Err(CompressionError::Extent {
            what: "drive",
            expected: nodes,
            found: drive.len(),
        });
    }
    let capacitance = constitution.capacitance()?;
    if capacitance.rank()? < nodes {
        return Err(CompressionError::SingularCapacity);
    }
    let reactive = constitution
        .stiffness()?
        .subtract(&capacitance.scaled(eigenvalue))?;
    let modes = reactive.kernel_basis()?;
    let resonating = if modes.is_empty() {
        zeros(nodes)
    } else {
        let loaded = modes
            .iter()
            .map(|mode| capacitance.apply(mode))
            .collect::<Result<Vec<_>, _>>()?;
        let gram = matrix(modes.len(), modes.len(), |i, j| dot(&modes[i], &loaded[j]))?;
        let load: Vec<Rat> = loaded.iter().map(|column| dot(column, drive)).collect();
        let coefficients = gram.inverse()?.apply(&load)?;
        modes
            .iter()
            .zip(&coefficients)
            .fold(zeros(nodes), |sum, (mode, coefficient)| {
                add(&sum, &scale(coefficient, mode))
            })
    };
    let emanating = sub(drive, &resonating);
    let effort = reactive.apply(drive)?;
    let work = eigenvalue * constitution.storage(constitution.capacity(), &emanating)?
        - constitution.storage(constitution.inverse_inductance(), &emanating)?;
    Ok(ResonanceSplit {
        eigenvalue: eigenvalue.clone(),
        drive: drive.to_vec(),
        modes,
        resonating,
        emanating,
        effort,
        work,
    })
}

impl ResonanceSplit {
    /// `λ = ω²`.
    pub fn eigenvalue(&self) -> &Rat {
        &self.eigenvalue
    }

    /// The drive profile `d = r + e`.
    pub fn drive(&self) -> &[Rat] {
        &self.drive
    }

    /// A basis of the mode space `E_λ = ker(K − λC)`; empty when `λ` is not an eigenvalue.
    pub fn mode_space(&self) -> &[Vec<Rat>] {
        &self.modes
    }

    /// The resonating part `r ∈ E_λ` (RIDE).
    pub fn resonating(&self) -> &[Rat] {
        &self.resonating
    }

    /// The emanating part `e ⟂_C E_λ` (FOUND).
    pub fn emanating(&self) -> &[Rat] {
        &self.emanating
    }

    /// **The holding-effort amplitude** `(K − λC) d`, which is `(K − λC) e`: the resonating part
    /// is annihilated (Lean `effort_split`). Holding `x = cos(ωt) d` needs `cos(ωt)` times it
    /// (`holdingEffort_newton`).
    pub fn effort_amplitude(&self) -> &[Rat] {
        &self.effort
    }

    /// **Whether the drive rides**: its emanating part is zero, exactly when its holding effort is
    /// zero (Lean `emanating_effort_eq_zero_iff`).
    pub fn rides(&self) -> bool {
        self.emanating.iter().all(Zero::is_zero)
    }

    /// **The work form** `W = λ S_C(e) − S_K(e)` of the emanating part alone, equal to the drive's
    /// own `λ S_C(d) − S_K(d)` (Lean `reactive_split`). The energy the held motion exchanges with
    /// its port over `[0, t]` is `sin²(ωt) · W` (`work_ledger`); `W = 0` is the clamp.
    pub fn work(&self) -> &Rat {
        &self.work
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geometry::screw::RationalPhase;
    use crate::ratio::linear::vector::{integer_matrix, ints};
    use crate::ratio::{integer, rat};

    /// Lean `Objects/Parametron.chainIncidence`, `chainStiffness`, `chainCapacity`: the chain
    /// `ground–0–1–ground` with every branch inductive and only the grounded branches capacitive,
    /// so `K = [[2, −1], [−1, 2]]` and `C = I`; its modes are `(1, 1)` at `λ = 1` and `(1, −1)` at
    /// `λ = 3`.
    fn chain() -> Parametron {
        Parametron::new(
            integer_matrix(&[&[1, 0], &[-1, 1], &[0, 1]]).unwrap(),
            ints(&[1, 0, 1]),
            ints(&[1, 1, 1]),
        )
        .unwrap()
    }

    /// Clock phases read at rational points of the Cayley chart.
    fn phases() -> Vec<RationalPhase> {
        [
            integer(0),
            rat(1, 3),
            integer(1),
            integer(-2),
            rat(5, 7),
            rat(-9, 4),
        ]
        .into_iter()
        .map(|parameter| RationalPhase::new(parameter, 0))
        .collect()
    }

    /// The capacity form `⟨u, C v⟩`.
    fn capacity_pairing(ring: &Parametron, left: &[Rat], right: &[Rat]) -> Rat {
        dot(left, &ring.capacitance().unwrap().apply(right).unwrap())
    }

    /// Lean `split_exists_unique`, `split_orthogonal`: `d = r + e` with `r` in the mode space and
    /// `e` `C`-orthogonal to all of it; moving any mode between the parts breaks orthogonality, so
    /// the split is unique.
    #[test]
    fn the_split_is_unique_and_capacity_orthogonal() {
        let ring = chain();
        let stiffness = ring.stiffness().unwrap();
        let capacitance = ring.capacitance().unwrap();
        for (eigenvalue, modes) in [(1, 1), (2, 0), (3, 1), (5, 0)] {
            let operator = stiffness
                .subtract(&capacitance.scaled(&integer(eigenvalue)))
                .unwrap();
            for drive in [ints(&[2, 0]), ints(&[3, -1]), ints(&[0, 7])] {
                let split = resonance_split(&ring, &drive, &integer(eigenvalue)).unwrap();
                assert_eq!(split.mode_space().len(), modes);
                assert_eq!(add(split.resonating(), split.emanating()), drive);
                let residual = operator.apply(split.resonating()).unwrap();
                assert!(residual.iter().all(Zero::is_zero));
                for mode in split.mode_space() {
                    assert!(capacity_pairing(&ring, mode, split.emanating()).is_zero());
                    let moved = sub(split.emanating(), mode);
                    assert!(!capacity_pairing(&ring, mode, &moved).is_zero());
                }
            }
        }
    }

    /// Lean `effort_split`, `emanating_effort_eq_zero_iff`: the drive's effort is its emanating
    /// part's effort, and it vanishes exactly when the emanating part does.
    #[test]
    fn the_effort_is_the_emanating_effort() {
        let ring = chain();
        let operator = ring
            .stiffness()
            .unwrap()
            .subtract(&ring.capacitance().unwrap())
            .unwrap();
        for drive in [ints(&[2, 0]), ints(&[1, 1]), ints(&[-4, -4]), ints(&[0, 3])] {
            let split = resonance_split(&ring, &drive, &integer(1)).unwrap();
            assert_eq!(
                split.effort_amplitude(),
                operator.apply(split.emanating()).unwrap()
            );
            assert_eq!(
                split.rides(),
                split.effort_amplitude().iter().all(Zero::is_zero)
            );
        }
        assert!(
            resonance_split(&ring, &ints(&[1, 1]), &integer(1))
                .unwrap()
                .rides()
        );
        assert!(
            !resonance_split(&ring, &ints(&[2, 0]), &integer(1))
                .unwrap()
                .rides()
        );
    }

    /// Lean `reactive_split`: the work form of the emanating part is the drive's own
    /// `λ S_C(d) − S_K(d)`, and the effort pairs with the motion as `⟨d, (K − λC) d⟩ = −2 W`.
    #[test]
    fn the_work_form_sees_only_the_emanating_part() {
        let ring = chain();
        for eigenvalue in [1, 2, 3] {
            let eigenvalue = integer(eigenvalue);
            for drive in [ints(&[2, 0]), ints(&[5, -2]), ints(&[1, 1])] {
                let split = resonance_split(&ring, &drive, &eigenvalue).unwrap();
                let own = &eigenvalue * ring.storage(ring.capacity(), &drive).unwrap()
                    - ring.storage(ring.inverse_inductance(), &drive).unwrap();
                assert_eq!(split.work(), &own);
                assert_eq!(
                    dot(&drive, split.effort_amplitude()),
                    integer(-2) * split.work()
                );
            }
        }
    }

    /// Lean `holdingEffort_newton`, `hasDerivAt_modeEnergy`, `work_ledger`, read at rational clock
    /// phases `θ = ωt`: `cos θ` times the effort amplitude is Newton's residual `C ẍ + K x`, the
    /// stored energy changes by `sin²θ · W`, and its phase derivative is the port power formed
    /// from the effort and velocity vectors, `⟨f, dx/dθ⟩ = 2 sin θ cos θ · W`.
    #[test]
    fn the_held_motion_balances_energy_and_work() {
        let ring = chain();
        let (stiffness, capacitance) = (ring.stiffness().unwrap(), ring.capacitance().unwrap());
        for eigenvalue in [1, 2, 3] {
            let eigenvalue = integer(eigenvalue);
            for drive in [ints(&[2, 0]), ints(&[3, -1])] {
                let split = resonance_split(&ring, &drive, &eigenvalue).unwrap();
                let rest = ring
                    .mode_energy(&eigenvalue, &drive, &RationalPhase::new(integer(0), 0))
                    .unwrap();
                for phase in phases() {
                    let (cos, sin) = phase.chart();
                    let effort = scale(&cos, split.effort_amplitude());
                    let position = scale(&cos, &drive);
                    let acceleration = scale(&-(&eigenvalue * &cos), &drive);
                    assert_eq!(
                        effort,
                        add(
                            &capacitance.apply(&acceleration).unwrap(),
                            &stiffness.apply(&position).unwrap()
                        )
                    );
                    let energy = ring.mode_energy(&eigenvalue, &drive, &phase).unwrap();
                    assert_eq!(energy.total() - rest.total(), &sin * &sin * split.work());
                    let velocity = scale(&-sin.clone(), &drive);
                    assert_eq!(
                        dot(&effort, &velocity),
                        integer(2) * &sin * &cos * split.work()
                    );
                }
            }
        }
    }

    /// Lean `resonant_drive_rides`: a resonant increment of a mode is still a mode at the same
    /// frequency; it needs zero effort and exchanges no work, and its energy stays `λ S_C` at every
    /// phase.
    #[test]
    fn riding_is_free() {
        let ring = chain();
        let driven = add(&ints(&[1, 1]), &ints(&[2, 2]));
        let split = resonance_split(&ring, &driven, &integer(1)).unwrap();
        assert!(split.rides());
        assert!(ring.is_mode(&integer(1), &driven).unwrap());
        assert!(split.effort_amplitude().iter().all(Zero::is_zero));
        assert!(split.work().is_zero());
        let conserved = ring.storage(ring.capacity(), &driven).unwrap();
        for phase in phases() {
            let energy = ring.mode_energy(&integer(1), &driven, &phase).unwrap();
            assert_eq!(energy.total(), conserved);
        }
    }

    /// Lean `emanating_drive_needs_effort`, `founded_mode_energy_pos`: a nonzero emanating part
    /// needs a nonzero effort, unchanged by any resonating part; a mode's energy is positive.
    #[test]
    fn founding_needs_effort() {
        let ring = chain();
        for resonant in [ints(&[0, 0]), ints(&[1, 1]), ints(&[-3, -3])] {
            let drive = add(&resonant, &ints(&[1, -1]));
            let split = resonance_split(&ring, &drive, &integer(1)).unwrap();
            assert_eq!(split.emanating(), ints(&[1, -1]));
            assert!(!split.effort_amplitude().iter().all(Zero::is_zero));
            assert_eq!(
                split.effort_amplitude(),
                resonance_split(&ring, &ints(&[1, -1]), &integer(1))
                    .unwrap()
                    .effort_amplitude()
            );
        }
        let mode = ints(&[1, -1]);
        assert!(resonance_split(&ring, &mode, &integer(3)).unwrap().rides());
        for phase in phases() {
            let energy = ring.mode_energy(&integer(3), &mode, &phase).unwrap();
            assert!(energy.total() > Rat::zero());
        }
    }

    /// Lean `clamp_witness`: at `λ = 2` the chain has no mode, so `(2, 0)` is wholly emanating.
    /// Holding it needs the effort amplitude `(0, −2)` on a node that never moves, yet its work form
    /// is zero, so the port power vanishes at every phase and the energy stays `4`: effort is not
    /// work.
    #[test]
    fn the_clamp_holds_without_work() {
        let ring = chain();
        let drive = ints(&[2, 0]);
        let split = resonance_split(&ring, &drive, &integer(2)).unwrap();
        assert!(split.mode_space().is_empty());
        assert_eq!(split.emanating(), drive);
        assert_eq!(split.effort_amplitude(), ints(&[0, -2]));
        assert!(split.work().is_zero());
        for phase in phases() {
            let energy = ring.mode_energy(&integer(2), &drive, &phase).unwrap();
            assert_eq!(energy.total(), integer(4));
        }
    }

    /// Lean `work_witness`: at `λ = 1`, `(2, 0) = (1, 1) + (1, −1)`, resonating plus emanating, and
    /// the work form is `−2`: the energy exchanged over `[0, t]` is `−2 sin²(ωt)`.
    #[test]
    fn emanation_that_exchanges_work() {
        let ring = chain();
        let split = resonance_split(&ring, &ints(&[2, 0]), &integer(1)).unwrap();
        assert_eq!(split.resonating(), ints(&[1, 1]));
        assert_eq!(split.emanating(), ints(&[1, -1]));
        assert_eq!(split.work(), &integer(-2));
    }

    /// A node without capacitance makes `C` singular, and the split is refused; so is a drive of
    /// another extent.
    #[test]
    fn a_singular_capacity_is_refused() {
        let starved = Parametron::new(
            integer_matrix(&[&[1, 0], &[-1, 1], &[0, 1]]).unwrap(),
            ints(&[1, 0, 0]),
            ints(&[1, 1, 1]),
        )
        .unwrap();
        assert_eq!(
            resonance_split(&starved, &ints(&[1, 0]), &integer(1)),
            Err(CompressionError::SingularCapacity)
        );
        assert_eq!(
            resonance_split(&chain(), &ints(&[1, 2, 3]), &integer(1)),
            Err(CompressionError::Extent {
                what: "drive",
                expected: 2,
                found: 3
            })
        );
    }
}
