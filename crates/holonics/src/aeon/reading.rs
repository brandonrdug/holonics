//! **Clocks and their readings: elapsed time is a pairing.**
//!
//! [definition] Lean `Aeon/Clock/Reading` and `Aeon/Clock/Winding`. A receiver's [`Clock`] is a
//! closed 1-form of the parametric complex, valued in turns; its reading of an aeon is the sum
//! over the aeon's signed steps, `t_R(γ) = ⟨ω_R | γ⟩` ([`reading`]). A [`Reading`] is that sum
//! split into **whole windings** (the quotient) and **open phase** (the remainder in `[0, 1)`),
//! which is the ratio's division with remainder; readings add under concatenation with the carry
//! cocycle of [`crate::geometry::winding::carry`].
//!
//! Two clocks are provided. [`ClosedForm`] is a closed form on a [`FiniteComplex`], checked
//! around every two-cell; a [`Form`] that is not closed is read by [`Form::read`] but is not a
//! clock, because its readings are not homotopy-invariant (`nonclosed_form_is_not_homotopy_invariant`).
//! [`TorusClock`] is an integral class `Σ cᵢ dθᵢ` on the lift of the navigators' joint clock torus,
//! `θᵢ = xᵢ/dᵢ` in turns: closed because two navigators commute around every square, and whole on
//! every cycle because its class is integral (`torus_cycle_reads_whole_windings`).
//!
//! **No clock is privileged.** The rate of receiver `a` against receiver `b` is the undivided pair
//! of their two readings ([`rate`]); exchanging the receivers exchanges the pair, so a receiver
//! that reads nothing while the other reads time gives the admitted pole `(t_a : 0)`. Only the
//! undetermined `(0 : 0)`, where neither reads the aeon, is refused: it is projectively equal to
//! every pair and breaks transitivity (Lean `Aeon/Clock/Reading.Admitted`,
//! `undetermined_breaks_transitivity`).

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use crate::aeon::AeonError;
use crate::aeon::groupoid::{Aeon, ClockLift, FiniteComplex, LiftPassage, ParametricComplex};
use crate::geometry::winding::carry;
use crate::navigator::PhaseLift;
use crate::ratio::{Presentation, Rat};

/// [definition] **A clock** of a parametric complex: a closed 1-form, its value in turns on each
/// passage. Lean `Reading.Clock`. An implementation is closed by construction or by a checked
/// constructor; `None` is a passage outside the clock's domain.
pub trait Clock<K: ParametricComplex> {
    fn value(&self, passage: &K::Passage) -> Option<Rat>;
}

/// [definition] **Elapsed time is a pairing**: the reading `⟨ω_R | γ⟩` of an aeon by a clock, split
/// into windings and open phase. Lean `Reading.reading`, `Winding.reading_split`.
pub fn reading<K: ParametricComplex, C: Clock<K>>(
    clock: &C,
    aeon: &Aeon<K>,
) -> Result<Reading, AeonError> {
    let mut turns = Rat::zero();
    for (position, step) in aeon.steps().iter().enumerate() {
        let value = clock
            .value(&step.passage)
            .ok_or(AeonError::OutsideClock { position })?;
        if step.forward {
            turns += value;
        } else {
            turns -= value;
        }
    }
    Ok(Reading::of_turns(&turns))
}

/// [definition] **The rate** of receiver `a` against receiver `b` along an aeon: the undivided
/// pair `(t_a : t_b)`, one per two. Lean `Aeon/Clock/Reading.rate`, returned only when admitted
/// (`Aeon/Clock/Reading.Admitted`): refused exactly when neither receiver reads the aeon, the
/// undetermined `(0 : 0)`.
pub fn rate<K: ParametricComplex, A: Clock<K>, B: Clock<K>>(
    a: &A,
    b: &B,
    aeon: &Aeon<K>,
) -> Result<Presentation, AeonError> {
    let pair = Presentation::new(reading(a, aeon)?.turns(), reading(b, aeon)?.turns());
    if pair.is_degenerate() {
        return Err(AeonError::Undetermined);
    }
    Ok(pair)
}

/// [definition] **A reading**: whole windings `n` and open phase `r`, with `t = n + r` and
/// `0 ≤ r < 1`. Lean `Winding.windings`, `Winding.openPhase`; the split is unique
/// (`split_unique`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reading {
    windings: BigInt,
    phase: Rat,
}

impl Reading {
    /// The split of `t` turns: `n = ⌊t⌋`, `r = t − ⌊t⌋`. For `t = m/d` this is the division with
    /// remainder `m = d·n + d·r`, `0 ≤ d·r < d` (Lean `Winding.ratio_split`).
    pub fn of_turns(turns: &Rat) -> Self {
        let floor = turns.floor();
        Self {
            windings: floor.to_integer(),
            phase: turns - floor,
        }
    }

    /// Whole windings: the quotient, the carry a circle forgets and the lift retains.
    pub fn windings(&self) -> &BigInt {
        &self.windings
    }

    /// Open phase in turns: the remainder, in `[0, 1)`.
    pub fn phase(&self) -> &Rat {
        &self.phase
    }

    /// `n + r`.
    pub fn turns(&self) -> Rat {
        Rat::from_integer(self.windings.clone()) + &self.phase
    }

    /// Whether the open phase vanishes: a whole number of turns, the reading of a cycle by an
    /// integral clock. Lean `Winding.openPhase_eq_zero_iff`.
    pub fn is_whole(&self) -> bool {
        self.phase.is_zero()
    }

    /// **The carry** of two readings: the turn completed by adding their open phases, `0` or `1`.
    /// Over the common denominator `D` of the two phases it is the Odometer's carry
    /// `winding::carry(D, D·r, D·r')` (Lean `Winding.carry_of_microsteps`).
    pub fn carry(&self, other: &Self) -> BigUint {
        let denominator = self.phase.denom() * other.phase.denom();
        let micro = |phase: &Rat| {
            (phase * Rat::from_integer(denominator.clone()))
                .to_integer()
                .to_biguint()
                .expect("an open phase is nonnegative")
        };
        carry(
            &denominator
                .to_biguint()
                .expect("a reduced denominator is positive"),
            &micro(&self.phase),
            &micro(&other.phase),
        )
        .expect("a reduced denominator is not zero")
    }

    /// **Readings add with carry**: `windings(s + t) = windings s + windings t + carry(s, t)` and
    /// `phase(s + t) = phase s + phase t − carry(s, t)`. Lean `Winding.windings_add`,
    /// `openPhase_add`; along aeons, `aeon_windings_concat`.
    pub fn add(&self, other: &Self) -> Self {
        let carried = BigInt::from(self.carry(other));
        Self {
            windings: &self.windings + &other.windings + &carried,
            phase: &self.phase + &other.phase - Rat::from_integer(carried),
        }
    }

    /// **Each whole winding is one lossless jump** of a navigator's lifted phase: the lift counts
    /// the windings and its chart point is unchanged (Lean `Winding.jump_iterate`, over
    /// `Holon/Generator.LiftedPhase.jump`). The open phase stays with the reading: the carrier
    /// reads only the open phase (`carrier_reads_only_open_phase`).
    pub fn wind(&self, lift: &PhaseLift) -> PhaseLift {
        PhaseLift::new(lift.phase().clone(), lift.winding() + &self.windings)
    }
}

// ---------------------------------------------------------------------------------------------
// Forms on a finite complex
// ---------------------------------------------------------------------------------------------

/// [definition] **A 1-form** on a finite parametric complex: one value in turns per passage, not
/// necessarily closed (Lean `E → A`; `HodgeTime`'s time form).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Form {
    values: Vec<Rat>,
}

impl Form {
    pub fn new(values: Vec<Rat>) -> Self {
        Self { values }
    }

    pub fn values(&self) -> &[Rat] {
        &self.values
    }

    /// [definition] **The reading of an aeon** by any form: the sum over its signed steps. Lean
    /// `wordReading`; it is the pairing with the aeon's chain, `⟨ω | chainOf γ⟩`
    /// (`wordReading_eq_dotProduct`, the bridge to `HodgeTime.reading`).
    pub fn read(&self, aeon: &Aeon<FiniteComplex>) -> Result<Rat, AeonError> {
        let mut turns = Rat::zero();
        for (position, step) in aeon.steps().iter().enumerate() {
            let value = self
                .values
                .get(step.passage)
                .ok_or(AeonError::OutsideClock { position })?;
            if step.forward {
                turns += value;
            } else {
                turns -= value;
            }
        }
        Ok(turns)
    }

    /// [definition] **The curvature** `d₁ω`: the form's reading around each two-cell. The form is
    /// closed exactly when every entry vanishes (Lean `IsClosed`).
    pub fn curvature(&self, complex: &FiniteComplex) -> Result<Vec<Rat>, AeonError> {
        self.check_extent(complex)?;
        (0..complex.two_cells())
            .map(|cell| {
                let (base, word) = complex.cell(&cell).ok_or(AeonError::NotACell)?;
                self.read(&Aeon::new(complex, base, word)?)
            })
            .collect()
    }

    fn check_extent(&self, complex: &FiniteComplex) -> Result<(), AeonError> {
        if self.values.len() != complex.passages() {
            return Err(AeonError::Shape {
                what: "form values (one per passage)",
                expected: complex.passages(),
                found: self.values.len(),
            });
        }
        Ok(())
    }
}

/// [definition] **A closed form**: a clock of a finite complex. Lean `Reading.Clock`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosedForm {
    form: Form,
}

impl ClosedForm {
    /// The form as a clock, refused at the first two-cell it reads nonzero around.
    pub fn new(complex: &FiniteComplex, form: Form) -> Result<Self, AeonError> {
        for (cell, reading) in form.curvature(complex)?.into_iter().enumerate() {
            if !reading.is_zero() {
                return Err(AeonError::NotClosed { cell, reading });
            }
        }
        Ok(Self { form })
    }

    pub fn form(&self) -> &Form {
        &self.form
    }
}

impl Clock<FiniteComplex> for ClosedForm {
    fn value(&self, passage: &usize) -> Option<Rat> {
        self.form.values.get(*passage).cloned()
    }
}

// ---------------------------------------------------------------------------------------------
// The clock of the joint clock torus
// ---------------------------------------------------------------------------------------------

/// [definition] **A receiver's clock on the joint clock torus**: the integral class
/// `Σᵢ cᵢ dθᵢ`, `θᵢ = xᵢ/dᵢ` in turns of navigator `i`'s ring. It reads `cᵢ/dᵢ` turns per
/// micro-step of navigator `i`. Lean `Winding.navigatorClock` read in turns (`turns`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TorusClock {
    periods: Vec<BigUint>,
    coefficients: Vec<BigInt>,
}

impl TorusClock {
    /// The class `Σ cᵢ dθᵢ` on a lift, one integer coefficient per navigator.
    pub fn new(lift: &ClockLift, coefficients: Vec<BigInt>) -> Result<Self, AeonError> {
        if coefficients.len() != lift.navigators() {
            return Err(AeonError::Shape {
                what: "clock coefficients (one per navigator)",
                expected: lift.navigators(),
                found: coefficients.len(),
            });
        }
        Ok(Self {
            periods: lift.periods().to_vec(),
            coefficients,
        })
    }

    /// Navigator `navigator`'s own clock `dθᵢ`: one turn per turn of its ring.
    pub fn navigator(lift: &ClockLift, navigator: usize) -> Result<Self, AeonError> {
        if navigator >= lift.navigators() {
            return Err(AeonError::Shape {
                what: "navigator index",
                expected: lift.navigators(),
                found: navigator,
            });
        }
        let coefficients = (0..lift.navigators())
            .map(|index| {
                if index == navigator {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }
            })
            .collect();
        Self::new(lift, coefficients)
    }
}

impl Clock<ClockLift> for TorusClock {
    fn value(&self, passage: &LiftPassage) -> Option<Rat> {
        let coefficient = self.coefficients.get(passage.navigator)?;
        let period = self.periods.get(passage.navigator)?;
        Some(Rat::new(coefficient.clone(), BigInt::from(period.clone())))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aeon::groupoid::{Cycle, LiftSquare, Step};
    use crate::geometry::complex::CellComplex;
    use crate::geometry::screw::RationalPhase;
    use crate::geometry::winding::{phase as ring_phase, winding};
    use crate::ratio::linear::vector::{integer_matrix, ints};
    use crate::ratio::{integer, rat};

    fn lattice(values: &[i64]) -> Vec<BigInt> {
        values.iter().map(|value| BigInt::from(*value)).collect()
    }

    /// The triangle `0→1→2→0` filled by one face (Lean `Reading.filledTriangle`) with the hollow
    /// triangle `2→3→0` beside it sharing the passage `2→0`.
    fn filled_and_hollow() -> FiniteComplex {
        // Passages: 0: 0→1, 1: 1→2, 2: 2→0, 3: 2→3, 4: 3→0.
        let boundary_one = integer_matrix(&[
            &[-1, 0, 1, 0, 1],
            &[1, -1, 0, 0, 0],
            &[0, 1, -1, -1, 0],
            &[0, 0, 0, 1, -1],
        ])
        .unwrap();
        let boundary_two = integer_matrix(&[&[1], &[1], &[1], &[0], &[0]]).unwrap();
        FiniteComplex::new(
            CellComplex::new(vec![4, 5, 1], vec![boundary_one, boundary_two]).unwrap(),
            vec![(0, vec![Step::along(0), Step::along(1), Step::along(2)])],
        )
        .unwrap()
    }

    fn filled_triangle() -> FiniteComplex {
        let boundary_one = integer_matrix(&[&[-1, 0, 1], &[1, -1, 0], &[0, 1, -1]]).unwrap();
        let boundary_two = integer_matrix(&[&[1], &[1], &[1]]).unwrap();
        FiniteComplex::new(
            CellComplex::new(vec![3, 3, 1], vec![boundary_one, boundary_two]).unwrap(),
            vec![(0, vec![Step::along(0), Step::along(1), Step::along(2)])],
        )
        .unwrap()
    }

    /// **The clock is a representation of the aeon groupoid** in `(ℚ, +)`: readings add under
    /// concatenation, reversal negates, rest reads zero. Lean `Reading.reading_concat`,
    /// `reading_reverse`, `reading_rest` (`classReading_comp`, `classReading_inv`).
    #[test]
    fn the_clock_is_a_representation_of_the_aeon_groupoid() {
        let lift = ClockLift::new(vec![BigUint::from(3u32), BigUint::from(5u32)]).unwrap();
        let clock = TorusClock::new(&lift, lattice(&[2, -1])).unwrap();
        let gamma = lift
            .walk(
                lattice(&[1, 4]),
                &[(0, true), (1, true), (1, true), (0, false)],
            )
            .unwrap();
        let delta = lift
            .walk(gamma.end().clone(), &[(0, true), (0, true), (1, false)])
            .unwrap();
        let joined = reading(&clock, &gamma.concat(&delta).unwrap()).unwrap();
        assert_eq!(
            joined.turns(),
            reading(&clock, &gamma).unwrap().turns() + reading(&clock, &delta).unwrap().turns()
        );
        assert_eq!(
            reading(&clock, &gamma.reverse()).unwrap().turns(),
            -reading(&clock, &gamma).unwrap().turns()
        );
        assert_eq!(
            reading(&clock, &Aeon::rest(lattice(&[1, 4])))
                .unwrap()
                .turns(),
            Rat::zero()
        );
    }

    /// **The split is the ratio's division with remainder.** For `m` micro-steps of a `d`-step
    /// ring, `m = d·windings + d·phase` with `0 ≤ d·phase < d`, and for `m ≥ 0` these are the
    /// Odometer's `winding` and `phase`. Lean `Winding.ratio_split`, `windings_of_microsteps`,
    /// `openPhase_of_microsteps`, `split_unique`.
    #[test]
    fn the_split_is_the_division_with_remainder() {
        for d in 1i64..=6 {
            for m in -20i64..=20 {
                let split = Reading::of_turns(&rat(m, d));
                let remainder = split.phase() * integer(d);
                assert!(remainder.is_integer() && remainder >= Rat::zero());
                assert!(remainder < integer(d));
                assert_eq!(
                    Rat::from_integer(split.windings() * BigInt::from(d)) + &remainder,
                    integer(m)
                );
                if m >= 0 {
                    let (dd, mm) = (BigUint::from(d as u64), BigUint::from(m as u64));
                    assert_eq!(split.windings(), &BigInt::from(winding(&dd, &mm).unwrap()));
                    assert_eq!(
                        remainder,
                        Rat::from_integer(BigInt::from(ring_phase(&dd, &mm).unwrap()))
                    );
                }
            }
        }
    }

    /// **Readings add with the carry cocycle**: the whole windings of a concatenated aeon are the
    /// sum plus the Odometer's carry of the two open phases, the carry is one turn or none, and it
    /// is a cocycle. Lean `Winding.aeon_windings_concat`, `windings_add`, `carry_le_one`,
    /// `carry_cocycle`, `carry_of_microsteps`.
    #[test]
    fn readings_add_with_the_carry_cocycle() {
        let lift = ClockLift::new(vec![BigUint::from(4u32)]).unwrap();
        let clock = TorusClock::navigator(&lift, 0).unwrap();
        let forward = |from: i64, count: usize| {
            lift.walk(lattice(&[from]), &vec![(0, true); count])
                .unwrap()
        };
        for a in 0..9 {
            for b in 0..9 {
                let gamma = forward(0, a);
                let delta = forward(a as i64, b);
                let (s, t) = (
                    reading(&clock, &gamma).unwrap(),
                    reading(&clock, &delta).unwrap(),
                );
                let joined = reading(&clock, &gamma.concat(&delta).unwrap()).unwrap();
                assert_eq!(joined, s.add(&t));
                assert_eq!(
                    joined.windings(),
                    &(s.windings() + t.windings() + BigInt::from(s.carry(&t)))
                );
                assert!(s.carry(&t) <= BigUint::one());
                let four = BigUint::from(4u32);
                assert_eq!(
                    s.carry(&t),
                    carry(&four, &BigUint::from(a), &BigUint::from(b)).unwrap()
                );
                for c in [rat(1, 3), rat(5, 7), rat(-2, 9)] {
                    let u = Reading::of_turns(&c);
                    assert_eq!(
                        s.carry(&t) + s.add(&t).carry(&u),
                        t.carry(&u) + s.carry(&t.add(&u))
                    );
                }
            }
        }
    }

    /// **Homotopy invariance.** A closed clock reads the two sides of every elementary move alike
    /// — a backtrack or a two-cell boundary in either orientation — on a finite complex and on the
    /// lift, where the square is two navigators commuting. Lean `Reading.reading_homotopy_invariant`,
    /// `wordReading_move`, `Winding.clockLift_wellFormed`.
    #[test]
    fn a_closed_clock_reads_homotopic_aeons_alike() {
        let complex = filled_and_hollow();
        let clock = ClosedForm::new(&complex, Form::new(ints(&[1, 2, -3, 5, -2]))).unwrap();
        let loop_b = Aeon::new(
            &complex,
            2,
            vec![Step::along(3), Step::along(4), Step::against(2)],
        )
        .unwrap();
        // The face sits at occurrence 0, which the loop reaches after two steps.
        let moved = loop_b
            .with_cell(&complex, 2, &0, false)
            .unwrap()
            .with_backtrack(&complex, 0, Step::against(1))
            .unwrap();
        assert_ne!(moved, loop_b);
        assert_eq!(
            reading(&clock, &moved).unwrap(),
            reading(&clock, &loop_b).unwrap()
        );

        let lift = ClockLift::new(vec![BigUint::from(3u32), BigUint::from(2u32)]).unwrap();
        let torus = TorusClock::new(&lift, lattice(&[1, 1])).unwrap();
        let gamma = lift
            .walk(lattice(&[0, 0]), &[(0, true), (1, true)])
            .unwrap();
        let square = LiftSquare {
            base: lattice(&[1, 1]),
            first: 1,
            second: 0,
        };
        let moved = gamma.with_cell(&lift, 2, &square, true).unwrap();
        assert_eq!(
            reading(&torus, &moved).unwrap(),
            reading(&torus, &gamma).unwrap()
        );
    }

    /// [counterexample] **A non-closed form is not a clock.** On the filled triangle the form
    /// reading `1` on one passage is refused as a clock; the boundary loop is homotopic to rest by
    /// one face move, yet the form reads it `1` against rest's `0`. Lean
    /// `Reading.nonclosed_form_is_not_homotopy_invariant`.
    #[test]
    fn a_nonclosed_form_is_not_homotopy_invariant() {
        let triangle = filled_triangle();
        let tick = Form::new(ints(&[1, 0, 0]));
        assert_eq!(
            ClosedForm::new(&triangle, tick.clone()),
            Err(AeonError::NotClosed {
                cell: 0,
                reading: integer(1)
            })
        );
        let rest = Aeon::rest(0);
        let loop_aeon = rest.with_cell(&triangle, 0, &0, true).unwrap();
        assert_eq!(tick.read(&rest).unwrap(), Rat::zero());
        assert_eq!(tick.read(&loop_aeon).unwrap(), integer(1));
    }

    /// **A cycle's reading factors through homology**: it is the pairing of the clock with the
    /// cycle's chain, the chain is a cycle (`∂₁ chain = 0`), and cycles whose chains differ by a
    /// cell boundary read alike. Lean `Reading.cycle_reading_factors_through_homology`,
    /// `chainOf_mem_cycles`, `homologous_cycles_read_alike`, `wordReading_eq_dotProduct`.
    #[test]
    fn a_cycle_reading_factors_through_homology() {
        let complex = filled_and_hollow();
        let clock = ClosedForm::new(&complex, Form::new(ints(&[1, 2, -3, 5, -2]))).unwrap();
        let loop_b = Aeon::new(
            &complex,
            2,
            vec![Step::along(3), Step::along(4), Step::against(2)],
        )
        .unwrap();
        let through_face = Aeon::new(
            &complex,
            0,
            vec![
                Step::along(0),
                Step::along(1),
                Step::along(3),
                Step::along(4),
            ],
        )
        .unwrap();
        let (chain_b, chain_face) = (complex.chain(&loop_b), complex.chain(&through_face));
        let boundary_one = complex.cell_complex().boundary(1).unwrap();
        assert!(
            boundary_one
                .apply(&chain_b)
                .unwrap()
                .iter()
                .all(Zero::is_zero)
        );
        let pairing = |chain: &[Rat]| {
            chain
                .iter()
                .zip(clock.form().values())
                .fold(Rat::zero(), |sum, (c, w)| sum + c * w)
        };
        assert_eq!(reading(&clock, &loop_b).unwrap().turns(), pairing(&chain_b));
        // chain(through_face) = chain(loop_b) + ∂₂·(1): homologous.
        let boundary_two = complex.cell_complex().boundary(2).unwrap();
        let cell = boundary_two.apply(&ints(&[1])).unwrap();
        assert!(
            chain_face
                .iter()
                .zip(chain_b.iter().zip(&cell))
                .all(|(face, (b, c))| face == &(b + c))
        );
        assert_eq!(
            reading(&clock, &through_face).unwrap(),
            reading(&clock, &loop_b).unwrap()
        );
    }

    /// **A torus cycle reads whole windings, and the lift retains what the torus forgets.** Three
    /// micro-steps of a three-step ring and rest close at one torus point, reading one and zero
    /// turns; an aeon that does not close is not a cycle; each whole winding is one lossless jump
    /// of the navigator's lifted phase. Lean `Winding.torus_cycle_reads_whole_windings`,
    /// `lift_retains_winding`, `torus_closes_iff`, `jump_iterate`.
    #[test]
    fn a_torus_cycle_reads_whole_windings_and_the_lift_retains_them() {
        let clocks = [
            crate::navigator::Clock::ring(integer(1), 3).unwrap(),
            crate::navigator::Clock::ring(rat(1, 2), 2).unwrap(),
        ];
        let lift = ClockLift::of_clocks(&clocks);
        let first = TorusClock::navigator(&lift, 0).unwrap();
        let class = TorusClock::new(&lift, lattice(&[2, -3])).unwrap();
        let turn = lift.walk(lattice(&[0, 0]), &[(0, true); 3]).unwrap();
        let rest = Aeon::<ClockLift>::rest(lattice(&[0, 0]));
        assert_eq!(lift.torus_point(turn.end()), lift.torus_point(rest.end()));
        assert_eq!(
            reading(&first, &turn).unwrap(),
            Reading::of_turns(&integer(1))
        );
        assert_eq!(
            reading(&first, &rest).unwrap(),
            Reading::of_turns(&integer(0))
        );
        let joint = lift
            .walk(
                lattice(&[1, 0]),
                &[
                    (0, true),
                    (1, true),
                    (0, true),
                    (1, false),
                    (0, false),
                    (0, true),
                    (0, true),
                    (1, true),
                    (1, true),
                ],
            )
            .unwrap();
        let cycle = Cycle::close(&lift, joint.clone()).unwrap();
        let read = reading(&class, cycle.aeon()).unwrap();
        // Displacement (3, 2) on periods (3, 2): 2·(3/3) − 3·(2/2) = −1 whole turn.
        assert!(read.is_whole());
        assert_eq!(read.windings(), &BigInt::from(-1));
        let open = lift.walk(lattice(&[0, 0]), &[(0, true)]).unwrap();
        assert!(matches!(
            Cycle::close(&lift, open),
            Err(AeonError::NotACycle)
        ));
        let lifted = PhaseLift::new(RationalPhase::new(rat(1, 3), 0), BigInt::from(5));
        let wound = reading(&first, &turn).unwrap().wind(&lifted);
        assert_eq!(wound.winding(), &BigInt::from(6));
        assert_eq!(wound.chart(), lifted.chart());
    }

    /// **No clock is privileged.** The rate is the undivided pair of two readings; exchanging the
    /// receivers exchanges the pair, the pole `(t_a : 0)` included; composing through a third clock
    /// is exactly the direct rate scaled by that clock's reading, projectively the direct rate when
    /// it reads the aeon and the undetermined `(0 : 0)` when it does not; a cycle repeated `m ≥ 1`
    /// times keeps its rate's class; `(0 : 0)` is refused. Lean `Aeon/Clock/Reading.rate_swap`,
    /// `rate_through`, `rate_through_projectivelyEq`, `rate_through_zero`, `rate_iterate`,
    /// `Admitted`.
    #[test]
    fn the_rate_is_the_undivided_pair_of_two_readings() {
        let complex = filled_and_hollow();
        let clock = |values: &[i64]| ClosedForm::new(&complex, Form::new(ints(values))).unwrap();
        let (a, b, c) = (
            clock(&[1, 2, -3, 5, -2]),
            clock(&[0, 0, 0, 1, 0]),
            clock(&[1, -1, 0, 1, 1]),
        );
        let gamma = Aeon::new(
            &complex,
            0,
            vec![Step::along(0), Step::along(1), Step::along(3)],
        )
        .unwrap();
        let ab = rate(&a, &b, &gamma).unwrap();
        let ba = rate(&b, &a, &gamma).unwrap();
        assert_eq!(
            (ba.numerator(), ba.denominator()),
            (ab.denominator(), ab.numerator())
        );
        let bc = rate(&b, &c, &gamma).unwrap();
        let ac = rate(&a, &c, &gamma).unwrap();
        let through = Presentation::new(
            ab.numerator() * bc.numerator(),
            ab.denominator() * bc.denominator(),
        );
        assert_eq!(through, ac.scaled(&reading(&b, &gamma).unwrap().turns()));
        assert!(through.projectively_equal(&ac));
        let loop_b = Aeon::new(
            &complex,
            2,
            vec![Step::along(3), Step::along(4), Step::against(2)],
        )
        .unwrap();
        for times in 1..4 {
            let repeated = rate(&a, &c, &loop_b.repeated(times).unwrap()).unwrap();
            assert_eq!(
                repeated,
                rate(&a, &c, &loop_b)
                    .unwrap()
                    .scaled(&integer(times as i64))
            );
        }
        let before_the_cut = Aeon::new(&complex, 0, vec![Step::along(0)]).unwrap();
        let pole = rate(&a, &b, &before_the_cut).unwrap();
        assert_eq!(pole, Presentation::new(integer(1), integer(0)));
        assert_eq!(
            rate(&b, &a, &before_the_cut).unwrap(),
            Presentation::new(integer(0), integer(1))
        );
        assert!(
            pole.follow(&rate(&b, &c, &before_the_cut).unwrap())
                .is_degenerate()
        );
        assert_eq!(rate(&a, &b, &Aeon::rest(0)), Err(AeonError::Undetermined));
    }
}
