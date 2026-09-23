//! **Generators `G`: transport, initial configuration, clock and phase lift.**
//!
//! [definition] A generator is a transport with an **initial configuration** (the key) and its own
//! clock. Its phase is lifted, `θ̃ = θ + 2πn` (`Holon/Generator.lean::LiftedPhase`, chart
//! `Holon/Generator.lean::LiftedPhase.chart`); the clock jump at a section crossing
//! (`Holon/Generator.lean::LiftedPhase.jump`) advances the winding by one and leaves the chart
//! phase unchanged, so every storage read through the chart is unchanged
//! (`Holon/Generator.lean::jump_lossless`) while the lift retains the turn
//! (`Holon/Generator.lean::jump_carries_winding`). Jump counts are carries and compose as a cocycle
//! (`Holon/Generator.lean::jumps_are_carries`, over `Geometry/PhaseCarry.lean::winding_add`,
//! `Geometry/PhaseCarry.lean::carry_cocycle`, `Geometry/PhaseCarry.lean::carry_le_one`); a rational
//! clock passage jumps losslessly (`Holon/Generator.lean::clockPassage_jumps_lossless`).
//!
//! [definition; agent-inferred] Exact charts. The phase is `relational_geometry::RationalPhase`, the
//! Cayley half-angle chart (a point of the rational unit circle), and the winding is a `BigInt`; no
//! real angle is formed. The clock's ticks run on `relational_geometry::winding::Odometer`, whose
//! overflow is the counted jump population. The transport is the flow generator `ẋ = A x + b`
//! ([`Transport::Linear`], [`Transport::Affine`], or a screw `ω × x + v` through
//! `relational_geometry::ScrewGenerator`); one clock tick is its Cayley (implicit-midpoint) step
//! `(I − hA/2) x⁺ = (I + hA/2) x + h b`, which is the exact rational stepping of the Holon law
//! (`Holon/Element.lean::midpoint_balance` with `J = A` skew, `R = 0`, `Q = I`) and is norm
//! preserving for a skew `A` with `b = 0`.
//!
//! | Lean | Rust |
//! |---|---|
//! | `LiftedPhase`, `LiftedPhase.chart`, `LiftedPhase.jump` | [`PhaseLift`] |
//! | `jump_lossless`, `jump_carries_winding` | [`PhaseLift::jump`], [`PhaseLift::jump_is_lossless`] |
//! | `jumps_are_carries`, `clockPassage_jumps_lossless` | [`Clock::advance`], [`jump_cocycle`] |

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::{
    Odometer, Rat, RatVec3, RationalPhase, ScrewGenerator, SituatedScrew, carry, winding,
};

use crate::exact_linear::ExactRatMatrix;
use crate::holon::HolonError;
use crate::scalar::{add, at, matrix, rat, scale};

/// [definition] **A clock**: a positive step `h` per tick and a tick odometer whose overflow is the
/// jump (section-crossing) count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clock {
    step: Rat,
    ticks: Odometer,
}

impl Clock {
    /// A clock of step `h > 0` ticking on a ring of `radices` levels (the last level's overflow is
    /// the jump count). Refuses a nonpositive step or a degenerate radix.
    pub fn new(step: Rat, radices: Vec<BigUint>) -> Result<Self, HolonError> {
        if step <= Rat::zero() {
            return Err(HolonError::NonpositiveStep);
        }
        Ok(Self {
            step,
            ticks: Odometer::new(radices)?,
        })
    }

    /// A clock of step `h` on one ring of `period ≥ 2` ticks.
    pub fn ring(step: Rat, period: u64) -> Result<Self, HolonError> {
        Self::new(step, vec![BigUint::from(period)])
    }

    /// [definition] **An unwound clock**: step `h` and no ring level. Its odometer has no phase
    /// digit, so every tick is one counted passage and the winding is the tick count itself. It
    /// is the core chart of a declared duration clock, which claims no closure; a ring (a period)
    /// is a separate claim supplied through [`Self::new`] or [`Self::ring`].
    pub fn unwound(step: Rat) -> Result<Self, HolonError> {
        Self::new(step, Vec::new())
    }

    pub fn step(&self) -> &Rat {
        &self.step
    }

    /// The ring levels (empty for an unwound clock).
    pub fn radices(&self) -> &[BigUint] {
        self.ticks.radices()
    }

    /// The tick odometer itself.
    pub fn odometer(&self) -> &Odometer {
        &self.ticks
    }

    /// The ticks taken since rest: the odometer's value `Σ digits·radices + winding·Π radices`
    /// (`Geometry/PhaseCarry.lean::value_digits`).
    pub fn ticks(&self) -> BigUint {
        self.ticks.value()
    }

    /// The elapsed declared duration `h · ticks`.
    pub fn elapsed(&self) -> Rat {
        &self.step * Rat::from_integer(BigInt::from(self.ticks()))
    }

    /// Whether no tick has been taken.
    pub fn is_at_rest(&self) -> bool {
        self.ticks().is_zero()
    }

    /// The tick digits (the chart of the clock phase).
    pub fn phase(&self) -> &[BigUint] {
        self.ticks.digits()
    }

    /// The jumps counted so far.
    pub fn winding(&self) -> &BigUint {
        self.ticks.overflow_winding()
    }

    /// Advance by `ticks`; returns the number of jumps this advance made
    /// (`Holon/Generator.lean::jumps_are_carries`). Cost is independent of `ticks`' magnitude.
    pub fn advance(&mut self, ticks: &BigUint) -> BigUint {
        let before = self.ticks.overflow_winding().clone();
        self.ticks.advance(ticks);
        self.ticks.overflow_winding() - before
    }
}

/// [proved-derived; implemented-exact] **Jump counts compose as a cocycle** on a ring of period
/// `n` (`Holon/Generator.lean::jumps_are_carries`): returns whether
/// `winding(a+b) = winding a + winding b + carry(a,b)`, the carry cocycle identity for `(a, b, c)`
/// and `carry(a,b) ≤ 1` all hold.
pub fn jump_cocycle(
    period: &BigUint,
    a: &BigUint,
    b: &BigUint,
    c: &BigUint,
) -> Result<bool, HolonError> {
    let additive = winding(period, &(a + b))?
        == winding(period, a)? + winding(period, b)? + carry(period, a, b)?;
    let cocycle = carry(period, a, b)? + carry(period, &(a + b), c)?
        == carry(period, b, c)? + carry(period, a, &(b + c))?;
    let bounded = carry(period, a, b)? <= BigUint::one();
    Ok(additive && cocycle && bounded)
}

/// [definition] **A lifted phase** (`Holon/Generator.lean::LiftedPhase`): the Cayley chart phase and
/// the winding it has counted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhaseLift {
    phase: RationalPhase,
    winding: BigInt,
}

impl PhaseLift {
    pub fn new(phase: RationalPhase, winding: BigInt) -> Self {
        Self { phase, winding }
    }

    pub fn phase(&self) -> &RationalPhase {
        &self.phase
    }

    pub fn winding(&self) -> &BigInt {
        &self.winding
    }

    /// The chart point `(cos θ, sin θ)` on the rational unit circle
    /// (`Holon/Generator.lean::LiftedPhase.chart`).
    pub fn chart(&self) -> (Rat, Rat) {
        self.phase.chart()
    }

    /// **The clock jump** (`Holon/Generator.lean::LiftedPhase.jump`): a full turn is counted.
    pub fn jump(&self) -> Self {
        Self {
            phase: self.phase.clone(),
            winding: &self.winding + BigInt::one(),
        }
    }

    /// `k` jumps at once.
    pub fn jumps(&self, count: &BigUint) -> Self {
        Self {
            phase: self.phase.clone(),
            winding: &self.winding + BigInt::from(count.clone()),
        }
    }

    /// [proved-derived; implemented-exact] **The jump is lossless** for a storage read through the
    /// chart (`Holon/Generator.lean::jump_lossless`), carries winding and yields a new lifted state
    /// (`Holon/Generator.lean::jump_carries_winding`).
    pub fn jump_is_lossless(&self, storage: impl Fn(&(Rat, Rat)) -> Rat) -> bool {
        let jumped = self.jump();
        storage(&jumped.chart()) == storage(&self.chart())
            && jumped.winding == &self.winding + BigInt::one()
            && jumped.chart() == self.chart()
            && jumped != *self
    }
}

/// [definition] **The transport of a generator** as the flow generator `ẋ = A x + b`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Transport {
    Linear(ExactRatMatrix),
    Affine {
        linear: ExactRatMatrix,
        translation: Vec<Rat>,
    },
    /// `ω × x + v`, through `relational_geometry::ScrewGenerator` (boxed: six exact rationals).
    Screw(Box<ScrewGenerator>),
}

impl Transport {
    /// The configuration dimension.
    pub fn dimension(&self) -> usize {
        match self {
            Self::Linear(a) | Self::Affine { linear: a, .. } => a.rows(),
            Self::Screw(_) => 3,
        }
    }

    /// `(A, b)` with `ẋ = A x + b`; a screw gives `A = hat(ω)`, `b = v`.
    pub fn affine_parts(&self) -> Result<(ExactRatMatrix, Vec<Rat>), HolonError> {
        match self {
            Self::Linear(a) => {
                check_square(a)?;
                Ok((a.clone(), crate::scalar::zeros(a.rows())))
            }
            Self::Affine {
                linear,
                translation,
            } => {
                check_square(linear)?;
                if translation.len() != linear.rows() {
                    return Err(HolonError::Shape {
                        what: "affine translation",
                        expected: linear.rows(),
                        found: translation.len(),
                    });
                }
                Ok((linear.clone(), translation.clone()))
            }
            Self::Screw(screw) => {
                let w = screw.angular();
                let hat = matrix(3, 3, |row, column| match (row, column) {
                    (0, 1) => -w.z.clone(),
                    (0, 2) => w.y.clone(),
                    (1, 0) => w.z.clone(),
                    (1, 2) => -w.x.clone(),
                    (2, 0) => -w.y.clone(),
                    (2, 1) => w.x.clone(),
                    _ => Rat::zero(),
                })?;
                let v = screw.advance();
                Ok((hat, vec![v.x.clone(), v.y.clone(), v.z.clone()]))
            }
        }
    }

    /// The generator's velocity `A x + b` at a configuration.
    pub fn velocity(&self, configuration: &[Rat]) -> Result<Vec<Rat>, HolonError> {
        let (a, b) = self.affine_parts()?;
        Ok(add(&a.apply(configuration)?, &b))
    }
}

fn check_square(a: &ExactRatMatrix) -> Result<(), HolonError> {
    if a.is_square() {
        Ok(())
    } else {
        Err(HolonError::Shape {
            what: "square transport",
            expected: a.rows(),
            found: a.columns(),
        })
    }
}

/// [definition] **A generator**: transport, initial configuration, clock and phase lift.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Generator {
    transport: Transport,
    initial: Vec<Rat>,
    clock: Clock,
    lift: PhaseLift,
}

/// One generator advance: the configuration reached and the jumps the clock counted. No
/// intermediate configuration is retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratorAdvance {
    pub configuration: Vec<Rat>,
    pub jumps: BigUint,
}

impl Generator {
    pub fn new(
        transport: Transport,
        initial: Vec<Rat>,
        clock: Clock,
        lift: PhaseLift,
    ) -> Result<Self, HolonError> {
        transport.affine_parts()?;
        if initial.len() != transport.dimension() {
            return Err(HolonError::Shape {
                what: "initial configuration",
                expected: transport.dimension(),
                found: initial.len(),
            });
        }
        Ok(Self {
            transport,
            initial,
            clock,
            lift,
        })
    }

    /// A screw generator with its situated initial point.
    pub fn screw(
        situated: &SituatedScrew,
        clock: Clock,
        lift: PhaseLift,
    ) -> Result<Self, HolonError> {
        let p = situated.initial();
        Self::new(
            Transport::Screw(Box::new(situated.generator().clone())),
            vec![p.x.clone(), p.y.clone(), p.z.clone()],
            clock,
            lift,
        )
    }

    /// The situated screw, when the transport is a screw.
    pub fn situated_screw(&self) -> Option<SituatedScrew> {
        match &self.transport {
            Transport::Screw(generator) => Some(SituatedScrew::new(
                generator.as_ref().clone(),
                RatVec3::new(
                    self.initial[0].clone(),
                    self.initial[1].clone(),
                    self.initial[2].clone(),
                ),
            )),
            _ => None,
        }
    }

    pub fn transport(&self) -> &Transport {
        &self.transport
    }

    /// The initial configuration: the key.
    pub fn initial(&self) -> &[Rat] {
        &self.initial
    }

    pub fn clock(&self) -> &Clock {
        &self.clock
    }

    pub fn lift(&self) -> &PhaseLift {
        &self.lift
    }

    /// **One Cayley tick** `(I − hA/2) x⁺ = (I + hA/2) x + h b`, exact. Refuses a singular left
    /// side (the step meets an eigenvalue `2/h` of `A`).
    pub fn tick(&self, configuration: &[Rat]) -> Result<Vec<Rat>, HolonError> {
        let (a, b) = self.transport.affine_parts()?;
        let n = a.rows();
        if configuration.len() != n {
            return Err(HolonError::Shape {
                what: "configuration",
                expected: n,
                found: configuration.len(),
            });
        }
        let half_step = self.clock.step() * rat(1, 2);
        let left = matrix(n, n, |row, column| {
            let identity = if row == column {
                Rat::one()
            } else {
                Rat::zero()
            };
            identity - &half_step * at(&a, row, column)
        })?;
        let right = add(
            &add(configuration, &scale(&half_step, &a.apply(configuration)?)),
            &scale(self.clock.step(), &b),
        );
        match left.preimage_fibre(&right)? {
            Some((particular, kernel)) if kernel.is_empty() => Ok(particular),
            _ => Err(HolonError::Singular {
                what: "Cayley tick",
            }),
        }
    }

    /// Advance `ticks` Cayley ticks from `configuration`, counting the clock's jumps into the
    /// winding of the phase lift. Only the reached configuration is returned.
    pub fn advance(
        &mut self,
        configuration: &[Rat],
        ticks: u64,
    ) -> Result<GeneratorAdvance, HolonError> {
        let mut current = configuration.to_vec();
        for _ in 0..ticks {
            current = self.tick(&current)?;
        }
        let jumps = self.clock.advance(&BigUint::from(ticks));
        self.lift = self.lift.jumps(&jumps);
        Ok(GeneratorAdvance {
            configuration: current,
            jumps,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{dot, int, ints};

    fn lift() -> PhaseLift {
        PhaseLift::new(RationalPhase::new(rat(1, 2), 0), BigInt::zero())
    }

    /// `Holon/Generator.lean::jump_lossless`, `Holon/Generator.lean::jump_carries_winding`.
    #[test]
    fn the_clock_jump_is_lossless_and_carries_winding() {
        let p = lift();
        // A storage read through the carrier: the pump storage cos(2θ − ψ) is a polynomial of the
        // chart, here `c² − s²` for ψ = 0.
        assert!(p.jump_is_lossless(|(c, s)| c * c - s * s));
        assert_eq!(p.jump().winding(), &BigInt::one());
        assert_eq!(p.jump().chart(), p.chart());
    }

    /// `Holon/Generator.lean::jumps_are_carries` over the owner's carries.
    #[test]
    fn jumps_are_carries_and_compose_as_a_cocycle() {
        let n = BigUint::from(5u32);
        for a in 0u32..7 {
            for b in 0u32..7 {
                assert!(jump_cocycle(&n, &a.into(), &b.into(), &3u32.into()).unwrap());
                // The clock counts the same jumps: advancing a then b crosses
                // winding(a) + winding(b) + carry(a, b) sections.
                let mut clock = Clock::ring(int(1), 5).unwrap();
                let first = clock.advance(&a.into());
                let second = clock.advance(&b.into());
                assert_eq!(first + second, winding(&n, &(a + b).into()).unwrap());
            }
        }
    }

    /// The unwound clock counts every tick as a passage; a ring's ticks are the odometer's value
    /// (`Geometry/PhaseCarry.lean::value_digits`) and the elapsed duration is `h · ticks`.
    #[test]
    fn the_clock_reads_its_ticks_and_elapsed_duration() {
        let mut unwound = Clock::unwound(rat(2, 3)).unwrap();
        assert!(unwound.radices().is_empty() && unwound.is_at_rest());
        assert_eq!(unwound.advance(&BigUint::from(4u32)), BigUint::from(4u32));
        assert_eq!(unwound.ticks(), BigUint::from(4u32));
        assert_eq!(unwound.elapsed(), rat(8, 3));
        let mut ring = Clock::ring(rat(1, 5), 3).unwrap();
        assert_eq!(ring.advance(&BigUint::from(7u32)), BigUint::from(2u32));
        assert_eq!(ring.phase(), &[BigUint::from(1u32)]);
        assert_eq!(ring.ticks(), BigUint::from(7u32));
        assert_eq!(ring.elapsed(), rat(7, 5));
        assert_eq!(ring.odometer().levels(), 1);
        assert!(Clock::unwound(Rat::zero()).is_err());
    }

    /// A skew (rotation) generator's Cayley tick preserves `|x|²` exactly, and the screw carries
    /// its initial configuration.
    #[test]
    fn a_rotation_screw_ticks_losslessly_and_keeps_its_key() {
        let screw = SituatedScrew::new(
            ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
            RatVec3::from_i64(3, 4, 0),
        );
        let mut generator =
            Generator::screw(&screw, Clock::ring(rat(1, 3), 4).unwrap(), lift()).unwrap();
        assert_eq!(generator.situated_screw(), Some(screw));
        let start = generator.initial().to_vec();
        let reached = generator.advance(&start, 9).unwrap();
        assert_eq!(
            dot(&reached.configuration, &reached.configuration),
            dot(&start, &start)
        );
        assert_eq!(reached.jumps, BigUint::from(2u32));
        assert_eq!(generator.lift().winding(), &BigInt::from(2));
        // A different key is a different orbit under the same generator.
        let other = generator.tick(&ints(&[1, 0, 0])).unwrap();
        assert_ne!(dot(&other, &other), dot(&start, &start));
    }
}
