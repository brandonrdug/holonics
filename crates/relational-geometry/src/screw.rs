//! Elementary Euclidean screw generators and the local quadrance of two generated curves.
//!
//! This composes `RatVec3` and `AffineMap3`; it does not introduce another frame or matrix owner.
//! All operands belong to one declared oriented Euclidean frame and one parameter/unit chart.
//! A generator is `(omega, advance)` with velocity `omega cross point + advance`. Its initial
//! point is separate: the same screw has different-radius orbits. No sampled helix or float
//! angle is required to read its exact local first and second variation.
//!
//! Formal owner: `Geometry/ScrewGeometry.lean`. The identity atlas consumes `angular_pairing`
//! and `reciprocal_pairing`; `PairQuadranceJet` supplies the source-derived contact differential
//! and geometric second term. Physical force/heat requires the consumer's constitutive law.
//!
//! | Lean | Rust |
//! |---|---|
//! | `bracket_antisymm` | [`ScrewGenerator::bracket`] |
//! | `velocity_translation_covariance` | translation arm of [`ScrewGenerator::rechart`] |
//! | `pairK_translation_invariant`, `pairR_translation_invariant` | the two pairings |
//! | `pairQuadrancePath_eq_twoJet_plus_remainder` | coefficients returned by [`PairQuadranceJet::at`] |
//! | `pairQuadrance_twoJet_exchange` | exchanged pair jets |
//! | `pair_quadrance_is_existing_moment_contraction` | quadrance as an existing quadratic receiver |

use crate::{
    AffineMap3, ExactAnalysisError, Rat, RatComplex, RatVec3, polygon_winding, rational_circle,
};
use num_traits::Zero;
use thiserror::Error;

/// A situated infinitesimal rigid motion, in a caller-declared common frame and parameter chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScrewGenerator {
    angular: RatVec3,
    advance: RatVec3,
}

/// Axis extraction distinguishes the translation and stationary limits without dividing by zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScrewAxis {
    Rotating {
        /// Point on the axis closest to the frame origin.
        origin: RatVec3,
        /// Unnormalized direction, retaining the parameter's angular scale.
        direction: RatVec3,
        /// Axial advance per angular parameter; time reversal of the whole generator preserves it.
        pitch: Rat,
    },
    Translating {
        direction: RatVec3,
    },
    Stationary,
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ScrewError {
    #[error("screw transport requires a proper Euclidean frame map (R^T R = I, det R = 1)")]
    NotProperRigidFrame,
    #[error(
        "the supplied phase chart does not equal the supported finite z rotation and identity partner"
    )]
    PhaseMapMismatch,
}

/// A screw together with the initial point whose orbit is being received.
///
/// The generator alone does not determine a helix: changing `initial` changes the radius and
/// the received phase while leaving the infinitesimal field fixed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SituatedScrew {
    generator: ScrewGenerator,
    initial: RatVec3,
}

impl SituatedScrew {
    pub fn new(generator: ScrewGenerator, initial: RatVec3) -> Self {
        Self { generator, initial }
    }

    pub fn generator(&self) -> &ScrewGenerator {
        &self.generator
    }

    pub fn initial(&self) -> &RatVec3 {
        &self.initial
    }

    pub fn axis(&self) -> ScrewAxis {
        self.generator.axis()
    }

    pub fn transported(&self, map: &AffineMap3) -> Result<Self, ScrewError> {
        Ok(Self::new(
            self.generator.rechart(map)?,
            map.apply(&self.initial),
        ))
    }
}

/// The two independent situated objects entering one pair receiver.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScrewPair {
    first: SituatedScrew,
    second: SituatedScrew,
}

impl ScrewPair {
    pub fn new(first: SituatedScrew, second: SituatedScrew) -> Self {
        Self { first, second }
    }

    pub fn first(&self) -> &SituatedScrew {
        &self.first
    }

    pub fn second(&self) -> &SituatedScrew {
        &self.second
    }

    /// The two initial configurations, retaining their independent axes and degenerations.
    pub fn initial_current(&self) -> [Rat; 6] {
        [
            self.first.initial.x.clone(),
            self.first.initial.y.clone(),
            self.first.initial.z.clone(),
            self.second.initial.x.clone(),
            self.second.initial.y.clone(),
            self.second.initial.z.clone(),
        ]
    }

    pub fn quadrance(&self) -> Rat {
        self.first
            .initial
            .subtract(&self.second.initial)
            .norm_squared()
    }

    pub fn transported(&self, motion: &PairFiniteMotion) -> Result<Self, ScrewError> {
        Ok(Self::new(
            self.first.transported(&motion.first)?,
            self.second.transported(&motion.second)?,
        ))
    }
}

/// One exact finite affine action on the two independently situated objects.
///
/// The maps are supplied by an existing exact chart (for example `cayley_rotation_z(1)` for a
/// quarter turn or the identity linear map with a rational translation). No exponential or Euler
/// approximation is inferred from the infinitesimal generators.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairFiniteMotion {
    first: AffineMap3,
    second: AffineMap3,
    phase: Option<RationalPhase>,
}

/// An exact Cayley phase chart. `parameter` is the tangent half-angle coordinate, so a quarter
/// turn is parameter `1`. `winding` is the declared number of *extra full turns per elementary
/// Cayley passage*; it is lifted across a closed period rather than used as the polygon winding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RationalPhase {
    parameter: Rat,
    extra_turns: i64,
}

#[derive(Debug, Error)]
pub enum RationalPhaseError {
    #[error("phase chart power {period} does not close; endpoint is ({real}, {imaginary})")]
    NotClosedAtPeriod {
        period: usize,
        real: Rat,
        imaginary: Rat,
    },
    #[error("phase winding lift overflowed at period {period} and extra turns {extra_turns}")]
    WindingOverflow { period: usize, extra_turns: i64 },
    #[error(transparent)]
    Analysis(#[from] ExactAnalysisError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RationalPhaseWinding {
    pub polygon: i64,
    pub extra_turns: i64,
    pub lifted: i64,
}

impl RationalPhase {
    pub fn new(parameter: Rat, extra_turns: i64) -> Self {
        Self {
            parameter,
            extra_turns,
        }
    }

    pub fn parameter(&self) -> &Rat {
        &self.parameter
    }

    pub fn winding(&self) -> i64 {
        self.extra_turns
    }

    pub fn extra_turns(&self) -> i64 {
        self.extra_turns
    }

    /// The exact unit-circle face owned by the rational Cayley chart.
    pub fn chart(&self) -> (Rat, Rat) {
        rational_circle(&self.parameter)
    }

    /// Read the oriented phase through the existing exact winding receiver. The polygon is the
    /// admitted finite word of the Cayley point, so a result is supplied only at the declared
    /// word length; no generic torus closure is inferred.
    pub fn chart_winding(&self, period: usize) -> Result<i32, RationalPhaseError> {
        if period == 0 {
            return Err(RationalPhaseError::NotClosedAtPeriod {
                period,
                real: Rat::from_integer(1.into()),
                imaginary: Rat::from_integer(0.into()),
            });
        }
        let (cosine, sine) = self.chart();
        let mut points = Vec::with_capacity(period);
        let mut current = RatComplex::new(Rat::from_integer(1.into()), Rat::from_integer(0.into()));
        let phase = RatComplex::new(cosine, sine);
        for _ in 0..period {
            points.push(current.clone());
            current = RatComplex::new(
                &current.re * &phase.re - &current.im * &phase.im,
                &current.re * &phase.im + &current.im * &phase.re,
            );
        }
        if current.re != Rat::from_integer(1.into()) || !current.im.is_zero() {
            return Err(RationalPhaseError::NotClosedAtPeriod {
                period,
                real: current.re,
                imaginary: current.im,
            });
        }
        Ok(polygon_winding(&points)?.0.winding())
    }

    /// Lift the polygon winding by the declared number of extra full turns on each elementary
    /// passage. The polygon is read only after the finite chart closes.
    pub fn lifted_winding(
        &self,
        period: usize,
    ) -> Result<RationalPhaseWinding, RationalPhaseError> {
        let polygon = i64::from(self.chart_winding(period)?);
        let periods = i64::try_from(period).map_err(|_| RationalPhaseError::WindingOverflow {
            period,
            extra_turns: self.extra_turns,
        })?;
        let lifted = periods
            .checked_mul(self.extra_turns)
            .and_then(|turns| polygon.checked_add(turns))
            .ok_or(RationalPhaseError::WindingOverflow {
                period,
                extra_turns: self.extra_turns,
            })?;
        Ok(RationalPhaseWinding {
            polygon,
            extra_turns: self.extra_turns,
            lifted,
        })
    }
}

impl PairFiniteMotion {
    pub fn new(first: AffineMap3, second: AffineMap3) -> Result<Self, ScrewError> {
        if !first.linear.is_special_orthogonal() || !second.linear.is_special_orthogonal() {
            return Err(ScrewError::NotProperRigidFrame);
        }
        Ok(Self {
            first,
            second,
            phase: None,
        })
    }

    /// Bind the phase chart only to the supported exact relation: the first map is the Cayley
    /// rotation about the frame z axis through the chart parameter, with no translation, and the
    /// partner is identity. Other finite affine actions remain lawful through [`Self::new`] but
    /// carry no phase claim.
    pub fn with_phase(
        first: AffineMap3,
        second: AffineMap3,
        phase: RationalPhase,
    ) -> Result<Self, ScrewError> {
        let expected_first = AffineMap3 {
            linear: crate::cayley_rotation_z(phase.parameter()),
            translation: RatVec3::zero(),
        };
        if first != expected_first || second != AffineMap3::identity() {
            return Err(ScrewError::PhaseMapMismatch);
        }
        Self::new(first, second).map(|mut motion| {
            motion.phase = Some(phase);
            motion
        })
    }

    pub fn first(&self) -> &AffineMap3 {
        &self.first
    }

    pub fn second(&self) -> &AffineMap3 {
        &self.second
    }

    pub fn phase(&self) -> Option<&RationalPhase> {
        self.phase.as_ref()
    }

    /// Compose this motion, then `next`, independently on both pair members.
    pub fn followed_by(&self, next: &Self) -> Self {
        Self {
            first: self.first.followed_by(&next.first),
            second: self.second.followed_by(&next.second),
            phase: None,
        }
    }

    /// Exact finite repetition. A return is claimed only when the resulting affine maps equal
    /// identity; a declared period is not assumed to close an arbitrary screw orbit.
    pub fn power(&self, exponent: usize) -> Self {
        let mut result = Self {
            first: AffineMap3::identity(),
            second: AffineMap3::identity(),
            phase: None,
        };
        let mut base = self.clone();
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining % 2 == 1 {
                result = result.followed_by(&base);
            }
            remaining /= 2;
            if remaining > 0 {
                base = base.followed_by(&base);
            }
        }
        result
    }

    pub fn closes_after(&self, period: usize) -> bool {
        period > 0
            && self.power(period)
                == Self {
                    first: AffineMap3::identity(),
                    second: AffineMap3::identity(),
                    phase: None,
                }
    }
}

impl ScrewGenerator {
    pub fn new(angular: RatVec3, advance: RatVec3) -> Self {
        Self { angular, advance }
    }

    pub fn angular(&self) -> &RatVec3 {
        &self.angular
    }

    pub fn advance(&self) -> &RatVec3 {
        &self.advance
    }

    /// The first jet of this generator's orbit through `point`.
    pub fn velocity(&self, point: &RatVec3) -> RatVec3 {
        self.angular.cross(point).add(&self.advance)
    }

    /// The second jet for a constant generator, not a general changing-field acceleration.
    pub fn acceleration(&self, point: &RatVec3) -> RatVec3 {
        self.angular.cross(&self.velocity(point))
    }

    /// The `se(3)` matrix commutator, including the translation arm.
    ///
    /// Pure translations in different directions commute. Coaxiality alone is therefore not
    /// an exhaustive test once degenerate rotations are admitted.
    pub fn bracket(&self, other: &Self) -> Self {
        Self::new(
            self.angular.cross(&other.angular),
            self.angular
                .cross(&other.advance)
                .subtract(&other.angular.cross(&self.advance)),
        )
    }

    pub fn commutes_with(&self, other: &Self) -> bool {
        let bracket = self.bracket(other);
        bracket.angular == RatVec3::zero() && bracket.advance == RatVec3::zero()
    }

    /// A fixed normalization of the rotational invariant form, not a complete pair invariant.
    pub fn angular_pairing(&self, other: &Self) -> Rat {
        self.angular.dot(&other.angular)
    }

    /// The Klein reciprocal form on two twist coordinates.
    ///
    /// Interpreting it as physical power additionally identifies one operand with a wrench,
    /// with the corresponding units and dual transport. It is not power from geometry alone.
    pub fn reciprocal_pairing(&self, other: &Self) -> Rat {
        self.angular.dot(&other.advance) + self.advance.dot(&other.angular)
    }

    pub fn axis(&self) -> ScrewAxis {
        let angular_square = self.angular.norm_squared();
        if angular_square.is_zero() {
            return if self.advance == RatVec3::zero() {
                ScrewAxis::Stationary
            } else {
                ScrewAxis::Translating {
                    direction: self.advance.clone(),
                }
            };
        }
        let inverse = Rat::from_integer(1.into()) / &angular_square;
        ScrewAxis::Rotating {
            origin: self.angular.cross(&self.advance).scale(&inverse),
            direction: self.angular.clone(),
            pitch: self.angular.dot(&self.advance) / angular_square,
        }
    }

    /// Transport from coordinates x to x' = R x + t through the existing affine map.
    /// The returned velocity satisfies V'(x') = R V(x).
    pub fn rechart(&self, frame: &AffineMap3) -> Result<Self, ScrewError> {
        if !frame.linear.is_special_orthogonal() {
            return Err(ScrewError::NotProperRigidFrame);
        }
        let angular = frame.linear.apply(&self.angular);
        let advance = frame
            .linear
            .apply(&self.advance)
            .add(&frame.translation.cross(&angular));
        Ok(Self::new(angular, advance))
    }
}

/// Source-conditioned differential of Q(s,t) = |x_a(s)-x_b(t)|² at two declared orbit points.
///
/// `s` and `t` are independent parameters. A consumer supplies any synchronization/clock law.
/// The Hessian retains the geometric terms `delta dot acceleration`, not only the Gram term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairQuadranceJet {
    separation: RatVec3,
    quadrance: Rat,
    gradient: [Rat; 2],
    hessian: [[Rat; 2]; 2],
}

impl PairQuadranceJet {
    pub fn at(
        first: &ScrewGenerator,
        first_point: &RatVec3,
        second: &ScrewGenerator,
        second_point: &RatVec3,
    ) -> Self {
        let separation = first_point.subtract(second_point);
        let first_velocity = first.velocity(first_point);
        let second_velocity = second.velocity(second_point);
        let first_acceleration = first.acceleration(first_point);
        let second_acceleration = second.acceleration(second_point);
        let two = Rat::from_integer(2.into());
        let mixed = -&two * first_velocity.dot(&second_velocity);
        Self {
            quadrance: separation.norm_squared(),
            gradient: [
                &two * separation.dot(&first_velocity),
                -&two * separation.dot(&second_velocity),
            ],
            hessian: [
                [
                    &two * (first_velocity.norm_squared() + separation.dot(&first_acceleration)),
                    mixed.clone(),
                ],
                [
                    mixed,
                    &two * (second_velocity.norm_squared() - separation.dot(&second_acceleration)),
                ],
            ],
            separation,
        }
    }

    pub fn separation(&self) -> &RatVec3 {
        &self.separation
    }
    pub fn quadrance(&self) -> &Rat {
        &self.quadrance
    }
    pub fn gradient(&self) -> &[Rat; 2] {
        &self.gradient
    }
    pub fn hessian(&self) -> &[[Rat; 2]; 2] {
        &self.hessian
    }

    /// Pull a receiving covector through the actual contact differential.
    pub fn pullback(&self, received: &Rat) -> [Rat; 2] {
        self.gradient.clone().map(|component| component * received)
    }

    /// Local second-order change along a declared joint parameter direction.
    /// This is a jet, not an assertion that a finite helical passage is quadratic.
    pub fn directional(&self, direction: &[Rat; 2]) -> (Rat, Rat) {
        let first = &self.gradient[0] * &direction[0] + &self.gradient[1] * &direction[1];
        let second = &direction[0]
            * (&self.hessian[0][0] * &direction[0] + &self.hessian[0][1] * &direction[1])
            + &direction[1]
                * (&self.hessian[1][0] * &direction[0] + &self.hessian[1][1] * &direction[1]);
        (first, second)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{RatMat3, cayley_rotation_z, integer};

    #[test]
    fn translation_and_stationary_limits_are_retained() {
        let x = ScrewGenerator::new(RatVec3::zero(), RatVec3::from_i64(1, 0, 0));
        let y = ScrewGenerator::new(RatVec3::zero(), RatVec3::from_i64(0, 1, 0));
        assert!(x.commutes_with(&y));
        assert!(matches!(x.axis(), ScrewAxis::Translating { .. }));
        assert_eq!(
            ScrewGenerator::new(RatVec3::zero(), RatVec3::zero()).axis(),
            ScrewAxis::Stationary
        );
    }

    #[test]
    fn axis_reconstructs_the_generator_without_unit_normalization() {
        let xi = ScrewGenerator::new(RatVec3::from_i64(1, 2, 3), RatVec3::from_i64(4, -2, 5));
        let ScrewAxis::Rotating {
            origin,
            direction,
            pitch,
        } = xi.axis()
        else {
            panic!()
        };
        assert!(origin.dot(&direction).is_zero());
        assert_eq!(
            origin.cross(&direction).add(&direction.scale(&pitch)),
            *xi.advance()
        );
        let reversed = ScrewGenerator::new(
            xi.angular.scale(&integer(-1)),
            xi.advance.scale(&integer(-1)),
        );
        let ScrewAxis::Rotating {
            pitch: reversed_pitch,
            ..
        } = reversed.axis()
        else {
            panic!()
        };
        assert_eq!(pitch, reversed_pitch);
    }

    #[test]
    fn frame_transport_preserves_velocity_pairings_and_bracket() {
        let frame = AffineMap3 {
            linear: cayley_rotation_z(&integer(2)),
            translation: RatVec3::from_i64(3, -2, 1),
        };
        let first = ScrewGenerator::new(RatVec3::from_i64(1, 2, 3), RatVec3::from_i64(4, -2, 5));
        let second = ScrewGenerator::new(RatVec3::from_i64(0, 1, -2), RatVec3::from_i64(2, 3, 1));
        let a = first.rechart(&frame).unwrap();
        let b = second.rechart(&frame).unwrap();
        let point = RatVec3::from_i64(2, -4, 1);
        assert_eq!(
            a.velocity(&frame.apply(&point)),
            frame.linear.apply(&first.velocity(&point))
        );
        assert_eq!(a.angular_pairing(&b), first.angular_pairing(&second));
        assert_eq!(a.reciprocal_pairing(&b), first.reciprocal_pairing(&second));
        assert_eq!(
            a.bracket(&b),
            first.bracket(&second).rechart(&frame).unwrap()
        );
        let bad = AffineMap3 {
            linear: RatMat3::from_i64([[-1, 0, 0], [0, 1, 0], [0, 0, 1]]),
            translation: RatVec3::zero(),
        };
        assert_eq!(first.rechart(&bad), Err(ScrewError::NotProperRigidFrame));
    }

    #[test]
    fn pair_jet_retains_common_rigid_motion_and_exchange() {
        let xi = ScrewGenerator::new(RatVec3::from_i64(0, 0, 2), RatVec3::from_i64(0, 0, 3));
        let a = RatVec3::from_i64(2, 0, 1);
        let b = RatVec3::from_i64(0, 1, -1);
        let jet = PairQuadranceJet::at(&xi, &a, &xi, &b);
        assert_eq!(
            jet.directional(&[integer(1), integer(1)]),
            (integer(0), integer(0))
        );
        let swapped = PairQuadranceJet::at(&xi, &b, &xi, &a);
        assert_eq!(jet.quadrance(), swapped.quadrance());
        assert_eq!(jet.gradient()[0], swapped.gradient()[1]);
        assert_eq!(jet.hessian()[0][0], swapped.hessian()[1][1]);
        let frame = AffineMap3 {
            linear: cayley_rotation_z(&integer(3)),
            translation: RatVec3::from_i64(2, -1, 4),
        };
        let moved = xi.rechart(&frame).unwrap();
        let moved_jet = PairQuadranceJet::at(&moved, &frame.apply(&a), &moved, &frame.apply(&b));
        assert_eq!(jet.gradient(), moved_jet.gradient());
        assert_eq!(jet.hessian(), moved_jet.hessian());
    }

    #[test]
    fn geometric_second_term_separates_orbits_of_one_axis() {
        let turn = ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero());
        let held = ScrewGenerator::new(RatVec3::zero(), RatVec3::zero());
        let jet = PairQuadranceJet::at(
            &turn,
            &RatVec3::from_i64(1, 0, 0),
            &held,
            &RatVec3::from_i64(2, 0, 0),
        );
        assert_eq!(jet.hessian()[0][0], integer(4));
        // Dropping the geometric term would return 2. Same axis/generator alone does not fix
        // the pair's receiving geometry: move the initial orbit point to the axis.
        let collapsed =
            PairQuadranceJet::at(&turn, &RatVec3::zero(), &held, &RatVec3::from_i64(2, 0, 0));
        assert_eq!(collapsed.hessian()[0][0], integer(0));
        assert_eq!(jet.pullback(&integer(7)), [integer(0), integer(0)]);
    }

    #[test]
    fn situated_pair_keeps_independent_degenerations_and_exact_quarter_turn() {
        let rotating = SituatedScrew::new(
            ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
            RatVec3::from_i64(1, 0, 0),
        );
        let translating = SituatedScrew::new(
            ScrewGenerator::new(RatVec3::zero(), RatVec3::from_i64(0, 0, 2)),
            RatVec3::from_i64(0, 2, 0),
        );
        assert!(matches!(rotating.axis(), ScrewAxis::Rotating { .. }));
        assert!(matches!(translating.axis(), ScrewAxis::Translating { .. }));
        let quarter = PairFiniteMotion::new(
            AffineMap3::rotation_about(&RatVec3::zero(), cayley_rotation_z(&integer(1))),
            AffineMap3 {
                linear: RatMat3::identity(),
                translation: RatVec3::from_i64(1, 0, 0),
            },
        )
        .unwrap();
        assert!(quarter.closes_after(4) == false);
        assert!(
            PairFiniteMotion::new(
                AffineMap3::rotation_about(&RatVec3::zero(), cayley_rotation_z(&integer(1))),
                AffineMap3::identity(),
            )
            .unwrap()
            .closes_after(4)
        );
        assert_eq!(
            RationalPhase::new(integer(1), 1).chart_winding(4).unwrap(),
            1
        );
        assert_eq!(
            RationalPhase::new(integer(1), 0)
                .lifted_winding(4)
                .unwrap()
                .lifted,
            1
        );
        assert_eq!(
            RationalPhase::new(integer(1), 1)
                .lifted_winding(4)
                .unwrap()
                .lifted,
            5
        );
        assert_eq!(
            RationalPhase::new(integer(0), 0).chart_winding(1).unwrap(),
            0
        );
        assert!(matches!(
            RationalPhase::new(integer(1), 1).chart_winding(3),
            Err(RationalPhaseError::NotClosedAtPeriod { period: 3, .. })
        ));
        let pair = ScrewPair::new(rotating, translating);
        let moved = pair
            .transported(&quarter)
            .expect("proper exact pair motion");
        assert_ne!(pair.initial_current(), moved.initial_current());
        assert_ne!(pair.quadrance(), moved.quadrance());
    }
}
