//! **Möbius navigators: their fixed points are the landmarks where their paths converge.**
//!
//! [definition] A **Möbius navigator** is the fractional chart `z ↦ (αz + β)/(γz + δ)` of the
//! undivided block `[[α, β], [γ, δ]]` over ℚ (Lean `Compression/Landmark/FixedPoint.Mobius`,
//! `act_eq_blockTransport`), with `det = αδ − βγ ≠ 0`. It acts on the projective line; its fixed
//! points are the block's eigenlines, and the eigenvalue `μ` of each is its **multiplier face**.
//! Its site faces `(tr, det)` are read projectively ([`SiteFactor::kind`], [`lorentz_factor_squared`]).
//!
//! ```text
//! fixed z:       γz² + (δ − α)z − β = 0          Δ = (δ − α)² + 4βγ = tr² − 4 det
//! eigenvalues:   μ± = (tr ± √Δ)/2                 z± = (μ± − δ)/γ   (γ ≠ 0)
//! derivative at z±:  μ∓/μ±                        chart w = (z − z₊)/(z − z₋):  w ↦ (μ₋/μ₊) w
//! ```
//!
//! [proved-derived; implemented-exact] The fixed points are carried exactly: rational when `Δ` is
//! a rational square, otherwise in `ℚ(√Δ)` ([`QuadraticSurd`]), and as the retained quadratic when
//! `Δ < 0` (no real fixed point). **Attraction is gated on `tr ≠ 0`, not on `det > 0`** (Lean
//! `attracting_iff_trace_ne_zero`): with two real fixed points `μ₊² − μ₋² = tr·√Δ`, so
//! `|μ₊| ≠ |μ₋|` exactly when `tr ≠ 0`, and then the fixed point of the larger multiplier attracts
//! every path off the other and the pole orbit (`iterate_tendsto_fixed`). The map
//! `z ↦ (z + 2)/(2z + 1)` has `det = −3` and still attracts at `1` with multiplier `−1/3`
//! (`reflection_attracts`); the Swing `z ↦ 1/z` has `tr = 0` and is neutral at both fixed points
//! (`swing_neither_attracts`).
//!
//! [definition; agent-inferred] Lean classifies attraction for `c ≠ 0`, where both fixed points
//! are finite. This owner also reads the affine case `γ = 0`, whose fixed points are `∞` (the
//! eigenline of `α`) and `β/(δ − α)` with multipliers `α` and `δ`; the same gate applies there,
//! since `|α| = |δ|` with `α ≠ δ` is `tr = 0`. Its Lean counterpart is owed in #62: the affine
//! `c = 0` case of `attracting_iff_trace_ne_zero` and `iterate_tendsto_fixed`.
//!
//! [proved-derived; implemented-exact] **Velocity addition fixes `±c` for every rational `c > 0`.**
//! `u ⊕ v = (u + v)/(1 + uv/c²)` is the navigator `[[1, v], [v/c², 1]]`, velocity addition in units
//! of `c` (Lean `vaddC_fixes`, `vaddC_iterate`); in the Doppler chart `D(u) = (c + u)/(c − u)` it
//! multiplies, `D(u ⊕ v) = D(u)·D(v)` (`doppler_vadd` at `u/c`), so the iterates of one boost from
//! `|u| < c` have `D(u_n) = D(u₀)·D(v)ⁿ` exactly, and `c − u_n = 2c/(D(u_n) + 1)`: for `0 < v < c`
//! they converge to `c` and for `−c < v < 0` to `−c` (`vaddC_iterate_tendsto_c`,
//! `vaddC_iterate_tendsto_neg_c`). `±c` are the landmarks of the boost family.
//!
//! | Lean `Compression/Landmark/FixedPoint` | Rust |
//! |---|---|
//! | `Mobius`, `Mobius.act`, `trace`, `det`, `Fixed`, `act_eq_blockTransport`, `act_eq_self_iff` | [`MobiusNavigator`] |
//! | `sub_fixed`, `act_sub_fixed`, `other_multiplier`, `fixed_points_at_most_two`, `multipliers_sum`, `multipliers_prod`, `discriminant_eq_sq`, `chart_conjugates` | [`MobiusNavigator::fixed_points`], [`MobiusNavigator::chart`] |
//! | `two_fixed_points_disc_pos`, `two_fixed_points_is_boost` (with `det > 0`); `SiteKind.siteKind_eq_reflection_iff` (`det < 0`) | [`MobiusNavigator::kind`] |
//! | `multipliers_ne`, `attracting_iff_trace_ne_zero`, `act_ne_fixed`, `iterate_tendsto_fixed` (`c ≠ 0`) | [`MobiusNavigator::attraction`] |
//! | `swingNavigator`, `swing_neither_attracts`, `reflectingNavigator`, `reflection_attracts` | tests |
//! | `vadd`, `velocityNavigator`, `velocity_act`, `velocity_is_boost`, `vadd_fixes_one`, `vadd_fixes_neg_one`, `doppler`, `doppler_vadd`, `vadd_mem`, `iterate_doppler`, `one_sub_iterate`, `vadd_iterate_tendsto_one`, `vadd_iterate_tendsto_neg_one` (`c = 1`) | [`velocity_addition`], [`doppler_chart`] |
//! | `vaddC`, `vaddC_fixes`, `vaddC_iterate`, `vaddC_iterate_tendsto_c`, `vaddC_iterate_tendsto_neg_c` | [`velocity_addition`] |

use std::cmp::Ordering;

use num_traits::{One, Signed, Zero};

use crate::compression::landmark::LandmarkError;
use crate::compression::landmark::quadratic::QuadraticSurd;
use crate::compression::landmark::site::lorentz_factor_squared;
use crate::navigator::trace::{SiteFactor, SiteKind};
use crate::ratio::polynomial::RationalPolynomial;
use crate::ratio::{Rat, integer};

/// [definition] **A point of the projective line**: a finite value in its quadratic field, or `∞`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectivePoint {
    Finite(QuadraticSurd),
    Infinity,
}

/// [definition] **A fixed point and its multiplier face**, the eigenvalue of its eigenline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedPoint {
    pub point: ProjectivePoint,
    pub multiplier: QuadraticSurd,
}

/// [definition] **The fixed points of a Möbius navigator.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FixedPoints {
    /// The identity: every point is fixed.
    Identity,
    /// Two distinct real fixed points, `Δ > 0`; `plus` carries `μ₊ = (tr + √Δ)/2`.
    Two { plus: FixedPoint, minus: FixedPoint },
    /// One double fixed point, `Δ = 0` (parabolic).
    Double(FixedPoint),
    /// No real fixed point, `Δ < 0`: the conjugate pair is retained as its quadratic
    /// `γz² + (δ − α)z − β`.
    Conjugate(RationalPolynomial),
}

/// [definition] **Where the navigator's paths go.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Attraction {
    /// `tr ≠ 0` with two real fixed points: `attracting` has derivative `ratio`, `|ratio| < 1`,
    /// and `repelling` has `1/ratio`.
    Converging {
        attracting: FixedPoint,
        repelling: FixedPoint,
        ratio: QuadraticSurd,
    },
    /// `tr = 0` with two real fixed points: both derivatives are `−1`; the navigator is an
    /// involution and no path converges.
    Neutral,
    /// A double fixed point.
    Parabolic(FixedPoint),
    /// No real fixed point: the paths rotate.
    Elliptic,
    /// Every point is fixed.
    Identity,
}

/// [definition] **A Möbius navigator** `z ↦ (αz + β)/(γz + δ)` with `det ≠ 0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MobiusNavigator {
    alpha: Rat,
    beta: Rat,
    gamma: Rat,
    delta: Rat,
}

impl MobiusNavigator {
    /// The navigator of the block `[[α, β], [γ, δ]]`; a singular block is refused.
    pub fn new(alpha: Rat, beta: Rat, gamma: Rat, delta: Rat) -> Result<Self, LandmarkError> {
        let navigator = Self {
            alpha,
            beta,
            gamma,
            delta,
        };
        if navigator.determinant().is_zero() {
            return Err(LandmarkError::SingularNavigator);
        }
        Ok(navigator)
    }

    /// `tr = α + δ`.
    pub fn trace(&self) -> Rat {
        &self.alpha + &self.delta
    }

    /// `det = αδ − βγ`.
    pub fn determinant(&self) -> Rat {
        &self.alpha * &self.delta - &self.beta * &self.gamma
    }

    /// The site faces `(tr, det)`, defined up to the projective scaling `(λ tr, λ² det)`.
    pub fn site(&self) -> SiteFactor {
        SiteFactor::new(self.trace(), self.determinant())
    }

    /// The site kind, invariant under that scaling.
    pub fn kind(&self) -> SiteKind {
        self.site().kind()
    }

    /// `γ² = tr²/(4 det)`, the projective Lorentz face, refused unless the site is null or a
    /// boost.
    pub fn lorentz_factor_squared(&self) -> Result<Rat, LandmarkError> {
        lorentz_factor_squared(&self.site())
    }

    /// **One step** at a finite rational point, refused at the pole `γz + δ = 0`.
    pub fn act(&self, point: &Rat) -> Result<Rat, LandmarkError> {
        let denominator = &self.gamma * point + &self.delta;
        if denominator.is_zero() {
            return Err(LandmarkError::Pole {
                point: point.clone(),
            });
        }
        Ok((&self.alpha * point + &self.beta) / denominator)
    }

    /// **The fixed points, exactly** (Lean `fixed_points_at_most_two`, `multipliers_sum`,
    /// `multipliers_prod`, `discriminant_eq_sq`).
    pub fn fixed_points(&self) -> Result<FixedPoints, LandmarkError> {
        let trace = self.trace();
        let discriminant = &trace * &trace - integer(4) * self.determinant();
        if self.gamma.is_zero() {
            // Affine: `∞` is the eigenline of `α`, and `β/(δ − α)` that of `δ`.
            let at_infinity = FixedPoint {
                point: ProjectivePoint::Infinity,
                multiplier: QuadraticSurd::rational(self.alpha.clone()),
            };
            if self.alpha == self.delta {
                return Ok(if self.beta.is_zero() {
                    FixedPoints::Identity
                } else {
                    FixedPoints::Double(at_infinity)
                });
            }
            let finite = FixedPoint {
                point: ProjectivePoint::Finite(QuadraticSurd::rational(
                    &self.beta / (&self.delta - &self.alpha),
                )),
                multiplier: QuadraticSurd::rational(self.delta.clone()),
            };
            return Ok(if self.alpha > self.delta {
                FixedPoints::Two {
                    plus: at_infinity,
                    minus: finite,
                }
            } else {
                FixedPoints::Two {
                    plus: finite,
                    minus: at_infinity,
                }
            });
        }
        if discriminant.is_negative() {
            return Ok(FixedPoints::Conjugate(RationalPolynomial::new(vec![
                -self.beta.clone(),
                &self.delta - &self.alpha,
                self.gamma.clone(),
            ])));
        }
        let half = Rat::one() / integer(2);
        let fixed = |sign: &Rat| -> Result<FixedPoint, LandmarkError> {
            let multiplier =
                QuadraticSurd::new(&trace * &half, sign * &half, discriminant.clone())?;
            let point = multiplier
                .shifted(&-self.delta.clone())
                .scaled(&self.gamma.recip());
            Ok(FixedPoint {
                point: ProjectivePoint::Finite(point),
                multiplier,
            })
        };
        let plus = fixed(&Rat::one())?;
        if discriminant.is_zero() {
            return Ok(FixedPoints::Double(plus));
        }
        Ok(FixedPoints::Two {
            plus,
            minus: fixed(&-Rat::one())?,
        })
    }

    /// **Where the paths go**: with two real fixed points the one of larger multiplier attracts
    /// exactly when `tr ≠ 0` (Lean `attracting_iff_trace_ne_zero`, `iterate_tendsto_fixed`), with
    /// derivative `μ_other/μ_own`.
    pub fn attraction(&self) -> Result<Attraction, LandmarkError> {
        Ok(match self.fixed_points()? {
            FixedPoints::Identity => Attraction::Identity,
            FixedPoints::Conjugate(_) => Attraction::Elliptic,
            FixedPoints::Double(point) => Attraction::Parabolic(point),
            FixedPoints::Two { plus, minus } => {
                match plus.multiplier.compare_magnitude(&minus.multiplier)? {
                    Ordering::Equal => Attraction::Neutral,
                    Ordering::Greater => Attraction::Converging {
                        ratio: minus.multiplier.div(&plus.multiplier)?,
                        attracting: plus,
                        repelling: minus,
                    },
                    Ordering::Less => Attraction::Converging {
                        ratio: plus.multiplier.div(&minus.multiplier)?,
                        attracting: minus,
                        repelling: plus,
                    },
                }
            }
        })
    }

    /// **The fixed-point chart** `w = (z − z₊)/(z − z₋)` of a finite point, in which the navigator
    /// is the scaling `w ↦ (μ₋/μ₊) w` (Lean `chart_conjugates`). Refused unless both fixed points are
    /// finite and distinct, and at `z = z₋`.
    pub fn chart(&self, point: &Rat) -> Result<QuadraticSurd, LandmarkError> {
        let FixedPoints::Two {
            plus:
                FixedPoint {
                    point: ProjectivePoint::Finite(plus),
                    ..
                },
            minus:
                FixedPoint {
                    point: ProjectivePoint::Finite(minus),
                    ..
                },
        } = self.fixed_points()?
        else {
            return Err(LandmarkError::NoFixedPointChart);
        };
        let here = QuadraticSurd::rational(point.clone());
        here.sub(&plus)?.div(&here.sub(&minus)?)
    }

    /// The chart's scaling `μ₋/μ₊`.
    pub fn chart_scaling(&self) -> Result<QuadraticSurd, LandmarkError> {
        match self.fixed_points()? {
            FixedPoints::Two { plus, minus } => minus.multiplier.div(&plus.multiplier),
            _ => Err(LandmarkError::NoFixedPointChart),
        }
    }
}

/// **Velocity addition with a characteristic** `c > 0`: `u ↦ (u + v)/(1 + uv/c²)`, the navigator
/// `[[1, v], [v/c², 1]]` (Lean `velocityNavigator` at `c = 1`, `vaddC`, `vaddC_fixes`). Refused for
/// `c ≤ 0` and for `|v| ≥ c`, outside the open cone.
pub fn velocity_addition(
    velocity: &Rat,
    characteristic: &Rat,
) -> Result<MobiusNavigator, LandmarkError> {
    if !characteristic.is_positive() || velocity.abs() >= *characteristic {
        return Err(LandmarkError::OutsideTheCone {
            velocity: velocity.clone(),
            characteristic: characteristic.clone(),
        });
    }
    MobiusNavigator::new(
        Rat::one(),
        velocity.clone(),
        velocity / (characteristic * characteristic),
        Rat::one(),
    )
}

/// **The Doppler chart** `D(u) = (c + u)/(c − u)` of a velocity in the open cone `|u| < c`, in which
/// velocity addition multiplies (Lean `doppler`, `doppler_vadd` at `u/c`, by `vaddC_fixes`).
pub fn doppler_chart(velocity: &Rat, characteristic: &Rat) -> Result<Rat, LandmarkError> {
    if !characteristic.is_positive() || velocity.abs() >= *characteristic {
        return Err(LandmarkError::OutsideTheCone {
            velocity: velocity.clone(),
            characteristic: characteristic.clone(),
        });
    }
    Ok((characteristic + velocity) / (characteristic - velocity))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::rat;

    fn navigator(alpha: i64, beta: i64, gamma: i64, delta: i64) -> MobiusNavigator {
        MobiusNavigator::new(
            integer(alpha),
            integer(beta),
            integer(gamma),
            integer(delta),
        )
        .unwrap()
    }

    fn finite(point: &FixedPoint) -> QuadraticSurd {
        match &point.point {
            ProjectivePoint::Finite(value) => value.clone(),
            ProjectivePoint::Infinity => panic!("the test fixes a finite point"),
        }
    }

    /// `γz² + (δ − α)z − β` at a point of the quadratic field.
    fn fixed_equation(map: &MobiusNavigator, point: &QuadraticSurd) -> QuadraticSurd {
        point
            .mul(point)
            .unwrap()
            .scaled(&map.gamma)
            .add(&point.scaled(&(&map.delta - &map.alpha)))
            .unwrap()
            .shifted(&-map.beta.clone())
    }

    /// Lean `fixed_points_at_most_two`, `multipliers_sum`, `multipliers_prod`,
    /// `discriminant_eq_sq`: two fixed points satisfy the quadratic exactly, rational or in
    /// `ℚ(√Δ)`; their multipliers sum to `tr`, multiply to `det`, and `(μ₊ − μ₋)² = tr² − 4 det`.
    #[test]
    fn the_fixed_points_are_carried_exactly() {
        for map in [
            navigator(1, 2, 2, 1),
            navigator(2, 1, 1, 1),
            navigator(0, 1, 1, 0),
            navigator(3, 1, 4, 5),
        ] {
            let FixedPoints::Two { plus, minus } = map.fixed_points().unwrap() else {
                panic!("two real fixed points");
            };
            for point in [&plus, &minus] {
                assert_eq!(
                    fixed_equation(&map, &finite(point)),
                    QuadraticSurd::rational(Rat::zero())
                );
            }
            let (mu_plus, mu_minus) = (&plus.multiplier, &minus.multiplier);
            assert_eq!(
                mu_plus.add(mu_minus).unwrap(),
                QuadraticSurd::rational(map.trace())
            );
            assert_eq!(
                mu_plus.mul(mu_minus).unwrap(),
                QuadraticSurd::rational(map.determinant())
            );
            let gap = mu_plus.sub(mu_minus).unwrap();
            assert_eq!(
                gap.mul(&gap).unwrap(),
                QuadraticSurd::rational(map.trace() * map.trace() - integer(4) * map.determinant())
            );
        }
        let FixedPoints::Two { plus, .. } = navigator(2, 1, 1, 1).fixed_points().unwrap() else {
            panic!("the cat map has two fixed points");
        };
        assert_eq!(
            finite(&plus).as_rational(),
            None,
            "(1 + √5)/2 stays a constraint"
        );
    }

    /// Lean `reflection_attracts`: **`z ↦ (z + 2)/(2z + 1)` has `det = −3` and still attracts.**
    /// Its fixed points are `±1`; the derivative is `−1/3` at `1` and `−3` at `−1`; the kind is a
    /// reflection; the fixed-point chart scales by `−1/3` at every step, and every iterate from `0`
    /// moves closer to `1`.
    #[test]
    fn attraction_needs_a_nonzero_trace_not_a_positive_determinant() {
        let map = navigator(1, 2, 2, 1);
        assert_eq!(map.determinant(), integer(-3));
        assert_eq!(map.kind(), SiteKind::Reflection);
        let Attraction::Converging {
            attracting,
            repelling,
            ratio,
        } = map.attraction().unwrap()
        else {
            panic!("tr = 2 ≠ 0 converges");
        };
        assert_eq!(finite(&attracting).as_rational(), Some(&integer(1)));
        assert_eq!(finite(&repelling).as_rational(), Some(&integer(-1)));
        assert_eq!(ratio.as_rational(), Some(&rat(-1, 3)));
        assert_eq!(
            map.chart_scaling().unwrap().as_rational(),
            Some(&rat(-1, 3))
        );
        let mut point = integer(0);
        for _ in 0..30 {
            let next = map.act(&point).unwrap();
            let (before, after) = (map.chart(&point).unwrap(), map.chart(&next).unwrap());
            assert_eq!(after, before.scaled(&rat(-1, 3)));
            assert_eq!(after.compare_magnitude(&before).unwrap(), Ordering::Less);
            point = next;
        }
        assert!((&point - integer(1)).abs() < rat(1, 1_000_000_000));
    }

    /// Lean `swing_neither_attracts`: the Swing `z ↦ 1/z` fixes `±1` with `tr = 0`, both derivatives
    /// are `−1` and it is an involution: neutral. Every `tr = 0` navigator with two real fixed
    /// points is neutral.
    #[test]
    fn a_traceless_navigator_is_neutral() {
        for map in [
            navigator(0, 1, 1, 0),
            navigator(3, 1, 2, -3),
            navigator(1, 4, 1, -1),
        ] {
            assert!(map.trace().is_zero());
            assert_eq!(map.attraction().unwrap(), Attraction::Neutral);
            assert_eq!(
                map.chart_scaling().unwrap().as_rational(),
                Some(&integer(-1))
            );
        }
        let swing = navigator(0, 1, 1, 0);
        for point in [integer(2), rat(-3, 7), rat(5, 4)] {
            assert_eq!(swing.act(&swing.act(&point).unwrap()).unwrap(), point);
        }
    }

    /// Lean `chart_conjugates` in `ℚ(√5)`: the cat-map navigator `z ↦ (2z + 1)/(z + 1)` attracts at
    /// `φ = (1 + √5)/2` with derivative `φ⁻⁴`, and its chart scales by that ratio exactly.
    #[test]
    fn the_chart_conjugates_to_a_scaling_in_the_quadratic_field() {
        let map = navigator(2, 1, 1, 1);
        let Attraction::Converging {
            attracting, ratio, ..
        } = map.attraction().unwrap()
        else {
            panic!("the cat map converges");
        };
        let phi = QuadraticSurd::new(rat(1, 2), rat(1, 2), integer(5)).unwrap();
        assert_eq!(finite(&attracting), phi);
        assert_eq!(ratio, phi.power(4).unwrap().inverse().unwrap());
        let mut point = integer(0);
        for _ in 0..12 {
            let next = map.act(&point).unwrap();
            assert_eq!(
                map.chart(&next).unwrap(),
                map.chart(&point).unwrap().mul(&ratio).unwrap()
            );
            point = next;
        }
    }

    /// The other cases: a rotation has no real fixed point (its quadratic is retained), a double
    /// fixed point is parabolic, an affine map fixes `∞`, and a singular block is refused.
    #[test]
    fn rotations_and_parabolic_navigators_do_not_converge_geometrically() {
        let rotation = navigator(0, -1, 1, 0);
        assert_eq!(rotation.kind(), SiteKind::Rotation);
        assert_eq!(rotation.attraction().unwrap(), Attraction::Elliptic);
        assert!(matches!(
            rotation.fixed_points().unwrap(),
            FixedPoints::Conjugate(_)
        ));
        let parabolic = navigator(1, 1, 0, 1);
        assert_eq!(parabolic.kind(), SiteKind::Null);
        assert!(matches!(
            parabolic.attraction().unwrap(),
            Attraction::Parabolic(FixedPoint {
                point: ProjectivePoint::Infinity,
                ..
            })
        ));
        let affine = navigator(3, 2, 0, 1);
        let Attraction::Converging { attracting, .. } = affine.attraction().unwrap() else {
            panic!("an expanding affine map converges to ∞");
        };
        assert_eq!(attracting.point, ProjectivePoint::Infinity);
        assert_eq!(
            MobiusNavigator::new(integer(1), integer(2), integer(2), integer(4)),
            Err(LandmarkError::SingularNavigator)
        );
        assert_eq!(
            navigator(1, 2, 2, 1).act(&rat(-1, 2)),
            Err(LandmarkError::Pole { point: rat(-1, 2) })
        );
    }

    /// Lean `velocity_act`, `velocity_is_boost`, `vadd_fixes_one`, `vaddC_fixes`, `vaddC_iterate`,
    /// `doppler_vadd`, `one_sub_iterate`, `vaddC_iterate_tendsto_c`, `vaddC_iterate_tendsto_neg_c`:
    /// for `c = 3`, `c = 1/2` and `c = 1`, velocity addition fixes `±c`, has `γ² = 1/(1 − v²/c²)`,
    /// attracts at `c` for `v > 0` and at `−c` for `v < 0`, and its iterates' Doppler ratio is
    /// exactly `D(u₀)·D(v)ⁿ` while `c − u_n = 2c/(D(u_n) + 1)`: the gap to the attracting landmark
    /// falls strictly toward zero.
    #[test]
    fn velocity_addition_converges_to_its_characteristic() {
        for (characteristic, velocity, start) in [
            (integer(3), integer(1), integer(-2)),
            (rat(1, 2), rat(1, 5), rat(-1, 3)),
            (integer(1), rat(3, 5), integer(0)),
            (integer(3), integer(-1), integer(2)),
            (rat(1, 2), rat(-1, 5), rat(1, 3)),
        ] {
            let map = velocity_addition(&velocity, &characteristic).unwrap();
            let Attraction::Converging {
                attracting,
                repelling,
                ..
            } = map.attraction().unwrap()
            else {
                panic!("a boost converges");
            };
            let landmark = if velocity.is_positive() {
                characteristic.clone()
            } else {
                -characteristic.clone()
            };
            assert_eq!(finite(&attracting).as_rational(), Some(&landmark));
            assert_eq!(finite(&repelling).as_rational(), Some(&-landmark.clone()));
            let ratio = &velocity / &characteristic;
            assert_eq!(
                map.lorentz_factor_squared().unwrap(),
                (Rat::one() - &ratio * &ratio).recip()
            );
            assert_eq!(map.kind(), SiteKind::Boost);
            let boost = doppler_chart(&velocity, &characteristic).unwrap();
            let origin = doppler_chart(&start, &characteristic).unwrap();
            let mut velocity_now = start.clone();
            let mut power = Rat::one();
            let mut gap = (&landmark - &start).abs();
            for _ in 0..40 {
                velocity_now = map.act(&velocity_now).unwrap();
                power *= &boost;
                let doppler = doppler_chart(&velocity_now, &characteristic).unwrap();
                assert_eq!(doppler, &origin * &power);
                assert_eq!(
                    &characteristic - &velocity_now,
                    integer(2) * &characteristic / (&doppler + Rat::one())
                );
                let next_gap = (&landmark - &velocity_now).abs();
                assert!(next_gap.is_positive() && next_gap < gap);
                gap = next_gap;
            }
            assert!(gap < rat(1, 1_000_000));
        }
        assert!(velocity_addition(&integer(3), &integer(3)).is_err());
        assert!(velocity_addition(&integer(1), &integer(-2)).is_err());
    }
}
