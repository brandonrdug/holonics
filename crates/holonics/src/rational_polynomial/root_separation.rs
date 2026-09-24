use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use crate::geometry::Rat;
use serde::{Deserialize, Serialize};

use super::{ExactPolynomialError, squared_shrinking_steps};

/// The exact material Mahler's bound is read off, and the bound itself.
///
/// **The wire re-derives the bound.** `squared_lower_bound` is a function of the three fields
/// beside it — `3 |disc| / ( n^(n+2) (‖f‖²)^(n-1) )` — so a remounted bound is recomputed from
/// them and refused when it disagrees, rather than carried as a number nobody checked. A caller who
/// declared a *larger* bound would make [`RootSeparation::holds_at_most_one_root`] claim an
/// interval holds one root when it holds two, and `super::isolate_within` reports exactly that
/// disagreement as a Sturm/discriminant contradiction — which it would not be.
///
/// `degree` is a caller-declared extent and it sizes both powers above, so it is gated before
/// either is taken.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "RootSeparationBoundWire")]
pub struct RootSeparationBound {
    pub degree: usize,
    /// `disc(f)`, nonzero exactly because `f` is squarefree.
    pub discriminant: BigInt,
    /// `||f||_2^2 = sum a_i^2`.
    pub coefficient_norm_squared: BigInt,
    /// `3 |disc(f)| / ( n^(n+2) (||f||_2^2)^(n-1) )`, which is strictly below `sep(f)^2`.
    pub squared_lower_bound: Rat,
    /// Exact work of the Euclidean resultant, in division steps. Never a clock.
    pub euclidean_steps: u64,
}

#[derive(Deserialize)]
struct RootSeparationBoundWire {
    degree: usize,
    discriminant: BigInt,
    coefficient_norm_squared: BigInt,
    squared_lower_bound: Rat,
    euclidean_steps: u64,
}

impl TryFrom<RootSeparationBoundWire> for RootSeparationBound {
    type Error = ExactPolynomialError;

    fn try_from(wire: RootSeparationBoundWire) -> Result<Self, Self::Error> {
        if wire.degree < 2 {
            return Err(ExactPolynomialError::DiscriminantDegreeTooLow {
                degree: wire.degree,
            });
        }
        // Mahler's bound needs a squarefree polynomial, which is exactly a nonvanishing
        // discriminant; a zero one names no bound at all.
        if wire.discriminant.is_zero() {
            return Err(ExactPolynomialError::VanishingDiscriminant);
        }
        // `degree` sizes `n^(n+2)` and `(‖f‖²)^(n-1)` below, and `‖f‖²` sizes the second
        // outright, so both are refused before either power is taken.
        crate::exact_value::check_declared_sturm_work(
            wire.degree,
            wire.coefficient_norm_squared.bits(),
        )?;
        let exponent =
            u32::try_from(wire.degree + 2).map_err(|_| ExactPolynomialError::DegreeTooLarge)?;
        let power =
            u32::try_from(wire.degree - 1).map_err(|_| ExactPolynomialError::DegreeTooLarge)?;
        let denominator = BigInt::from(wire.degree).pow(exponent)
            * wire.coefficient_norm_squared.pow(power);
        if denominator.is_zero() {
            return Err(ExactPolynomialError::MalformedRootSeparation);
        }
        let derived = Rat::new(BigInt::from(3) * wire.discriminant.abs(), denominator);
        if derived != wire.squared_lower_bound {
            return Err(ExactPolynomialError::MalformedRootSeparation);
        }
        Ok(Self {
            degree: wire.degree,
            discriminant: wire.discriminant,
            coefficient_norm_squared: wire.coefficient_norm_squared,
            squared_lower_bound: wire.squared_lower_bound,
            euclidean_steps: wire.euclidean_steps,
        })
    }
}

/// What the material says about how close two of its roots may be.
///
/// The wire refuses a `NothingToSeparate` that claims a degree with a pair of roots in it; the
/// `Bounded` arm carries its own re-derivation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "RootSeparationWire")]
pub enum RootSeparation {
    /// Degree below two. There is no pair of roots, so no interval can hold two of them and no
    /// split can ever be required. This is a statement about the polynomial, not a missing bound.
    NothingToSeparate {
        degree: usize,
    },
    Bounded(RootSeparationBound),
}

#[derive(Deserialize)]
enum RootSeparationWire {
    NothingToSeparate { degree: usize },
    Bounded(RootSeparationBound),
}

impl TryFrom<RootSeparationWire> for RootSeparation {
    type Error = ExactPolynomialError;

    fn try_from(wire: RootSeparationWire) -> Result<Self, Self::Error> {
        match wire {
            RootSeparationWire::NothingToSeparate { degree } => {
                if degree >= 2 {
                    // Degree two has a pair of roots, so "nothing to separate" is false of it and
                    // `holds_at_most_one_root` would answer `true` for every width.
                    return Err(ExactPolynomialError::MalformedRootSeparation);
                }
                Ok(Self::NothingToSeparate { degree })
            }
            RootSeparationWire::Bounded(bound) => Ok(Self::Bounded(bound)),
        }
    }
}

impl RootSeparation {
    /// The squared separation floor, when the polynomial has degree at least two.
    pub fn squared_lower_bound(&self) -> Option<&Rat> {
        match self {
            Self::NothingToSeparate { .. } => None,
            Self::Bounded(bound) => Some(&bound.squared_lower_bound),
        }
    }

    /// Whether an interval of this width provably holds at most one root.
    ///
    /// `width^2 <= S < sep(f)^2` forces `width < sep(f)`, and two distinct roots inside one open
    /// interval are closer than its width.
    pub fn holds_at_most_one_root(&self, width: &Rat) -> bool {
        match self.squared_lower_bound() {
            None => true,
            Some(square) => &(width * width) <= square,
        }
    }

    /// How many splits at a retained fraction of `retained` bring an interval of width
    /// `initial_width` down to one that provably holds at most one root.
    ///
    /// `retained` is the largest fraction of an interval that one child of a split may keep — a
    /// property of the declared split schedule, obtained from [`super::worst_retained_fraction`]. Nothing
    /// here is chosen: the width comes from the caller, the schedule from the organ, and the floor
    /// from the discriminant.
    pub fn splitting_depth(
        &self,
        initial_width: &Rat,
        retained: &Rat,
    ) -> Result<u64, ExactPolynomialError> {
        match self.squared_lower_bound() {
            None => Ok(0),
            Some(square) => {
                squared_shrinking_steps(&(initial_width * initial_width), retained, square)
            }
        }
    }
}
