use crate::ratio::Rat;
use num_bigint::BigInt;

use super::{ExactPolynomialError, squared_shrinking_steps};

/// The exact material Mahler's bound is read off, and the bound itself.
///
/// `squared_lower_bound` is a function of the three fields beside it,
/// `3 |disc| / ( n^(n+2) (‖f‖²)^(n-1) )`. A *larger* bound would make
/// [`RootSeparation::holds_at_most_one_root`] claim an interval holds one root when it holds two.
///
/// `degree` is a caller-declared extent and it sizes both powers above, so it is gated before
/// either is taken.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RootSeparationBound {
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

/// What the material says about how close two of its roots may be.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RootSeparation {
    /// Degree below two. There is no pair of roots, so no interval can hold two of them and no
    /// split can ever be required. This is a statement about the polynomial, not a missing bound.
    NothingToSeparate {
        degree: usize,
    },
    Bounded(RootSeparationBound),
}

impl RootSeparation {
    /// The squared separation floor, when the polynomial has degree at least two.
    pub(crate) fn squared_lower_bound(&self) -> Option<&Rat> {
        match self {
            Self::NothingToSeparate { .. } => None,
            Self::Bounded(bound) => Some(&bound.squared_lower_bound),
        }
    }

    /// Whether an interval of this width provably holds at most one root.
    ///
    /// `width^2 <= S < sep(f)^2` forces `width < sep(f)`, and two distinct roots inside one open
    /// interval are closer than its width.
    pub(crate) fn holds_at_most_one_root(&self, width: &Rat) -> bool {
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
    pub(crate) fn splitting_depth(
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
