//! **Exact local-place reading of a nonzero rational.**
//!
//! [definition] A rational is read as its sign, finite prime-valuation series, and
//! archimedean absolute value. For every admitted prime `p`, the finite local
//! factor is `p^(-v_p(x))`. The finite support is ascending and contains no zero
//! valuation. This arithmetic receiver carries no physical conservation claim.
//!
//! # Mathematical contract
//!
//! The existing Lean owner is
//! `lean/HolonicsResearch/Geometry/PlaceLedger.lean`, namespace
//! `Holonics.Geometry.PlaceLedger`:
//!
//! - `ledger`, `localFactor`, `places` define the finite reading;
//! - `theLedgerIsThePAdicValuation` identifies its valuation;
//! - `theProductOverEveryPlaceIsOne` proves, for `x != 0`,
//!   `|x| * product_p p^(-v_p(x)) = 1`;
//! - `theInversionNegatesTheLedger` proves the inversion law;
//! - `theFiniteLedgerDeterminesTheRationalUpToSign` names the sign fibre retained
//!   explicitly by this receiver.
//!
//! [`PlaceReading::archimedean_factor`] is `|x|`, as used by the product formula.
//! The height factor `max(1, |x|)` is a different receiver in that Lean owner.
//!
//! Construction reuses the crate's single
//! exact factorization owner, [`super::surprisal::factor_biguint`]. It checks the
//! exact product and signed reconstruction of this input before returning. Those
//! equality receipts, when executed by a consumer, are finite runtime checks,
//! not a new formal proof or fresh
//! kernel acceptance of the Lean statements. The unit tests are bounded fixtures.
//!
//! # Domain and cost
//!
//! A zero numerator and a raw zero denominator are separate typed refusals.
//! Other raw `Rat` representations are reduced and their denominator sign is
//! normalized before any reading or factorization. All fields are private so a
//! caller cannot manufacture a prime or local factor without that construction.
//!
//! Factoring uses the existing exact trial division on the reduced numerator and
//! denominator, followed by exact prime powers and rational products. Cost depends
//! on their magnitudes and bit lengths; it is not constant or bounded by the
//! count of returned primes. The existing owner may refuse a residual prime above
//! its `u64` carrier. This receiver adds no duplicate factorizer, probabilistic
//! primality test, factor cache, or arbitrary workload ceiling.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use thiserror::Error;

use super::Rat;
use super::surprisal::{SurprisalError, factor_biguint};

/// The sign information the finite valuation series cannot distinguish.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlaceSign {
    Positive,
    Negative,
}

impl PlaceSign {
    /// The exact sign, suitable for multiplying a positive reconstruction.
    pub fn as_integer(self) -> i8 {
        match self {
            Self::Positive => 1,
            Self::Negative => -1,
        }
    }
}

/// A nonzero finite-place valuation and its exact normalized local factor.
///
/// Values can only be obtained from [`PlaceReading::of`], which consumes actual
/// factors returned by the existing factorization owner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinitePlace {
    prime: u64,
    valuation: i64,
    local_factor: Rat,
}

impl FinitePlace {
    pub fn prime(&self) -> u64 {
        self.prime
    }

    /// `v_p(x) = v_p(|numerator|) - v_p(denominator)`.
    ///
    /// The owner's exponents are `u32`. Both widen to `i64` before subtraction,
    /// so even their extreme difference is represented without signed overflow.
    pub fn valuation(&self) -> i64 {
        self.valuation
    }

    /// The positive exact rational `p^(-v_p(x))`.
    pub fn local_factor(&self) -> &Rat {
        &self.local_factor
    }
}

/// Every refusal of the rational-place receiver.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum PlaceError {
    #[error("a rational-place reading refuses a raw zero denominator")]
    ZeroDenominator,
    #[error("the product formula requires a nonzero rational")]
    ZeroRational,
    #[error(transparent)]
    Factorization(#[from] SurprisalError),
    #[error("the factored places did not reconstruct the admitted rational exactly")]
    ReconstructionFailed,
    #[error("the exact product over the admitted rational's places was not one")]
    ProductFormulaFailed,
}

/// A checked exact arithmetic receipt over this one nonzero rational's places.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlaceReading {
    sign: PlaceSign,
    places: Vec<FinitePlace>,
    archimedean_factor: Rat,
}

impl PlaceReading {
    /// Read the sign and every nontrivial finite local factor of `value`.
    ///
    /// Raw denominator validation precedes rational normalization, avoiding a
    /// panic from `Rat::new` on an exterior `Rat::new_raw(_, 0)` input. Valid raw
    /// representations are normalized; their exact represented rational is the
    /// input whose reconstruction and product-one equalities are checked.
    pub fn of(value: &Rat) -> Result<Self, PlaceError> {
        if value.denom().is_zero() {
            return Err(PlaceError::ZeroDenominator);
        }
        if value.numer().is_zero() {
            return Err(PlaceError::ZeroRational);
        }
        let normalized = Rat::new(value.numer().clone(), value.denom().clone());
        let sign = if normalized.is_negative() {
            PlaceSign::Negative
        } else {
            PlaceSign::Positive
        };

        // This map only merges exponents returned by the existing exact owner.
        // No caller-supplied prime or exponent enters this construction.
        let mut exponents: BTreeMap<u64, (u32, u32)> = BTreeMap::new();
        for (prime, exponent) in factor_biguint(normalized.numer().magnitude())? {
            exponents.entry(prime).or_default().0 = exponent;
        }
        for (prime, exponent) in factor_biguint(normalized.denom().magnitude())? {
            exponents.entry(prime).or_default().1 = exponent;
        }
        let places = exponents
            .into_iter()
            .filter_map(|(prime, (numerator_exponent, denominator_exponent))| {
                let valuation = i64::from(numerator_exponent) - i64::from(denominator_exponent);
                if valuation == 0 {
                    return None;
                }
                // Compute p^(-v) using only the owner's unsigned exponents.
                // There is no signed negation, abs, narrowing cast, or signed
                // pow operation whose minimum value could overflow.
                let base = BigInt::from(prime);
                let local_factor =
                    Rat::new(base.pow(denominator_exponent), base.pow(numerator_exponent));
                Some(FinitePlace {
                    prime,
                    valuation,
                    local_factor,
                })
            })
            .collect();

        let reading = Self {
            sign,
            places,
            archimedean_factor: normalized.abs(),
        };
        if reading.reconstruct() != normalized {
            return Err(PlaceError::ReconstructionFailed);
        }
        if !reading.product_one() {
            return Err(PlaceError::ProductFormulaFailed);
        }
        Ok(reading)
    }

    pub fn sign(&self) -> PlaceSign {
        self.sign
    }

    /// All primes with nonzero valuation, in ascending prime order.
    pub fn places(&self) -> &[FinitePlace] {
        &self.places
    }

    /// The archimedean factor `|x|`, without a logarithm or decimal evaluation.
    pub fn archimedean_factor(&self) -> &Rat {
        &self.archimedean_factor
    }

    /// Multiply the exact archimedean and finite local factors.
    pub fn product(&self) -> Rat {
        self.places
            .iter()
            .fold(self.archimedean_factor.clone(), |product, place| {
                product * place.local_factor()
            })
    }

    /// The exact equality receipt `|x| * product_p p^(-v_p(x)) == 1`.
    pub fn product_one(&self) -> bool {
        self.product() == Rat::one()
    }

    /// Reconstruct the rational from its finite local factors and retained sign.
    ///
    /// This does not return a stored copy of the input or use its archimedean
    /// reading: it multiplies `sign(x) * product_p p^(v_p(x))` exactly.
    pub fn reconstruct(&self) -> Rat {
        self.places.iter().fold(
            Rat::from_integer(BigInt::from(self.sign.as_integer())),
            |product, place| product / place.local_factor(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::{integer, rat};

    fn series(reading: &PlaceReading) -> Vec<(u64, i64)> {
        reading
            .places()
            .iter()
            .map(|place| (place.prime(), place.valuation()))
            .collect()
    }

    #[test]
    fn numerator_and_denominator_places_reconstruct_with_product_one() {
        let value = rat(12, 35);
        let reading = PlaceReading::of(&value).unwrap();
        assert_eq!(reading.sign(), PlaceSign::Positive);
        assert_eq!(series(&reading), vec![(2, 2), (3, 1), (5, -1), (7, -1)]);
        let local: Vec<_> = reading
            .places()
            .iter()
            .map(|place| place.local_factor().clone())
            .collect();
        assert_eq!(local, vec![rat(1, 4), rat(1, 3), integer(5), integer(7)]);
        // Distinguishes the product-formula factor from max(1, |x|).
        assert_eq!(reading.archimedean_factor(), &value);
        assert_eq!(reading.reconstruct(), value);
        assert_eq!(reading.product(), Rat::one());
        assert!(reading.product_one());
    }

    #[test]
    fn inversion_negates_every_valuation_and_inverts_each_factor() {
        let value = rat(-12, 35);
        let direct = PlaceReading::of(&value).unwrap();
        let inverse = PlaceReading::of(&value.recip()).unwrap();
        assert_eq!(direct.sign(), PlaceSign::Negative);
        assert_eq!(inverse.sign(), PlaceSign::Negative);
        assert_eq!(direct.places().len(), inverse.places().len());
        for (place, opposite) in direct.places().iter().zip(inverse.places()) {
            assert_eq!(place.prime(), opposite.prime());
            assert_eq!(place.valuation(), -opposite.valuation());
            assert_eq!(place.local_factor() * opposite.local_factor(), Rat::one());
        }
        assert_eq!(direct.reconstruct(), value);
        assert_eq!(inverse.reconstruct(), value.recip());
        assert_eq!(
            direct.archimedean_factor() * inverse.archimedean_factor(),
            Rat::one()
        );
        assert!(direct.product_one());
        assert!(inverse.product_one());
    }

    #[test]
    fn sign_is_retained_even_when_all_finite_places_are_identical() {
        let positive = PlaceReading::of(&rat(12, 35)).unwrap();
        let negative = PlaceReading::of(&rat(-12, 35)).unwrap();
        assert_eq!(positive.places(), negative.places());
        assert_eq!(positive.archimedean_factor(), negative.archimedean_factor());
        assert_eq!(positive.reconstruct(), -negative.reconstruct());
        for value in [integer(1), integer(-1)] {
            let unit = PlaceReading::of(&value).unwrap();
            assert!(unit.places().is_empty());
            assert_eq!(unit.reconstruct(), value);
            assert!(unit.product_one());
        }
    }

    #[test]
    fn valid_raw_input_is_reduced_before_its_sign_and_places_are_read() {
        let raw = Rat::new_raw(BigInt::from(-24), BigInt::from(-70));
        let reading = PlaceReading::of(&raw).unwrap();
        assert_eq!(reading, PlaceReading::of(&rat(12, 35)).unwrap());
        assert_eq!(reading.reconstruct(), rat(12, 35));
        let negative = Rat::new_raw(BigInt::from(24), BigInt::from(-70));
        assert_eq!(
            PlaceReading::of(&negative).unwrap(),
            PlaceReading::of(&rat(-12, 35)).unwrap()
        );
    }

    #[test]
    fn zero_and_raw_zero_denominator_are_typed_refusals() {
        assert_eq!(
            PlaceReading::of(&Rat::zero()),
            Err(PlaceError::ZeroRational)
        );
        for numerator in [BigInt::zero(), BigInt::one()] {
            let raw = Rat::new_raw(numerator, BigInt::zero());
            assert_eq!(PlaceReading::of(&raw), Err(PlaceError::ZeroDenominator));
        }
        let raw_zero = Rat::new_raw(BigInt::zero(), BigInt::from(-7));
        assert_eq!(PlaceReading::of(&raw_zero), Err(PlaceError::ZeroRational));
    }
}
