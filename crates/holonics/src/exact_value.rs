//! Typed exact values used by causal parameters and future geometric laws.
//!
//! A decimal approximation is never a member of this carrier.  Values which
//! cannot yet be ordered from their exact certificates return `Open` rather
//! than falling through to an epsilon comparison.
//!
//! ## The one floating-point boundary
//!
//! [`ieee754`] is the **single declared floating-point exception** in the library files of this
//! workspace, and it is a codec and nothing else: a bit pattern goes in, an exact dyadic comes out,
//! and no arithmetic is ever performed on the machine float. Everything downstream of it —
//! including `crate::reopening`, which is what it was built to feed — sees `BigInt`, `BigUint` and
//! `Rat` and never an IEEE scalar.

use std::cmp::Ordering;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use crate::geometry::{ExactExpr, Rat};
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Return the primitive integer representative of one homogeneous tuple.
///
/// A projective point, projective map, or homogeneous form is unchanged by a
/// common nonzero factor. Carrying the particular denominators introduced by
/// an earlier chart calculation therefore preserves arithmetic history rather
/// than geometry. This routine clears that history at the boundary where a
/// new homogeneous object is founded.
pub fn canonical_homogeneous<const N: usize>(values: [Rat; N]) -> [Rat; N] {
    let common_denominator = values.iter().fold(BigInt::one(), |common, value| {
        let denominator = value.denom().clone();
        let divisor = exact_integer_gcd(common.clone(), denominator.clone());
        common / divisor * denominator
    });
    let mut integer = values.map(|value| value.numer() * (&common_denominator / value.denom()));
    let content = integer
        .iter()
        .filter(|value| !value.is_zero())
        .map(Signed::abs)
        .reduce(exact_integer_gcd)
        .unwrap_or_else(BigInt::one);
    if !content.is_zero() {
        for value in &mut integer {
            *value /= &content;
        }
    }
    if integer
        .iter()
        .find(|value| !value.is_zero())
        .is_some_and(Signed::is_negative)
    {
        for value in &mut integer {
            *value = -value.clone();
        }
    }
    integer.map(Rat::from_integer)
}

fn exact_integer_gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    left = left.abs();
    right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactOrdering {
    Less,
    Equal,
    Greater,
    Open,
}

impl From<Ordering> for ExactOrdering {
    fn from(value: Ordering) -> Self {
        match value {
            Ordering::Less => Self::Less,
            Ordering::Equal => Self::Equal,
            Ordering::Greater => Self::Greater,
        }
    }
}

/// A remounted interval passes through [`ExactInterval::new`]: the wire has the same two fields, and
/// a reversed enclosure is refused at the boundary rather than reconstructed past the constructor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ExactIntervalWire")]
pub struct ExactInterval {
    pub lower: Rat,
    pub upper: Rat,
}

#[derive(Deserialize)]
struct ExactIntervalWire {
    lower: Rat,
    upper: Rat,
}

impl TryFrom<ExactIntervalWire> for ExactInterval {
    type Error = ExactValueError;

    fn try_from(wire: ExactIntervalWire) -> Result<Self, Self::Error> {
        Self::new(wire.lower, wire.upper)
    }
}

impl ExactInterval {
    pub fn new(lower: Rat, upper: Rat) -> Result<Self, ExactValueError> {
        if lower > upper {
            return Err(ExactValueError::ReversedInterval);
        }
        Ok(Self { lower, upper })
    }

    pub fn point(value: Rat) -> Self {
        Self {
            lower: value.clone(),
            upper: value,
        }
    }

    pub fn is_point(&self) -> bool {
        self.lower == self.upper
    }

    pub fn translated(&self, offset: &Rat) -> Self {
        Self {
            lower: &self.lower + offset,
            upper: &self.upper + offset,
        }
    }

    /// **Widen outward onto a dyadic grid, so a chain of enclosures cannot grow its denominator
    /// without bound.**
    ///
    /// The result strictly contains the original — the lower bound floors and the upper ceils — so
    /// nothing is lost, and the denominators stay at `2^octaves` however long the chain runs.
    /// Measured 2026-08-18: a geometric ladder of one hundred and twenty-eight enclosures founded
    /// by exact multiplication carried denominators of five thousand six hundred bits, and a
    /// twenty-four term series on each was the whole cost of a site.
    pub fn round_out(&self, octaves: u32) -> Result<Self, ExactValueError> {
        let scale = Rat::from_integer(BigInt::from(BigUint::one() << octaves as usize));
        let unit = scale.recip();
        let floor = |value: &Rat| -> Rat {
            let scaled = value * &scale;
            let truncated = scaled.to_integer();
            let corrected =
                if scaled.is_negative() && Rat::from_integer(truncated.clone()) != scaled {
                    truncated - BigInt::one()
                } else {
                    truncated
                };
            Rat::from_integer(corrected) * &unit
        };
        let ceiling = |value: &Rat| -> Rat {
            let scaled = value * &scale;
            let truncated = scaled.to_integer();
            let corrected =
                if scaled.is_positive() && Rat::from_integer(truncated.clone()) != scaled {
                    truncated + BigInt::one()
                } else {
                    truncated
                };
            Rat::from_integer(corrected) * &unit
        };
        Self::new(floor(&self.lower), ceiling(&self.upper))
    }

    /// The product of two enclosures. **An interval is a set, so the product is the set's.**
    pub fn times(&self, other: &Self) -> Result<Self, ExactValueError> {
        let corners = [
            &self.lower * &other.lower,
            &self.lower * &other.upper,
            &self.upper * &other.lower,
            &self.upper * &other.upper,
        ];
        let mut lower = corners[0].clone();
        let mut upper = corners[0].clone();
        for corner in &corners[1..] {
            if *corner < lower {
                lower = corner.clone();
            }
            if *corner > upper {
                upper = corner.clone();
            }
        }
        Self::new(lower, upper)
    }

    /// **Refuses across zero rather than widening to infinity**, which is the honest return: the
    /// reciprocal of a set containing zero is not an interval.
    pub fn reciprocal(&self) -> Result<Self, ExactValueError> {
        if !self.lower.is_positive() && !self.upper.is_negative() {
            return Err(ExactValueError::ReciprocalStraddlesZero);
        }
        let a = self.lower.recip();
        let b = self.upper.recip();
        if a <= b {
            Self::new(a, b)
        } else {
            Self::new(b, a)
        }
    }

    /// An integer power of the set, by **binary exponentiation**, held at a declared grain.
    ///
    /// Repeated multiplication costs the exponent; binary exponentiation costs its octaves.
    /// Measured 2026-08-18, a gated passage over ten thousand two hundred and forty entries spent
    /// `17.4` seconds of an `18.4`-second site inside this call, because a `tanh` at `|x| < 32`
    /// composes up to sixty-three steps and each entry paid all of them.
    ///
    /// `octaves` holds every intermediate outward on a dyadic grid, so a long power cannot grow its
    /// denominators; the enclosure only ever widens and what it could not carry is inside it.
    pub fn power_held(&self, exponent: u32, octaves: u32) -> Result<Self, ExactValueError> {
        let mut result = Self::point(Rat::one());
        let mut square = self.clone();
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining & 1 == 1 {
                result = result.times(&square)?.round_out(octaves)?;
            }
            remaining >>= 1;
            if remaining > 0 {
                square = square.times(&square)?.round_out(octaves)?;
            }
        }
        Ok(result)
    }

    /// An integer power of the set, exactly, with no grain. A caller composing a long chain wants
    /// [`Self::power_held`]; this is for a short one where the exactness is the point.
    pub fn power(&self, exponent: u32) -> Result<Self, ExactValueError> {
        let mut result = Self::point(Rat::one());
        let mut square = self.clone();
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining & 1 == 1 {
                result = result.times(&square)?;
            }
            remaining >>= 1;
            if remaining > 0 {
                square = square.times(&square)?;
            }
        }
        Ok(result)
    }

    pub fn disjoint_order(&self, other: &Self) -> ExactOrdering {
        if self.upper < other.lower {
            ExactOrdering::Less
        } else if self.lower > other.upper {
            ExactOrdering::Greater
        } else if self.is_point() && other.is_point() && self.lower == other.lower {
            ExactOrdering::Equal
        } else {
            ExactOrdering::Open
        }
    }
}

/// Integer polynomial with coefficients in ascending power order.
///
/// **The normal form is part of the type.** [`IntegerPolynomial::new`] trims trailing zeros and
/// refuses the zero polynomial, so a member of this type always carries a nonempty coefficient
/// list whose last entry is nonzero. The wire enforces exactly that normal form — empty is
/// refused as [`ExactValueError::ZeroPolynomial`], a zero leading coefficient as
/// [`ExactValueError::UntrimmedPolynomialWire`] — and additionally passes
/// [`IntegerPolynomial::check_declared_size`], because a remounted polynomial's degree and
/// coefficient width are caller-declared extents exactly as a constructed one's are.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "IntegerPolynomialWire")]
pub struct IntegerPolynomial {
    pub coefficients: Vec<BigInt>,
}

#[derive(Deserialize)]
struct IntegerPolynomialWire {
    coefficients: Vec<BigInt>,
}

impl TryFrom<IntegerPolynomialWire> for IntegerPolynomial {
    type Error = ExactValueError;

    fn try_from(wire: IntegerPolynomialWire) -> Result<Self, Self::Error> {
        if wire.coefficients.is_empty() {
            return Err(ExactValueError::ZeroPolynomial);
        }
        // `new` *normalizes* a trailing zero away; a wire that carries one is declaring a degree
        // it does not have, so it is refused rather than quietly re-normalized into a different
        // polynomial than the one the declaration named.
        if wire.coefficients.last().is_some_and(Zero::is_zero) {
            return Err(ExactValueError::UntrimmedPolynomialWire {
                declared: wire.coefficients.len(),
            });
        }
        let polynomial = Self {
            coefficients: wire.coefficients,
        };
        polynomial.check_declared_size()?;
        Ok(polynomial)
    }
}

impl IntegerPolynomial {
    pub fn new(mut coefficients: Vec<BigInt>) -> Result<Self, ExactValueError> {
        trim_integer_polynomial(&mut coefficients);
        if coefficients.is_empty() {
            return Err(ExactValueError::ZeroPolynomial);
        }
        Ok(Self { coefficients })
    }

    /// The degree.
    ///
    /// **Total.** The normal form makes the list nonempty, so this is `len - 1` for every
    /// polynomial the constructor or the wire admits. The field is public, so a direct mutation
    /// can still empty it; the convention for that unreachable-by-construction case is **degree
    /// zero**, because an empty list carries no power above the constant one. It is emphatically
    /// not `len() - 1`, which panics in a debug build and wraps to `usize::MAX` in a release
    /// build — this workspace's release profile carries no overflow checks — and then flows into
    /// [`IntegerPolynomial::check_declared_size`] and every consumer as a declared extent.
    pub fn degree(&self) -> usize {
        self.coefficients.len().saturating_sub(1)
    }

    pub fn evaluate(&self, point: &Rat) -> Rat {
        self.coefficients
            .iter()
            .rev()
            .fold(Rat::zero(), |value, coefficient| {
                value * point + Rat::from_integer(coefficient.clone())
            })
    }

    /// The coefficients over `Q`. Only the retained naive Sturm reference needs them.
    #[cfg(test)]
    fn rational_coefficients(&self) -> Vec<Rat> {
        self.coefficients
            .iter()
            .cloned()
            .map(Rat::from_integer)
            .collect()
    }

    /// Count distinct real roots in one strict rational interval using the
    /// exact Sturm sequence. Interval endpoints may not themselves be roots.
    ///
    /// **This builds the chain and throws it away.** A caller taking more than one count against
    /// the same polynomial — every bisection, every isolation, every refinement — should build one
    /// [`SturmChain`] with [`IntegerPolynomial::sturm_chain`] and count against it, which is what
    /// the chain exists for.
    pub fn distinct_root_count(&self, interval: &ExactInterval) -> Result<u32, ExactValueError> {
        SturmChain::of(self)?.distinct_root_count(interval)
    }

    /// The Sturm–Habicht chain of this polynomial, built once.
    pub fn sturm_chain(&self) -> Result<SturmChain, ExactValueError> {
        SturmChain::of(self)
    }

    /// **Refuse a declared degree or coefficient width above the root-counting owner's ceilings.**
    ///
    /// [definition] Degree and coefficient bit length are both caller-declared extents: the first
    /// sizes every loop, recursion and allocation in the chain and in the root bounds, the second
    /// sizes every integer operation in them. Every public entry point that will do work
    /// proportional to either passes through here first, so the refusal happens before the work
    /// and not inside it.
    pub fn check_declared_size(&self) -> Result<(), ExactValueError> {
        // The public field admits a direct mutation the constructor and the wire do not; an empty
        // list names no polynomial, so it is refused here rather than read as a degree-zero one.
        if self.coefficients.is_empty() {
            return Err(ExactValueError::ZeroPolynomial);
        }
        let degree = self.degree();
        if degree > STURM_DEGREE_CEILING {
            return Err(ExactValueError::SturmDegreeTooLarge {
                degree,
                ceiling: STURM_DEGREE_CEILING,
            });
        }
        let widest = self
            .coefficients
            .iter()
            .map(BigInt::bits)
            .max()
            .unwrap_or(0);
        if widest > STURM_COEFFICIENT_BIT_CEILING {
            return Err(ExactValueError::SturmCoefficientTooWide {
                bits: widest,
                ceiling: STURM_COEFFICIENT_BIT_CEILING,
            });
        }
        check_declared_sturm_work(degree, widest)
    }
}

/// **The declared ceiling on the degree a Sturm chain is built for.**
///
/// [definition] A polynomial's degree is a caller-declared extent: it sizes the chain's length, the
/// pseudo-division's inner loop and every coefficient that grows down the chain. A polynomial above
/// this degree is refused by name with [`ExactValueError::SturmDegreeTooLarge`] rather than
/// accepted and discovered at the machine's expense. The ceiling is far above anything this
/// workspace's exact spectra present — a `24 × 24` Laplacian is degree twenty-four.
///
/// **Measured, not chosen.** This was 4096 while the chain took primitive parts, and 4096 was not a
/// bound on anything: a degree-800 dense polynomial with five-bit coefficients took 38 s to build,
/// and the cost grows like the fourth power of the degree, so the declared ceiling admitted
/// computations of hours. Degree and width do not bound the work separately, which is what
/// [`STURM_WORK_CEILING`] is for; this ceiling is retained as the **cheap** first refusal, taken
/// before any coefficient is scanned.
pub const STURM_DEGREE_CEILING: usize = 1024;

/// **The declared ceiling on a coefficient's bit length at the Sturm owner.**
///
/// [definition] The second caller-declared size. Four megabits is about 1.2 million decimal digits
/// per coefficient, orders of magnitude above the Hadamard-sized coefficients an exact
/// characteristic polynomial produces. Refused by name as
/// [`ExactValueError::SturmCoefficientTooWide`]. Like [`STURM_DEGREE_CEILING`] it is a cheap
/// individual refusal; [`STURM_WORK_CEILING`] is what bounds the two together.
pub const STURM_COEFFICIENT_BIT_CEILING: u64 = 1 << 22;

/// **The declared ceiling on the combined work one Sturm chain may be asked for.**
///
/// [measured] Degree and coefficient width bound the chain's cost only *together*. The chain has
/// `O(degree)` members, each of `O(degree)` coefficients, and the subresultants' coefficients grow
/// to `O(degree · bits)`, so the natural index of a chain's work is
///
/// ```text
///   W = degree^3 · (widest coefficient bits + 1)
/// ```
///
/// which is what this ceiling is taken against. It is an **index**, not a cost model: it is
/// calibrated against real material rather than derived. The measurement is
/// `exact_value::sturm_chain_tests::the_subresultant_chain_is_measured_against_the_primitive_one`,
/// on dense integer polynomials with coefficients in `[-10, 10]`, release profile:
///
/// ```text
///   degree   W          subresultant   the primitive PRS this replaced
///       50   6.3e5         0.9 ms          2.6 ms
///      100   5.0e6         6.1 ms         13.5 ms
///      200   4.0e7          78 ms          161 ms
///      400   3.2e8         1.22 s          2.90 s
///      800   2.6e9        18.38 s         38.00 s
/// ```
///
/// `1 << 33` is about 8.6e9, a little over three times the largest index measured, so a declaration
/// admitted here is one the implementation has been *seen* to finish in tens of seconds. Anything
/// past it is refused by name with [`ExactValueError::SturmWorkTooLarge`] rather than accepted and
/// discovered at the machine's expense. A caller that legitimately needs more raises this with a
/// new measurement, which is the only thing that should move it.
pub const STURM_WORK_CEILING: u128 = 1 << 33;

/// **Refuse a declared degree and coefficient width whose combined work index is past
/// [`STURM_WORK_CEILING`].**
///
/// [definition] Taken on *declared numbers*, not on a polynomial, so a caller that can predict the
/// width of a polynomial it is about to build — `rational_polynomial::rational_root_census`'s monic
/// companion is the case this exists for — refuses **before** forming it rather than after.
pub fn check_declared_sturm_work(degree: usize, widest_bits: u64) -> Result<(), ExactValueError> {
    let work = (degree as u128)
        .saturating_mul(degree as u128)
        .saturating_mul(degree as u128)
        .saturating_mul(widest_bits as u128 + 1);
    if work > STURM_WORK_CEILING {
        return Err(ExactValueError::SturmWorkTooLarge {
            degree,
            bits: widest_bits,
            work,
            ceiling: STURM_WORK_CEILING,
        });
    }
    Ok(())
}

/// **The Sturm chain of one integer polynomial, over `Z`, built once and counted against many
/// times.**
///
/// [proved-derived; implemented-exact] The classical chain is `f_0 = f`, `f_1 = f'`,
/// `f_{i+1} = −rem(f_{i−1}, f_i)` over `Q`. Carrying it over `Q` makes every coefficient a
/// normalized fraction and every remainder step a cascade of gcds; carrying it over `Z` by
/// *pseudo*-division does not, because
///
/// ```text
///   prem(A, B) = lc(B)^(deg A − deg B + 1) · rem(A, B)
/// ```
///
/// is an identity in `Z[x]` whenever `A, B ∈ Z[x]`. The whole difficulty is the sign: the reading
/// this chain is for — the number of sign variations of the values — is invariant when every member
/// is rescaled by its **own positive** constant, and is *not* invariant under a negative one. So
/// each member is kept as an explicitly **positive** multiple of the classical one:
///
/// ```text
///   S_{i+1} = −sign( lc(S_i)^(δ+1) ) · prem(S_{i−1}, S_i) / |β_i|,     δ = deg S_{i−1} − deg S_i
/// ```
///
/// The leading `−` is the classical chain's own negation; the `sign(...)` factor cancels the sign
/// pseudo-division introduced; `|β_i|` is a **positive** integer and is therefore gauge. `δ` is
/// read off the actual degrees, so a degree gap — which is where a naive implementation loses the
/// sign — is handled by the same formula that handles `δ = 1`, and a negative leading coefficient
/// is handled by the same formula that handles a positive one. The resulting chain has, at every
/// rational point, **exactly the sign pattern of the classical chain** and therefore exactly its
/// sign-variation count.
///
/// ## The divisor is the subresultant one, not the content
///
/// [proved-derived] `β_i` is the **subresultant** divisor (Collins 1967; Brown & Traub 1971):
///
/// ```text
///   β_1 = 1,                  h_0 = 1
///   β_i = g_{i−1} · h_{i−1}^δ,   g_{i−1} = |lc(S_{i−2})|
///   h_i = g_i^δ / h_{i−1}^(δ−1),  g_i = |lc(S_{i−1})|
/// ```
///
/// and the Brown–Traub theorem is that `prem(S_{i−1}, S_i) / β_i` stays in `Z[x]` — every member of
/// the sequence is (up to sign) a *subresultant* of the opening pair, whose coefficients are
/// determinants of submatrices of the Sylvester matrix and are therefore bounded by Hadamard at
/// `O(d · (bits + log d))` rather than growing like the pseudo-remainder itself. Both divisions
/// above are exact; an inexact one is a defect in this routine and is returned as
/// [`ExactValueError::SturmSubresultantInexact`], never wrapped or rounded.
///
/// **What this replaced.** The earlier form divided each member by its integer *content*. That is
/// also sign-safe and also keeps the coefficients small, but it pays a full multiprecision gcd per
/// coefficient per step: at degree 400 the members carry thousands of bits and the chain is 400
/// long, so the gcds — not the pseudo-division — were the whole cost, and
/// [`STURM_DEGREE_CEILING`] did not bound the work it claimed to. The subresultant divisor is one
/// exact division by a known factor instead. Absolute values are used throughout because the sign
/// is carried by the rule above; divisibility does not see a sign, so the quotient is the same
/// integer either way.
///
/// The Lean owner of the invariance is
/// `formal/elementary-holonics/ElementaryHolonics/Foundation/RootCount.lean`:
/// `theReadingIsInvariantUnderPerEntryPositiveRescaling` closes the boundary
/// `ElementaryHolonics/Millennium/Sturm.lean` names open, and
/// `theReadingIsInvariantUnderCommonNonzeroRescaling` is why a non-squarefree polynomial's chain
/// still counts *distinct* roots. Sturm's theorem itself is that file's cited classical fact and
/// `Millennium/Sturm.lean`'s `TheReadingEqualsThePopulation`.
///
/// A sign at a rational point `u/v` is taken by **integer** Horner on the homogenized member:
/// `sign(S(u/v)) = sign(Σ s_i u^i v^(d−i))` because `v > 0`. No rational arithmetic occurs in a
/// count.
///
/// The member list is private and there is no `Deserialize`: a chain exists only by passing
/// [`SturmChain::of`].
///
/// **A chain carries the polynomial it was built from.** A sign-variation count is a statement
/// about *one* polynomial, and a chain handed to an isolation entry beside a different polynomial
/// used to return `Ok` with a certificate for a root that does not exist — pairing `x² + 1` with
/// the chain of `x` counted one root in `(−1, 1)`. The pairing is therefore a fact of the type:
/// [`SturmChain::polynomial`] returns the source, and every entry that takes a chain and a
/// polynomial verifies that they agree before reading anything.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SturmChain {
    /// The polynomial this chain belongs to, exactly as it was handed in.
    source: IntegerPolynomial,
    /// The second seed, for a chain built by [`SturmChain::from_pair`]; `None` for the Sturm chain
    /// of a polynomial and its own derivative. A Cauchy-index chain is not a Sturm chain and may
    /// not certify an isolation, so the two are distinguished rather than conflated.
    paired_with: Option<IntegerPolynomial>,
    /// Ascending-degree integer coefficient lists, each a positive multiple of the classical member.
    members: Vec<Vec<BigInt>>,
}

impl SturmChain {
    /// Build the chain. Refuses a declared degree or coefficient width above the owner's ceilings.
    pub fn of(polynomial: &IntegerPolynomial) -> Result<Self, ExactValueError> {
        polynomial.check_declared_size()?;
        let degree = polynomial.degree();
        let mut first = polynomial.coefficients.clone();
        make_primitive(&mut first);
        let second = integer_derivative(&first);
        Self::build(polynomial.clone(), None, first, second, degree)
    }

    /// **The polynomial this chain belongs to.**
    ///
    /// A count taken against this chain is a statement about this polynomial and about nothing
    /// else, which is why the pairing is carried rather than assumed.
    pub fn polynomial(&self) -> &IntegerPolynomial {
        &self.source
    }

    /// The second seed when the chain came from [`SturmChain::from_pair`]; `None` for the Sturm
    /// chain of a polynomial and its own derivative.
    pub fn paired_with(&self) -> Option<&IntegerPolynomial> {
        self.paired_with.as_ref()
    }

    /// Whether this is the Sturm chain of [`SturmChain::polynomial`] — `f, f'` — rather than a
    /// Cauchy-index sequence seeded by a declared pair.
    pub fn is_sturm_chain(&self) -> bool {
        self.paired_with.is_none()
    }

    /// Refuse a chain that does not belong to this polynomial, by name.
    pub(crate) fn check_belongs_to(
        &self,
        polynomial: &IntegerPolynomial,
    ) -> Result<(), ExactValueError> {
        if !self.is_sturm_chain() {
            return Err(ExactValueError::ChainIsNotASturmChain);
        }
        if &self.source != polynomial {
            return Err(ExactValueError::ChainPolynomialMismatch {
                chain_degree: self.source.degree(),
                declared_degree: polynomial.degree(),
            });
        }
        Ok(())
    }

    /// **The signed remainder sequence seeded by a declared pair**, with the same
    /// positive-multiple discipline.
    ///
    /// [`SturmChain::of`] is exactly `from_pair(f, f')`. The general form is what a **Cauchy
    /// index** `I(q/p)` needs: its sequence starts at `p, q` rather than at `f, f'`, and it reads
    /// the variations at `±∞` rather than at a point. Nothing else about the construction changes,
    /// so the sign discipline is shared rather than written twice.
    pub fn from_pair(
        first: &IntegerPolynomial,
        second: &IntegerPolynomial,
    ) -> Result<Self, ExactValueError> {
        first.check_declared_size()?;
        second.check_declared_size()?;
        let degree = first.degree().max(second.degree());
        if second.degree() >= first.degree() {
            return Err(ExactValueError::SturmPairNotProper {
                leading_degree: first.degree(),
                trailing_degree: second.degree(),
            });
        }
        let mut head = first.coefficients.clone();
        make_primitive(&mut head);
        Self::build(
            first.clone(),
            Some(second.clone()),
            head,
            second.coefficients.clone(),
            degree,
        )
    }

    fn build(
        source: IntegerPolynomial,
        paired_with: Option<IntegerPolynomial>,
        first: Vec<BigInt>,
        mut second: Vec<BigInt>,
        degree: usize,
    ) -> Result<Self, ExactValueError> {
        if first.is_empty() {
            return Err(ExactValueError::ZeroPolynomial);
        }
        make_primitive(&mut second);
        let mut members = vec![first];
        if second.is_empty() {
            return Ok(Self {
                source,
                paired_with,
                members,
            });
        }
        members.push(second);

        // The subresultant state. `g` is `|lc|` of the member two back and `h` is the Brown–Traub
        // auxiliary; both are positive, and `β = g · h^δ` at every step. The opening step has
        // `β = 1`, which is exactly `g = h = 1`.
        let mut g = BigInt::one();
        let mut h = BigInt::one();

        // Degrees strictly decrease down a remainder sequence, so the chain cannot be longer than
        // the degree plus its two opening members. A longer one is a defect in this routine, not an
        // exhausted budget, and is returned as one.
        let ceiling = degree + 2;
        loop {
            let length = members.len();
            let current = &members[length - 1];
            let current_degree = current.len() - 1;
            if current_degree == 0 {
                // A nonzero constant divides everything exactly: the chain ends here.
                break;
            }
            let previous = &members[length - 2];
            // `δ = deg S_{i−1} − deg S_i`, read off the actual degrees so a gap is not assumed away.
            // Degrees strictly decrease down a remainder sequence, so the subtraction cannot
            // underflow; a defect that made it underflow is returned rather than wrapped.
            let Some(gap) = (previous.len() - 1).checked_sub(current_degree) else {
                return Err(ExactValueError::SturmChainDidNotTerminate { degree });
            };
            let leading = current[current_degree].clone();
            let leading_negative = leading.is_negative();
            let mut next = pseudo_remainder(previous, current);
            // `−sign(lc^(δ+1))`: the classical negation, times the sign pseudo-division introduced.
            // `β` below is positive, so it cannot disturb this and the rule is unchanged from the
            // content form.
            if !(leading_negative && (gap + 1) % 2 == 1) {
                for value in &mut next {
                    *value = -std::mem::take(value);
                }
            }
            trim_integer_polynomial(&mut next);
            if next.is_empty() {
                break;
            }
            // `β = g · h^δ`, positive. `gap` is at least one — degrees strictly decrease — so the
            // exponent is a genuine power and `pow` is taken on a `u32` read off the degrees.
            let Ok(exponent) = u32::try_from(gap) else {
                return Err(ExactValueError::SturmChainDidNotTerminate { degree });
            };
            let beta = &g * h.pow(exponent);
            if !beta.is_one() {
                let position = members.len();
                for value in &mut next {
                    let (quotient, remainder) = (&*value / &beta, &*value % &beta);
                    if !remainder.is_zero() {
                        return Err(ExactValueError::SturmSubresultantInexact { member: position });
                    }
                    *value = quotient;
                }
                trim_integer_polynomial(&mut next);
                if next.is_empty() {
                    break;
                }
            }
            // Advance the auxiliaries for the following step: `g ← |lc(S_i)|` and
            // `h ← g^δ / h^(δ−1)`, both exact by Brown–Traub and both positive.
            let leading_magnitude = leading.abs();
            h = if exponent == 0 {
                h
            } else {
                let numerator = leading_magnitude.pow(exponent);
                let denominator = h.pow(exponent - 1);
                if denominator.is_one() {
                    numerator
                } else {
                    let remainder = &numerator % &denominator;
                    if !remainder.is_zero() {
                        return Err(ExactValueError::SturmSubresultantInexact {
                            member: members.len(),
                        });
                    }
                    numerator / denominator
                }
            };
            g = leading_magnitude;
            members.push(next);
            if members.len() > ceiling {
                return Err(ExactValueError::SturmChainDidNotTerminate { degree });
            }
        }
        Ok(Self {
            source,
            paired_with,
            members,
        })
    }

    /// How many members the chain carries.
    pub fn len(&self) -> usize {
        self.members.len()
    }

    /// A chain is never empty; this exists because [`SturmChain::len`] does.
    pub fn is_empty(&self) -> bool {
        self.members.is_empty()
    }

    /// Whether the polynomial itself vanishes at this point.
    pub fn vanishes_at(&self, point: &Rat) -> bool {
        self.members
            .first()
            .is_some_and(|member| homogeneous_sign(member, point.numer(), point.denom()) == 0)
    }

    /// The number of sign variations of the chain's values at one rational point.
    ///
    /// Zeros are dropped rather than counted, exactly as
    /// `Millennium/Sturm.lean`'s `variationCount` drops them.
    pub fn sign_variations(&self, point: &Rat) -> u32 {
        let numerator = point.numer();
        let denominator = point.denom();
        let mut variations = 0_u32;
        let mut previous = 0_i8;
        for member in &self.members {
            let sign = homogeneous_sign(member, numerator, denominator);
            if sign == 0 {
                continue;
            }
            if previous != 0 && sign != previous {
                variations += 1;
            }
            previous = sign;
        }
        variations
    }

    /// The sign of a member at `±∞`, from its degree and its leading coefficient alone.
    fn sign_at_infinity(member: &[BigInt], positive: bool) -> i8 {
        let Some(top) = member.len().checked_sub(1) else {
            return 0;
        };
        let leading = if member[top].is_negative() { -1_i8 } else { 1 };
        if positive || top % 2 == 0 {
            leading
        } else {
            -leading
        }
    }

    /// The number of sign variations of the chain at `+∞` or at `−∞`.
    ///
    /// A member's sign at infinity is its leading coefficient's sign, with a parity flip at `−∞`.
    /// Positive rescaling is invisible here for exactly the reason it is invisible at a point.
    pub fn sign_variations_at_infinity(&self, positive: bool) -> u32 {
        let mut variations = 0_u32;
        let mut previous = 0_i8;
        for member in &self.members {
            let sign = Self::sign_at_infinity(member, positive);
            if sign == 0 {
                continue;
            }
            if previous != 0 && sign != previous {
                variations += 1;
            }
            previous = sign;
        }
        variations
    }

    /// **The Cauchy index `I_{−∞}^{+∞}` carried by this chain**: `V(−∞) − V(+∞)`.
    ///
    /// Meaningful when the chain was seeded by [`SturmChain::from_pair`] with the *denominator*
    /// first and the *numerator* second, which is how Routh–Hurwitz reads a half-plane population.
    pub fn cauchy_index(&self) -> i64 {
        i64::from(self.sign_variations_at_infinity(false))
            - i64::from(self.sign_variations_at_infinity(true))
    }

    /// Count distinct real roots in one strict rational interval. Endpoints may not be roots.
    pub fn distinct_root_count(&self, interval: &ExactInterval) -> Result<u32, ExactValueError> {
        if interval.is_point() {
            return Err(ExactValueError::NonStrictRootInterval);
        }
        if self.vanishes_at(&interval.lower) || self.vanishes_at(&interval.upper) {
            return Err(ExactValueError::RootAtIntervalBoundary);
        }
        let lower = self.sign_variations(&interval.lower);
        let upper = self.sign_variations(&interval.upper);
        lower
            .checked_sub(upper)
            .ok_or(ExactValueError::InvalidSturmOrientation)
    }
}

/// The sign-variation pair an isolation was certified by.
///
/// **An isolating certificate drops exactly one variation.** That is the whole content of the
/// certificate, so the wire enforces it rather than carrying two arbitrary integers; a pair that
/// does not drop exactly one is refused as [`ExactValueError::NonIsolatingCertificate`]. What the
/// pair cannot check on its own is *which* polynomial produced it, which is why
/// [`AlgebraicRoot`]'s wire recomputes it from the polynomial it travels with.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "SturmIsolationCertificateWire")]
pub struct SturmIsolationCertificate {
    pub variations_at_lower: u32,
    pub variations_at_upper: u32,
}

#[derive(Deserialize)]
struct SturmIsolationCertificateWire {
    variations_at_lower: u32,
    variations_at_upper: u32,
}

impl TryFrom<SturmIsolationCertificateWire> for SturmIsolationCertificate {
    type Error = ExactValueError;

    fn try_from(wire: SturmIsolationCertificateWire) -> Result<Self, Self::Error> {
        if wire
            .variations_at_lower
            .checked_sub(wire.variations_at_upper)
            != Some(1)
        {
            return Err(ExactValueError::NonIsolatingCertificate {
                variations_at_lower: wire.variations_at_lower,
                variations_at_upper: wire.variations_at_upper,
            });
        }
        Ok(Self {
            variations_at_lower: wire.variations_at_lower,
            variations_at_upper: wire.variations_at_upper,
        })
    }
}

/// One real algebraic number, identified by a polynomial and an exact interval
/// containing exactly one of its real roots.
///
/// **A remounted root re-runs its own isolation.** The certificate is a claim that the polynomial
/// has exactly one real root inside the interval, and a hand-built wire can claim anything: a
/// declaration that `x² + 1` has a root in `[−1, 1]` used to deserialize with no Sturm computation
/// at all and then order itself against real roots through [`compare_algebraic`]. The wire
/// therefore rebuilds the chain of the polynomial it carries, recounts the variations at both
/// endpoints, and refuses unless the recomputed pair isolates exactly one root **and** equals the
/// declared pair. Nothing carried is trusted; the polynomial and the interval are the only data,
/// and the certificate is derived from them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "AlgebraicRootWire")]
pub struct AlgebraicRoot {
    pub polynomial: IntegerPolynomial,
    pub isolating_interval: ExactInterval,
    pub certificate: SturmIsolationCertificate,
}

#[derive(Deserialize)]
struct AlgebraicRootWire {
    polynomial: IntegerPolynomial,
    isolating_interval: ExactInterval,
    certificate: SturmIsolationCertificate,
}

impl TryFrom<AlgebraicRootWire> for AlgebraicRoot {
    type Error = ExactValueError;

    fn try_from(wire: AlgebraicRootWire) -> Result<Self, Self::Error> {
        let recomputed = AlgebraicRoot::isolate(wire.polynomial, wire.isolating_interval)?;
        if recomputed.certificate != wire.certificate {
            return Err(ExactValueError::IsolationCertificateDisagrees {
                declared_lower: wire.certificate.variations_at_lower,
                declared_upper: wire.certificate.variations_at_upper,
                recomputed_lower: recomputed.certificate.variations_at_lower,
                recomputed_upper: recomputed.certificate.variations_at_upper,
            });
        }
        Ok(recomputed)
    }
}

impl AlgebraicRoot {
    pub fn isolate(
        polynomial: IntegerPolynomial,
        isolating_interval: ExactInterval,
    ) -> Result<Self, ExactValueError> {
        let sturm = SturmChain::of(&polynomial)?;
        Self::isolate_with(&sturm, isolating_interval)
    }

    /// [`AlgebraicRoot::isolate`] against a chain the caller already built.
    ///
    /// [definition] `sturm` must be the chain **of this polynomial**, and that is now verified
    /// rather than assumed: pairing `x² + 1` with the chain of `x` used to return `Ok` with a
    /// certificate for a root that does not exist. The pairing is checked through
    /// [`SturmChain::polynomial`] and refused by name, so this entry is a thin wrapper over
    /// [`AlgebraicRoot::isolate_with`], which takes the chain alone and cannot be mispaired.
    /// Isolating twenty-four roots of one degree-twenty-four polynomial is the case this exists
    /// for: the chain is the expensive object and there is exactly one of it.
    pub fn isolate_against(
        polynomial: IntegerPolynomial,
        isolating_interval: ExactInterval,
        sturm: &SturmChain,
    ) -> Result<Self, ExactValueError> {
        sturm.check_belongs_to(&polynomial)?;
        Self::isolate_with(sturm, isolating_interval)
    }

    /// **Isolate against a chain, which carries its own polynomial.**
    ///
    /// The chain is the only argument that names a polynomial, so there is no pairing to get
    /// wrong. [`AlgebraicRoot::isolate`] and [`AlgebraicRoot::isolate_against`] both reduce to
    /// this.
    pub fn isolate_with(
        sturm: &SturmChain,
        isolating_interval: ExactInterval,
    ) -> Result<Self, ExactValueError> {
        if !sturm.is_sturm_chain() {
            return Err(ExactValueError::ChainIsNotASturmChain);
        }
        let polynomial = sturm.polynomial().clone();
        if polynomial.degree() == 0 {
            return Err(ExactValueError::ConstantPolynomial);
        }
        if isolating_interval.is_point() {
            return Err(ExactValueError::NonStrictRootInterval);
        }
        if polynomial.evaluate(&isolating_interval.lower).is_zero()
            || polynomial.evaluate(&isolating_interval.upper).is_zero()
        {
            return Err(ExactValueError::RootAtIntervalBoundary);
        }
        let lower = sturm.sign_variations(&isolating_interval.lower);
        let upper = sturm.sign_variations(&isolating_interval.upper);
        let roots = lower
            .checked_sub(upper)
            .ok_or(ExactValueError::InvalidSturmOrientation)?;
        if roots != 1 {
            return Err(ExactValueError::RootCount { exact_count: roots });
        }
        Ok(Self {
            polynomial,
            isolating_interval,
            certificate: SturmIsolationCertificate {
                variations_at_lower: lower,
                variations_at_upper: upper,
            },
        })
    }

    fn contains_rational_root(&self, value: &Rat) -> bool {
        self.isolating_interval.lower < *value
            && *value < self.isolating_interval.upper
            && self.polynomial.evaluate(value).is_zero()
    }
}

/// **The wire re-derives the remainder interval**, which is the one thing a tail certificate
/// claims. A geometric ratio at or above one closes no tail and a negative absolute bound is not a
/// bound; the derived `Deserialize` admitted both, and [`CertifiedSeries::enclosure`] then panicked
/// on the certificate its own constructor had refused.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "SeriesTailCertificateWire")]
pub enum SeriesTailCertificate {
    /// If every omitted term is bounded by
    /// `first_omitted_abs_bound * ratio_abs_bound^k`, the complete absolute
    /// tail is bounded by `first/(1-ratio)`.
    AbsoluteGeometric {
        first_omitted_abs_bound: Rat,
        ratio_abs_bound: Rat,
    },
    /// Alternating, monotonically decreasing magnitudes place the tail
    /// between zero and the first omitted signed term.
    AlternatingMonotone { first_omitted_term: Rat },
    /// The remainder has already been closed by an exact identity.
    ExactTail { remainder: Rat },
}

/// The same three shapes, unvalidated, so [`SeriesTailCertificate`] can take them through its own
/// remainder derivation on the way in.
#[derive(Deserialize)]
enum SeriesTailCertificateWire {
    AbsoluteGeometric {
        first_omitted_abs_bound: Rat,
        ratio_abs_bound: Rat,
    },
    AlternatingMonotone {
        first_omitted_term: Rat,
    },
    ExactTail {
        remainder: Rat,
    },
}

impl TryFrom<SeriesTailCertificateWire> for SeriesTailCertificate {
    type Error = ExactValueError;

    fn try_from(wire: SeriesTailCertificateWire) -> Result<Self, Self::Error> {
        let certificate = match wire {
            SeriesTailCertificateWire::AbsoluteGeometric {
                first_omitted_abs_bound,
                ratio_abs_bound,
            } => Self::AbsoluteGeometric {
                first_omitted_abs_bound,
                ratio_abs_bound,
            },
            SeriesTailCertificateWire::AlternatingMonotone { first_omitted_term } => {
                Self::AlternatingMonotone { first_omitted_term }
            }
            SeriesTailCertificateWire::ExactTail { remainder } => Self::ExactTail { remainder },
        };
        certificate.remainder_interval()?;
        Ok(certificate)
    }
}

impl SeriesTailCertificate {
    pub fn remainder_interval(&self) -> Result<ExactInterval, ExactValueError> {
        match self {
            Self::AbsoluteGeometric {
                first_omitted_abs_bound,
                ratio_abs_bound,
            } => {
                if first_omitted_abs_bound.is_negative() {
                    return Err(ExactValueError::NegativeTailBound);
                }
                if ratio_abs_bound.is_negative() || ratio_abs_bound >= &Rat::one() {
                    return Err(ExactValueError::InvalidGeometricRatio);
                }
                let bound = first_omitted_abs_bound / (Rat::one() - ratio_abs_bound);
                ExactInterval::new(-bound.clone(), bound)
            }
            Self::AlternatingMonotone { first_omitted_term } => {
                if first_omitted_term.is_negative() {
                    ExactInterval::new(first_omitted_term.clone(), Rat::zero())
                } else {
                    ExactInterval::new(Rat::zero(), first_omitted_term.clone())
                }
            }
            Self::ExactTail { remainder } => Ok(ExactInterval::point(remainder.clone())),
        }
    }
}

/// A convergent series face with an exact finite sum and an exact tail
/// enclosure derived from one supported certificate species.
/// **The roots a transport actually asks for, isolated by this owner's own certificate.**
///
/// A root-mean-square rebase asks for `1/sqrt(s)` and nothing else; a chart width asks for
/// `1/sqrt(d)`. Both are algebraic of degree two, which is exactly what [`AlgebraicRoot`] is for,
/// and the Sturm certificate it already carries is what makes the isolation a proof rather than an
/// iteration count. These are added inside this owner because that is where a root of an exact
/// rational belongs.
impl AlgebraicRoot {
    /// The positive `sqrt(radicand)`, isolated with a Sturm certificate.
    ///
    /// The bracket comes from an integer square root at `octaves` dyadic places, so it needs no
    /// starting guess; the certificate is what verifies it.
    pub fn square_root(radicand: &Rat, octaves: u32) -> Result<Self, ExactValueError> {
        Self::degree_two_root(radicand, octaves, false)
    }

    /// The positive `1/sqrt(radicand)`, isolated with a Sturm certificate.
    ///
    /// **This is the return a normalization actually needs**, and taking it directly rather than
    /// inverting a root keeps one certificate instead of two.
    pub fn reciprocal_square_root(radicand: &Rat, octaves: u32) -> Result<Self, ExactValueError> {
        Self::degree_two_root(radicand, octaves, true)
    }

    fn degree_two_root(
        radicand: &Rat,
        octaves: u32,
        reciprocal: bool,
    ) -> Result<Self, ExactValueError> {
        if !radicand.is_positive() {
            return Err(ExactValueError::NonPositiveRadicand);
        }
        let numerator = radicand.numer().magnitude().clone();
        let denominator = radicand.denom().magnitude().clone();
        // `q x^2 - p` has root sqrt(p/q); `p y^2 - q` has root 1/sqrt(p/q).
        let polynomial = if reciprocal {
            IntegerPolynomial::new(vec![
                -BigInt::from(denominator.clone()),
                BigInt::zero(),
                BigInt::from(numerator.clone()),
            ])?
        } else {
            IntegerPolynomial::new(vec![
                -BigInt::from(numerator.clone()),
                BigInt::zero(),
                BigInt::from(denominator.clone()),
            ])?
        };
        // An integer square root at `octaves` dyadic places brackets the value by construction.
        let scale = BigUint::one() << (2 * octaves as usize);
        let (over, under) = if reciprocal {
            (denominator * &scale, numerator)
        } else {
            (numerator * &scale, denominator)
        };
        let floor = (over / under).sqrt();
        let unit = Rat::new(
            BigInt::one(),
            BigInt::from(BigUint::one() << octaves as usize),
        );
        let mut lower = Rat::from_integer(BigInt::from(floor.clone())) * &unit;
        let mut upper = Rat::from_integer(BigInt::from(floor + 1u32)) * &unit;
        // A strict interval whose endpoints are not themselves roots, widened outward by one place
        // where the floor landed exactly on the root.
        if polynomial.evaluate(&lower).is_zero() {
            lower -= &unit;
        }
        if polynomial.evaluate(&upper).is_zero() {
            upper += &unit;
        }
        if !lower.is_positive() {
            // A positive root below one grid cell is still bracketed by zero. Replacing
            // zero with half a cell can cross the root and destroy the certificate.
            // The constant coefficient is nonzero, so zero is not a polynomial root.
            lower = Rat::zero();
        }
        Self::isolate(polynomial, ExactInterval::new(lower, upper)?)
    }

    /// The positive `radicand^(1/degree)`, isolated with a Sturm certificate.
    ///
    /// **A chronology ladder's per-band angle is exactly this object**: `base^(-2i/d)` is algebraic
    /// of degree `d/2`, and taking it as a root rather than through a logarithm keeps the whole
    /// ladder inside exact arithmetic. The bracket comes from an integer `n`-th root; the
    /// certificate is what verifies it.
    pub fn nth_root(radicand: &Rat, degree: u32, octaves: u32) -> Result<Self, ExactValueError> {
        if !radicand.is_positive() {
            return Err(ExactValueError::NonPositiveRadicand);
        }
        if degree == 0 {
            return Err(ExactValueError::ConstantPolynomial);
        }
        let numerator = radicand.numer().magnitude().clone();
        let denominator = radicand.denom().magnitude().clone();
        let mut coefficients = vec![BigInt::zero(); degree as usize + 1];
        coefficients[0] = -BigInt::from(numerator.clone());
        coefficients[degree as usize] = BigInt::from(denominator.clone());
        let polynomial = IntegerPolynomial::new(coefficients)?;
        let scale = BigUint::one() << (degree as usize * octaves as usize);
        let floor = (numerator * &scale / denominator).nth_root(degree);
        let unit = Rat::new(
            BigInt::one(),
            BigInt::from(BigUint::one() << octaves as usize),
        );
        let mut lower = Rat::from_integer(BigInt::from(floor.clone())) * &unit;
        let mut upper = Rat::from_integer(BigInt::from(floor + 1u32)) * &unit;
        if polynomial.evaluate(&lower).is_zero() {
            lower -= &unit;
        }
        if polynomial.evaluate(&upper).is_zero() {
            upper += &unit;
        }
        if !lower.is_positive() {
            lower = &unit / Rat::from_integer(BigInt::from(2));
        }
        Self::isolate(polynomial, ExactInterval::new(lower, upper)?)
    }

    /// The isolating interval, which **is** the enclosure: the root is inside it and the
    /// certificate says exactly one root is.
    pub fn enclosure(&self) -> &ExactInterval {
        &self.isolating_interval
    }
}

/// This bounded helper returns [0, 2^-REACH] beyond the stated negative reach.
/// The interval retains a positive possible value; this is not equality with zero or a
/// universal bound on the precision of other receiver charts.
const DECAY_REACH: u32 = 64;
/// Resource/domain aperture of this enclosure helper. A refusal is local to this
/// implementation, not a claim that a larger exponential has no exact representation.
const GROWTH_REACH: u32 = 64;
/// Past this reach `tanh` is within `2^(-2 REACH)` of its limit.
const TANGENT_REACH: u32 = 32;
/// The dyadic places a composed exponential is held at, so its denominators cannot grow with the
/// exponent. This is the helper's declared dyadic grain, not the source mode's precision.
const EXPONENTIAL_OCTAVES: u32 = 64;

/// **The wire takes [`CertifiedSeries::new`]**, which is what makes
/// [`CertifiedSeries::enclosure`]'s `expect` true rather than hopeful: the derived `Deserialize`
/// reconstructed the struct past that constructor, and a remounted series carrying an
/// unclosed tail then panicked inside a method that returns no `Result`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "CertifiedSeriesWire")]
pub struct CertifiedSeries {
    pub expression: ExactExpr,
    pub partial_sum: Rat,
    pub terms_folded: BigUint,
    pub tail_certificate: SeriesTailCertificate,
}

#[derive(Deserialize)]
struct CertifiedSeriesWire {
    expression: ExactExpr,
    partial_sum: Rat,
    terms_folded: BigUint,
    tail_certificate: SeriesTailCertificate,
}

impl TryFrom<CertifiedSeriesWire> for CertifiedSeries {
    type Error = ExactValueError;

    fn try_from(wire: CertifiedSeriesWire) -> Result<Self, Self::Error> {
        Self::new(
            wire.expression,
            wire.partial_sum,
            wire.terms_folded,
            wire.tail_certificate,
        )
    }
}

impl CertifiedSeries {
    pub fn new(
        expression: ExactExpr,
        partial_sum: Rat,
        terms_folded: BigUint,
        tail_certificate: SeriesTailCertificate,
    ) -> Result<Self, ExactValueError> {
        tail_certificate.remainder_interval()?;
        Ok(Self {
            expression,
            partial_sum,
            terms_folded,
            tail_certificate,
        })
    }

    pub fn enclosure(&self) -> ExactInterval {
        self.tail_certificate
            .remainder_interval()
            .expect("a CertifiedSeries retains its validated certificate")
            .translated(&self.partial_sum)
    }

    /// **`exp(x)` as a certified enclosure**, reduced through the exponential's own homomorphism.
    ///
    /// A Taylor series is only well-conditioned near zero: at `x = -15` with forty terms the first
    /// omitted term is `15^40/40!`, which is larger than `exp(-15)` itself, so the certificate
    /// closes on an interval hundreds of thousands of times wider than the value. That is not a
    /// defect of the certificate — it is the honest bound for that many terms — and the repair is
    /// the function's own law rather than more terms.
    ///
    /// `exp(a+b) = exp(a)exp(b)` splits `x` into a whole part and a fraction below one. The whole
    /// part rides an integer power of `exp(1)`; the fraction takes the series, where it converges
    /// fast and the geometric bound is tight. `CLAUDE.md` §0l: the additive chart carried to the
    /// multiplicative one is what `exp` **is**, so using it here is the owner carrying its own
    /// function.
    pub fn exponential_enclosure(x: &Rat, terms: usize) -> Result<ExactInterval, ExactValueError> {
        if terms == 0 {
            return Err(ExactValueError::EmptySeries);
        }
        let negative = x.is_negative();
        let magnitude = if negative { -x.clone() } else { x.clone() };
        // **THE APERTURE, and it is a bound rather than a shortcut.** For `x <= -REACH` the value
        // is below `2^-REACH` because `e > 2`, so `[0, 2^-REACH]` is a valid enclosure.
        // A finer receiver can distinguish values inside it; this helper retains that family.
        // Forming `e^REACH` to divide it back out is the same answer at hundreds of times the cost.
        if negative && magnitude >= Rat::from_integer(BigInt::from(DECAY_REACH)) {
            return ExactInterval::new(
                Rat::zero(),
                Rat::new(
                    BigInt::one(),
                    BigInt::from(BigUint::one() << DECAY_REACH as usize),
                ),
            );
        }
        let whole = magnitude.to_integer();
        let fraction = &magnitude - Rat::from_integer(whole.clone());
        let unit = Self::exponential_series(&Rat::one(), terms)?.enclosure();
        let steps = u32::try_from(&whole).map_err(|_| ExactValueError::TailDoesNotClose)?;
        if steps > GROWTH_REACH {
            return Err(ExactValueError::TailDoesNotClose);
        }
        // **Held at a grain at every step.** An unheld interval power grows its denominators with
        // the exponent, and `e^63` composed sixty-three times is the same cost defect as an unheld
        // ladder. The grain is read off the carrier and the enclosure only ever widens.
        let carried = unit
            .power_held(steps, EXPONENTIAL_OCTAVES)?
            .times(&Self::exponential_series(&fraction, terms)?.enclosure())?
            .round_out(EXPONENTIAL_OCTAVES)?;
        if negative {
            carried.reciprocal()
        } else {
            Ok(carried)
        }
    }

    /// **The normalized exponential mode as a certified series**, for the argument/term
    /// domain `|x|/(terms+1) < 1`, with the geometric tail this owner
    /// already validates.
    ///
    /// After `n` terms every omitted term is at most the first times `(|x|/(n+1))^j`, which is
    /// exactly [`SeriesTailCertificate::AbsoluteGeometric`]. Its source is E'=E, E(0)=1;
    /// `exp` names that constrained mode. The owner refuses the certificate
    /// where the ratio bound does not close the tail, so a caller cannot silently take too few
    /// terms for its argument. [`Self::exponential_enclosure`] is the reduction that keeps every
    /// caller inside this domain.
    pub fn exponential_series(x: &Rat, terms: usize) -> Result<Self, ExactValueError> {
        if terms == 0 {
            return Err(ExactValueError::EmptySeries);
        }
        let mut sum = Rat::zero();
        let mut term = Rat::one();
        for k in 0..terms {
            sum += &term;
            term = &term * x / Rat::from_integer(BigInt::from(k as u64 + 1));
        }
        let magnitude = |value: &Rat| -> Rat {
            if value.is_negative() {
                -value.clone()
            } else {
                value.clone()
            }
        };
        let ratio_bound = magnitude(x) / Rat::from_integer(BigInt::from(terms as u64 + 1));
        if ratio_bound >= Rat::one() {
            return Err(ExactValueError::TailDoesNotClose);
        }
        Self::new(
            // Retain the normalized exponential relation, not merely its rational argument face.
            ExactExpr::function("exp", vec![ExactExpr::rational(x.clone())]),
            sum,
            BigUint::from(terms as u64),
            SeriesTailCertificate::AbsoluteGeometric {
                first_omitted_abs_bound: magnitude(&term),
                ratio_abs_bound: ratio_bound,
            },
        )
    }

    /// **`cos(x)` and `sin(x)` for `|x| <= 1`**, alternating with monotonically decreasing terms.
    ///
    /// For `|x| <= 1` every ratio `x^2/((2k+1)(2k+2))` is at most one half, so the terms decrease
    /// from the first and the omitted tail is bounded by its first omitted term — exactly
    /// [`SeriesTailCertificate::AlternatingMonotone`]. A caller past that domain composes the
    /// rotation group's own law, `R(a+b) = R(a)R(b)`, rather than asking for more terms.
    pub fn circular_series(x: &Rat, terms: usize) -> Result<(Self, Self), ExactValueError> {
        if terms == 0 {
            return Err(ExactValueError::EmptySeries);
        }
        let magnitude = if x.is_negative() {
            -x.clone()
        } else {
            x.clone()
        };
        if magnitude > Rat::one() {
            return Err(ExactValueError::TailDoesNotClose);
        }
        let square = x * x;

        let mut cosine_sum = Rat::zero();
        let mut cosine_term = Rat::one();
        for k in 0..terms {
            if k % 2 == 0 {
                cosine_sum += &cosine_term;
            } else {
                cosine_sum -= &cosine_term;
            }
            let a = Rat::from_integer(BigInt::from(2 * k as u64 + 1));
            let b = Rat::from_integer(BigInt::from(2 * k as u64 + 2));
            cosine_term = &cosine_term * &square / (a * b);
        }
        let cosine = Self::new(
            // The phase series is a face of the cosine generator in its declared rotation chart.
            ExactExpr::function("cos", vec![ExactExpr::rational(x.clone())]),
            cosine_sum,
            BigUint::from(terms as u64),
            SeriesTailCertificate::AlternatingMonotone {
                first_omitted_term: if terms.is_multiple_of(2) {
                    cosine_term
                } else {
                    -cosine_term
                },
            },
        )?;

        let mut sine_sum = Rat::zero();
        let mut sine_term = x.clone();
        for k in 0..terms {
            if k % 2 == 0 {
                sine_sum += &sine_term;
            } else {
                sine_sum -= &sine_term;
            }
            let a = Rat::from_integer(BigInt::from(2 * k as u64 + 2));
            let b = Rat::from_integer(BigInt::from(2 * k as u64 + 3));
            sine_term = &sine_term * &square / (a * b);
        }
        let sine = Self::new(
            // Preserve sine as the oriented quadrature generator, including a negative input phase.
            ExactExpr::function("sin", vec![ExactExpr::rational(x.clone())]),
            sine_sum,
            BigUint::from(terms as u64),
            SeriesTailCertificate::AlternatingMonotone {
                first_omitted_term: if terms.is_multiple_of(2) {
                    sine_term
                } else {
                    -sine_term
                },
            },
        )?;
        Ok((cosine, sine))
    }

    /// **A rotation by an integer multiple of one angle, through the group's own law.**
    ///
    /// `R(p a) = R(a)^p` by repeated composition of the enclosed group element, so the
    /// transcendental is evaluated **once per band** and a position is an integer power. The
    /// chronology's exact carrier is therefore the integer `p`, and no series runs per position.
    pub fn rotation_power(
        angle: &Rat,
        power: u64,
        terms: usize,
    ) -> Result<(ExactInterval, ExactInterval), ExactValueError> {
        let (cosine, sine) = Self::circular_series(angle, terms)?;
        let mut carried = (
            ExactInterval::point(Rat::one()),
            ExactInterval::point(Rat::zero()),
        );
        let step = (cosine.enclosure(), sine.enclosure());
        for _ in 0..power {
            let real = carried.0.times(&step.0)?.translated(&Rat::zero());
            let cross = carried.1.times(&step.1)?;
            let cosine_out =
                ExactInterval::new(&real.lower - &cross.upper, &real.upper - &cross.lower)?;
            let left = carried.0.times(&step.1)?;
            let right = carried.1.times(&step.0)?;
            let sine_out =
                ExactInterval::new(&left.lower + &right.lower, &left.upper + &right.upper)?;
            carried = (cosine_out, sine_out);
        }
        Ok(carried)
    }

    /// **`tanh(x)`, taken through the DECAYING exponential so nothing large is ever formed.**
    ///
    /// `tanh(x) = sign(x) (1 - e^(-2|x|)) / (1 + e^(-2|x|))`. Written the other way the
    /// intermediate is `e^(2|x|)`, which leaves every bounded carrier long before the value itself
    /// stops moving. The identity is exact and the reformulation is the whole difference.
    ///
    /// Returns the enclosure rather than a series, because a quotient of two series is not one.
    pub fn hyperbolic_tangent_enclosure(
        x: &Rat,
        terms: usize,
    ) -> Result<ExactInterval, ExactValueError> {
        let negative = x.is_negative();
        let magnitude = if negative { -x.clone() } else { x.clone() };
        let two = Rat::from_integer(BigInt::from(2));
        // **THE APERTURE.** Past this reach `e^(-2|x|) <= 2^(-2 REACH)`, so `tanh` is within that
        // of one and the enclosure below is exact. `TANGENT_REACH` is read off the carrier the
        // grain uses, not chosen for a result.
        if magnitude >= Rat::from_integer(BigInt::from(TANGENT_REACH)) {
            let bound = Rat::new(
                BigInt::one(),
                BigInt::from(BigUint::one() << (2 * TANGENT_REACH) as usize),
            );
            let one = Rat::one();
            let low = (&one - &bound) / (&one + &bound);
            let interval = ExactInterval::new(low, one)?;
            return Ok(if negative {
                ExactInterval::new(-interval.upper.clone(), -interval.lower.clone())?
            } else {
                interval
            });
        }
        let decaying = Self::exponential_enclosure(&(-(&magnitude * &two)), terms)?;
        let one = Rat::one();
        // Both endpoints of a decreasing-in-`u` map, so the bounds swap.
        let low = (&one - &decaying.upper) / (&one + &decaying.upper);
        let high = (&one - &decaying.lower) / (&one + &decaying.lower);
        let (below, above) = if low <= high {
            (low, high)
        } else {
            (high, low)
        };
        let interval = ExactInterval::new(below, above)?;
        Ok(if negative {
            ExactInterval::new(-interval.upper.clone(), -interval.lower.clone())?
        } else {
            interval
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactValue {
    Integer(BigInt),
    Rational(Rat),
    Algebraic(AlgebraicRoot),
    CertifiedSeries(CertifiedSeries),
    Expression(ExactExpr),
}

impl ExactValue {
    pub fn rational(value: Rat) -> Self {
        if value.denom().is_one() {
            Self::Integer(value.numer().clone())
        } else {
            Self::Rational(value)
        }
    }

    pub fn as_rational(&self) -> Option<Rat> {
        match self {
            Self::Integer(value) => Some(Rat::from_integer(value.clone())),
            Self::Rational(value) => Some(value.clone()),
            Self::Algebraic(_) | Self::CertifiedSeries(_) | Self::Expression(_) => None,
        }
    }

    pub fn compare(&self, other: &Self) -> ExactOrdering {
        if self == other {
            return ExactOrdering::Equal;
        }
        match (self, other) {
            (Self::Integer(left), Self::Integer(right)) => left.cmp(right).into(),
            (Self::Integer(left), Self::Rational(right)) => {
                Rat::from_integer(left.clone()).cmp(right).into()
            }
            (Self::Rational(left), Self::Integer(right)) => {
                left.cmp(&Rat::from_integer(right.clone())).into()
            }
            (Self::Rational(left), Self::Rational(right)) => left.cmp(right).into(),
            (Self::Algebraic(left), Self::Algebraic(right)) => compare_algebraic(left, right),
            (Self::Integer(left), Self::Algebraic(right)) => {
                compare_rational_algebraic(&Rat::from_integer(left.clone()), right)
            }
            (Self::Rational(left), Self::Algebraic(right)) => {
                compare_rational_algebraic(left, right)
            }
            (Self::Algebraic(left), Self::Integer(right)) => reverse(compare_rational_algebraic(
                &Rat::from_integer(right.clone()),
                left,
            )),
            (Self::Algebraic(left), Self::Rational(right)) => {
                reverse(compare_rational_algebraic(right, left))
            }
            (Self::CertifiedSeries(left), Self::CertifiedSeries(right)) => {
                left.enclosure().disjoint_order(&right.enclosure())
            }
            (Self::Integer(left), Self::CertifiedSeries(right)) => {
                ExactInterval::point(Rat::from_integer(left.clone()))
                    .disjoint_order(&right.enclosure())
            }
            (Self::Rational(left), Self::CertifiedSeries(right)) => {
                ExactInterval::point(left.clone()).disjoint_order(&right.enclosure())
            }
            (Self::CertifiedSeries(left), Self::Integer(right)) => reverse(
                ExactInterval::point(Rat::from_integer(right.clone()))
                    .disjoint_order(&left.enclosure()),
            ),
            (Self::CertifiedSeries(left), Self::Rational(right)) => {
                reverse(ExactInterval::point(right.clone()).disjoint_order(&left.enclosure()))
            }
            _ => ExactOrdering::Open,
        }
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ExactValueError {
    #[error("a root was asked of a non-positive radicand")]
    NonPositiveRadicand,
    #[error("a series was asked for zero terms")]
    EmptySeries,
    #[error("a reciprocal was asked of an enclosure straddling zero")]
    ReciprocalStraddlesZero,
    #[error("the geometric ratio bound does not close the tail at the declared term count")]
    TailDoesNotClose,
    #[error("an exact interval cannot have its lower endpoint above its upper endpoint")]
    ReversedInterval,
    #[error("the zero polynomial does not identify an algebraic species")]
    ZeroPolynomial,
    #[error("a constant polynomial has no isolated algebraic root")]
    ConstantPolynomial,
    #[error("an algebraic isolating interval must have nonzero width")]
    NonStrictRootInterval,
    #[error("the proposed isolating interval has a root on its boundary")]
    RootAtIntervalBoundary,
    #[error("the Sturm variation count increased across an ordered interval")]
    InvalidSturmOrientation,
    #[error(
        "degree {degree} is past the declared Sturm ceiling {ceiling}: the chain's length, its \
         pseudo-divisions and its coefficient growth are all sized by it, so it is refused rather \
         than attempted"
    )]
    SturmDegreeTooLarge { degree: usize, ceiling: usize },
    #[error(
        "a coefficient of {bits} bits is past the declared Sturm ceiling of {ceiling} bits: the \
         chain's arithmetic is sized by it, so it is refused rather than attempted"
    )]
    SturmCoefficientTooWide { bits: u64, ceiling: u64 },
    #[error(
        "a degree-{degree} polynomial with {bits}-bit coefficients carries a Sturm work index of \
         {work}, past the declared ceiling of {ceiling}: degree and width bound the chain's cost \
         only together, so the pair is refused rather than attempted"
    )]
    SturmWorkTooLarge {
        degree: usize,
        bits: u64,
        work: u128,
        ceiling: u128,
    },
    #[error(
        "the Sturm chain of a degree-{degree} polynomial passed its own length bound; degrees \
         strictly decrease down a remainder sequence, so this is a defect in the chain and not an \
         exhausted budget"
    )]
    SturmChainDidNotTerminate { degree: usize },
    #[error(
        "a signed remainder sequence needs a strictly smaller trailing degree; degree \
         {trailing_degree} does not descend from {leading_degree}, so the sequence would not \
         terminate"
    )]
    SturmPairNotProper {
        leading_degree: usize,
        trailing_degree: usize,
    },
    #[error("the proposed interval contains {exact_count} roots rather than exactly one")]
    RootCount { exact_count: u32 },
    #[error(
        "a remounted integer polynomial declares {declared} coefficients whose leading entry is \
         zero; the constructor's normal form carries a nonzero leading coefficient, so the \
         declaration names a degree it does not have and is refused rather than re-normalized"
    )]
    UntrimmedPolynomialWire { declared: usize },
    #[error(
        "the subresultant divisor did not divide member {member} of the chain exactly; the \
         Brown-Traub identity says it must, so this is a defect in the chain and not an exhausted \
         budget"
    )]
    SturmSubresultantInexact { member: usize },
    #[error(
        "a Cauchy-index sequence seeded by a declared pair is not the Sturm chain of a polynomial \
         and may not certify an isolation"
    )]
    ChainIsNotASturmChain,
    #[error(
        "the supplied chain belongs to a degree-{chain_degree} polynomial and the isolation was \
         declared against a degree-{declared_degree} one; a sign-variation count is a statement \
         about one polynomial, so the pairing is refused rather than believed"
    )]
    ChainPolynomialMismatch {
        chain_degree: usize,
        declared_degree: usize,
    },
    #[error(
        "an isolating certificate must drop exactly one sign variation across its interval; \
         {variations_at_lower} at the lower endpoint and {variations_at_upper} at the upper one \
         isolate no single root"
    )]
    NonIsolatingCertificate {
        variations_at_lower: u32,
        variations_at_upper: u32,
    },
    #[error(
        "a remounted algebraic root declares the sign-variation pair ({declared_lower}, \
         {declared_upper}) and its own polynomial's Sturm chain gives ({recomputed_lower}, \
         {recomputed_upper}); the certificate is recomputed rather than trusted, so the \
         declaration is refused"
    )]
    IsolationCertificateDisagrees {
        declared_lower: u32,
        declared_upper: u32,
        recomputed_lower: u32,
        recomputed_upper: u32,
    },
    #[error("an absolute tail bound cannot be negative")]
    NegativeTailBound,
    #[error("an absolute geometric tail ratio must satisfy 0 <= r < 1")]
    InvalidGeometricRatio,
    #[error(
        "the exact value has magnitude past what {species} can carry, so emitting it would return an \
         infinity: refused rather than saturated"
    )]
    FloatMagnitudeOverflows { species: &'static str },
    #[error(
        "the {species} bit pattern 0x{bits:x} is not a number: it names no ratio, so it has no exact dyadic and no enclosure"
    )]
    NotANumberFloat { species: &'static str, bits: u64 },
    #[error(
        "the {species} bit pattern 0x{bits:x} is an infinity (negative: {negative}): it names no ratio, so it has no exact dyadic and no enclosure"
    )]
    InfiniteFloat {
        species: &'static str,
        negative: bool,
        bits: u64,
    },
    #[error("the bit pattern 0x{bits:x} carries bits above the {width}-bit {species} format")]
    OverWideBitPattern {
        species: &'static str,
        width: u32,
        bits: u64,
    },
    #[error(
        "a {species} datum does not re-encode to the pattern 0x{bits:x} it was decoded from; the decode is not a bijection and must not be trusted"
    )]
    NonInvertibleDecode { species: &'static str, bits: u64 },
    #[error("a {holding} datum cannot be re-encoded as a {wanted}")]
    FloatSpeciesMismatch {
        holding: &'static str,
        wanted: &'static str,
    },
}

fn reverse(ordering: ExactOrdering) -> ExactOrdering {
    match ordering {
        ExactOrdering::Less => ExactOrdering::Greater,
        ExactOrdering::Equal => ExactOrdering::Equal,
        ExactOrdering::Greater => ExactOrdering::Less,
        ExactOrdering::Open => ExactOrdering::Open,
    }
}

fn compare_algebraic(left: &AlgebraicRoot, right: &AlgebraicRoot) -> ExactOrdering {
    let interval_order = left
        .isolating_interval
        .disjoint_order(&right.isolating_interval);
    if interval_order != ExactOrdering::Open {
        return interval_order;
    }
    if left.polynomial == right.polynomial {
        // For one fixed Sturm sequence, the variation count immediately
        // before an isolated root is its exact order address among the real
        // roots. Overlapping intervals alone are not enough: two intervals
        // can overlap while isolating different roots.
        right
            .certificate
            .variations_at_lower
            .cmp(&left.certificate.variations_at_lower)
            .into()
    } else {
        ExactOrdering::Open
    }
}

fn compare_rational_algebraic(rational: &Rat, algebraic: &AlgebraicRoot) -> ExactOrdering {
    if *rational <= algebraic.isolating_interval.lower {
        ExactOrdering::Less
    } else if *rational >= algebraic.isolating_interval.upper {
        ExactOrdering::Greater
    } else if algebraic.contains_rational_root(rational) {
        ExactOrdering::Equal
    } else {
        ExactOrdering::Open
    }
}

fn trim_integer_polynomial(coefficients: &mut Vec<BigInt>) {
    while coefficients.last().is_some_and(Zero::is_zero) {
        coefficients.pop();
    }
}

/// The positive gcd of the coefficients. One for the zero polynomial, which has no content.
fn integer_content(coefficients: &[BigInt]) -> BigInt {
    coefficients
        .iter()
        .filter(|value| !value.is_zero())
        .map(Signed::abs)
        .reduce(exact_integer_gcd)
        .unwrap_or_else(BigInt::one)
}

/// Trim, then divide by the content. **The divisor is positive**, so the sign pattern — which is
/// the only thing a sign-variation reading sees — is untouched.
fn make_primitive(coefficients: &mut Vec<BigInt>) {
    trim_integer_polynomial(coefficients);
    if coefficients.is_empty() {
        return;
    }
    let content = integer_content(coefficients);
    if content.is_one() || content.is_zero() {
        return;
    }
    for value in coefficients.iter_mut() {
        *value /= &content;
    }
}

/// The derivative of an integer polynomial, over `Z`.
fn integer_derivative(coefficients: &[BigInt]) -> Vec<BigInt> {
    let mut derivative: Vec<BigInt> = coefficients
        .iter()
        .enumerate()
        .skip(1)
        .map(|(degree, coefficient)| coefficient * BigInt::from(degree))
        .collect();
    trim_integer_polynomial(&mut derivative);
    derivative
}

/// `prem(A, B) = lc(B)^(deg A − deg B + 1) · rem(A, B)`, entirely in `Z[x]`.
///
/// The factor is accumulated one power per elimination step and the remaining powers are applied at
/// the end, which is what makes a **degree gap** cost exactly the powers it should: a step that
/// drops the degree by more than one consumes one power, and the shortfall is paid once at the end.
fn pseudo_remainder(dividend: &[BigInt], divisor: &[BigInt]) -> Vec<BigInt> {
    let mut remainder = dividend.to_vec();
    trim_integer_polynomial(&mut remainder);
    if divisor.is_empty() {
        return remainder;
    }
    let divisor_degree = divisor.len() - 1;
    let leading = divisor[divisor_degree].clone();
    let mut powers = remainder.len().saturating_sub(divisor.len()) + 1;
    if remainder.len() < divisor.len() {
        return remainder;
    }
    while remainder.len() > divisor_degree {
        let top = remainder.len() - 1;
        let shift = top - divisor_degree;
        let lead = remainder[top].clone();
        for value in remainder.iter_mut() {
            *value *= &leading;
        }
        for (index, coefficient) in divisor.iter().enumerate() {
            remainder[index + shift] -= &lead * coefficient;
        }
        trim_integer_polynomial(&mut remainder);
        powers = powers.saturating_sub(1);
    }
    for _ in 0..powers {
        for value in remainder.iter_mut() {
            *value *= &leading;
        }
    }
    remainder
}

/// The sign of `S(u/v)` for `v > 0`, by integer Horner on the homogenized member
/// `Σ s_i u^i v^(d−i) = v^d · S(u/v)`. Multiplying by the positive `v^d` cannot change a sign.
fn homogeneous_sign(coefficients: &[BigInt], numerator: &BigInt, denominator: &BigInt) -> i8 {
    let Some(top) = coefficients.len().checked_sub(1) else {
        return 0;
    };
    let mut accumulated = coefficients[top].clone();
    if denominator.is_one() {
        for coefficient in coefficients[..top].iter().rev() {
            accumulated = accumulated * numerator + coefficient;
        }
    } else {
        let mut power = BigInt::one();
        for coefficient in coefficients[..top].iter().rev() {
            power *= denominator;
            accumulated = accumulated * numerator + coefficient * &power;
        }
    }
    if accumulated.is_zero() {
        0
    } else if accumulated.is_negative() {
        -1
    } else {
        1
    }
}

#[cfg(test)]
fn trim_rational_polynomial(coefficients: &mut Vec<Rat>) {
    while coefficients.last().is_some_and(Zero::is_zero) {
        coefficients.pop();
    }
}

#[cfg(test)]
fn derivative(polynomial: &[Rat]) -> Vec<Rat> {
    let mut derivative = polynomial
        .iter()
        .enumerate()
        .skip(1)
        .map(|(degree, coefficient)| coefficient * Rat::from_integer(BigInt::from(degree)))
        .collect::<Vec<_>>();
    trim_rational_polynomial(&mut derivative);
    derivative
}

#[cfg(test)]
fn polynomial_remainder(dividend: &[Rat], divisor: &[Rat]) -> Vec<Rat> {
    let mut remainder = dividend.to_vec();
    trim_rational_polynomial(&mut remainder);
    if divisor.is_empty() {
        return remainder;
    }
    let divisor_degree = divisor.len() - 1;
    while remainder.len() > divisor_degree {
        let remainder_degree = remainder.len() - 1;
        let shift = remainder_degree - divisor_degree;
        let factor = remainder[remainder_degree].clone() / &divisor[divisor_degree];
        for (index, coefficient) in divisor.iter().enumerate() {
            remainder[index + shift] -= &factor * coefficient;
        }
        trim_rational_polynomial(&mut remainder);
    }
    remainder
}

/// **The naive Euclidean remainder sequence over `Q`, retained as the reference.**
///
/// This is what [`SturmChain`] replaced. It is kept under `cfg(test)` and nothing but the tests
/// that hold the chain against it may call it, so the reference cannot silently come back into the
/// hot path while still being available to refute the replacement.
#[cfg(test)]
fn sturm_sequence(polynomial: &IntegerPolynomial) -> Vec<Vec<Rat>> {
    let first = polynomial.rational_coefficients();
    let second = derivative(&first);
    let mut sequence = vec![first, second];
    while !sequence
        .last()
        .expect("the sequence is nonempty")
        .is_empty()
    {
        let length = sequence.len();
        let mut remainder = polynomial_remainder(&sequence[length - 2], &sequence[length - 1]);
        for coefficient in &mut remainder {
            *coefficient = -coefficient.clone();
        }
        trim_rational_polynomial(&mut remainder);
        if remainder.is_empty() {
            break;
        }
        sequence.push(remainder);
    }
    sequence
}

#[cfg(test)]
fn evaluate_rational_polynomial(polynomial: &[Rat], point: &Rat) -> Rat {
    polynomial
        .iter()
        .rev()
        .fold(Rat::zero(), |value, coefficient| {
            value * point + coefficient
        })
}

#[cfg(test)]
fn sign_variations(sequence: &[Vec<Rat>], point: &Rat) -> u32 {
    let signs = sequence
        .iter()
        .map(|polynomial| evaluate_rational_polynomial(polynomial, point))
        .filter(|value| !value.is_zero())
        .map(|value| if value.is_positive() { 1_i8 } else { -1_i8 })
        .collect::<Vec<_>>();
    signs.windows(2).filter(|pair| pair[0] != pair[1]).count() as u32
}

/// **The mouth: an IEEE-754-shaped bit pattern in, an exact dyadic and its deleted tail out.**
///
/// This module is the workspace's one declared floating-point exception, and the declaration is
/// narrow on purpose. `f64` and `f32` occur in exactly four functions here — [`decode_f64`],
/// [`decode_f32`], [`encode_f64`], [`encode_f32`] — and each is one call to `to_bits` or
/// `from_bits`. **No arithmetic is performed on a machine float anywhere in this module or
/// downstream of it.** Everything else takes `u16`/`u32`/`u64` words, which is what a weight file,
/// a wire format or a sensor actually hands a program.
///
/// ## What a float is, stated precisely
///
/// `docs/canon/THE_MATHEMATICS_TABLET.md` §1: *a float is not a bad approximation of a ratio — it is the
/// ratio's series expansion in base two, truncated, with the remainder discarded.* The first half of
/// that sentence is the part usually missed: the truncated expansion is itself **exact**. An
/// IEEE-754 value is precisely `±m · 2^e` with `m` an integer, and nothing in that statement is
/// approximate. What was destroyed is the **tail** — everything below the last retained bit — and
/// the tail's width is exactly one unit in the last place, `2^e`.
///
/// So the honest face of a float has two possible shapes and **which one it is is not a property of
/// the bits**:
///
/// | the bits are… | the face is… | width |
/// |---|---|---|
/// | the datum itself — a stored weight, a wire word, a constant | a **point** | `0` |
/// | a rounding of a quantity that is not representable | an **enclosure** | one ulp |
///
/// [`FloatReading`] is that declaration and the caller must make it. A codec that guessed would be
/// choosing, for every consumer it will ever have, whether a deletion happened — which is the
/// defect `docs/canon/THE_MATHEMATICS_TABLET.md` §1 names in its own generalisation: *a carrier that
/// reduces on construction has decided, for every consumer it will ever have, which distinctions
/// are invisible.*
///
/// ## What is refused, by name
///
/// `NaN` and `±∞` name no ratio. They are refused as [`ExactValueError::NotANumberFloat`] and
/// [`ExactValueError::InfiniteFloat`] rather than mapped to some sentinel, because a sentinel is a
/// third thing pretending to be a number. Subnormals and both zeros are **accepted** — a subnormal
/// is an ordinary dyadic with the leading one absent, and `−0.0` is a sign bit over an empty
/// magnitude, which is why the sign is retained separately from the significand here rather than
/// folded into a `BigInt` that cannot hold it.
///
/// ## The decode is a bijection and says so
///
/// [`decode_bits`] re-encodes what it just decoded and refuses with
/// [`ExactValueError::NonInvertibleDecode`] if the pattern does not come back identical. The round
/// trip is therefore a **law of the codec**, checked on every call, rather than a property a driver
/// asserts about it afterwards.
pub mod ieee754 {
    use num_bigint::{BigInt, BigUint};
    use num_traits::{One, ToPrimitive, Zero};
    use crate::geometry::Rat;
    use serde::{Deserialize, Serialize};

    use super::{ExactInterval, ExactValueError};

    /// The four binary interchange shapes this codec accepts.
    ///
    /// `bfloat16` is not an IEEE-754 interchange format, but it has the same three fields with the
    /// same meanings and the same subnormal convention, so one decode covers all three. It is here
    /// because it is the format the material arrives in: a transformer weight file is `BF16`, and
    /// `crates/holonic-life/examples/eros_self_emanated_law.rs` refuses every other dtype by name.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
    pub enum BinaryFloatSpecies {
        /// IEEE-754 `binary16`: 1 sign, 5 exponent, 10 stored significand bits.
        Binary16,
        /// 1 sign, 8 exponent, 7 stored significand bits. Same exponent range as `binary32`, eight
        /// significand bits of ratio.
        Bfloat16,
        /// IEEE-754 `binary32`: 1 sign, 8 exponent, 23 stored significand bits.
        Binary32,
        /// IEEE-754 `binary64`: 1 sign, 11 exponent, 52 stored significand bits.
        Binary64,
    }

    impl BinaryFloatSpecies {
        pub const ALL: [BinaryFloatSpecies; 4] = [
            Self::Binary16,
            Self::Bfloat16,
            Self::Binary32,
            Self::Binary64,
        ];

        pub const fn name(self) -> &'static str {
            match self {
                Self::Binary16 => "binary16",
                Self::Bfloat16 => "bfloat16",
                Self::Binary32 => "binary32",
                Self::Binary64 => "binary64",
            }
        }

        pub const fn width_bits(self) -> u32 {
            match self {
                Self::Binary16 | Self::Bfloat16 => 16,
                Self::Binary32 => 32,
                Self::Binary64 => 64,
            }
        }

        /// Bits of **stored** significand. A normal value's leading one is not stored, so the
        /// integer significand of a normal value has `stored_significand_bits() + 1` bits.
        pub const fn stored_significand_bits(self) -> u32 {
            match self {
                Self::Binary16 => 10,
                Self::Bfloat16 => 7,
                Self::Binary32 => 23,
                Self::Binary64 => 52,
            }
        }

        pub const fn exponent_bits(self) -> u32 {
            match self {
                Self::Binary16 => 5,
                Self::Bfloat16 | Self::Binary32 => 8,
                Self::Binary64 => 11,
            }
        }

        pub const fn exponent_bias(self) -> i32 {
            (1_i32 << (self.exponent_bits() - 1)) - 1
        }

        const fn exponent_mask(self) -> u64 {
            (1_u64 << self.exponent_bits()) - 1
        }

        const fn significand_mask(self) -> u64 {
            (1_u64 << self.stored_significand_bits()) - 1
        }

        /// The dyadic grid the subnormals and both zeros of this format sit on: every subnormal is
        /// an integer multiple of `2^{subnormal_ulp_exponent()}`, and so is zero.
        pub const fn subnormal_ulp_exponent(self) -> i32 {
            1 - self.exponent_bias() - self.stored_significand_bits() as i32
        }
    }

    /// How the bits are to be read, which is a declaration and never an inference.
    ///
    /// The same 64 bits are a different mathematical object under each reading, and
    /// `crate::reopening`'s admission law separates them: a point admits every grain, an enclosure
    /// of width one ulp admits no grain finer than the ulp and is refused past it by name.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
    pub enum FloatReading {
        /// **The bits are the datum.** A stored network weight, a wire word, a table constant: the
        /// value in the file *is* `±m·2^e` and no rounding of anything else happened at this
        /// boundary. The enclosure is a point and nothing was deleted **here** — whatever deleted a
        /// tail did so upstream, and that deletion is not this face's to certify.
        ExactBitPattern,
        /// **The bits are the round-to-nearest image of a quantity that is not representable.** The
        /// enclosure is the point plus or minus half a unit in the last place, so its width is
        /// exactly one ulp.
        ///
        /// The enclosure is **outward**: at the low edge of a binade the true rounding preimage is
        /// only a quarter-ulp wide below the point, and this returns a half-ulp there. Outward is
        /// the honest direction — it can only refuse a relation that a sharper enclosure would have
        /// admitted, never admit one a sharper enclosure would have refused.
        RoundedToNearest,
        /// **The bits are the truncation toward zero of the quantity.** The enclosure runs one full
        /// ulp away from zero. A zero datum under this reading straddles zero by one ulp on each
        /// side, since every quantity of magnitude below one ulp truncates to it.
        TruncatedTowardZero,
    }

    impl FloatReading {
        pub const ALL: [FloatReading; 3] = [
            Self::ExactBitPattern,
            Self::RoundedToNearest,
            Self::TruncatedTowardZero,
        ];

        pub const fn name(self) -> &'static str {
            match self {
                Self::ExactBitPattern => "exact bit pattern",
                Self::RoundedToNearest => "rounded to nearest",
                Self::TruncatedTowardZero => "truncated toward zero",
            }
        }

        /// Whether this reading declares that a tail was deleted at this boundary.
        pub const fn deletes_a_tail(self) -> bool {
            !matches!(self, Self::ExactBitPattern)
        }
    }

    /// One decoded binary floating-point datum: an exact dyadic, plus the scale of what the format
    /// could not carry.
    ///
    /// `significand` is **not reduced**. `0.5_f64` decodes to `2^51 · 2^-52`, not to `1 · 2^-1`,
    /// because the two carry different information: the value is the same and the **ulp is not**.
    /// The unit in the last place is a property of the format at this magnitude, and stripping
    /// trailing zeros from the significand would destroy exactly the quantity this whole module
    /// exists to retain. [`BinaryFloatDatum::reduced_dyadic`] offers the stripped form as a
    /// *reading*, which is where a reduction belongs.
    /// **The wire re-encodes the datum and holds it to its own pattern.** Every field below is
    /// decoded from `bits`, and [`BinaryFloatDatum::to_bits`] is the inverse the decoders are
    /// checked against; the derived `Deserialize` admitted a datum whose significand, exponent and
    /// pattern named three different numbers, and [`BinaryFloatDatum::value`] then returned a
    /// rational that is not the float the pattern carries. The wire therefore re-encodes and
    /// refuses unless the result is exactly `bits` — the same
    /// [`ExactValueError::NonInvertibleDecode`] the decoders raise.
    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(try_from = "BinaryFloatDatumWire")]
    pub struct BinaryFloatDatum {
        pub species: BinaryFloatSpecies,
        /// The pattern this datum was decoded from, zero-extended to 64 bits.
        pub bits: u64,
        /// The sign bit, retained **separately** from the magnitude. A signed integer significand
        /// cannot hold the sign of `−0.0`, and a codec that cannot round-trip `−0.0` is not a
        /// bijection on the format it claims to decode.
        pub negative: bool,
        /// The unsigned integer significand, with a normal value's hidden leading one restored.
        pub significand: BigUint,
        /// `value = ±significand · 2^{ulp_exponent}`, and `2^{ulp_exponent}` is one unit in the
        /// last place.
        pub ulp_exponent: i32,
        pub subnormal: bool,
    }

    #[derive(Deserialize)]
    struct BinaryFloatDatumWire {
        species: BinaryFloatSpecies,
        bits: u64,
        negative: bool,
        significand: BigUint,
        ulp_exponent: i32,
        subnormal: bool,
    }

    impl TryFrom<BinaryFloatDatumWire> for BinaryFloatDatum {
        type Error = ExactValueError;

        fn try_from(wire: BinaryFloatDatumWire) -> Result<Self, Self::Error> {
            let datum = BinaryFloatDatum {
                species: wire.species,
                bits: wire.bits,
                negative: wire.negative,
                significand: wire.significand,
                ulp_exponent: wire.ulp_exponent,
                subnormal: wire.subnormal,
            };
            if datum.to_bits()? != datum.bits {
                return Err(ExactValueError::NonInvertibleDecode {
                    species: datum.species.name(),
                    bits: datum.bits,
                });
            }
            Ok(datum)
        }
    }

    impl BinaryFloatDatum {
        /// The exact value, as a rational. This is not an approximation of the float; it **is** the
        /// float.
        pub fn value(&self) -> Rat {
            let magnitude = scaled(BigInt::from(self.significand.clone()), self.ulp_exponent);
            if self.negative { -magnitude } else { magnitude }
        }

        /// One unit in the last place, exactly: `2^{ulp_exponent}`. This is the width of what the
        /// format deleted, and under a rounding reading it is the width of the enclosure.
        pub fn unit_in_last_place(&self) -> Rat {
            power_of_two(self.ulp_exponent)
        }

        /// The ulp said as a bit count: `ulp = 2^{-ulp_bits()}`. Negative for values so large that
        /// the format's spacing exceeds one.
        pub fn ulp_bits(&self) -> i32 {
            -self.ulp_exponent
        }

        pub fn is_zero(&self) -> bool {
            self.significand.is_zero()
        }

        pub fn signed_significand(&self) -> BigInt {
            let magnitude = BigInt::from(self.significand.clone());
            if self.negative { -magnitude } else { magnitude }
        }

        /// The same value with trailing factors of two stripped: `(m, e)` with `m` odd or zero.
        ///
        /// A **reading**, offered rather than imposed. The ulp is not recoverable from it.
        pub fn reduced_dyadic(&self) -> (BigInt, i32) {
            let mut numerator = self.signed_significand();
            let mut exponent = self.ulp_exponent;
            if numerator.is_zero() {
                return (numerator, 0);
            }
            let trailing = numerator
                .magnitude()
                .trailing_zeros()
                .unwrap_or(0)
                .min(i32::MAX as u64) as usize;
            numerator >>= trailing;
            exponent += trailing as i32;
            (numerator, exponent)
        }

        /// The face this datum presents under a declared reading.
        ///
        /// This is the whole content of the module in four lines: the point is the truncated
        /// expansion, and the interval is the point plus the tail the format threw away.
        pub fn enclosure(&self, reading: FloatReading) -> ExactInterval {
            let value = self.value();
            let ulp = self.unit_in_last_place();
            match reading {
                FloatReading::ExactBitPattern => ExactInterval::point(value),
                FloatReading::RoundedToNearest => {
                    let half = ulp / Rat::from_integer(BigInt::from(2));
                    ExactInterval {
                        lower: &value - &half,
                        upper: &value + &half,
                    }
                }
                FloatReading::TruncatedTowardZero => {
                    if self.is_zero() {
                        ExactInterval {
                            lower: -ulp.clone(),
                            upper: ulp,
                        }
                    } else if self.negative {
                        ExactInterval {
                            lower: &value - &ulp,
                            upper: value,
                        }
                    } else {
                        ExactInterval {
                            lower: value.clone(),
                            upper: &value + &ulp,
                        }
                    }
                }
            }
        }

        /// Re-encode to the interchange pattern, computed from the decoded fields rather than
        /// echoed from [`BinaryFloatDatum::bits`].
        ///
        /// [`decode_bits`] calls this on every decode and refuses when the two disagree, which is
        /// what makes the round trip a law rather than a claim.
        pub fn to_bits(&self) -> Result<u64, ExactValueError> {
            let species = self.species;
            let stored = species.stored_significand_bits();
            let significand = self.significand.to_u64().ok_or({
                ExactValueError::NonInvertibleDecode {
                    species: species.name(),
                    bits: self.bits,
                }
            })?;
            let sign = u64::from(self.negative) << (species.width_bits() - 1);
            if self.subnormal {
                if significand > species.significand_mask()
                    || self.ulp_exponent != species.subnormal_ulp_exponent()
                {
                    return Err(ExactValueError::NonInvertibleDecode {
                        species: species.name(),
                        bits: self.bits,
                    });
                }
                return Ok(sign | significand);
            }
            let hidden = 1_u64 << stored;
            let raw_exponent = self.ulp_exponent + species.exponent_bias() + stored as i32;
            if significand < hidden
                || significand >= hidden << 1
                || raw_exponent < 1
                || raw_exponent as u64 >= species.exponent_mask()
            {
                return Err(ExactValueError::NonInvertibleDecode {
                    species: species.name(),
                    bits: self.bits,
                });
            }
            Ok(sign | ((raw_exponent as u64) << stored) | (significand - hidden))
        }
    }

    /// Decode one interchange pattern of a declared species into its exact dyadic.
    ///
    /// The sole arithmetic is on integers: a shift, a mask, and one subtraction of the bias. `NaN`
    /// and `±∞` are refused by name; subnormals, `+0.0` and `−0.0` are decoded like anything else.
    pub fn decode_bits(
        species: BinaryFloatSpecies,
        bits: u64,
    ) -> Result<BinaryFloatDatum, ExactValueError> {
        let width = species.width_bits();
        if width < 64 && (bits >> width) != 0 {
            return Err(ExactValueError::OverWideBitPattern {
                species: species.name(),
                width,
                bits,
            });
        }
        let stored = species.stored_significand_bits();
        let negative = (bits >> (width - 1)) & 1 == 1;
        let raw_exponent = (bits >> stored) & species.exponent_mask();
        let fraction = bits & species.significand_mask();
        if raw_exponent == species.exponent_mask() {
            return Err(if fraction == 0 {
                ExactValueError::InfiniteFloat {
                    species: species.name(),
                    negative,
                    bits,
                }
            } else {
                ExactValueError::NotANumberFloat {
                    species: species.name(),
                    bits,
                }
            });
        }
        let (significand, ulp_exponent, subnormal) = if raw_exponent == 0 {
            (fraction, species.subnormal_ulp_exponent(), true)
        } else {
            (
                (1_u64 << stored) | fraction,
                raw_exponent as i32 - species.exponent_bias() - stored as i32,
                false,
            )
        };
        let datum = BinaryFloatDatum {
            species,
            bits,
            negative,
            significand: BigUint::from(significand),
            ulp_exponent,
            subnormal,
        };
        if datum.to_bits()? != bits {
            return Err(ExactValueError::NonInvertibleDecode {
                species: species.name(),
                bits,
            });
        }
        Ok(datum)
    }

    /// A `bfloat16` word, as `crates/holonic-life/examples/eros_self_emanated_law.rs` reads them out of a
    /// safetensors payload.
    pub fn decode_bfloat16_bits(word: u16) -> Result<BinaryFloatDatum, ExactValueError> {
        decode_bits(BinaryFloatSpecies::Bfloat16, u64::from(word))
    }

    /// An IEEE-754 `binary16` word, including the `<f2` uncertainty arrays used by the admitted
    /// physical-fold material.
    pub fn decode_binary16_bits(word: u16) -> Result<BinaryFloatDatum, ExactValueError> {
        decode_bits(BinaryFloatSpecies::Binary16, u64::from(word))
    }

    /// An IEEE-754 `binary32` word.
    pub fn decode_binary32_bits(word: u32) -> Result<BinaryFloatDatum, ExactValueError> {
        decode_bits(BinaryFloatSpecies::Binary32, u64::from(word))
    }

    /// An IEEE-754 `binary64` word.
    pub fn decode_binary64_bits(word: u64) -> Result<BinaryFloatDatum, ExactValueError> {
        decode_bits(BinaryFloatSpecies::Binary64, word)
    }

    /// **The mouth for a live machine float.** One `to_bits`, then integers the rest of the way.
    ///
    /// This is one of the four functions in this workspace's library files that mention an IEEE
    /// type at all. It performs no arithmetic on `value`; `f64::to_bits` is a reinterpretation of
    /// the same storage.
    pub fn decode_f64(value: f64) -> Result<BinaryFloatDatum, ExactValueError> {
        decode_binary64_bits(value.to_bits())
    }

    /// [`decode_f64`] for `binary32`.
    pub fn decode_f32(value: f32) -> Result<BinaryFloatDatum, ExactValueError> {
        decode_binary32_bits(value.to_bits())
    }

    /// ★ **THE EMIT-SIDE MOUTH: round an exact value into a float and KEEP THE REMAINDER.**
    ///
    /// Every float mouth in this workspace ran one way — a stored word decoded to an exact dyadic,
    /// so a float could enter and never leave. Emitting requires the other direction, and the
    /// direction that *loses* something is exactly the one that must certify what it lost.
    ///
    /// Returns the datum together with an **exact rational residual** satisfying
    ///
    /// ```text
    ///     value  =  datum.value()  +  residual          exactly, over the rationals
    /// ```
    ///
    /// so nothing about the rounding is unknown. A caller emitting a tensor can sum, bound, or
    /// exhibit the residuals rather than reporting a tolerance that got smaller — which is the
    /// error relocating, not shrinking.
    ///
    /// **Round-to-nearest, ties-to-even**, computed on integers: no float arithmetic occurs here
    /// and no comparison is approximate. A magnitude past the format's top binade is **refused**
    /// rather than saturated to an infinity, because an infinity names no ratio and this carrier
    /// admits no member that names no ratio.
    pub fn round_into(
        value: &Rat,
        species: BinaryFloatSpecies,
    ) -> Result<(BinaryFloatDatum, Rat), ExactValueError> {
        let negative = num_traits::Signed::is_negative(value);
        let magnitude = if negative {
            -value.clone()
        } else {
            value.clone()
        };
        let stored = species.stored_significand_bits() as i32;
        let subnormal_ulp = species.subnormal_ulp_exponent();

        // The zero datum, and it is exact.
        if magnitude.is_zero() {
            let datum = BinaryFloatDatum {
                species,
                bits: 0,
                negative,
                significand: BigUint::from(0u32),
                ulp_exponent: subnormal_ulp,
                subnormal: true,
            };
            return Ok((datum, Rat::zero()));
        }

        // The binade: the greatest `k` with `2^k <= magnitude`. Found by comparing exact
        // rationals, never by a logarithm.
        let mut binade: i32 = 0;
        let two = Rat::from_integer(BigInt::from(2));
        let mut probe = Rat::one();
        while probe > magnitude {
            probe /= &two;
            binade -= 1;
            if binade < subnormal_ulp - 1 {
                break;
            }
        }
        while &probe * &two <= magnitude {
            probe *= &two;
            binade += 1;
        }

        // Normal numbers place the ulp `stored` bits below the binade; subnormals sit on the
        // format's fixed floor grid.
        let normal_ulp = binade - stored;
        let ulp_exponent = normal_ulp.max(subnormal_ulp);
        let subnormal = ulp_exponent > normal_ulp || binade < subnormal_ulp + stored;

        // significand = round_half_even(magnitude / 2^ulp_exponent), on integers.
        let scale = power_of_two(-ulp_exponent);
        let scaled_value = &magnitude * &scale;
        let floor = scaled_value.numer() / scaled_value.denom();
        let remainder = &scaled_value - Rat::from_integer(floor.clone());
        let half = Rat::new(BigInt::from(1), BigInt::from(2));
        let rounded = match remainder.cmp(&half) {
            core::cmp::Ordering::Less => floor,
            core::cmp::Ordering::Greater => floor + BigInt::from(1),
            // Ties to even: the tie is exactly representable and the choice is declared.
            core::cmp::Ordering::Equal => {
                if (&floor % BigInt::from(2)).is_zero() {
                    floor
                } else {
                    floor + BigInt::from(1)
                }
            }
        };

        // Rounding up may carry into the next binade: `0b1111... -> 0b10000...`. Re-seat rather
        // than emit a significand the format cannot hold.
        //
        // **The carry is exact and needs no re-rounding.** `2·hidden · 2^ulp = hidden · 2^(ulp+1)`,
        // so the carried datum is the hidden bit one binade up, full stop. An earlier form
        // recomputed the FLOOR at the lifted exponent, which lands one below the hidden bit and
        // produced a significand the format cannot hold — refused at `to_bits` with a bijection
        // complaint that named the wrong defect. The exhaustive sweep over every bf16 pattern could
        // not catch it, because a representable value never carries; real material found it on its
        // first unrepresentable half-integer.
        let hidden = BigInt::from(1) << (stored as usize);
        let (significand, ulp_exponent, subnormal) = if !subnormal && rounded >= (&hidden << 1) {
            (hidden.clone(), ulp_exponent + 1, false)
        } else if subnormal && rounded >= hidden {
            // A subnormal that rounded up into the smallest normal is a normal.
            (rounded, ulp_exponent, false)
        } else {
            (rounded, ulp_exponent, subnormal)
        };

        let raw_exponent = ulp_exponent + species.exponent_bias() + stored;
        if !subnormal && raw_exponent as u64 >= species.exponent_mask() {
            return Err(ExactValueError::FloatMagnitudeOverflows {
                species: species.name(),
            });
        }

        let significand: BigUint =
            significand
                .to_biguint()
                .ok_or(ExactValueError::FloatMagnitudeOverflows {
                    species: species.name(),
                })?;
        let mut datum = BinaryFloatDatum {
            species,
            bits: 0,
            negative,
            significand,
            ulp_exponent,
            subnormal,
        };
        datum.bits = datum.to_bits()?;
        let residual = value - datum.value();
        Ok((datum, residual))
    }

    /// [`round_into`] for `Bfloat16`, returning the stored word beside the exact residual.
    pub fn round_into_bfloat16(value: &Rat) -> Result<(u16, Rat), ExactValueError> {
        let (datum, residual) = round_into(value, BinaryFloatSpecies::Bfloat16)?;
        let word = u16::try_from(datum.to_bits()?).map_err(|_| {
            ExactValueError::FloatMagnitudeOverflows {
                species: BinaryFloatSpecies::Bfloat16.name(),
            }
        })?;
        Ok((word, residual))
    }

    /// The inverse mouth, so the bijection can be exercised end to end by a driver.
    pub fn encode_f64(datum: &BinaryFloatDatum) -> Result<f64, ExactValueError> {
        if datum.species != BinaryFloatSpecies::Binary64 {
            return Err(ExactValueError::FloatSpeciesMismatch {
                holding: datum.species.name(),
                wanted: BinaryFloatSpecies::Binary64.name(),
            });
        }
        Ok(f64::from_bits(datum.to_bits()?))
    }

    /// [`encode_f64`] for `binary32`.
    pub fn encode_f32(datum: &BinaryFloatDatum) -> Result<f32, ExactValueError> {
        if datum.species != BinaryFloatSpecies::Binary32 {
            return Err(ExactValueError::FloatSpeciesMismatch {
                holding: datum.species.name(),
                wanted: BinaryFloatSpecies::Binary32.name(),
            });
        }
        let bits = datum.to_bits()?;
        let word = u32::try_from(bits).map_err(|_| ExactValueError::NonInvertibleDecode {
            species: datum.species.name(),
            bits,
        })?;
        Ok(f32::from_bits(word))
    }

    fn power_of_two(exponent: i32) -> Rat {
        if exponent >= 0 {
            Rat::from_integer(BigInt::one() << (exponent as usize))
        } else {
            Rat::new(BigInt::one(), BigInt::one() << ((-exponent) as usize))
        }
    }

    fn scaled(numerator: BigInt, exponent: i32) -> Rat {
        if exponent >= 0 {
            Rat::from_integer(numerator << (exponent as usize))
        } else {
            Rat::new(numerator, BigInt::one() << ((-exponent) as usize))
        }
    }
}

#[cfg(test)]
mod emit_side_mouth_tests {
    use super::Rat;
    use super::ieee754::{
        BinaryFloatDatum, BinaryFloatSpecies, decode_bfloat16_bits, round_into, round_into_bfloat16,
    };
    use num_bigint::BigInt;
    use num_traits::Zero;

    fn rat(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    #[test]
    fn a_representable_value_emits_with_residual_exactly_zero() {
        // Every one of these is a dyadic bf16 can hold exactly, so the mouth must lose NOTHING.
        for value in [
            rat(0, 1),
            rat(1, 1),
            rat(-1, 1),
            rat(1, 2),
            rat(3, 4),
            rat(-5, 8),
            rat(256, 1),
            rat(1, 256),
            rat(127, 128),
        ] {
            let (word, residual) = round_into_bfloat16(&value).expect("emits");
            assert!(
                residual.is_zero(),
                "a representable value lost {residual} at {value}"
            );
            // And the round trip through the READ side must return the same exact value.
            let back = decode_bfloat16_bits(word).expect("decodes").value();
            assert_eq!(back, value, "the two mouths disagree at {value}");
        }
    }

    #[test]
    fn an_unrepresentable_value_closes_exactly_over_the_residual() {
        // **The law: value = datum.value() + residual, exactly, over the rationals.** A tenth is
        // not a dyadic, so the residual is genuinely non-zero and must account for the whole
        // difference -- nothing is unknown about what the emission cost.
        for value in [
            rat(1, 10),
            rat(-1, 3),
            rat(22, 7),
            rat(1, 1000),
            rat(-9999, 7),
        ] {
            let (datum, residual) =
                round_into(&value, BinaryFloatSpecies::Bfloat16).expect("emits");
            assert_eq!(
                datum.value() + residual.clone(),
                value,
                "the residual did not close at {value}"
            );
            assert!(!residual.is_zero(), "{value} should not be representable");
            // The residual may never exceed half an ulp: that is what round-to-nearest MEANS, and
            // a residual past it would mean a nearer float existed and was not taken.
            let half_ulp = datum.unit_in_last_place() / Rat::from_integer(BigInt::from(2));
            let magnitude = if num_traits::Signed::is_negative(&residual) {
                -residual.clone()
            } else {
                residual.clone()
            };
            assert!(
                magnitude <= half_ulp,
                "residual {residual} exceeds half an ulp {half_ulp} at {value}"
            );
        }
    }

    #[test]
    fn every_bfloat16_word_survives_the_round_trip_through_both_mouths() {
        // The read mouth decodes a word to an exact value; the emit mouth must return that word.
        // Swept over every finite bf16 pattern -- this is a bijection claim and it is checked
        // exhaustively rather than sampled.
        let mut checked = 0u32;
        for bits in 0..=u16::MAX {
            let Ok(datum) = decode_bfloat16_bits(bits) else {
                continue; // NaN and the infinities name no ratio and are refused by the reader.
            };
            let value = datum.value();
            let (word, residual) = round_into_bfloat16(&value).expect("emits");
            assert!(residual.is_zero(), "0x{bits:04x} lost {residual}");
            // -0.0 and +0.0 carry the same value; the sign is retained separately and the emit
            // mouth reads it from the value, which has no negative zero. That is the one place the
            // round trip is not on the nose, and it is named rather than hidden.
            if datum.is_zero() {
                assert!(word == 0x0000 || word == 0x8000);
            } else {
                assert_eq!(word, bits, "0x{bits:04x} did not return itself");
            }
            checked += 1;
        }
        assert!(
            checked > 60_000,
            "only {checked} finite patterns were swept"
        );
    }

    #[test]
    fn a_rounding_carry_across_a_binade_re_seats_rather_than_overflowing() {
        // **The case the exhaustive sweep cannot reach**: a value BETWEEN two representables that
        // rounds UP across a binade boundary. 32729/2 = 16364.5 sits just under 2^14 and rounds to
        // 16384, carrying `0b11111111 -> 0b100000000`. Found by real material, not by the sweep.
        for value in [rat(32729, 2), rat(-32729, 2), rat(511, 256), rat(1023, 512)] {
            let (datum, residual) =
                round_into(&value, BinaryFloatSpecies::Bfloat16).expect("emits");
            assert_eq!(
                datum.value() + residual.clone(),
                value,
                "the carry did not close at {value}"
            );
            let half_ulp = datum.unit_in_last_place() / Rat::from_integer(BigInt::from(2));
            let magnitude = if num_traits::Signed::is_negative(&residual) {
                -residual.clone()
            } else {
                residual.clone()
            };
            assert!(magnitude <= half_ulp, "{value} rounded past half an ulp");
            // And the carried datum must re-encode, which is what the defect broke.
            datum
                .to_bits()
                .expect("the carried datum must hold in the format");
        }
    }

    /// **A float datum whose fields do not re-encode to its own pattern is refused at the wire.**
    ///
    /// Every field of a `BinaryFloatDatum` is decoded from `bits`, and `to_bits` is the inverse the
    /// decoders are checked against. The derived `Deserialize` admitted a datum whose significand
    /// and pattern named different numbers, and `value()` then returned a rational that is not the
    /// float the pattern carries.
    #[test]
    fn a_float_datum_that_does_not_re_encode_to_its_own_pattern_is_refused() {
        let datum = decode_bfloat16_bits(0x3f80).expect("1.0 decodes");
        let wire = serde_json::to_string(&datum).expect("serialized");
        assert_eq!(
            serde_json::from_str::<BinaryFloatDatum>(&wire).expect("a lawful wire"),
            datum
        );

        let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("the lawful wire");
        hostile["bits"] = serde_json::Value::from(0x4000_u64);
        assert!(
            serde_json::from_value::<BinaryFloatDatum>(hostile)
                .err()
                .is_some_and(|refusal| refusal.to_string().contains("does not re-encode")),
            "a pattern the fields do not produce must be refused"
        );

        let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("the lawful wire");
        hostile["ulp_exponent"] = serde_json::Value::from(-40_i32);
        assert!(
            serde_json::from_value::<BinaryFloatDatum>(hostile).is_err(),
            "an exponent outside the format must be refused"
        );
    }

    #[test]
    fn a_magnitude_past_the_format_refuses_rather_than_saturating() {
        // An infinity names no ratio, so this carrier admits no member that names no ratio.
        let past = Rat::from_integer(BigInt::from(1) << 400);
        assert!(round_into(&past, BinaryFloatSpecies::Bfloat16).is_err());
        assert!(round_into(&(-past), BinaryFloatSpecies::Bfloat16).is_err());
    }

    #[test]
    fn the_tie_goes_to_even_and_the_choice_is_declared() {
        // Exactly halfway between two bf16 neighbours. bf16 has 8 significand bits, so
        // 257/256 sits between 1 and 1+2^-7; the tie must land on the even significand.
        let (low, residual) =
            round_into(&rat(513, 512), BinaryFloatSpecies::Bfloat16).expect("emits");
        assert_eq!(low.value() + residual, rat(513, 512));
        assert!(
            low.significand.clone() % num_bigint::BigUint::from(2u32)
                == num_bigint::BigUint::from(0u32)
        );
    }
}

#[cfg(test)]
mod tests {
    /// **A reversed enclosure is refused at the wire, not reconstructed past the constructor.**
    #[test]
    fn a_reversed_interval_wire_is_refused_and_a_lawful_one_round_trips() {
        let lawful = ExactInterval::new(
            Rat::from_integer(BigInt::from(1)),
            Rat::from_integer(BigInt::from(2)),
        )
        .expect("ordered");
        let wire = serde_json::to_string(&lawful).expect("serialized");
        let remounted: ExactInterval = serde_json::from_str(&wire).expect("lawful wire");
        assert_eq!(remounted, lawful);

        let reversed = ExactInterval {
            lower: lawful.upper.clone(),
            upper: lawful.lower.clone(),
        };
        let hostile = serde_json::to_string(&reversed).expect("serialized");
        assert!(serde_json::from_str::<ExactInterval>(&hostile).is_err());
    }

    /// **An integer polynomial's normal form survives the wire, and `degree` is total.**
    ///
    /// The empty coefficient list is the case that mattered: `len() - 1` panics in a debug build
    /// and wraps to `usize::MAX` in a release build — this workspace's release profile carries no
    /// overflow checks — and that number then flows into `check_declared_size` and into every
    /// consumer as a declared extent.
    #[test]
    fn an_empty_or_untrimmed_polynomial_wire_is_refused_and_the_degree_is_total() {
        // The wire the constructor produces remounts unchanged.
        let lawful = IntegerPolynomial::new(vec![-BigInt::from(2), BigInt::zero(), BigInt::one()])
            .expect("nonzero");
        let wire = serde_json::to_string(&lawful).expect("serialized");
        assert_eq!(
            serde_json::from_str::<IntegerPolynomial>(&wire).expect("lawful wire"),
            lawful
        );

        // Empty: refused by name rather than deserialized into a degree of `usize::MAX`.
        let emptied = IntegerPolynomial {
            coefficients: Vec::new(),
        };
        let hostile = serde_json::to_string(&emptied).expect("serialized");
        let refusal = serde_json::from_str::<IntegerPolynomial>(&hostile)
            .expect_err("an empty coefficient list names no polynomial");
        assert!(
            refusal.to_string().contains("zero polynomial"),
            "the empty wire was refused for the wrong reason: {refusal}"
        );

        // Untrimmed: a declared degree the polynomial does not have.
        let untrimmed = IntegerPolynomial {
            coefficients: vec![BigInt::one(), BigInt::from(2), BigInt::zero()],
        };
        let hostile = serde_json::to_string(&untrimmed).expect("serialized");
        let refusal = serde_json::from_str::<IntegerPolynomial>(&hostile)
            .expect_err("a zero leading coefficient is not the normal form");
        assert!(
            refusal.to_string().contains("leading entry is zero"),
            "the untrimmed wire was refused for the wrong reason: {refusal}"
        );

        // And the public field still admits a direct mutation, so `degree` is total against it.
        assert_eq!(
            emptied.degree(),
            0,
            "an empty coefficient list must not wrap the degree"
        );
        assert_eq!(
            emptied.check_declared_size(),
            Err(ExactValueError::ZeroPolynomial)
        );
        assert_eq!(
            SturmChain::of(&emptied),
            Err(ExactValueError::ZeroPolynomial)
        );
    }

    /// **A remounted polynomial passes the declared-size gate the constructor's callers pass.**
    #[test]
    fn a_polynomial_wire_past_the_declared_ceilings_is_refused() {
        let mut tall = vec![BigInt::zero(); STURM_DEGREE_CEILING + 2];
        tall[0] = -BigInt::one();
        tall[STURM_DEGREE_CEILING + 1] = BigInt::one();
        let hostile =
            serde_json::to_string(&IntegerPolynomial { coefficients: tall }).expect("serialized");
        assert!(
            serde_json::from_str::<IntegerPolynomial>(&hostile)
                .err()
                .is_some_and(|refusal| refusal.to_string().contains("Sturm ceiling")),
            "a degree past the owner's ceiling must be refused at the wire"
        );

        // The same for the combined work index, which is what actually bounds a chain: a degree
        // well inside the degree ceiling with coefficients well inside the width ceiling can still
        // name a computation of hours.
        let mut wide = vec![BigInt::zero(); 101];
        wide[0] = -(BigInt::one() << 1_000_000_usize);
        wide[100] = BigInt::one();
        let heavy = IntegerPolynomial::new(wide).expect("nonzero");
        assert!(
            heavy.degree() <= STURM_DEGREE_CEILING
                && heavy
                    .coefficients
                    .iter()
                    .map(BigInt::bits)
                    .max()
                    .unwrap_or(0)
                    <= STURM_COEFFICIENT_BIT_CEILING,
            "the point of this case is that neither individual ceiling refuses it"
        );
        assert!(
            matches!(
                heavy.check_declared_size(),
                Err(ExactValueError::SturmWorkTooLarge { .. })
            ),
            "a work index past the ceiling must be refused by name"
        );
        let hostile = serde_json::to_string(&heavy).expect("serialized");
        assert!(
            serde_json::from_str::<IntegerPolynomial>(&hostile)
                .err()
                .is_some_and(|refusal| refusal.to_string().contains("work index")),
            "the wire must take the same gate the constructor's callers take"
        );
    }

    /// **A forged isolation certificate is refused because the wire re-runs the isolation.**
    ///
    /// `x² + 1` has no real root at all, so a hand-built declaration that it has one in `[-1, 1]`
    /// is the sharpest case: nothing about the two carried integers is checkable on its own, and
    /// the polynomial and the interval are exactly what make it false. `ExactHodgeSpectrum`
    /// genuinely round-trips these objects through serde, so the wire is a real surface.
    #[test]
    fn a_forged_algebraic_root_wire_is_refused_and_a_lawful_one_round_trips() {
        // Lawful: sqrt(2), isolated by this owner's own certificate, remounts unchanged.
        let lawful =
            AlgebraicRoot::square_root(&Rat::from_integer(BigInt::from(2)), 16).expect("isolated");
        let wire = serde_json::to_string(&lawful).expect("serialized");
        assert_eq!(
            serde_json::from_str::<AlgebraicRoot>(&wire).expect("a lawful wire"),
            lawful
        );

        // Forged: `x² + 1` with a claimed root in `(-1, 1)` and a certificate that looks like one.
        // The fields are public, so this is exactly what a hand-built wire can present.
        let forged = AlgebraicRoot {
            polynomial: IntegerPolynomial::new(vec![BigInt::one(), BigInt::zero(), BigInt::one()])
                .expect("nonzero"),
            isolating_interval: ExactInterval::new(
                Rat::from_integer(-BigInt::one()),
                Rat::from_integer(BigInt::one()),
            )
            .expect("ordered"),
            certificate: SturmIsolationCertificate {
                variations_at_lower: 1,
                variations_at_upper: 0,
            },
        };
        let forged = serde_json::to_string(&forged).expect("serialized");
        let refusal = serde_json::from_str::<AlgebraicRoot>(&forged)
            .expect_err("a polynomial with no real root cannot isolate one");
        assert!(
            refusal
                .to_string()
                .contains("roots rather than exactly one"),
            "the forged wire was refused for the wrong reason: {refusal}"
        );

        // Forged the other way: a real root, but a certificate that is not the one the chain gives.
        let mut hostile: serde_json::Value =
            serde_json::from_str(&wire).expect("the lawful wire parses");
        hostile["certificate"]["variations_at_lower"] =
            serde_json::Value::from(lawful.certificate.variations_at_lower + 1);
        hostile["certificate"]["variations_at_upper"] =
            serde_json::Value::from(lawful.certificate.variations_at_upper + 1);
        let refusal = serde_json::from_value::<AlgebraicRoot>(hostile)
            .expect_err("a certificate the chain does not give is refused");
        assert!(
            refusal.to_string().contains("recomputed"),
            "the disagreeing certificate was refused for the wrong reason: {refusal}"
        );

        // And a bare certificate that isolates nothing is refused on its own.
        let two_roots = serde_json::to_string(&SturmIsolationCertificate {
            variations_at_lower: 3,
            variations_at_upper: 1,
        })
        .expect("serialized");
        assert!(
            serde_json::from_str::<SturmIsolationCertificate>(&two_roots).is_err(),
            "a pair that drops two variations isolates no single root"
        );
        let one_root = serde_json::to_string(&SturmIsolationCertificate {
            variations_at_lower: 3,
            variations_at_upper: 2,
        })
        .expect("serialized");
        assert!(serde_json::from_str::<SturmIsolationCertificate>(&one_root).is_ok());
    }

    /// **A tail certificate that closes no tail is refused at the wire.**
    ///
    /// `CertifiedSeries::new` validates the certificate and `CertifiedSeries::enclosure` then
    /// `expect`s that validation — it returns no `Result` and cannot report a failure. The derived
    /// `Deserialize` reconstructed the struct past the constructor, so a remounted series carrying
    /// a geometric ratio of one **panicked** inside `enclosure`. This is the same constructor
    /// bypass as the forged algebraic root, with a panic at the end of it instead of a wrong order.
    #[test]
    fn a_series_whose_tail_does_not_close_is_refused_at_the_wire() {
        let lawful = CertifiedSeries::new(
            ExactExpr::from(Rat::zero()),
            Rat::zero(),
            BigUint::from(4_u32),
            SeriesTailCertificate::AbsoluteGeometric {
                first_omitted_abs_bound: Rat::new(BigInt::one(), BigInt::from(8)),
                ratio_abs_bound: Rat::new(BigInt::one(), BigInt::from(2)),
            },
        )
        .expect("a closing certificate");
        let wire = serde_json::to_string(&lawful).expect("serialized");
        assert_eq!(
            serde_json::from_str::<CertifiedSeries>(&wire).expect("a lawful wire"),
            lawful
        );

        for hostile in [
            SeriesTailCertificate::AbsoluteGeometric {
                first_omitted_abs_bound: Rat::new(BigInt::one(), BigInt::from(8)),
                // A ratio of one sums to an infinite tail: it closes nothing.
                ratio_abs_bound: Rat::one(),
            },
            SeriesTailCertificate::AbsoluteGeometric {
                // A negative absolute bound is not a bound.
                first_omitted_abs_bound: -Rat::one(),
                ratio_abs_bound: Rat::new(BigInt::one(), BigInt::from(2)),
            },
        ] {
            assert!(
                hostile.remainder_interval().is_err(),
                "the fixture must be one the constructor refuses"
            );
            let bare = serde_json::to_string(&hostile).expect("serialized");
            assert!(
                serde_json::from_str::<SeriesTailCertificate>(&bare).is_err(),
                "a certificate that closes no tail must be refused on its own"
            );
            let carried = serde_json::to_string(&CertifiedSeries {
                expression: lawful.expression.clone(),
                partial_sum: lawful.partial_sum.clone(),
                terms_folded: lawful.terms_folded.clone(),
                tail_certificate: hostile,
            })
            .expect("serialized");
            assert!(
                serde_json::from_str::<CertifiedSeries>(&carried).is_err(),
                "a series carrying it must be refused rather than left to panic in `enclosure`"
            );
        }
    }

    /// **A chain belongs to one polynomial, and pairing it with another is refused.**
    ///
    /// The chain of `x` is `[x, 1]`, which has one sign variation below zero and none above it, so
    /// counting `x² + 1` against it used to return `Ok` with a certificate for a root that does not
    /// exist.
    #[test]
    fn a_chain_built_for_another_polynomial_cannot_certify_an_isolation() {
        let linear = IntegerPolynomial::new(vec![BigInt::zero(), BigInt::one()]).expect("nonzero");
        let no_real_root =
            IntegerPolynomial::new(vec![BigInt::one(), BigInt::zero(), BigInt::one()])
                .expect("nonzero");
        let chain = SturmChain::of(&linear).expect("the chain builds");
        assert_eq!(chain.polynomial(), &linear);
        assert!(chain.is_sturm_chain());

        let interval = ExactInterval::new(
            Rat::from_integer(-BigInt::one()),
            Rat::from_integer(BigInt::one()),
        )
        .expect("ordered");

        // The mispairing the chain used to accept.
        assert!(matches!(
            AlgebraicRoot::isolate_against(no_real_root.clone(), interval.clone(), &chain),
            Err(ExactValueError::ChainPolynomialMismatch { .. })
        ));
        // Taking the chain alone cannot be mispaired: it isolates the root of `x`, correctly.
        let isolated = AlgebraicRoot::isolate_with(&chain, interval.clone()).expect("x has a root");
        assert_eq!(isolated.polynomial, linear);
        // And the lawful pairing still works.
        assert_eq!(
            AlgebraicRoot::isolate_against(linear.clone(), interval.clone(), &chain)
                .expect("the lawful pairing"),
            isolated
        );
        // A Cauchy-index sequence is not a Sturm chain and may not certify anything.
        let pair = SturmChain::from_pair(&no_real_root, &linear).expect("a proper pair");
        assert_eq!(pair.paired_with(), Some(&linear));
        assert!(!pair.is_sturm_chain());
        assert!(matches!(
            AlgebraicRoot::isolate_with(&pair, interval),
            Err(ExactValueError::ChainIsNotASturmChain)
        ));
    }

    /// **A root is isolated by a Sturm certificate, not by an iteration count.**
    ///
    /// The reciprocal root is what a normalization actually asks for, and taking it directly keeps
    /// one certificate instead of two.
    #[test]
    fn the_roots_a_transport_asks_for_are_isolated_by_certificate() {
        let two = Rat::from_integer(BigInt::from(2));
        let root = AlgebraicRoot::square_root(&two, 40).expect("isolated");
        assert_eq!(root.polynomial.degree(), 2);
        let enclosure = root.enclosure();
        // sqrt(2) = 1.41421356237...; the bracket is stated, not computed.
        let below = Rat::new(BigInt::from(141421356), BigInt::from(100000000));
        let above = Rat::new(BigInt::from(141421357), BigInt::from(100000000));
        assert!(enclosure.lower >= below && enclosure.upper <= above);
        assert_eq!(
            root.polynomial
                .distinct_root_count(enclosure)
                .expect("counted"),
            1,
            "the certificate's whole content is that exactly one root is inside"
        );

        let inverse = AlgebraicRoot::reciprocal_square_root(&two, 40).expect("isolated");
        // 1/sqrt(2) = 0.70710678118...
        let below = Rat::new(BigInt::from(70710678), BigInt::from(100000000));
        let above = Rat::new(BigInt::from(70710679), BigInt::from(100000000));
        assert!(inverse.enclosure().lower >= below && inverse.enclosure().upper <= above);

        // A perfect square returns an interval containing its exact root and refuses no less.
        let four = Rat::from_integer(BigInt::from(4));
        let exact = AlgebraicRoot::square_root(&four, 20).expect("isolated");
        assert!(
            exact.enclosure().lower <= Rat::from_integer(BigInt::from(2))
                && exact.enclosure().upper >= Rat::from_integer(BigInt::from(2))
        );
        assert!(AlgebraicRoot::square_root(&-two, 20).is_err());
    }

    /// **The chronology is an integer, and the rotation stays on the circle.**
    ///
    /// The transcendental runs once per band; a position is an integer power of the enclosed group
    /// element. Composing two positions equals rotating once by their sum, and the modulus is
    /// preserved — which is what a group element has and a pair of independently bounded numbers
    /// does not.
    #[test]
    fn the_chronology_rides_as_an_integer_power_of_one_group_element() {
        let step = Rat::new(BigInt::from(1), BigInt::from(8));
        for position in [1u64, 3, 7, 16] {
            let (cosine, sine) =
                CertifiedSeries::rotation_power(&step, position, 30).expect("rotated");
            let modulus = cosine
                .times(&cosine)
                .expect("square")
                .times(&ExactInterval::point(Rat::one()))
                .expect("scaled");
            let cross = sine.times(&sine).expect("square");
            let total =
                ExactInterval::new(&modulus.lower + &cross.lower, &modulus.upper + &cross.upper)
                    .expect("summed");
            assert!(
                total.lower <= Rat::one() && total.upper >= Rat::one(),
                "position {position} left the circle: {total:?}"
            );
        }
        // A band angle is an n-th root, isolated by the same certificate a square root is.
        let base = Rat::from_integer(BigInt::from(10_000));
        let band = AlgebraicRoot::nth_root(&base, 128, 40).expect("isolated");
        assert_eq!(band.polynomial.degree(), 128);
        // 10000^(1/128) = 1.0746078...; the bracket is stated rather than computed, and the
        // isolating interval must sit strictly inside it.
        let below = Rat::new(BigInt::from(10746078), BigInt::from(10000000));
        let above = Rat::new(BigInt::from(10746079), BigInt::from(10000000));
        assert!(
            band.enclosure().lower >= below && band.enclosure().upper <= above,
            "{:?}",
            band.enclosure()
        );
        assert_eq!(
            band.polynomial
                .distinct_root_count(band.enclosure())
                .expect("counted"),
            1
        );
    }

    /// **The certified series carries the two transcendentals a transport needs**, and refuses
    /// rather than taking too few terms for its argument.
    #[test]
    fn the_certified_series_carries_the_exponential_and_the_tangent() {
        let three_eighths = Rat::new(BigInt::from(3), BigInt::from(8));
        let series = CertifiedSeries::exponential_series(&three_eighths, 24).expect("certified");
        let enclosure = series.enclosure();
        // exp(3/8) = 1.4549914146...
        let below = Rat::new(BigInt::from(14549914), BigInt::from(10000000));
        let above = Rat::new(BigInt::from(14549915), BigInt::from(10000000));
        assert!(enclosure.lower >= below && enclosure.upper <= above);
        assert!(matches!(
            series.tail_certificate,
            SeriesTailCertificate::AbsoluteGeometric { .. }
        ));
        // Too few terms for the argument is refused, not silently taken.
        assert_eq!(
            CertifiedSeries::exponential_series(&Rat::from_integer(BigInt::from(40)), 4),
            Err(ExactValueError::TailDoesNotClose)
        );
        // And the reduction keeps every caller inside the series' own domain: exp(-15) returns a
        // usable enclosure where a direct forty-term series' honest bound is wider than the value.
        let far = CertifiedSeries::exponential_enclosure(&Rat::from_integer(BigInt::from(-15)), 32)
            .expect("reduced");
        assert!(far.lower.is_positive(), "an exponential is never negative");
        assert!(far.upper < Rat::new(BigInt::from(1), BigInt::from(1_000_000)));

        // tanh through the DECAYING exponential: monotone, bounded, and nothing large forms.
        let mut previous: Option<ExactInterval> = None;
        for numerator in [-30i64, -8, -1, 0, 1, 8, 30] {
            let x = Rat::new(BigInt::from(numerator), BigInt::from(4));
            let value = CertifiedSeries::hyperbolic_tangent_enclosure(&x, 40).expect("enclosed");
            assert!(value.lower >= Rat::from_integer(BigInt::from(-1)));
            assert!(value.upper <= Rat::one());
            if let Some(before) = previous {
                assert_eq!(
                    before.disjoint_order(&value),
                    ExactOrdering::Less,
                    "tanh must separate at {numerator}/4"
                );
            }
            previous = Some(value);
        }
        // tanh(1/2) = 0.46211715726...
        let half = Rat::new(BigInt::from(1), BigInt::from(2));
        let value = CertifiedSeries::hyperbolic_tangent_enclosure(&half, 40).expect("enclosed");
        let below = Rat::new(BigInt::from(46211715), BigInt::from(100000000));
        let above = Rat::new(BigInt::from(46211716), BigInt::from(100000000));
        assert!(value.lower >= below && value.upper <= above, "{value:?}");
    }

    #[test]
    fn circular_series_retains_species_and_orients_alternating_tails() {
        let half = Rat::new(BigInt::from(1), BigInt::from(2));
        let (cosine_one, sine_one) = CertifiedSeries::circular_series(&half, 1).unwrap();
        assert_eq!(
            cosine_one.enclosure(),
            ExactInterval::new(rat(7, 8), rat(1, 1)).unwrap()
        );
        assert_eq!(
            sine_one.enclosure(),
            ExactInterval::new(rat(23, 48), rat(1, 2)).unwrap()
        );
        assert!(matches!(
            cosine_one.expression,
            ExactExpr::Function { ref name, .. } if name == "cos"
        ));
        assert!(matches!(
            sine_one.expression,
            ExactExpr::Function { ref name, .. } if name == "sin"
        ));

        let exponential = CertifiedSeries::exponential_series(&half, 8).unwrap();
        assert_eq!(
            exponential.expression,
            ExactExpr::function("exp", vec![ExactExpr::rational(half.clone())])
        );
        let (cosine_two, sine_two) = CertifiedSeries::circular_series(&half, 2).unwrap();
        assert!(cosine_two.enclosure().lower >= cosine_one.enclosure().lower);
        assert!(cosine_two.enclosure().upper <= cosine_one.enclosure().upper);
        assert!(sine_two.enclosure().lower >= sine_one.enclosure().lower);
        assert!(sine_two.enclosure().upper <= sine_one.enclosure().upper);

        let negative = Rat::new(BigInt::from(-1), BigInt::from(2));
        let (cosine_negative, sine_negative) =
            CertifiedSeries::circular_series(&negative, 1).unwrap();
        assert_eq!(cosine_negative.enclosure(), cosine_one.enclosure());
        assert_eq!(
            sine_negative.enclosure(),
            ExactInterval::new(rat(-1, 2), rat(-23, 48)).unwrap()
        );
    }

    use crate::geometry::{integer, rat};

    use super::*;

    #[test]
    fn sturm_certificate_isolates_sqrt_two_without_a_float() {
        let polynomial =
            IntegerPolynomial::new(vec![BigInt::from(-2), BigInt::zero(), BigInt::one()]).unwrap();
        let root = AlgebraicRoot::isolate(
            polynomial,
            ExactInterval::new(integer(1), integer(2)).unwrap(),
        )
        .unwrap();
        assert_eq!(
            root.certificate.variations_at_lower - root.certificate.variations_at_upper,
            1
        );
        assert_eq!(
            ExactValue::Algebraic(root).compare(&ExactValue::rational(rat(3, 2))),
            ExactOrdering::Open
        );
    }

    #[test]
    fn disjoint_certificates_order_values_and_overlap_stays_open() {
        let left = CertifiedSeries::new(
            ExactExpr::symbol("left"),
            integer(1),
            BigUint::from(8_u8),
            SeriesTailCertificate::AbsoluteGeometric {
                first_omitted_abs_bound: rat(9, 100),
                ratio_abs_bound: rat(1, 10),
            },
        )
        .unwrap();
        let right = CertifiedSeries::new(
            ExactExpr::symbol("right"),
            integer(2),
            BigUint::from(8_u8),
            SeriesTailCertificate::AbsoluteGeometric {
                first_omitted_abs_bound: rat(9, 100),
                ratio_abs_bound: rat(1, 10),
            },
        )
        .unwrap();
        assert_eq!(
            ExactValue::CertifiedSeries(left).compare(&ExactValue::CertifiedSeries(right)),
            ExactOrdering::Less
        );
    }

    /// Every pattern this codec accepts must come back out of it identical.
    ///
    /// Stated at the level of **bits** rather than of `f64`, deliberately: no float **value** is
    /// constructed or operated on outside the four functions of `ieee754`, in any library file of
    /// this workspace, and that includes this test module. (The earlier wording said the *tokens*
    /// `f32`/`f64` occur nowhere else, which is false — they occur in a doc line of `reopening.rs`,
    /// in a `#[test]` comment of `embedding_fiber.rs` recording a removal, and as the string
    /// literals `".f16"`/`".f32"`/`".f64"` inside `crates/holonics-cuda`'s *negative* assertion that the
    /// generated PTX contains none. None of those is a float value; the claim about values holds
    /// and the claim about tokens did not. Measured 2026-08-16,
    /// `grep -rn --include='*.rs' -w 'f64\|f32' crates soma`.) The live-float round trip is
    /// exercised by
    /// `examples/a_float_is_a_dyadic_and_a_deleted_tail.rs`, which is a boundary driver and may
    /// hold one.
    #[test]
    fn every_accepted_bit_pattern_re_encodes_identically() {
        use ieee754::{BinaryFloatSpecies, decode_bits};
        let declared: &[(BinaryFloatSpecies, u64)] = &[
            // IEEE binary16, including both zeros, the least subnormal and the maximum finite.
            (BinaryFloatSpecies::Binary16, 0x3c00),
            (BinaryFloatSpecies::Binary16, 0x0001),
            (BinaryFloatSpecies::Binary16, 0x8000),
            (BinaryFloatSpecies::Binary16, 0x7bff),
            // binary64: one, pi, both zeros, the extreme subnormals, a long mantissa, max finite.
            (BinaryFloatSpecies::Binary64, 0x3ff0_0000_0000_0000),
            (BinaryFloatSpecies::Binary64, 0x4009_21fb_5444_2d18),
            (BinaryFloatSpecies::Binary64, 0x0000_0000_0000_0000),
            (BinaryFloatSpecies::Binary64, 0x8000_0000_0000_0000),
            (BinaryFloatSpecies::Binary64, 0x0000_0000_0000_0001),
            (BinaryFloatSpecies::Binary64, 0x000f_ffff_ffff_ffff),
            (BinaryFloatSpecies::Binary64, 0xbfe5_5555_5555_5555),
            (BinaryFloatSpecies::Binary64, 0x7fef_ffff_ffff_ffff),
            // binary32, including a real GPT-2 attention weight.
            (BinaryFloatSpecies::Binary32, 0x3f80_0000),
            (BinaryFloatSpecies::Binary32, 0x0000_0001),
            (BinaryFloatSpecies::Binary32, 0x8000_0000),
            (BinaryFloatSpecies::Binary32, 0x7f7f_ffff),
            (BinaryFloatSpecies::Binary32, 0xbef2_9c42),
            // bfloat16, including a real Qwen down-projection weight.
            (BinaryFloatSpecies::Bfloat16, 0x3f80),
            (BinaryFloatSpecies::Bfloat16, 0x0001),
            (BinaryFloatSpecies::Bfloat16, 0x8000),
            (BinaryFloatSpecies::Bfloat16, 0xbd1e),
        ];
        for (species, bits) in declared {
            let datum = decode_bits(*species, *bits)
                .unwrap_or_else(|error| panic!("{} 0x{bits:x} decodes: {error}", species.name()));
            assert_eq!(
                datum.to_bits().expect("a decoded datum re-encodes"),
                *bits,
                "{} 0x{bits:x} must return identical",
                species.name()
            );
        }
    }

    /// `NaN` and `±∞` name no ratio, so they are refused by name rather than mapped to a sentinel.
    #[test]
    fn not_a_number_and_the_infinities_are_refused_by_name() {
        use ieee754::{BinaryFloatSpecies, decode_bits};
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary64, 0x7ff0_0000_0000_0000),
            Err(ExactValueError::InfiniteFloat {
                negative: false,
                ..
            })
        ));
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary64, 0xfff0_0000_0000_0000),
            Err(ExactValueError::InfiniteFloat { negative: true, .. })
        ));
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary64, 0x7ff8_0000_0000_0000),
            Err(ExactValueError::NotANumberFloat { .. })
        ));
        // A signalling pattern is refused for the same reason as a quiet one.
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary64, 0x7ff0_0000_0000_0001),
            Err(ExactValueError::NotANumberFloat { .. })
        ));
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary16, 0x7c00),
            Err(ExactValueError::InfiniteFloat { .. })
        ));
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary16, 0x7e00),
            Err(ExactValueError::NotANumberFloat { .. })
        ));
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Bfloat16, 0x7f80),
            Err(ExactValueError::InfiniteFloat { .. })
        ));
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary32, 0x7fc0_0000),
            Err(ExactValueError::NotANumberFloat { .. })
        ));
        // And a pattern too wide for its declared format is not silently masked.
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Bfloat16, 0x1_0000),
            Err(ExactValueError::OverWideBitPattern { width: 16, .. })
        ));
    }

    /// The ulp belongs to the **format at this magnitude**, not to the value, and the codec must
    /// not reduce the significand or it destroys exactly that.
    #[test]
    fn the_unit_in_the_last_place_survives_a_value_that_reduces() {
        use ieee754::{BinaryFloatSpecies, decode_bits};
        // 1.0 and 0.5 reduce to 1*2^0 and 1*2^-1; their ulps differ by a factor of two.
        let one = decode_bits(BinaryFloatSpecies::Binary64, 0x3ff0_0000_0000_0000).unwrap();
        let half = decode_bits(BinaryFloatSpecies::Binary64, 0x3fe0_0000_0000_0000).unwrap();
        assert_eq!(one.value(), integer(1));
        assert_eq!(half.value(), rat(1, 2));
        assert_eq!(one.reduced_dyadic(), (BigInt::one(), 0));
        assert_eq!(half.reduced_dyadic(), (BigInt::one(), -1));
        assert_eq!(one.ulp_bits(), 52);
        assert_eq!(half.ulp_bits(), 53);
        assert_eq!(one.unit_in_last_place(), rat(1, 1_i64 << 52));

        // The smallest subnormal is one ulp of the subnormal grid, and it is exact.
        let tiny = decode_bits(BinaryFloatSpecies::Binary64, 0x0000_0000_0000_0001).unwrap();
        assert!(tiny.subnormal);
        assert_eq!(tiny.ulp_bits(), 1074);
        assert_eq!(tiny.value(), tiny.unit_in_last_place());

        // Both zeros carry the subnormal ulp, and the sign of zero survives the decode.
        let plus = decode_bits(BinaryFloatSpecies::Binary64, 0).unwrap();
        let minus = decode_bits(BinaryFloatSpecies::Binary64, 0x8000_0000_0000_0000).unwrap();
        assert!(plus.is_zero() && minus.is_zero());
        assert_eq!(plus.value(), minus.value());
        assert!(!plus.negative && minus.negative);
        assert_ne!(plus.to_bits().unwrap(), minus.to_bits().unwrap());
    }

    /// The bfloat16 decode must agree with the reader it was taken from,
    /// `crates/holonic-life/examples/eros_self_emanated_law.rs:60`, on real material.
    #[test]
    fn the_bfloat16_decode_agrees_with_the_reader_it_was_taken_from() {
        use ieee754::{BinaryFloatSpecies, decode_bfloat16_bits, decode_bits};
        // `model.language_model.layers.1.mlp.down_proj.weight[0]` of Qwen3.5-4B.
        let weight = decode_bfloat16_bits(0xbd1e).unwrap();
        assert_eq!(weight.reduced_dyadic(), (BigInt::from(-79), -11));
        assert_eq!(weight.signed_significand(), BigInt::from(-158));
        assert_eq!(weight.ulp_exponent, -12);
        assert_eq!(weight.value(), rat(-158, 4096));
        // The archetype's subnormal exponent is -133 and its normal exponent is `raw - 134`.
        assert_eq!(BinaryFloatSpecies::Bfloat16.subnormal_ulp_exponent(), -133);
        let subnormal = decode_bits(BinaryFloatSpecies::Bfloat16, 0x0001).unwrap();
        assert_eq!(subnormal.ulp_exponent, -133);
    }

    /// The admitted PAE matrices arrive as NumPy `<f2`: IEEE binary16, not bfloat16. The two
    /// sixteen-bit species must therefore remain distinct even when their storage width agrees.
    #[test]
    fn the_binary16_mouth_is_exact_and_is_not_the_bfloat16_mouth() {
        use ieee754::{BinaryFloatSpecies, decode_binary16_bits};

        let one = decode_binary16_bits(0x3c00).expect("binary16 one");
        assert_eq!(one.species, BinaryFloatSpecies::Binary16);
        assert_eq!(one.value(), integer(1));
        assert_eq!(one.ulp_exponent, -10);
        assert_eq!(one.to_bits().expect("re-encodes"), 0x3c00);

        let least = decode_binary16_bits(0x0001).expect("least binary16 subnormal");
        assert!(least.subnormal);
        assert_eq!(least.ulp_exponent, -24);
        assert_eq!(least.value(), rat(1, 1_i64 << 24));
        assert_eq!(BinaryFloatSpecies::Binary16.subnormal_ulp_exponent(), -24);

        let largest = decode_binary16_bits(0x7bff).expect("largest finite binary16");
        assert_eq!(largest.value(), integer(65_504));

        // The same bits in bfloat16 name 1/128, not one. Width is an apparatus coincidence, not
        // species equality.
        let bfloat = ieee754::decode_bfloat16_bits(0x3c00).expect("finite bfloat16");
        assert_eq!(bfloat.value(), rat(1, 128));
        assert_ne!(one.value(), bfloat.value());
    }

    /// The three readings of one pattern are three different faces, and the difference is the
    /// entire content of the distinction.
    #[test]
    fn one_pattern_presents_three_faces_under_three_readings() {
        use ieee754::{BinaryFloatSpecies, FloatReading, decode_bits};
        let datum = decode_bits(BinaryFloatSpecies::Binary64, 0x3ff0_0000_0000_0000).unwrap();
        let ulp = datum.unit_in_last_place();

        let point = datum.enclosure(FloatReading::ExactBitPattern);
        assert!(point.is_point());
        assert_eq!(point.lower, integer(1));

        let rounded = datum.enclosure(FloatReading::RoundedToNearest);
        assert_eq!(&rounded.upper - &rounded.lower, ulp);
        assert!(rounded.lower < integer(1) && rounded.upper > integer(1));

        let truncated = datum.enclosure(FloatReading::TruncatedTowardZero);
        assert_eq!(&truncated.upper - &truncated.lower, ulp);
        assert_eq!(truncated.lower, integer(1));

        // A zero truncated toward zero straddles zero by one ulp on each side: every quantity
        // smaller than one ulp truncates onto it.
        let zero = decode_bits(BinaryFloatSpecies::Binary64, 0).unwrap();
        let straddle = zero.enclosure(FloatReading::TruncatedTowardZero);
        assert_eq!(straddle.lower, -zero.unit_in_last_place());
        assert_eq!(straddle.upper, zero.unit_in_last_place());
        assert!(zero.enclosure(FloatReading::ExactBitPattern).is_point());
    }

    #[test]
    fn overlapping_intervals_for_distinct_roots_do_not_collapse_identity() {
        let polynomial =
            IntegerPolynomial::new(vec![-BigInt::one(), BigInt::zero(), BigInt::one()]).unwrap();
        let negative = AlgebraicRoot::isolate(
            polynomial.clone(),
            ExactInterval::new(integer(-2), rat(1, 2)).unwrap(),
        )
        .unwrap();
        let positive = AlgebraicRoot::isolate(
            polynomial,
            ExactInterval::new(rat(-1, 2), integer(2)).unwrap(),
        )
        .unwrap();
        assert_eq!(
            ExactValue::Algebraic(negative).compare(&ExactValue::Algebraic(positive)),
            ExactOrdering::Less
        );
    }
}

/// **The chain held against the reference it replaced.**
///
/// Every test here compares [`SturmChain`] — the sign-tracked pseudo-remainder sequence over `Z` —
/// against [`sturm_sequence`], the naive Euclidean remainder sequence over `Q` that was the owner
/// before. The reference is retained under `cfg(test)` for exactly this purpose. The corpus is
/// deliberately shaped at the three places a sign rule breaks: **repeated roots** (the chain's last
/// member is then a nonconstant gcd), **degree gaps** (a remainder that drops more than one degree,
/// which is where the `lc^(δ+1)` exponent stops being `2`), and **negative leading coefficients**
/// (where that power's sign is the whole question).
#[cfg(test)]
mod sturm_chain_tests {
    use super::*;

    fn polynomial(coefficients: &[i64]) -> IntegerPolynomial {
        IntegerPolynomial::new(coefficients.iter().copied().map(BigInt::from).collect())
            .expect("a nonzero polynomial")
    }

    fn multiply(left: &[i64], right: &[i64]) -> Vec<i64> {
        let mut product = vec![0_i64; left.len() + right.len() - 1];
        for (i, a) in left.iter().enumerate() {
            for (j, b) in right.iter().enumerate() {
                product[i + j] += a * b;
            }
        }
        product
    }

    fn negated(coefficients: &[i64]) -> Vec<i64> {
        coefficients.iter().map(|value| -value).collect()
    }

    /// The corpus: products of declared factors, the three shapes named above, and every one of
    /// them again with its sign flipped.
    fn corpus() -> Vec<Vec<i64>> {
        let linear: [&[i64]; 5] = [&[-1, 1], &[1, 1], &[-2, 1], &[3, 1], &[-1, 2]];
        let quadratic: [&[i64]; 3] = [&[1, 0, 1], &[2, 1, 1], &[-2, 0, 1]];
        let mut population: Vec<Vec<i64>> = Vec::new();

        // Degree gaps: `rem(x^n + c, n x^(n-1))` is a constant, a gap of `n - 1`.
        for power in 3..=7_usize {
            for constant in [-1_i64, 1, 5] {
                let mut coefficients = vec![0_i64; power + 1];
                coefficients[0] = constant;
                coefficients[power] = 1;
                population.push(coefficients);
            }
        }
        // Repeated roots of every order up to four, and a repeated irreducible quadratic.
        for factor in &linear {
            let mut power = factor.to_vec();
            for _ in 0..3 {
                power = multiply(&power, factor);
                population.push(power.clone());
            }
        }
        population.push(multiply(&[1, 0, 1], &[1, 0, 1]));
        population.push(multiply(&multiply(&[-1, 1], &[-1, 1]), &[2, 1]));
        population.push(multiply(
            &multiply(&[-1, 1], &[1, 1]),
            &multiply(&[-1, 1], &[1, 1]),
        ));
        // Plain products with simple roots.
        for left in &linear {
            for right in &linear {
                population.push(multiply(left, right));
            }
            for right in &quadratic {
                population.push(multiply(left, right));
                population.push(multiply(&multiply(left, right), right));
            }
        }
        // A deterministic spread of dense polynomials, degrees one to eight.
        let mut state: u64 = 0x5eed_1234_9abc_def1;
        for degree in 1..=8_usize {
            for _ in 0..16 {
                let mut coefficients = Vec::with_capacity(degree + 1);
                for _ in 0..=degree {
                    state = state
                        .wrapping_mul(6_364_136_223_846_793_005)
                        .wrapping_add(1_442_695_040_888_963_407);
                    coefficients.push(((state >> 33) % 19) as i64 - 9);
                }
                if coefficients[degree] == 0 {
                    coefficients[degree] = 1;
                }
                population.push(coefficients);
            }
        }
        let flipped: Vec<Vec<i64>> = population.iter().map(|entry| negated(entry)).collect();
        population.extend(flipped);
        population
    }

    /// **The primitive-PRS chain builder, retained as the reference the subresultant one replaced.**
    ///
    /// This is the earlier implementation verbatim: the same sign rule, with each member divided by
    /// its integer *content* instead of by the subresultant divisor. It is kept under `cfg(test)`
    /// so the replacement can be held against it entry for entry, and so the measurement below has
    /// something to measure against. Nothing outside these tests may call it.
    fn primitive_prs_members(polynomial: &IntegerPolynomial) -> Vec<Vec<BigInt>> {
        let mut first = polynomial.coefficients.clone();
        make_primitive(&mut first);
        let mut second = integer_derivative(&first);
        make_primitive(&mut second);
        let mut members = vec![first];
        if second.is_empty() {
            return members;
        }
        members.push(second);
        loop {
            let length = members.len();
            let current = &members[length - 1];
            let current_degree = current.len() - 1;
            if current_degree == 0 {
                break;
            }
            let previous = &members[length - 2];
            let gap = (previous.len() - 1) - current_degree;
            let leading_negative = current[current_degree].is_negative();
            let mut next = pseudo_remainder(previous, current);
            if !(leading_negative && (gap + 1) % 2 == 1) {
                for value in &mut next {
                    *value = -std::mem::take(value);
                }
            }
            make_primitive(&mut next);
            if next.is_empty() {
                break;
            }
            members.push(next);
        }
        members
    }

    /// The sign variations of a raw member list at one rational point, by the same integer Horner
    /// the chain uses. This is how the reference is read, so the two readings differ only in the
    /// members.
    fn reference_sign_variations(members: &[Vec<BigInt>], point: &Rat) -> u32 {
        let mut variations = 0_u32;
        let mut previous = 0_i8;
        for member in members {
            let sign = homogeneous_sign(member, point.numer(), point.denom());
            if sign == 0 {
                continue;
            }
            if previous != 0 && sign != previous {
                variations += 1;
            }
            previous = sign;
        }
        variations
    }

    /// **The subresultant chain is the same chain, member for member, up to a positive factor.**
    ///
    /// Signs are the entire content of this object, so the replacement is held against the
    /// implementation it replaced at every member, at every probe point, and at both infinities —
    /// not merely at a final root count. Degree gaps, negative leading coefficients and repeated
    /// roots are all in [`corpus`], which is exactly where a PRS variant loses a sign.
    #[test]
    fn the_subresultant_chain_matches_the_primitive_chain_it_replaced() {
        let points = probe_points();
        for coefficients in corpus() {
            let source = polynomial(&coefficients);
            let chain = SturmChain::of(&source).expect("the chain builds");
            let reference = primitive_prs_members(&source);
            assert_eq!(
                chain.members.len(),
                reference.len(),
                "chain length differs for {coefficients:?}"
            );
            for (index, (held, reference_member)) in
                chain.members.iter().zip(reference.iter()).enumerate()
            {
                assert_eq!(
                    held.len(),
                    reference_member.len(),
                    "member {index} has a different degree for {coefficients:?}"
                );
                let top = held.len() - 1;
                let factor = Rat::new(held[top].clone(), reference_member[top].clone());
                assert!(
                    factor > Rat::zero(),
                    "member {index} of {coefficients:?} is a NEGATIVE multiple ({factor}) of the \
                     primitive member: the subresultant sign rule is wrong"
                );
                for (position, (a, b)) in held.iter().zip(reference_member.iter()).enumerate() {
                    assert_eq!(
                        Rat::from_integer(a.clone()),
                        &factor * Rat::from_integer(b.clone()),
                        "member {index} coefficient {position} of {coefficients:?} is not the same \
                         positive multiple"
                    );
                }
            }
            for point in &points {
                assert_eq!(
                    chain.sign_variations(point),
                    reference_sign_variations(&reference, point),
                    "the variation count of {coefficients:?} at {point} differs"
                );
            }
            for positive in [false, true] {
                assert_eq!(
                    chain.sign_variations_at_infinity(positive),
                    {
                        let mut variations = 0_u32;
                        let mut last = 0_i8;
                        for member in &reference {
                            let sign = SturmChain::sign_at_infinity(member, positive);
                            if sign == 0 {
                                continue;
                            }
                            if last != 0 && sign != last {
                                variations += 1;
                            }
                            last = sign;
                        }
                        variations
                    },
                    "the reading of {coefficients:?} at infinity (positive: {positive}) differs"
                );
            }
        }
    }

    /// A deterministic dense integer polynomial of the declared degree, coefficients in `[-10, 10]`
    /// with a nonzero leading one. The measurement's material.
    fn dense_material(degree: usize, seed: u64) -> IntegerPolynomial {
        let mut state = seed;
        let mut coefficients = Vec::with_capacity(degree + 1);
        for _ in 0..=degree {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            coefficients.push(BigInt::from(((state >> 33) % 21) as i64 - 10));
        }
        if coefficients[degree].is_zero() {
            coefficients[degree] = BigInt::one();
        }
        IntegerPolynomial::new(coefficients).expect("a nonzero polynomial")
    }

    /// **The measured basis of [`STURM_DEGREE_CEILING`].**
    ///
    /// Run once, by name, on real material: the two builders on the same dense polynomials, so the
    /// ceiling can be set against what the implementation actually finishes rather than against
    /// what the degree alone suggests. The readings are asserted equal at every degree; the times
    /// are printed, never asserted, because a clock decides nothing here.
    #[test]
    #[ignore = "a measurement, not a law: run it by name when the ceiling is being set"]
    fn the_subresultant_chain_is_measured_against_the_primitive_one() {
        let probe = Rat::new(BigInt::from(7), BigInt::from(3));
        for degree in [50_usize, 100, 200, 400, 800] {
            let source = dense_material(degree, 0x51ee_d000_1234_5678 ^ degree as u64);

            let started = std::time::Instant::now();
            let chain = SturmChain::of(&source).expect("the chain builds");
            let subresultant = started.elapsed();

            let started = std::time::Instant::now();
            let reference = primitive_prs_members(&source);
            let primitive = started.elapsed();

            assert_eq!(chain.members.len(), reference.len(), "degree {degree}");
            assert_eq!(
                chain.sign_variations(&probe),
                reference_sign_variations(&reference, &probe),
                "degree {degree} reads differently"
            );
            let widest = chain
                .members
                .iter()
                .flat_map(|member| member.iter())
                .map(BigInt::bits)
                .max()
                .unwrap_or(0);
            println!(
                "degree {degree:>4}: subresultant {:>10.3?}  primitive {:>10.3?}  widest \
                 subresultant coefficient {widest} bits",
                subresultant, primitive
            );
        }
    }

    fn probe_points() -> Vec<Rat> {
        let mut points = Vec::new();
        for numerator in -12_i64..=12 {
            for denominator in [1_i64, 2, 3, 7] {
                points.push(Rat::new(BigInt::from(numerator), BigInt::from(denominator)));
            }
        }
        points.push(Rat::new(BigInt::from(1_000_003), BigInt::from(999_983)));
        points.push(Rat::new(BigInt::from(-1_000_003), BigInt::from(999_983)));
        points
    }

    /// **The chain member is a positive rational multiple of the naive member, entry for entry.**
    ///
    /// This is the sign rule itself. A single wrong power of `lc(S_i)` makes one member a
    /// *negative* multiple, which is invisible to a count at one lucky point and fatal everywhere
    /// else, so it is checked structurally rather than sampled.
    #[test]
    fn every_chain_member_is_a_positive_multiple_of_the_naive_member() {
        for coefficients in corpus() {
            let source = polynomial(&coefficients);
            let chain = SturmChain::of(&source).expect("the chain builds");
            let naive: Vec<Vec<Rat>> = sturm_sequence(&source)
                .into_iter()
                .filter(|member| !member.is_empty())
                .collect();
            assert_eq!(
                chain.members.len(),
                naive.len(),
                "chain length differs for {coefficients:?}"
            );
            for (index, (held, reference)) in chain.members.iter().zip(naive.iter()).enumerate() {
                assert_eq!(
                    held.len(),
                    reference.len(),
                    "member {index} has a different degree for {coefficients:?}"
                );
                let top = held.len() - 1;
                let factor = Rat::from_integer(held[top].clone()) / reference[top].clone();
                assert!(
                    factor > Rat::zero(),
                    "member {index} of {coefficients:?} is a NEGATIVE multiple ({factor}) of the \
                     naive member: the sign rule is wrong"
                );
                for (position, (a, b)) in held.iter().zip(reference.iter()).enumerate() {
                    assert_eq!(
                        Rat::from_integer(a.clone()),
                        &factor * b,
                        "member {index} coefficient {position} of {coefficients:?} is not the same \
                         positive multiple"
                    );
                }
            }
        }
    }

    /// **The reading agrees with the reference at every probed rational point.**
    #[test]
    fn the_chain_reads_what_the_naive_sequence_reads() {
        let points = probe_points();
        for coefficients in corpus() {
            let source = polynomial(&coefficients);
            let chain = SturmChain::of(&source).expect("the chain builds");
            let naive = sturm_sequence(&source);
            for point in &points {
                assert_eq!(
                    chain.sign_variations(point),
                    sign_variations(&naive, point),
                    "the reading of {coefficients:?} at {point} differs"
                );
            }
        }
    }

    /// A coarser grid for the quadratic interval sweep below. The full grid is used for the
    /// pointwise reading; pairing it with itself would be a hundred times the work for the same
    /// law.
    fn interval_points() -> Vec<Rat> {
        let mut points = Vec::new();
        for numerator in -6_i64..=6 {
            points.push(Rat::from_integer(BigInt::from(numerator)));
            points.push(Rat::new(BigInt::from(2 * numerator + 1), BigInt::from(2)));
        }
        points
    }

    /// **The distinct-root count agrees with the reference on every probed interval.**
    #[test]
    fn the_chain_counts_what_the_naive_sequence_counts() {
        let points = interval_points();
        for coefficients in corpus() {
            let source = polynomial(&coefficients);
            let chain = SturmChain::of(&source).expect("the chain builds");
            let naive = sturm_sequence(&source);
            // The reference reading is taken once per point, not once per pair.
            let readings: Vec<(Rat, Option<u32>)> = points
                .iter()
                .map(|point| {
                    let reading = if source.evaluate(point).is_zero() {
                        None
                    } else {
                        Some(sign_variations(&naive, point))
                    };
                    (point.clone(), reading)
                })
                .collect();
            for (lower, low_reading) in &readings {
                for (upper, high_reading) in &readings {
                    if lower >= upper {
                        continue;
                    }
                    let (Some(low_reading), Some(high_reading)) = (low_reading, high_reading)
                    else {
                        continue;
                    };
                    let interval = ExactInterval::new(lower.clone(), upper.clone())
                        .expect("ordered endpoints");
                    let reference = low_reading - high_reading;
                    assert_eq!(
                        chain
                            .distinct_root_count(&interval)
                            .expect("the count returns"),
                        reference,
                        "the count of {coefficients:?} on [{lower}, {upper}] differs"
                    );
                }
            }
        }
    }

    /// **The count is the actual number of distinct roots**, held against a population written
    /// down by hand rather than against another implementation.
    #[test]
    fn the_chain_counts_a_declared_root_population() {
        // `(x−1)^3 (x+2) (x^2+1)`: two distinct real roots, one of them triple.
        let coefficients = multiply(
            &multiply(&multiply(&multiply(&[-1, 1], &[-1, 1]), &[-1, 1]), &[2, 1]),
            &[1, 0, 1],
        );
        let source = polynomial(&coefficients);
        let chain = SturmChain::of(&source).expect("the chain builds");
        let wide = ExactInterval::new(
            Rat::from_integer(BigInt::from(-10)),
            Rat::from_integer(BigInt::from(10)),
        )
        .expect("ordered");
        assert_eq!(chain.distinct_root_count(&wide).expect("counts"), 2);
        let around_one = ExactInterval::new(
            Rat::new(BigInt::from(1), BigInt::from(2)),
            Rat::new(BigInt::from(3), BigInt::from(2)),
        )
        .expect("ordered");
        assert_eq!(chain.distinct_root_count(&around_one).expect("counts"), 1);
    }

    /// **The two declared sizes are refused, not attempted.**
    #[test]
    fn the_declared_sizes_are_refused_above_the_ceilings() {
        let wide = vec![
            BigInt::from(2).pow(u32::try_from(STURM_COEFFICIENT_BIT_CEILING + 1).unwrap()),
            BigInt::one(),
        ];
        let source = IntegerPolynomial::new(wide).expect("nonzero");
        assert!(matches!(
            SturmChain::of(&source),
            Err(ExactValueError::SturmCoefficientTooWide { .. })
        ));

        let mut tall = vec![BigInt::zero(); STURM_DEGREE_CEILING + 2];
        tall[0] = -BigInt::one();
        tall[STURM_DEGREE_CEILING + 1] = BigInt::one();
        let source = IntegerPolynomial::new(tall).expect("nonzero");
        assert!(matches!(
            SturmChain::of(&source),
            Err(ExactValueError::SturmDegreeTooLarge { .. })
        ));
    }

    /// **A constant polynomial has a one-member chain and reads zero everywhere.**
    #[test]
    fn a_constant_polynomial_has_a_single_member_chain() {
        let chain = SturmChain::of(&polynomial(&[7])).expect("the chain builds");
        assert_eq!(chain.len(), 1);
        assert!(!chain.is_empty());
        for point in probe_points() {
            assert_eq!(chain.sign_variations(&point), 0);
        }
    }

    /// **An endpoint that is a root is refused by name**, at the chain as at the polynomial.
    #[test]
    fn a_root_on_the_boundary_is_refused_by_the_chain() {
        let source = polynomial(&[-1, 0, 1]);
        let chain = SturmChain::of(&source).expect("the chain builds");
        let boundary = ExactInterval::new(
            Rat::from_integer(BigInt::one()),
            Rat::from_integer(BigInt::from(3)),
        )
        .expect("ordered");
        assert!(matches!(
            chain.distinct_root_count(&boundary),
            Err(ExactValueError::RootAtIntervalBoundary)
        ));
        assert!(matches!(
            source.distinct_root_count(&boundary),
            Err(ExactValueError::RootAtIntervalBoundary)
        ));
    }

    /// **The homogeneous integer sign agrees with the rational evaluation**, which is the one
    /// thing standing between a count and a rational-arithmetic count.
    #[test]
    fn the_integer_horner_sign_agrees_with_the_rational_evaluation() {
        for coefficients in corpus() {
            let source = polynomial(&coefficients);
            for point in probe_points() {
                let exact = source.evaluate(&point);
                let expected = if exact.is_zero() {
                    0_i8
                } else if exact < Rat::zero() {
                    -1
                } else {
                    1
                };
                assert_eq!(
                    homogeneous_sign(&source.coefficients, point.numer(), point.denom()),
                    expected,
                    "the integer sign of {coefficients:?} at {point} disagrees"
                );
            }
        }
    }
    #[test]
    fn degree_two_roots_below_the_grid_keep_a_valid_zero_endpoint() {
        let tiny = Rat::new(BigInt::one(), BigInt::one() << 160usize);
        let root = AlgebraicRoot::square_root(&tiny, 16).unwrap();
        let exact = Rat::new(BigInt::one(), BigInt::one() << 80usize);
        assert_eq!(root.isolating_interval.lower, Rat::zero());
        assert!(root.isolating_interval.upper > exact);
        let inverse = AlgebraicRoot::reciprocal_square_root(&tiny.recip(), 16).unwrap();
        assert_eq!(root.isolating_interval, inverse.isolating_interval);
    }
}
