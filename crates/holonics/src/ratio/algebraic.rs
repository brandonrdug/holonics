//! **Algebraic values as constraint identities: exact enclosures, Sturm chains and isolated roots.**
//!
//! An algebraic or transcendental quantity is its constraint identity; a number is a face of it,
//! and error enters only in how a face is attained. This module carries the exact faces the laws
//! read: an interval enclosure ([`ExactInterval`], never a point standing in for a set), the
//! four-state [`ExactOrdering`] whose `Open` keeps both operands rather than tie-breaking, the
//! Sturm chain of an integer polynomial ([`SturmChain`], Lean `Foundation/RootCount`), and a real
//! algebraic root named by its minimal polynomial and an isolating interval ([`AlgebraicRoot`]).
//! Nothing here is a float.

use crate::ratio::{ExactOrdering, Rat};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use thiserror::Error;

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

/// **The natural logarithm of a positive rational, enclosed.**
///
/// [proved-standard] With `x = 2^e·r`, `r ∈ [1, 2)`, `ln x = e·ln 2 + ln r`, and
/// `ln r = 2 atanh z = 2 Σ_k z^{2k+1}/(2k+1)` with `z = (r − 1)/(r + 1) ∈ [0, 1/3]`. Every term is
/// nonnegative, so the partial sum is a lower bound, and the tail after `n` terms is at most
/// `2 z^{2n+1} / ((2n+1)(1 − z²))`. Each partial sum is held outward on the dyadic grid of
/// `octaves`, so the enclosure only widens. The logarithm is a constraint identity; this returns a
/// set containing it, never a point.
pub(crate) fn natural_log_enclosure(
    value: &Rat,
    terms: u32,
    octaves: u32,
) -> Result<ExactInterval, ExactValueError> {
    if !value.is_positive() {
        return Err(ExactValueError::NonPositiveLogarithm);
    }
    if value.is_one() {
        return Ok(ExactInterval::point(Rat::zero()));
    }
    let two = Rat::from_integer(BigInt::from(2));
    let mut reduced = value.clone();
    let mut exponent = 0i64;
    while reduced >= two {
        reduced /= &two;
        exponent += 1;
    }
    while reduced < Rat::one() {
        reduced *= &two;
        exponent -= 1;
    }
    let unit = |r: &Rat| -> Result<ExactInterval, ExactValueError> {
        let z = (r - Rat::one()) / (r + Rat::one());
        let square = &z * &z;
        let mut lower = Rat::zero();
        let mut upper = Rat::zero();
        let mut power = ExactInterval::point(z);
        for index in 0..terms {
            let coefficient = &two / Rat::from_integer(BigInt::from(2 * index + 1));
            let held = ExactInterval::new(
                &lower + &power.lower * &coefficient,
                &upper + &power.upper * &coefficient,
            )?
            .round_out(octaves)?;
            (lower, upper) = (held.lower, held.upper);
            power = power
                .times(&ExactInterval::point(square.clone()))?
                .round_out(octaves)?;
        }
        let tail = &two * &power.upper
            / (Rat::from_integer(BigInt::from(2 * terms + 1)) * (Rat::one() - &square));
        ExactInterval::new(lower, upper + tail)?.round_out(octaves)
    };
    let reduced_log = unit(&reduced)?;
    let log_two = unit(&two)?;
    let scale = Rat::from_integer(BigInt::from(exponent));
    let (scaled_lower, scaled_upper) = if scale.is_negative() {
        (&log_two.upper * &scale, &log_two.lower * &scale)
    } else {
        (&log_two.lower * &scale, &log_two.upper * &scale)
    };
    ExactInterval::new(
        reduced_log.lower + scaled_lower,
        reduced_log.upper + scaled_upper,
    )?
    .round_out(octaves)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactInterval {
    pub lower: Rat,
    pub upper: Rat,
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

    /// **Widen outward onto a dyadic grid, so a chain of enclosures cannot grow its denominator
    /// without bound.**
    ///
    /// The result strictly contains the original — the lower bound floors and the upper ceils — so
    /// nothing is lost, and the denominators stay at `2^octaves` however long the chain runs.
    pub(crate) fn round_out(&self, octaves: u32) -> Result<Self, ExactValueError> {
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
    pub(crate) fn times(&self, other: &Self) -> Result<Self, ExactValueError> {
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
/// list whose last entry is nonzero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IntegerPolynomial {
    pub coefficients: Vec<BigInt>,
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
    /// polynomial the constructor admits. The field is public, so a direct mutation
    /// can still empty it; the convention for that unreachable-by-construction case is **degree
    /// zero**, because an empty list carries no power above the constant one. It is emphatically
    /// not `len() - 1`, which panics in a debug build and wraps to `usize::MAX` in a release
    /// build — this workspace's release profile carries no overflow checks — and then flows into
    /// [`IntegerPolynomial::check_declared_size`] and every consumer as a declared extent.
    pub(crate) fn degree(&self) -> usize {
        self.coefficients.len().saturating_sub(1)
    }

    pub(crate) fn evaluate(&self, point: &Rat) -> Rat {
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

    /// The Sturm–Habicht chain of this polynomial, built once.
    pub(crate) fn sturm_chain(&self) -> Result<SturmChain, ExactValueError> {
        SturmChain::of(self)
    }

    /// **Refuse a declared degree or coefficient width above the root-counting owner's ceilings.**
    ///
    /// [definition] Degree and coefficient bit length are both caller-declared extents: the first
    /// sizes every loop, recursion and allocation in the chain and in the root bounds, the second
    /// sizes every integer operation in them. Every public entry point that will do work
    /// proportional to either passes through here first, so the refusal happens before the work
    /// and not inside it.
    pub(crate) fn check_declared_size(&self) -> Result<(), ExactValueError> {
        // The public field admits a direct mutation the constructor does not; an empty
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
/// Degree and width do not bound the work separately, which is what [`STURM_WORK_CEILING`] is for;
/// this ceiling is the **cheap** first refusal, taken before any coefficient is scanned.
pub(crate) const STURM_DEGREE_CEILING: usize = 1024;

/// **The declared ceiling on a coefficient's bit length at the Sturm owner.**
///
/// [definition] The second caller-declared size. Four megabits is about 1.2 million decimal digits
/// per coefficient, orders of magnitude above the Hadamard-sized coefficients an exact
/// characteristic polynomial produces. Refused by name as
/// [`ExactValueError::SturmCoefficientTooWide`]. Like [`STURM_DEGREE_CEILING`] it is a cheap
/// individual refusal; [`STURM_WORK_CEILING`] is what bounds the two together.
pub(crate) const STURM_COEFFICIENT_BIT_CEILING: u64 = 1 << 22;

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
/// which is what this ceiling is taken against. It is an **index**, not a cost model: a declared
/// resource ceiling, and a declaration past it is refused by name with
/// [`ExactValueError::SturmWorkTooLarge`] before any chain is built.
pub(crate) const STURM_WORK_CEILING: u128 = 1 << 33;

/// **Refuse a declared degree and coefficient width whose combined work index is past
/// [`STURM_WORK_CEILING`].**
///
/// [definition] Taken on *declared numbers*, not on a polynomial, so a caller that can predict the
/// width of a polynomial it is about to build — `rational_polynomial::rational_root_census`'s monic
/// companion is the case this exists for — refuses **before** forming it rather than after.
pub(crate) fn check_declared_sturm_work(
    degree: usize,
    widest_bits: u64,
) -> Result<(), ExactValueError> {
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
/// `Foundation/RootCount` (library `HolonicsResearch`, as is `Millennium/Sturm`):
/// `theReadingIsInvariantUnderPerEntryPositiveRescaling` closes the boundary
/// `Millennium/Sturm` names open, and
/// `theReadingIsInvariantUnderCommonNonzeroRescaling` is why a non-squarefree polynomial's chain
/// still counts *distinct* roots. Sturm's theorem itself is that file's cited classical fact and
/// `Millennium/Sturm`'s `TheReadingEqualsThePopulation`.
///
/// A sign at a rational point `u/v` is taken by **integer** Horner on the homogenized member:
/// `sign(S(u/v)) = sign(Σ s_i u^i v^(d−i))` because `v > 0`. No rational arithmetic occurs in a
/// count.
///
/// The member list is private: a chain exists only by passing [`SturmChain::of`].
///
/// **A chain carries the polynomial it was built from.** A sign-variation count is a statement
/// about *one* polynomial, and a chain handed to an isolation entry beside a different polynomial
/// used to return `Ok` with a certificate for a root that does not exist — pairing `x² + 1` with
/// the chain of `x` counted one root in `(−1, 1)`. The pairing is therefore a fact of the type:
/// [`SturmChain::polynomial`] returns the source, and every entry that takes a chain and a
/// polynomial verifies that they agree before reading anything.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SturmChain {
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
    pub(crate) fn of(polynomial: &IntegerPolynomial) -> Result<Self, ExactValueError> {
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
    pub(crate) fn polynomial(&self) -> &IntegerPolynomial {
        &self.source
    }

    /// Whether this is the Sturm chain of [`SturmChain::polynomial`] — `f, f'` — rather than a
    /// Cauchy-index sequence seeded by a declared pair.
    pub(crate) fn is_sturm_chain(&self) -> bool {
        self.paired_with.is_none()
    }

    /// **The signed remainder sequence seeded by a declared pair**, with the same
    /// positive-multiple discipline.
    ///
    /// [`SturmChain::of`] is exactly `from_pair(f, f')`. The general form is what a **Cauchy
    /// index** `I(q/p)` needs: its sequence starts at `p, q` rather than at `f, f'`, and it reads
    /// the variations at `±∞` rather than at a point. Nothing else about the construction changes,
    /// so the sign discipline is shared rather than written twice.
    pub(crate) fn from_pair(
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

    /// Whether the polynomial itself vanishes at this point.
    pub(crate) fn vanishes_at(&self, point: &Rat) -> bool {
        self.members
            .first()
            .is_some_and(|member| homogeneous_sign(member, point.numer(), point.denom()) == 0)
    }

    /// The number of sign variations of the chain's values at one rational point.
    ///
    /// Zeros are dropped rather than counted, exactly as
    /// `Millennium/Sturm`'s `variationCount` drops them.
    pub(crate) fn sign_variations(&self, point: &Rat) -> u32 {
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
    pub(crate) fn sign_variations_at_infinity(&self, positive: bool) -> u32 {
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
    pub(crate) fn cauchy_index(&self) -> i64 {
        i64::from(self.sign_variations_at_infinity(false))
            - i64::from(self.sign_variations_at_infinity(true))
    }

    /// Count distinct real roots in one strict rational interval. Endpoints may not be roots.
    pub(crate) fn distinct_root_count(
        &self,
        interval: &ExactInterval,
    ) -> Result<u32, ExactValueError> {
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
/// certificate; [`AlgebraicRoot::isolate`] derives it from the polynomial the root carries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SturmIsolationCertificate {
    pub variations_at_lower: u32,
    pub variations_at_upper: u32,
}

/// One real algebraic number, identified by a polynomial and an exact interval
/// containing exactly one of its real roots.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AlgebraicRoot {
    pub polynomial: IntegerPolynomial,
    pub isolating_interval: ExactInterval,
    pub certificate: SturmIsolationCertificate,
}

impl AlgebraicRoot {
    pub(crate) fn isolate(
        polynomial: IntegerPolynomial,
        isolating_interval: ExactInterval,
    ) -> Result<Self, ExactValueError> {
        let sturm = SturmChain::of(&polynomial)?;
        Self::isolate_with(&sturm, isolating_interval)
    }

    /// **Isolate against a chain, which carries its own polynomial.**
    ///
    /// The chain is the only argument that names a polynomial, so there is no pairing to get
    /// wrong. [`AlgebraicRoot::isolate`] and [`AlgebraicRoot::isolate_against`] both reduce to
    /// this.
    pub(crate) fn isolate_with(
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
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ExactValueError {
    #[error("a logarithm was asked of a non-positive value")]
    NonPositiveLogarithm,
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
mod tests {
    use super::*;
    use crate::ratio::{integer, rat};

    /// A Sturm certificate isolates `√2` in `[1, 2]` with one sign variation lost, and a rational
    /// inside the isolating interval stays `Open` against it rather than being ordered.
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
            ExactInterval::point(rat(3, 2)).disjoint_order(&root.isolating_interval),
            ExactOrdering::Open
        );
        assert_eq!(
            ExactInterval::point(rat(5, 2)).disjoint_order(&root.isolating_interval),
            ExactOrdering::Greater
        );
    }

    /// The logarithm enclosure contains `ln 2` (between `6931/10⁴` and `6932/10⁴`) and is additive:
    /// the enclosure of `ln 6` meets the sum of the enclosures of `ln 2` and `ln 3`.
    #[test]
    fn the_logarithm_enclosure_contains_its_constraint_and_is_additive() {
        let two = natural_log_enclosure(&integer(2), 40, 128).unwrap();
        assert!(two.lower > rat(6931, 10_000) && two.upper < rat(6932, 10_000));
        let three = natural_log_enclosure(&integer(3), 40, 128).unwrap();
        let six = natural_log_enclosure(&integer(6), 40, 128).unwrap();
        assert!(six.lower <= &two.upper + &three.upper && six.upper >= &two.lower + &three.lower);
        assert_eq!(
            natural_log_enclosure(&Rat::zero(), 40, 128),
            Err(ExactValueError::NonPositiveLogarithm)
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
}
