//! Exact turns on the unit circle, carried in a multiquadratic field.
//!
//! ## Why this carrier exists
//!
//! `contact_gluing::Corner` reads a triangle's corner as an exact rational cosine,
//! `cos C = (a² + b² − c²)/(2ab)`, and never takes an angle. Composing two corners into the turn a
//! triangle contributes upward is exact complex multiplication,
//! `(c₁,s₁)·(c₂,s₂) = (c₁c₂ − s₁s₂, c₁s₂ + s₁c₂)` — but the sines are not rational. `sin C = √d`
//! with `d = 1 − cos² ∈ ℚ≥0`, and only a Pythagorean corner has `d` a rational square.
//!
//! So composition leaves `ℚ` immediately. `contact_gluing::CoarseTurn::Open` said so and named the
//! missing carrier: *"Composing distinct turns exactly needs the quadratic extension `ℚ(√(1−c²))`
//! … which is not wired here."* That statement is one field too small. Three corners need
//! `ℚ(√d₁, √d₂, √d₃)` — a **multiquadratic** field of degree up to `2³`, not a single quadratic
//! extension — because each corner contributes its own root.
//!
//! ## What the carrier is
//!
//! For distinct squarefree integers `k₁ < … < kₙ`, each `> 1`, an element of `ℚ(√k₁,…,√kₙ)` is
//!
//! ```text
//!   x = Σ_{S ⊆ {1..n}}  q_S · ∏_{i ∈ S} √kᵢ ,        q_S ∈ ℚ
//! ```
//!
//! carried as `2ⁿ` rational coefficients indexed by `S` as a bitmask. Multiplication is exact and
//! closes because a repeated root collapses to a rational:
//!
//! ```text
//!   (∏_{i∈S} √kᵢ)(∏_{j∈T} √kⱼ)  =  (∏_{i ∈ S∩T} kᵢ) · ∏_{m ∈ S△T} √k_m
//! ```
//!
//! **That is the twisted group algebra of `(ℤ/2)ⁿ` over `ℚ`.** The grading group is subsets under
//! symmetric difference, and the structure constant of a product is the rational
//! `∏_{i ∈ S∩T} kᵢ`. Two facts about that are the reason this module is worth having and not
//! merely necessary:
//!
//! - **The grading group is the fork.** `H.0150`: `n` regions cut a face into `2ⁿ` pieces, one per
//!   membership word, and the region *is* the word. Here the basis monomials are indexed by exactly
//!   those `2ⁿ` words, and multiplying two turns is symmetric difference of their words. The
//!   crossing-word algebra and the turn-composition algebra are the same algebra.
//! - **Each generator carries a hand.** `√kᵢ` is determined only up to sign, and by `CLAUDE.md`
//!   §2b that sign is the half turn a squaring erased. Choosing a sign per generator is choosing a
//!   sheet, and the `2ⁿ` sign choices are the Galois group `(ℤ/2)ⁿ` acting on the field. Nothing
//!   here resolves that choice; a `Multiquadratic` is a *field element*, and its numeric value
//!   depends on an embedding this module does not declare.
//!
//! ## Exactness and what is refused
//!
//! Every coefficient is a `Rat` and every operation is exact rational arithmetic on `2ⁿ`
//! coefficients. There is no float, no tolerance, and no angle.
//!
//! The one place exactness is at risk is reducing `√d` to a canonical generator: `d = m²k` needs
//! the squarefree kernel `k`, and extracting it in general is factorization. This module trial
//! divides to a **declared bound** and then refuses by name rather than returning a kernel it
//! cannot certify squarefree. A refusal is a return; a silently non-canonical generator would make
//! two equal turns compare unequal, which is worse than an obstruction.

use core::cmp::Ordering;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;

/// Trial-division bound for squarefree extraction, declared by the caller.
///
/// Not a level authored inside the organ: [`squarefree_kernel`] takes it, and every constructor
/// that needs it takes it. The value a caller declares bounds which square factors can be found,
/// and anything beyond is refused by name rather than approximated.
pub const DECLARED_KERNEL_BOUND: u64 = 1 << 20;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MultiquadraticRefusal {
    /// The radicand is negative; this carrier is real.
    NegativeRadicand { radicand: Rat },
    /// A square factor may remain but lies beyond the declared trial-division bound, so the kernel
    /// cannot be certified squarefree. Returned rather than guessed.
    KernelBeyondDeclaredBound { kernel: BigInt, bound: u64 },
    /// The generator population would exceed what the caller declared it will hold. The basis is
    /// `2^n` wide, so this is a real resource statement and not a preference.
    GeneratorApertureExhausted { generators: usize, aperture: usize },
    /// Two elements were combined whose coefficient vectors do not match their generator lists.
    MalformedElement,
}

/// The squarefree kernel `k` of a positive integer `n = m²k`, with `m` returned beside it.
///
/// Trial divides by squares `p²` for `p` up to `bound`, then checks whether what remains is itself
/// a perfect square. If a square factor could still remain — which requires a repeated prime factor
/// larger than `bound`, hence a residue exceeding `bound²` — the residue is refused rather than
/// returned as a kernel.
pub fn squarefree_kernel(
    value: &BigInt,
    bound: u64,
) -> Result<(BigInt, BigInt), MultiquadraticRefusal> {
    if value.is_negative() {
        return Err(MultiquadraticRefusal::NegativeRadicand {
            radicand: Rat::from_integer(value.clone()),
        });
    }
    if value.is_zero() {
        return Ok((BigInt::zero(), BigInt::zero()));
    }
    let mut kernel = value.clone();
    let mut square_part = BigInt::one();
    let mut divisor = BigInt::from(2u32);
    while &divisor * &divisor <= kernel {
        if divisor > BigInt::from(bound) {
            break;
        }
        let square = &divisor * &divisor;
        while (&kernel % &square).is_zero() {
            kernel /= &square;
            square_part *= &divisor;
        }
        divisor += 1;
    }
    // What remains may still be a perfect square of one large prime; that is exactly decidable.
    let root = kernel.sqrt();
    if &root * &root == kernel {
        square_part *= &root;
        kernel = BigInt::one();
    } else if kernel > BigInt::from(bound) * BigInt::from(bound) {
        // A repeated prime factor above the bound would need the residue to exceed bound², and the
        // perfect-square check above only rules out the case where the residue is exactly p². The
        // remaining possibility p²·q is not excluded, so the kernel is not certified.
        return Err(MultiquadraticRefusal::KernelBeyondDeclaredBound { kernel, bound });
    }
    Ok((kernel, square_part))
}

/// One element of `ℚ(√k₁, …, √kₙ)`, in the `ℚ`-basis of square-root products.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Multiquadratic {
    /// Distinct squarefree integers `> 1`, strictly ascending. The empty list is `ℚ` itself.
    generators: Vec<BigInt>,
    /// `2^generators.len()` coefficients; index `s` is the coefficient of `∏_{i ∈ bits(s)} √kᵢ`.
    coefficients: Vec<Rat>,
}

impl Multiquadratic {
    /// A rational, in the trivial extension.
    pub fn rational(value: Rat) -> Self {
        Self {
            generators: Vec::new(),
            coefficients: vec![value],
        }
    }

    pub fn zero() -> Self {
        Self::rational(Rat::zero())
    }

    pub fn one() -> Self {
        Self::rational(Rat::one())
    }

    /// `√radicand` for a non-negative rational, reduced to its canonical generator.
    ///
    /// `√(p/q) = √(pq)/q`, and `pq = m²k` with `k` squarefree gives `(m/q)·√k`. When `k = 1` the
    /// result is rational and carries no generator at all, which is exactly the Pythagorean case.
    pub fn square_root(radicand: &Rat, bound: u64) -> Result<Self, MultiquadraticRefusal> {
        if radicand.is_negative() {
            return Err(MultiquadraticRefusal::NegativeRadicand {
                radicand: radicand.clone(),
            });
        }
        if radicand.is_zero() {
            return Ok(Self::zero());
        }
        let numerator = radicand.numer().clone();
        let denominator = radicand.denom().clone();
        let (kernel, square_part) = squarefree_kernel(&(&numerator * &denominator), bound)?;
        let scale = Rat::new(square_part, denominator);
        if kernel.is_one() {
            return Ok(Self::rational(scale));
        }
        Ok(Self {
            generators: vec![kernel],
            coefficients: vec![Rat::zero(), scale],
        })
    }

    /// The generators this element is written over.
    pub fn generators(&self) -> &[BigInt] {
        &self.generators
    }

    /// The `2ⁿ` coefficients, indexed by subset bitmask.
    pub fn coefficients(&self) -> &[Rat] {
        &self.coefficients
    }

    /// The rational value when this element carries no root, and `None` otherwise.
    pub fn as_rational(&self) -> Option<Rat> {
        let mut rational = None;
        for (index, coefficient) in self.coefficients.iter().enumerate() {
            if index == 0 {
                rational = Some(coefficient.clone());
            } else if !coefficient.is_zero() {
                return None;
            }
        }
        rational
    }

    /// Drop generators whose every coefficient is zero, so equality is canonical.
    fn reduced(mut self) -> Self {
        let mut index = 0usize;
        while index < self.generators.len() {
            let bit = 1usize << index;
            let unused = self
                .coefficients
                .iter()
                .enumerate()
                .all(|(mask, coefficient)| mask & bit == 0 || coefficient.is_zero());
            if unused {
                let mut folded = Vec::with_capacity(self.coefficients.len() / 2);
                for mask in 0..self.coefficients.len() {
                    if mask & bit == 0 {
                        let lower = mask & (bit - 1);
                        let upper = (mask >> 1) & !(bit - 1);
                        let _ = lower;
                        let _ = upper;
                        folded.push(self.coefficients[mask].clone());
                    }
                }
                self.coefficients = folded;
                self.generators.remove(index);
            } else {
                index += 1;
            }
        }
        self
    }

    /// Rewrite two elements over the union of their generators.
    fn aligned(
        left: &Self,
        right: &Self,
        aperture: usize,
    ) -> Result<(Vec<BigInt>, Vec<Rat>, Vec<Rat>), MultiquadraticRefusal> {
        let mut generators = left.generators.clone();
        for generator in &right.generators {
            if !generators.contains(generator) {
                generators.push(generator.clone());
            }
        }
        generators.sort();
        if generators.len() > aperture {
            return Err(MultiquadraticRefusal::GeneratorApertureExhausted {
                generators: generators.len(),
                aperture,
            });
        }
        let width = 1usize << generators.len();
        let lift = |source: &Self| -> Result<Vec<Rat>, MultiquadraticRefusal> {
            if source.coefficients.len() != 1usize << source.generators.len() {
                return Err(MultiquadraticRefusal::MalformedElement);
            }
            let mut lifted = vec![Rat::zero(); width];
            for (mask, coefficient) in source.coefficients.iter().enumerate() {
                if coefficient.is_zero() {
                    continue;
                }
                let mut target = 0usize;
                for (bit, generator) in source.generators.iter().enumerate() {
                    if mask & (1usize << bit) != 0 {
                        let position = generators
                            .iter()
                            .position(|candidate| candidate == generator)
                            .expect("union contains every source generator");
                        target |= 1usize << position;
                    }
                }
                lifted[target] += coefficient.clone();
            }
            Ok(lifted)
        };
        let lifted_left = lift(left)?;
        let lifted_right = lift(right)?;
        Ok((generators, lifted_left, lifted_right))
    }

    /// Exact sum.
    pub fn add(&self, other: &Self, aperture: usize) -> Result<Self, MultiquadraticRefusal> {
        let (generators, left, right) = Self::aligned(self, other, aperture)?;
        let coefficients = left
            .into_iter()
            .zip(right)
            .map(|(a, b)| a + b)
            .collect::<Vec<_>>();
        Ok(Self {
            generators,
            coefficients,
        }
        .reduced())
    }

    /// Exact negation.
    pub fn negated(&self) -> Self {
        Self {
            generators: self.generators.clone(),
            coefficients: self.coefficients.iter().map(|value| -value.clone()).collect(),
        }
    }

    /// Exact difference.
    pub fn subtract(&self, other: &Self, aperture: usize) -> Result<Self, MultiquadraticRefusal> {
        self.add(&other.negated(), aperture)
    }

    /// Exact product. This is where the algebra closes: a repeated root becomes a rational.
    pub fn multiply(&self, other: &Self, aperture: usize) -> Result<Self, MultiquadraticRefusal> {
        let (generators, left, right) = Self::aligned(self, other, aperture)?;
        let width = 1usize << generators.len();
        let mut coefficients = vec![Rat::zero(); width];
        for (left_mask, left_value) in left.iter().enumerate() {
            if left_value.is_zero() {
                continue;
            }
            for (right_mask, right_value) in right.iter().enumerate() {
                if right_value.is_zero() {
                    continue;
                }
                // (∏_S √k)(∏_T √k) = (∏_{S∩T} k) · ∏_{S△T} √k
                let shared = left_mask & right_mask;
                let mut structure = Rat::one();
                for (bit, generator) in generators.iter().enumerate() {
                    if shared & (1usize << bit) != 0 {
                        structure *= Rat::from_integer(generator.clone());
                    }
                }
                let target = left_mask ^ right_mask;
                coefficients[target] += left_value.clone() * right_value.clone() * structure;
            }
        }
        Ok(Self {
            generators,
            coefficients,
        }
        .reduced())
    }
}

impl PartialOrd for Multiquadratic {
    /// Only the trivial comparison is offered, and deliberately.
    ///
    /// Ordering two multiquadratic numbers requires choosing an **embedding** — a sign for every
    /// generator — and this carrier declares none, for the reason the module header states: the
    /// sign of `√k` is a hand, and choosing it is choosing a sheet. Equal elements compare equal;
    /// anything else returns `None` and the caller must declare an embedding to say more.
    ///
    /// A caller that *does* declare one calls [`Multiquadratic::sign_in_principal_embedding`],
    /// which names the sheet it takes in its own name.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self == other).then_some(Ordering::Equal)
    }
}

// -------------------------------------------------------------------------------------------------
// One declared embedding, and the sign it makes readable
// -------------------------------------------------------------------------------------------------

/// The sign of a field element under a declared embedding, or the reason it could not be read.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum EmbeddedSign {
    /// Every coefficient is zero. **This needs no embedding at all**: over an independent generator
    /// set the basis monomials are linearly independent over `ℚ`, so the element is zero in *every*
    /// embedding exactly when its coefficient vector vanishes. Structural, exact, and sheet-free.
    Zero,
    Positive,
    Negative,
    /// **The generator set is multiplicatively dependent modulo squares** — some non-empty subset
    /// multiplies to a perfect square, so `√(∏ kᵢ)` is rational and the `2ⁿ` monomials are *not* a
    /// basis.
    ///
    /// On such a set a non-zero coefficient vector can represent zero (`√21 − √3·√7 = 0` over
    /// `{3, 7, 21}`), which breaks both the structural zero test and `PartialEq`. This is refused
    /// by name rather than answered, and it is the one condition under which the refinement loop
    /// below could fail to terminate.
    DependentGenerators,
}

/// Integer square root of a non-negative `BigInt`, exactly, by Newton descent.
///
/// Returns `⌊√n⌋`. No float, and no dependency on `num-integer`, which this workspace does not
/// carry.
fn integer_square_root(value: &BigInt) -> BigInt {
    if value.is_zero() || value.is_one() {
        return value.clone();
    }
    let mut guess = BigInt::one() << ((value.bits() as usize).div_ceil(2) + 1);
    loop {
        let next = (&guess + value / &guess) >> 1;
        if next >= guess {
            break;
        }
        guess = next;
    }
    guess
}

/// A dyadic rational enclosure `[lo, hi]` of `√k` for a non-negative integer `k`, at `bits` of
/// binary precision, with `hi − lo ≤ 2^{−bits}`.
///
/// `⌊√(k·4^b)⌋ / 2^b ≤ √k < (⌊√(k·4^b)⌋ + 1) / 2^b`, which is exact integer arithmetic and never
/// an approximation with a discarded tail — the two endpoints *are* the return, in the sense
/// `exact_value.rs` requires of an enclosure.
fn root_enclosure(kernel: &BigInt, bits: u64) -> (Rat, Rat) {
    let scale = BigInt::one() << bits;
    let floor = integer_square_root(&(kernel * &scale * &scale));
    (
        Rat::new(floor.clone(), scale.clone()),
        Rat::new(floor + BigInt::one(), scale),
    )
}

impl Multiquadratic {
    /// **Whether the generator set is multiplicatively independent modulo squares.**
    ///
    /// The `2ⁿ` monomials `∏_{i∈S} √kᵢ` are a `ℚ`-basis exactly when no non-empty subset product is
    /// a perfect square. This tests every subset directly by exact integer square root — no
    /// factorization, no bound, and `n` subsets' worth of work is the same order as the coefficient
    /// vector this element already carries.
    ///
    /// **Why it is worth testing rather than assuming.** The constructors keep the generator list
    /// distinct, squarefree and ascending, which is *not* the same as independent: `{3, 7, 21}`
    /// satisfies every one of those and is dependent, because `3·7·21 = 21²`. On such a set
    /// `√21 − √3·√7 = 0` with a non-zero coefficient vector, so both the structural zero test and
    /// the derived `PartialEq` are unsound. No constructor in this module produces such a set from
    /// another element's generators — [`Multiquadratic::multiply`] takes a union and never mints a
    /// kernel — but [`Multiquadratic::square_root`] can, from radicands a caller supplies, and
    /// nothing prevented two such elements from meeting.
    pub fn generators_are_independent(&self) -> bool {
        let count = self.generators.len();
        for subset in 1u32..(1u32 << count) {
            let mut product = BigInt::one();
            for (index, generator) in self.generators.iter().enumerate() {
                if subset & (1 << index) != 0 {
                    product *= generator;
                }
            }
            let root = integer_square_root(&product);
            if &root * &root == product {
                return false;
            }
        }
        true
    }

    /// **The sign of this element in the principal embedding, where every `√kᵢ` is taken positive.**
    ///
    /// The module refuses to order two elements because ordering needs a sheet. This method takes
    /// one — the principal sheet, `√k > 0` for every generator — and says so in its name, so a
    /// reader never has to discover a smuggled hand. It is the receiver declaration
    /// `CLAUDE.md` §13 rule 2 requires: the embedding *measures*, and the caller declares it.
    ///
    /// **There is no aperture here and there deliberately is not one.** Zero is decided structurally
    /// from the coefficient vector; the generator set is checked for independence, which is the one
    /// condition that could make that test wrong; and a non-zero element is then enclosed by exact
    /// dyadic intervals and refined by doubling. The width halves each doubling while the value is a
    /// fixed non-zero real, so separation occurs at finite precision — **termination is a theorem,
    /// not a budget**, and an authored cap here would have been a level the material determines.
    pub fn sign_in_principal_embedding(&self) -> EmbeddedSign {
        if !self.generators_are_independent() {
            return EmbeddedSign::DependentGenerators;
        }
        if self.coefficients.iter().all(Zero::is_zero) {
            return EmbeddedSign::Zero;
        }
        // The value of basis monomial `S` is `√(∏_{i∈S} kᵢ)`, one integer root per subset.
        let mut radicands: Vec<BigInt> = Vec::with_capacity(self.coefficients.len());
        for subset in 0..self.coefficients.len() {
            let mut radicand = BigInt::one();
            for (index, generator) in self.generators.iter().enumerate() {
                if subset & (1 << index) != 0 {
                    radicand *= generator;
                }
            }
            radicands.push(radicand);
        }

        // The starting precision is read off the material: enough bits to hold the largest
        // coefficient and radicand in play, so the first pass already separates in the ordinary
        // case and nothing is authored.
        let mut bits: u64 = self
            .coefficients
            .iter()
            .map(|coefficient| coefficient.numer().bits().max(coefficient.denom().bits()))
            .chain(radicands.iter().map(|radicand| radicand.bits()))
            .max()
            .unwrap_or(1)
            + 1;
        loop {
            let mut low = Rat::zero();
            let mut high = Rat::zero();
            for (subset, coefficient) in self.coefficients.iter().enumerate() {
                if coefficient.is_zero() {
                    continue;
                }
                let (root_low, root_high) = root_enclosure(&radicands[subset], bits);
                if coefficient.is_positive() {
                    low += coefficient * &root_low;
                    high += coefficient * &root_high;
                } else {
                    low += coefficient * &root_high;
                    high += coefficient * &root_low;
                }
            }
            if low.is_positive() {
                return EmbeddedSign::Positive;
            }
            if high.is_negative() {
                return EmbeddedSign::Negative;
            }
            bits *= 2;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    const APERTURE: usize = 8;

    #[test]
    fn a_pythagorean_sine_carries_no_generator_at_all() {
        // cos = 3/5 gives 1 - cos² = 16/25, whose root is 4/5: rational, no extension.
        let radicand = Rat::one() - rat(3, 5) * rat(3, 5);
        let sine = Multiquadratic::square_root(&radicand, DECLARED_KERNEL_BOUND).unwrap();
        assert_eq!(sine.generators().len(), 0);
        assert_eq!(sine.as_rational(), Some(rat(4, 5)));
    }

    #[test]
    fn the_equilateral_corner_needs_exactly_one_generator() {
        // cos = 1/2 gives 1 - cos² = 3/4, whose root is (1/2)√3.
        let radicand = Rat::one() - rat(1, 2) * rat(1, 2);
        let sine = Multiquadratic::square_root(&radicand, DECLARED_KERNEL_BOUND).unwrap();
        assert_eq!(sine.generators(), &[BigInt::from(3)]);
        assert_eq!(sine.coefficients()[0], Rat::zero());
        assert_eq!(sine.coefficients()[1], rat(1, 2));
        assert!(sine.as_rational().is_none());
    }

    #[test]
    fn a_root_squared_returns_to_the_rationals_exactly() {
        // The algebra closes: √3 · √3 = 3, with no generator left standing.
        let root = Multiquadratic::square_root(&Rat::from_integer(BigInt::from(3)), DECLARED_KERNEL_BOUND).unwrap();
        let squared = root.multiply(&root, APERTURE).unwrap();
        assert_eq!(squared.as_rational(), Some(Rat::from_integer(BigInt::from(3))));
        assert_eq!(squared.generators().len(), 0);
    }

    #[test]
    fn distinct_generators_multiply_into_the_joint_word() {
        // √2 · √3 = √6 as the {0,1} basis monomial, and squaring it returns 6.
        let two = Multiquadratic::square_root(&Rat::from_integer(BigInt::from(2)), DECLARED_KERNEL_BOUND).unwrap();
        let three = Multiquadratic::square_root(&Rat::from_integer(BigInt::from(3)), DECLARED_KERNEL_BOUND).unwrap();
        let product = two.multiply(&three, APERTURE).unwrap();
        assert_eq!(product.generators(), &[BigInt::from(2), BigInt::from(3)]);
        // the coefficient sits on the both-generators word, index 0b11
        assert_eq!(product.coefficients()[3], Rat::one());
        let squared = product.multiply(&product, APERTURE).unwrap();
        assert_eq!(squared.as_rational(), Some(Rat::from_integer(BigInt::from(6))));
    }

    #[test]
    fn a_square_radicand_reduces_rather_than_founding_a_redundant_generator() {
        // √12 must be 2√3, not a generator "12": otherwise 2√3 and √12 would compare unequal.
        let twelve = Multiquadratic::square_root(&Rat::from_integer(BigInt::from(12)), DECLARED_KERNEL_BOUND).unwrap();
        assert_eq!(twelve.generators(), &[BigInt::from(3)]);
        assert_eq!(twelve.coefficients()[1], Rat::from_integer(BigInt::from(2)));
        let three = Multiquadratic::square_root(&Rat::from_integer(BigInt::from(3)), DECLARED_KERNEL_BOUND).unwrap();
        let doubled = three
            .multiply(&Multiquadratic::rational(Rat::from_integer(BigInt::from(2))), APERTURE)
            .unwrap();
        assert_eq!(twelve, doubled, "√12 and 2√3 must be the same element");
    }

    #[test]
    fn the_pythagorean_identity_holds_exactly_for_an_irrational_corner() {
        // cos² + sin² = 1 for cos = 1/2, sin = (1/2)√3 — the identity the composition depends on.
        let cosine = Multiquadratic::rational(rat(1, 2));
        let radicand = Rat::one() - rat(1, 2) * rat(1, 2);
        let sine = Multiquadratic::square_root(&radicand, DECLARED_KERNEL_BOUND).unwrap();
        let sum = cosine
            .multiply(&cosine, APERTURE)
            .unwrap()
            .add(&sine.multiply(&sine, APERTURE).unwrap(), APERTURE)
            .unwrap();
        assert_eq!(sum.as_rational(), Some(Rat::one()));
    }

    #[test]
    fn composing_two_equilateral_corners_returns_the_exact_two_thirds_turn() {
        // Two π/3 turns compose to 2π/3: cos = −1/2, sin = (1/2)√3. Exact, no angle taken.
        let cosine = Multiquadratic::rational(rat(1, 2));
        let sine = Multiquadratic::square_root(
            &(Rat::one() - rat(1, 2) * rat(1, 2)),
            DECLARED_KERNEL_BOUND,
        )
        .unwrap();
        // (c,s)·(c,s) = (c² − s², 2cs)
        let composed_cosine = cosine
            .multiply(&cosine, APERTURE)
            .unwrap()
            .subtract(&sine.multiply(&sine, APERTURE).unwrap(), APERTURE)
            .unwrap();
        let composed_sine = cosine
            .multiply(&sine, APERTURE)
            .unwrap()
            .multiply(&Multiquadratic::rational(Rat::from_integer(BigInt::from(2))), APERTURE)
            .unwrap();
        assert_eq!(composed_cosine.as_rational(), Some(rat(-1, 2)));
        assert_eq!(composed_sine.generators(), &[BigInt::from(3)]);
        assert_eq!(composed_sine.coefficients()[1], rat(1, 2));
    }

    #[test]
    fn the_kernel_bound_refuses_rather_than_returning_an_uncertified_generator() {
        // With a deliberately tiny bound, a radicand whose kernel exceeds bound² is refused by
        // name. A silently non-canonical generator would make equal turns compare unequal.
        let large = BigInt::from(1_000_003u64) * BigInt::from(1_000_033u64);
        let refusal = squarefree_kernel(&large, 16);
        assert!(matches!(
            refusal,
            Err(MultiquadraticRefusal::KernelBeyondDeclaredBound { .. })
        ));
    }

    #[test]
    fn the_generator_aperture_is_a_real_resource_statement() {
        // The basis is 2^n wide, so exceeding the declared aperture is refused rather than held.
        let two = Multiquadratic::square_root(&Rat::from_integer(BigInt::from(2)), DECLARED_KERNEL_BOUND).unwrap();
        let three = Multiquadratic::square_root(&Rat::from_integer(BigInt::from(3)), DECLARED_KERNEL_BOUND).unwrap();
        let refusal = two.multiply(&three, 1);
        assert!(matches!(
            refusal,
            Err(MultiquadraticRefusal::GeneratorApertureExhausted { generators: 2, aperture: 1 })
        ));
    }
}

// -------------------------------------------------------------------------------------------------
// The structural aperture: what this carrier can represent, stated once
// -------------------------------------------------------------------------------------------------

/// **The aperture of this carrier is a degree condition, and it is not [`DECLARED_KERNEL_BOUND`].**
///
/// `DECLARED_KERNEL_BOUND` bounds a *search* — how far trial division looks for a squarefree kernel —
/// and a refusal from it is an obstruction of the apparatus. The **structural** aperture is a
/// property of the field itself and no bound can move it:
///
/// ```text
///   x ∈ ℚ(√k₁,…,√kₙ)   ⟹   [ℚ(x):ℚ] divides 2ⁿ
/// ```
///
/// because each generator adjoins at most one square root, so the whole tower has degree `2ⁿ` over
/// `ℚ` and every subfield's degree divides it. **A number whose minimal polynomial has degree not a
/// power of two is not in this carrier and cannot be put there by raising any bound.**
///
/// # What that makes this module
///
/// A tower of quadratic extensions is exactly what a **straightedge and compass** construct: the two
/// instruments intersect lines and circles, so every new coordinate solves a linear or quadratic
/// equation over what is already built. So this carrier's reach *is* the classical constructible
/// field, and `2^(1/3)` — the Delian constant, the side of a doubled cube — is outside it for a
/// reason that has nothing to do with any bound this module declares.
///
/// MathWorld's `CubeDuplication` states the classical half verbatim: *"the problem cannot be solved
/// because the Delian constant `2^(1/3)` … is not a Euclidean number… The problem can be solved,
/// however, using a **Neusis construction**."* Adjoining the marked ruler is `H.0420`'s purchased
/// channel: it reaches cubics, and it is not built here.
///
/// **The direction matters and is the whole content of [`admits_degree`].** Failing the condition
/// **refuses exactly**; passing it is **necessary and not sufficient**, because sufficiency needs the
/// Galois closure to be a 2-group and this function does not decide that.
///
/// Record:
/// `research/records/2026-08-10_THE_INSTRUMENT_DECLARES_THE_APERTURE_AND_THE_REFUSAL_IS_THE_RETURN.md`.
pub const fn structural_aperture_is_a_power_of_two() -> bool {
    true
}

/// Whether a degree is a power of two — the compass rung's necessary condition.
///
/// `0` is not a degree and returns `false`; `1` is `2⁰` and returns `true`.
pub fn admits_degree(degree: usize) -> bool {
    degree != 0 && degree.is_power_of_two()
}

impl Multiquadratic {
    /// The degree of the tower this element is written over: `2ⁿ` for `n` generators.
    ///
    /// This is the *ambient* tower's degree, not the degree of this element's own minimal
    /// polynomial, which divides it. Returned as the exact bound it is.
    pub fn tower_degree(&self) -> u64 {
        1u64 << self.generators.len()
    }
}
