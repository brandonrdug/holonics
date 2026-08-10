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
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self == other).then_some(Ordering::Equal)
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
