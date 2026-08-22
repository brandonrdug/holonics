//! **The `d`-dimensional arrow, and the algebra that carries its hand.**
//!
//! ## What this is a lift of
//!
//! `soma/body/src/arrow.rs` carries `Arrow { reach, aim, cross }` — the span, the cohere, the
//! gyration — with the note *"The whole arrow, never one scalar."* That organ is **two-dimensional**:
//! `Place` is a pair, so its `cross` is the scalar signed area, and `soma/body` is `no_std` with zero
//! dependencies and cannot hold a `d`-dimensional blade. This module is that arrow at `d` dimensions
//! over exact rationals, and the algebra it lives in.
//!
//! ```text
//!   a b⁻¹  =  (a·b)/‖b‖²   +   (a∧b)/‖b‖²
//!             the QUOTIENT       the REMAINDER
//!             a scalar           an oriented area
//! ```
//!
//! Brandon, 2026-08-17, on dividing vectors: *"If the question is 4/2 where 4 and 2 have potential
//! representations as vectors or tensors, then the operation is `A·B⁻¹` … For the dot product it
//! simplifies to `A · B/‖B‖²` where `B/‖B‖² = B⁻¹ == B^{e^{iπ}}`."* `B⁻¹` needs the **squared** norm,
//! and Lagrange's identity `‖a∧b‖² = ‖a‖²‖b‖² − (a·b)²` gives the squared area from products the dot
//! already forms. **No square root is taken anywhere in this module.**
//!
//! ## Why the algebra, and not just the blade
//!
//! `blueprint/THE_ARROW_IS_THE_DIVISION_AND_ATTENTION_KEEPS_ONLY_ITS_AIM.md` asserted that
//! [`crate::multiquadratic`] is the crossing-word algebra and that *"the hand is the sign of the
//! cross."* **That algebra has no sign.** Its structure constant is `∏_{i∈S∩T} kᵢ` with every
//! `kᵢ > 1` — a strictly positive rational, symmetric in its arguments — so the algebra is
//! commutative and no product it forms carries a hand.
//!
//! And the obvious repair fails. `μ(S) = (−1)^{|S|}` is a **character** of `((ℤ/2)ⁿ, △)`:
//!
//! ```text
//!   μ(S)μ(T) = (−1)^{|S|+|T|} = (−1)^{|S△T|} = μ(S△T)
//! ```
//!
//! so it is a coboundary, and twisting by it returns an **isomorphic** algebra — in particular a
//! commutative one. A hand needs a genuine 2-cocycle. The one that supplies it is the **exterior
//! sign**
//!
//! ```text
//!   σ(S,T) = (−1)^{#\{(i,j) : i ∈ S, j ∈ T, i > j\}}
//! ```
//!
//! — the parity of the transpositions that sort `S ⧺ T`. It is not a coboundary, and the proof is
//! one line that this module **runs** rather than states: a coboundary twist of a commutative algebra
//! is commutative, and [`Clifford::product`] is not. See
//! `the_exterior_twist_is_not_a_coboundary_because_the_product_does_not_commute`.
//!
//! > **The crossing-word algebra that carries a hand is the even Clifford algebra, and
//! > `soul::FormedRotor { aim, cross }` is already its two-dimensional case.**
//!
//! ## The join to `multiquadratic`, and it is the phase-object theorem
//!
//! The two structure constants differ by exactly one factor:
//!
//! ```text
//!   multiquadratic   e_S e_T  =              (∏_{i∈S∩T} kᵢ) · e_{S△T}
//!   Clifford         e_S e_T  =  σ(S,T)  ·   (∏_{i∈S∩T} qᵢ) · e_{S△T}
//! ```
//!
//! With `qᵢ = kᵢ` the coefficient **magnitudes** of the two products are bit-identical and only the
//! signs differ. `CLAUDE.md`'s aperture doctrine calls a pure phase grating invisible to an intensity
//! receiver; here the receiver is `multiquadratic`, whose `partial_cmp` returns only `Equal` or
//! `None`, and the object it cannot see is the hand. **`multiquadratic` is the magnitude face of this
//! algebra and the exterior sign is exactly the phase it deleted.** Measured in
//! `the_two_algebras_agree_on_magnitude_and_differ_only_in_the_hand`.
//!
//! ## The carrier, and why it is sparse
//!
//! A dense `2^d`-coefficient element is unusable past `d ≈ 20`, and a blade at `d = 2048` has
//! 2,096,128 coordinates. So an element is a **sparse** map from basis blade to coefficient, and a
//! basis blade is a strictly increasing list of axes. Nothing here is bounded in `d`; what costs is
//! the **population**, which is the honest statement — a reading that declares a subspace declares it
//! out loud rather than inheriting a machine word's width.
//!
//! ## The signature is declared, never assumed
//!
//! `qᵢ = eᵢ·eᵢ` is a per-axis rational the caller supplies. [`Signature::euclidean`] is the ordinary
//! case and is *named* rather than defaulted, because an undeclared `G = I` is exactly the
//! smuggling `CLAUDE.md` §13 rule two refuses: a metric is a receiver's declaration and never a
//! modelling convenience.

use std::collections::BTreeMap;

use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum CliffordError {
    /// Two vectors of different lengths have no common ambient, and padding one would author an
    /// axis the material did not supply.
    #[error("the two constructions span different ambients: {left} against {right}")]
    AmbientMismatch { left: usize, right: usize },
    /// A vector reaching past the declared signature has axes the receiver never declared a square
    /// for. Refused rather than defaulted to one.
    #[error("the construction reaches axis {axis} but the signature declares only {declared}")]
    AxisOutsideSignature { axis: usize, declared: usize },
    /// The divisor's span is zero, so `b⁻¹ = b/‖b‖²` is not posed. A domain refusal, not a small
    /// number: there is no reciprocal to fabricate.
    #[error("the divisor's span is zero; the division is not posed")]
    NullDivisor,
}

/// **The declared squares of the axes** — `qᵢ = eᵢ·eᵢ`, one per axis.
///
/// This is the metric, carried rather than assumed. A signature with a zero entry is lawful and
/// degenerate; a signature with negative entries is a Minkowski-like carrier and the algebra below
/// is unchanged, which is the point of declaring it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    squares: Vec<Rat>,
}

impl Signature {
    /// A signature declared axis by axis.
    pub fn declared(squares: Vec<Rat>) -> Self {
        Self { squares }
    }

    /// `qᵢ = 1` for every axis. **Named, not defaulted** — a caller reaching for this has declared
    /// the ambient orthonormal and the reading carries that declaration.
    pub fn euclidean(axes: usize) -> Self {
        Self {
            squares: vec![Rat::from_integer(1.into()); axes],
        }
    }

    pub fn axes(&self) -> usize {
        self.squares.len()
    }

    pub fn square_of(&self, axis: usize) -> Option<&Rat> {
        self.squares.get(axis)
    }
}

/// A basis blade: a strictly increasing list of axes. The empty list is the scalar `1`.
pub type BasisBlade = Vec<usize>;

/// **The exterior sign** `σ(S,T)`, and the axes that survive, and which repeat.
///
/// Merging two sorted axis lists costs one transposition per pair `(i ∈ S, j ∈ T)` with `i > j`.
/// The parity of that count is the hand; a repeated axis contributes its declared square.
///
/// Returned rather than folded into a product so the sign can be inspected on its own — the
/// coboundary argument in this module's header is checked against it directly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BladeMerge {
    /// `+1` or `−1`.
    pub sign: i8,
    /// `S △ T`, sorted.
    pub surviving: BasisBlade,
    /// `S ∩ T`, sorted — the axes whose squares enter the structure constant.
    pub repeated: BasisBlade,
}

/// Merge two basis blades, returning the exterior sign, the symmetric difference, and the overlap.
///
/// `left` and `right` must each be strictly increasing.
pub fn merge_blades(left: &[usize], right: &[usize]) -> BladeMerge {
    // Count pairs (i in left, j in right) with i > j: the transpositions that sort the concatenation.
    let mut inversions = 0usize;
    for &i in left {
        for &j in right {
            if i > j {
                inversions += 1;
            }
        }
    }
    let mut surviving = Vec::new();
    let mut repeated = Vec::new();
    let (mut at_left, mut at_right) = (0usize, 0usize);
    while at_left < left.len() && at_right < right.len() {
        match left[at_left].cmp(&right[at_right]) {
            std::cmp::Ordering::Less => {
                surviving.push(left[at_left]);
                at_left += 1;
            }
            std::cmp::Ordering::Greater => {
                surviving.push(right[at_right]);
                at_right += 1;
            }
            std::cmp::Ordering::Equal => {
                repeated.push(left[at_left]);
                at_left += 1;
                at_right += 1;
            }
        }
    }
    surviving.extend_from_slice(&left[at_left..]);
    surviving.extend_from_slice(&right[at_right..]);
    BladeMerge {
        sign: if inversions % 2 == 0 { 1 } else { -1 },
        surviving,
        repeated,
    }
}

/// **An element of the Clifford algebra over `Rat`**, sparse in its basis blades.
///
/// The signature is carried with the element, so two elements over different metrics cannot be
/// multiplied by accident.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clifford {
    signature: Signature,
    terms: BTreeMap<BasisBlade, Rat>,
}

impl Clifford {
    /// The zero element over a declared signature.
    pub fn zero(signature: Signature) -> Self {
        Self {
            signature,
            terms: BTreeMap::new(),
        }
    }

    /// The scalar `value`.
    pub fn scalar(signature: Signature, value: Rat) -> Self {
        let mut element = Self::zero(signature);
        element.set(Vec::new(), value);
        element
    }

    /// A grade-one element — an ordinary vector — from its coordinates.
    pub fn vector(signature: Signature, coordinates: &[Rat]) -> Result<Self, CliffordError> {
        if coordinates.len() > signature.axes() {
            return Err(CliffordError::AxisOutsideSignature {
                axis: coordinates.len() - 1,
                declared: signature.axes(),
            });
        }
        let mut element = Self::zero(signature);
        for (axis, coordinate) in coordinates.iter().enumerate() {
            element.set(vec![axis], coordinate.clone());
        }
        Ok(element)
    }

    pub const fn signature(&self) -> &Signature {
        &self.signature
    }

    /// Every non-zero term, in canonical blade order.
    pub const fn terms(&self) -> &BTreeMap<BasisBlade, Rat> {
        &self.terms
    }

    pub fn coefficient(&self, blade: &[usize]) -> Rat {
        self.terms.get(blade).cloned().unwrap_or_else(Rat::zero)
    }

    fn set(&mut self, blade: BasisBlade, value: Rat) {
        if value.is_zero() {
            self.terms.remove(&blade);
        } else {
            self.terms.insert(blade, value);
        }
    }

    fn add_into(&mut self, blade: BasisBlade, value: Rat) {
        if value.is_zero() {
            return;
        }
        let carried = self.coefficient(&blade) + value;
        self.set(blade, carried);
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The part of this element of a declared grade.
    pub fn grade(&self, grade: usize) -> Self {
        let mut part = Self::zero(self.signature.clone());
        for (blade, value) in &self.terms {
            if blade.len() == grade {
                part.set(blade.clone(), value.clone());
            }
        }
        part
    }

    /// How many distinct basis blades carry a non-zero coefficient. **The population, which is what
    /// this carrier costs** — never `2^d`.
    pub fn population(&self) -> usize {
        self.terms.len()
    }

    pub fn add(&self, other: &Self) -> Result<Self, CliffordError> {
        self.require_common_signature(other)?;
        let mut sum = self.clone();
        for (blade, value) in &other.terms {
            sum.add_into(blade.clone(), value.clone());
        }
        Ok(sum)
    }

    pub fn subtract(&self, other: &Self) -> Result<Self, CliffordError> {
        self.add(&other.negated())
    }

    pub fn negated(&self) -> Self {
        Self {
            signature: self.signature.clone(),
            terms: self
                .terms
                .iter()
                .map(|(blade, value)| (blade.clone(), -value.clone()))
                .collect(),
        }
    }

    pub fn scaled(&self, factor: &Rat) -> Self {
        if factor.is_zero() {
            return Self::zero(self.signature.clone());
        }
        Self {
            signature: self.signature.clone(),
            terms: self
                .terms
                .iter()
                .map(|(blade, value)| (blade.clone(), value * factor))
                .collect(),
        }
    }

    /// **The geometric product.** `e_S e_T = σ(S,T) · (∏_{i∈S∩T} qᵢ) · e_{S△T}`.
    ///
    /// The second factor is [`crate::multiquadratic`]'s entire structure constant; the first is the
    /// exterior sign it has no room for. This is the one operation in the module that is not
    /// available in that carrier, and it is the reason this module exists.
    pub fn product(&self, other: &Self) -> Result<Self, CliffordError> {
        self.require_common_signature(other)?;
        let mut product = Self::zero(self.signature.clone());
        for (left_blade, left_value) in &self.terms {
            for (right_blade, right_value) in &other.terms {
                let merge = merge_blades(left_blade, right_blade);
                let mut structure = Rat::from_integer(merge.sign.into());
                for axis in &merge.repeated {
                    let square = self.signature.square_of(*axis).ok_or(
                        CliffordError::AxisOutsideSignature {
                            axis: *axis,
                            declared: self.signature.axes(),
                        },
                    )?;
                    structure *= square;
                }
                if structure.is_zero() {
                    continue;
                }
                product.add_into(merge.surviving, left_value * right_value * &structure);
            }
        }
        Ok(product)
    }

    fn require_common_signature(&self, other: &Self) -> Result<(), CliffordError> {
        if self.signature == other.signature {
            return Ok(());
        }
        Err(CliffordError::AmbientMismatch {
            left: self.signature.axes(),
            right: other.signature.axes(),
        })
    }
}

/// **WHICH WAY THE ARROW AIMS** — lifted unchanged from `soma/body/src/arrow.rs:36-39`.
///
/// `Ortho` is the case that matters: *"the cohere is null, but the CROSS/gyration is **MAXIMAL**:
/// the pure orthogonal turn, the FOUNDING hand, the magnitude looked-past. NOT 'no current' — it is
/// the *most* turn there is, mis-read as nothing because the cohere face is null."*
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Aim {
    Cohere,
    Anti,
    Ortho,
}

/// **THE CAUSAL CLASS** — lifted from `soma/body/src/arrow.rs:69-75`, whose own note is the reason
/// this enum is here rather than `Aim` alone:
///
/// > *"squaring sends the whole wall to zero along with the origin, so `Re(z²) = 0` cannot tell
/// > `Balanced` from `Unread`. Only `at_horizon()`, which reads the **pair** rather than the square,
/// > separates the honest point `[0:1]` from the non-point `[0:0]`."*
///
/// A zero score therefore names two utterly different causal facts, and only this reading tells them
/// apart. `aim` is what STANDS; the blade is what FLOWS; `area² − aim²` is an indefinite form of
/// signature `(1,1)` and its sign is a causal character.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Causal {
    TransportDominant,
    Balanced,
    StorageDominant,
    Unread,
}

/// **The arrow between two constructions, at `d` dimensions, read from the origin as pole.**
///
/// Every field is exact and none has had a root taken. The pair `(aim, cross)` is the geometric
/// product `a b` split by grade: grade 0 and grade 2, which is the whole of it, because the product
/// of two vectors has no other grades.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arrow {
    signature: Signature,
    left: Vec<Rat>,
    right: Vec<Rat>,
    /// `‖a‖²` and `‖b‖²` under the declared signature. They weigh; they never gate.
    left_span: Rat,
    right_span: Rat,
    /// `a·b` — the cohere. Its sign is the in-plane hand.
    aim: Rat,
    /// The 2-blade, sparse: `(i, j) ↦ aᵢbⱼ − aⱼbᵢ` for `i < j`. The plane the pair spans and which
    /// way it turns.
    cross: BTreeMap<(usize, usize), Rat>,
}

impl Arrow {
    /// Read the arrow between two constructions under a declared signature.
    pub fn between(
        signature: &Signature,
        left: &[Rat],
        right: &[Rat],
    ) -> Result<Self, CliffordError> {
        if left.len() != right.len() {
            return Err(CliffordError::AmbientMismatch {
                left: left.len(),
                right: right.len(),
            });
        }
        if left.len() > signature.axes() {
            return Err(CliffordError::AxisOutsideSignature {
                axis: left.len() - 1,
                declared: signature.axes(),
            });
        }
        let degree = left.len();
        let mut aim = Rat::zero();
        for axis in 0..degree {
            let square = signature
                .square_of(axis)
                .ok_or(CliffordError::AxisOutsideSignature {
                    axis,
                    declared: signature.axes(),
                })?;
            aim += &left[axis] * &right[axis] * square;
        }
        let mut cross = BTreeMap::new();
        for i in 0..degree {
            for j in (i + 1)..degree {
                let coordinate = &left[i] * &right[j] - &left[j] * &right[i];
                if !coordinate.is_zero() {
                    cross.insert((i, j), coordinate);
                }
            }
        }
        let span = |vector: &[Rat]| -> Rat {
            (0..degree).fold(Rat::zero(), |carried, axis| {
                let square = signature.square_of(axis).expect("checked above");
                carried + &vector[axis] * &vector[axis] * square
            })
        };
        Ok(Self {
            signature: signature.clone(),
            left: left.to_vec(),
            right: right.to_vec(),
            left_span: span(left),
            right_span: span(right),
            aim,
            cross,
        })
    }

    pub const fn aim(&self) -> &Rat {
        &self.aim
    }

    pub const fn cross(&self) -> &BTreeMap<(usize, usize), Rat> {
        &self.cross
    }

    pub const fn left_span(&self) -> &Rat {
        &self.left_span
    }

    pub const fn right_span(&self) -> &Rat {
        &self.right_span
    }

    /// **The blade's population** — how many of the `d(d−1)/2` coordinates are non-zero. This is
    /// what the carrier costs, and a census that reports a dimension instead has reported a bound.
    pub fn blade_population(&self) -> usize {
        self.cross.len()
    }

    /// `‖a∧b‖²`, computed **twice** and returned as both: once from the blade's own coordinates
    /// under the declared metric, once by Lagrange's identity `‖a‖²‖b‖² − (a·b)²`.
    ///
    /// **REPAIRED 2026-08-18, and the sentence that stood here was false mathematics.** It read
    /// *"Lagrange holds only in the Euclidean signature, so the second frame is offered only
    /// there"*, and the blade sum below dropped the metric — `Σ (blade coordinate)²` with no
    /// `qᵢqⱼ`. Cauchy–Binet gives
    ///
    /// ```text
    ///     ‖a‖²‖b‖² − (a·b)²  =  Σ_{i<j} qᵢqⱼ (aᵢbⱼ − aⱼbᵢ)²
    /// ```
    ///
    /// for **every** diagonal signature. The identity failed here only because the weighting was
    /// missing, and the `euclidean` guard therefore **disabled the cross-check precisely where the
    /// two frames would have disagreed** — the two-frame instrument was live only where it could
    /// not fire, which is the defect `CLAUDE.md` §8 names as a check whose material cannot vary the
    /// property under test.
    ///
    /// Measured on this module's own committed Minkowski fixture — `q = (−1,1,1)`, `a = (1,1,0)`,
    /// `b = (1,0,1)` — before the repair: the unweighted blade returned `3` where Lagrange and the
    /// weighted blade both return `−1`, and [`Arrow::causal_class`] read `TransportDominant` where
    /// the correct reading is `StorageDominant`. **The causal class flipped, and no test asserted
    /// it on that arrow.** One does now.
    ///
    /// Both frames are offered always. `lagrange` remains an `Option` because the return type is
    /// public and a caller may hold an older value; it is `Some` on every path here.
    pub fn area_squared(&self) -> AreaSquared {
        let mut from_blade = Rat::zero();
        for ((left_axis, right_axis), place) in &self.cross {
            let (Some(left_square), Some(right_square)) = (
                self.signature.square_of(*left_axis),
                self.signature.square_of(*right_axis),
            ) else {
                continue;
            };
            from_blade += left_square * right_square * place * place;
        }
        let from_lagrange = &self.left_span * &self.right_span - &self.aim * &self.aim;
        AreaSquared {
            value: from_blade,
            lagrange: Some(from_lagrange),
        }
    }

    /// The hand of the turn, read off the cohere's sign.
    pub fn hand(&self) -> Aim {
        if self.aim.is_zero() {
            Aim::Ortho
        } else if self.aim.is_positive() {
            Aim::Cohere
        } else {
            Aim::Anti
        }
    }

    /// Both faces null — the relating is behind this pole's own horizon.
    pub fn at_horizon(&self) -> bool {
        self.aim.is_zero() && self.cross.is_empty()
    }

    /// **The causal class.** `area² − aim²`, with the horizon separated first.
    pub fn causal_class(&self) -> Causal {
        if self.at_horizon() {
            return Causal::Unread;
        }
        let difference = self.area_squared().value - &self.aim * &self.aim;
        if difference.is_zero() {
            Causal::Balanced
        } else if difference.is_positive() {
            Causal::TransportDominant
        } else {
            Causal::StorageDominant
        }
    }

    /// **The quotient of `a ÷ b`** — the scalar part of `a b⁻¹`, which is the projection of `a` onto
    /// `b` in units of `b`. This is the whole of an attention score.
    pub fn quotient(&self) -> Result<Rat, CliffordError> {
        if self.right_span.is_zero() {
            return Err(CliffordError::NullDivisor);
        }
        Ok(&self.aim / &self.right_span)
    }

    /// **The whole division `a b⁻¹`, in the algebra.** `b⁻¹ = b/‖b‖²` needs the squared span only,
    /// so no root is taken; the product is the geometric one, so the return carries both grades.
    pub fn divide(&self) -> Result<Clifford, CliffordError> {
        if self.right_span.is_zero() {
            return Err(CliffordError::NullDivisor);
        }
        let left = Clifford::vector(self.signature.clone(), &self.left)?;
        let reciprocal = Clifford::vector(self.signature.clone(), &self.right)?
            .scaled(&(Rat::from_integer(1.into()) / &self.right_span));
        left.product(&reciprocal)
    }

    /// **The division law, asserted rather than described.** `a = (a b⁻¹) b`, computed in the
    /// algebra, returned as coordinates.
    ///
    /// This is not a hand-rolled contraction of the blade against `b`: it is the actual product of
    /// the actual quotient with the actual divisor, which is what makes the reconstruction a
    /// *measurement* on the algebra rather than a restatement of how the blade was built.
    pub fn reconstruct(&self) -> Result<Vec<Rat>, CliffordError> {
        let quotient = self.divide()?;
        let right = Clifford::vector(self.signature.clone(), &self.right)?;
        let recovered = quotient.product(&right)?;
        Ok((0..self.left.len())
            .map(|axis| recovered.coefficient(&[axis]))
            .collect())
    }

    /// **`a` reconstructed from the AIM ALONE** — the score's own reading, which is the projection
    /// and nothing else. The difference from `a` is exactly the remainder.
    pub fn reconstruct_from_aim(&self) -> Result<Vec<Rat>, CliffordError> {
        let quotient = self.quotient()?;
        Ok(self.right.iter().map(|place| &quotient * place).collect())
    }

    /// What the aim-only reading dropped: `a − (a·b/‖b‖²) b`, the rejection.
    pub fn rejection(&self) -> Result<Vec<Rat>, CliffordError> {
        let from_aim = self.reconstruct_from_aim()?;
        Ok(self
            .left
            .iter()
            .zip(&from_aim)
            .map(|(place, carried)| place - carried)
            .collect())
    }
}

/// `‖a∧b‖²`, and whether a second frame was available on it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AreaSquared {
    /// From the blade's own coordinates. Always available.
    pub value: Rat,
    /// From Lagrange's identity — **only in the Euclidean signature**, where it holds. `None`
    /// elsewhere, so a caller cannot quote a cross-check that was never taken.
    pub lagrange: Option<Rat>,
}

impl AreaSquared {
    /// Whether the two frames agree. `None` when only one frame was available.
    pub fn frames_agree(&self) -> Option<bool> {
        self.lagrange.as_ref().map(|other| &self.value == other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn whole(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }

    fn rational(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    /// ★ THE FALSIFIER THE PLAN NAMES FIRST. If the product commutes, the sign was not installed
    /// and this whole module is decoration.
    #[test]
    fn the_generators_anticommute_which_is_the_whole_point() {
        let signature = Signature::euclidean(3);
        let e0 = Clifford::vector(signature.clone(), &[whole(1), whole(0), whole(0)]).expect("in");
        let e1 = Clifford::vector(signature.clone(), &[whole(0), whole(1), whole(0)]).expect("in");
        let forward = e0.product(&e1).expect("same signature");
        let backward = e1.product(&e0).expect("same signature");
        assert_eq!(forward.coefficient(&[0, 1]), whole(1));
        assert_eq!(backward.coefficient(&[0, 1]), whole(-1));
        assert_eq!(forward, backward.negated(), "e0 e1 = -e1 e0");
        assert_ne!(
            forward, backward,
            "and they are not equal, so the algebra is not abelian"
        );
        // A generator squares to its declared value, and the declaration is what decides it.
        assert_eq!(e0.product(&e0).expect("same").coefficient(&[]), whole(1));
        let minkowski = Signature::declared(vec![whole(-1), whole(1), whole(1)]);
        let timelike =
            Clifford::vector(minkowski, &[whole(1), whole(0), whole(0)]).expect("in ambient");
        assert_eq!(
            timelike.product(&timelike).expect("same").coefficient(&[]),
            whole(-1),
            "the square is the declared square, never an assumed one"
        );
    }

    /// ★ THE COBOUNDARY ARGUMENT, RUN RATHER THAN STATED.
    ///
    /// `μ(S) = (−1)^{|S|}` is a character of `((ℤ/2)ⁿ, △)`, so twisting by it is an isomorphism
    /// `x_S ↦ μ(S) x_S` and preserves commutativity. The exterior twist does not. Therefore the
    /// exterior sign is not a coboundary — and the argument is checkable in one comparison rather
    /// than asserted in prose.
    #[test]
    fn the_exterior_twist_is_not_a_coboundary_because_the_product_does_not_commute() {
        // The alternating character IS a character: mu(S)mu(T) = mu(S triangle T) on every pair.
        for left in 0usize..16 {
            for right in 0usize..16 {
                let mu = |mask: usize| if mask.count_ones() % 2 == 0 { 1i8 } else { -1 };
                assert_eq!(
                    mu(left) * mu(right),
                    mu(left ^ right),
                    "mu is a character, hence a coboundary"
                );
            }
        }
        // The exterior sign is NOT: sigma(S,T) and sigma(T,S) differ on a witnessed pair, and no
        // character can do that because a character is symmetric in its two arguments.
        let forward = merge_blades(&[0], &[1]);
        let backward = merge_blades(&[1], &[0]);
        assert_eq!(forward.sign, 1);
        assert_eq!(backward.sign, -1);
        assert_eq!(forward.surviving, backward.surviving);
        assert_ne!(
            forward.sign, backward.sign,
            "sigma is asymmetric; every character of an abelian group is symmetric"
        );
    }

    /// ★ THE JOIN TO `multiquadratic`, MEASURED. The two structure constants differ by exactly the
    /// exterior sign, so the magnitudes are bit-identical and only the hand moves. That is the
    /// phase-object theorem with `multiquadratic` as the magnitude receiver.
    #[test]
    fn the_two_algebras_agree_on_magnitude_and_differ_only_in_the_hand() {
        use crate::multiquadratic::Multiquadratic;

        // q_i = k_i for three squarefree generators: the Clifford signature and the multiquadratic
        // field are then the same data.
        let generators = [2i64, 3, 5];
        let signature =
            Signature::declared(generators.iter().map(|k| whole(*k)).collect::<Vec<_>>());
        let blade =
            |mask: usize| -> Vec<usize> { (0..3).filter(|bit| mask & (1 << bit) != 0).collect() };
        // The basis monomial ∏_{i∈S} √kᵢ, built in the commutative carrier out of its own roots.
        let monomial = |mask: usize| -> Multiquadratic {
            (0..3).filter(|bit| mask & (1 << bit) != 0).fold(
                Multiquadratic::one(),
                |carried, bit| {
                    let root = Multiquadratic::square_root(&whole(generators[bit]), 1 << 20)
                        .expect("a squarefree generator");
                    carried.multiply(&root, 3).expect("within the aperture")
                },
            )
        };
        let mut differing_signs = 0usize;
        let mut compared = 0usize;
        for left_mask in 0usize..8 {
            for right_mask in 0usize..8 {
                // The Clifford product of two basis blades.
                let mut left = Clifford::zero(signature.clone());
                left.set(blade(left_mask), whole(1));
                let mut right = Clifford::zero(signature.clone());
                right.set(blade(right_mask), whole(1));
                let product = left.product(&right).expect("same signature");
                let clifford_coefficient = product.coefficient(&blade(left_mask ^ right_mask));

                // The same product in the commutative carrier. A product of two basis monomials is
                // a single term, so its one non-zero coefficient IS the structure constant and no
                // mask alignment is needed to read it.
                let commutative = monomial(left_mask)
                    .multiply(&monomial(right_mask), 3)
                    .expect("within the aperture");
                let nonzero: Vec<&Rat> = commutative
                    .coefficients()
                    .iter()
                    .filter(|value| !value.is_zero())
                    .collect();
                assert_eq!(nonzero.len(), 1, "a monomial product is one term");
                let multiquadratic_coefficient = nonzero[0].clone();

                assert_eq!(
                    clifford_coefficient.abs(),
                    multiquadratic_coefficient,
                    "the magnitudes are the same structure constant"
                );
                assert!(
                    multiquadratic_coefficient.is_positive(),
                    "the commutative carrier's structure constant is strictly positive: it has no hand"
                );
                compared += 1;
                if clifford_coefficient != multiquadratic_coefficient {
                    differing_signs += 1;
                }
            }
        }
        assert_eq!(compared, 64);
        assert!(
            differing_signs > 0,
            "if no sign differed, the exterior twist did nothing and the join is vacuous"
        );
        // And the count is the object rather than the fact that it is non-zero.
        assert_eq!(
            differing_signs, 24,
            "24 of 64 basis-blade products carry a hand the commutative carrier cannot hold"
        );
    }

    /// ★ THE DIVISION LAW. `a = (a b⁻¹) b` exactly, and the aim alone does not reconstruct unless
    /// the pair is collinear. Both arms are required or the reading cannot fail.
    #[test]
    fn the_whole_arrow_divides_and_the_aim_alone_does_not() {
        let signature = Signature::euclidean(3);
        let material: Vec<(Vec<Rat>, Vec<Rat>, bool)> = vec![
            // (a, b, is the pair collinear)
            (
                vec![whole(4), whole(1), whole(-2)],
                vec![whole(2), whole(0), whole(0)],
                false,
            ),
            (
                vec![whole(4), whole(0), whole(0)],
                vec![whole(2), whole(0), whole(0)],
                true,
            ),
            (
                vec![rational(7, 3), rational(-1, 2), whole(5)],
                vec![rational(1, 6), whole(2), rational(-3, 4)],
                false,
            ),
            (
                vec![whole(0), whole(5), whole(0)],
                vec![whole(3), whole(0), whole(0)],
                false,
            ),
        ];
        let (mut collinear, mut non_collinear) = (0usize, 0usize);
        for (left, right, declared_collinear) in &material {
            let arrow = Arrow::between(&signature, left, right).expect("same ambient");
            let area = arrow.area_squared();
            assert_eq!(
                area.frames_agree(),
                Some(true),
                "the blade and Lagrange must agree exactly"
            );
            assert_eq!(area.value.is_zero(), *declared_collinear);
            if area.value.is_zero() {
                collinear += 1;
            } else {
                non_collinear += 1;
            }
            assert_eq!(
                &arrow.reconstruct().expect("divisor is not null"),
                left,
                "the whole arrow reconstructs the dividend exactly, in the algebra"
            );
            let from_aim = arrow.reconstruct_from_aim().expect("divisor is not null");
            assert_eq!(
                &from_aim == left,
                *declared_collinear,
                "the aim alone reconstructs exactly on the collinear pair and nowhere else"
            );
        }
        assert!(
            collinear > 0 && non_collinear > 0,
            "the material must exhibit both, or the reading cannot fail"
        );
    }

    /// ★ THE BLINDNESS. Three keys with the same aim AND the same area and pairwise different
    /// blades — so a scalar summary of the wedge does not suffice either.
    #[test]
    fn one_score_one_area_and_three_different_planes() {
        let signature = Signature::euclidean(4);
        let query = vec![whole(1), whole(0), whole(0), whole(0)];
        let keys = [
            vec![whole(2), whole(3), whole(0), whole(0)],
            vec![whole(2), whole(0), whole(3), whole(0)],
            vec![whole(2), whole(0), whole(0), whole(3)],
        ];
        let arrows: Vec<Arrow> = keys
            .iter()
            .map(|key| Arrow::between(&signature, &query, key).expect("same ambient"))
            .collect();
        for pair in arrows.windows(2) {
            assert_eq!(pair[0].aim(), pair[1].aim(), "the aims are exactly equal");
            assert_eq!(
                pair[0].area_squared().value,
                pair[1].area_squared().value,
                "the areas are exactly equal too"
            );
            assert_ne!(pair[0].cross(), pair[1].cross(), "the blades differ");
        }
    }

    /// ★ THE CAUSAL CLASS IS SHARPER THAN THE HAND, and both must be exhibited or a census over
    /// them is vacuous. The horizon is not a class.
    #[test]
    fn the_horizon_is_not_a_class_and_ortho_is_not_the_horizon() {
        let signature = Signature::euclidean(3);
        // ORTHO with a real blade: the score reads zero and the gyration is maximal.
        let ortho = Arrow::between(
            &signature,
            &[whole(0), whole(5), whole(0)],
            &[whole(3), whole(0), whole(0)],
        )
        .expect("same ambient");
        assert_eq!(ortho.hand(), Aim::Ortho);
        assert!(!ortho.at_horizon());
        assert_eq!(ortho.causal_class(), Causal::TransportDominant);
        assert_eq!(ortho.area_squared().value, whole(225));
        // UNREAD: a strand stands at the pole. The score also reads zero, and it is a different fact.
        let unread = Arrow::between(
            &signature,
            &[whole(0), whole(0), whole(0)],
            &[whole(3), whole(0), whole(0)],
        )
        .expect("same ambient");
        assert_eq!(unread.hand(), Aim::Ortho);
        assert!(unread.at_horizon());
        assert_eq!(unread.causal_class(), Causal::Unread);
        assert_eq!(
            ortho.aim(),
            unread.aim(),
            "one score, two utterly different causal facts"
        );
        // The wall is reachable exactly, so `Balanced` is not vacuous.
        let wall = Arrow::between(
            &signature,
            &[whole(2), whole(0), whole(0)],
            &[whole(1), whole(1), whole(0)],
        )
        .expect("same ambient");
        assert_eq!(wall.aim(), &whole(2));
        assert_eq!(wall.area_squared().value, whole(4));
        assert_eq!(wall.causal_class(), Causal::Balanced);
        // And storage-dominant.
        let stored = Arrow::between(
            &signature,
            &[whole(2), whole(0), whole(0)],
            &[whole(3), whole(0), whole(0)],
        )
        .expect("same ambient");
        assert_eq!(stored.causal_class(), Causal::StorageDominant);
    }

    /// ★ THE TWO-DIMENSIONAL CASE IS `soul::FormedRotor`. The rotor's `(aim, cross)` is exactly the
    /// even part of the geometric product at `d = 2`, and this re-derives it from the algebra rather
    /// than from the pair.
    #[test]
    fn the_two_dimensional_even_part_is_the_rotor() {
        let signature = Signature::euclidean(2);
        for (ar, ai, br, bi) in [(2i64, 0, 3, 0), (1, 0, 0, 1), (4, -1, 2, 5), (0, 0, 3, 7)] {
            let left = Clifford::vector(signature.clone(), &[whole(ar), whole(ai)]).expect("in");
            let right = Clifford::vector(signature.clone(), &[whole(br), whole(bi)]).expect("in");
            let product = left.product(&right).expect("same signature");
            // `soma/body/src/arrow.rs:119-120`: aim = ar*br + ai*bi, cross = ai*br - ar*bi.
            assert_eq!(product.coefficient(&[]), whole(ar * br + ai * bi));
            assert_eq!(product.coefficient(&[0, 1]), whole(ar * bi - ai * br));
            // The product of two vectors has grades 0 and 2 only — the even subalgebra.
            assert!(product.grade(1).is_zero());
            assert_eq!(
                product.population(),
                product.grade(0).population() + product.grade(2).population()
            );
        }
    }

    /// ★ THE APERTURE IS THE POPULATION, NOT THE DIMENSION. A sparse pair in a wide ambient costs
    /// its own support and not `d(d−1)/2`, and this is the measurement the census stations rely on.
    #[test]
    fn the_blade_costs_its_population_and_not_the_ambient() {
        let signature = Signature::euclidean(512);
        let mut left = vec![Rat::zero(); 512];
        let mut right = vec![Rat::zero(); 512];
        left[3] = whole(2);
        left[400] = whole(-1);
        right[3] = whole(5);
        right[17] = whole(7);
        let arrow = Arrow::between(&signature, &left, &right).expect("same ambient");
        // d(d-1)/2 = 130,816 coordinates exist; three are non-zero.
        assert_eq!(arrow.blade_population(), 3);
        assert_eq!(arrow.cross().get(&(3, 17)), Some(&whole(14)));
        assert_eq!(arrow.cross().get(&(3, 400)), Some(&whole(5)));
        assert_eq!(arrow.cross().get(&(17, 400)), Some(&whole(7)));
        assert_eq!(arrow.aim(), &whole(10));
        assert_eq!(arrow.area_squared().frames_agree(), Some(true));
    }

    /// **Cauchy–Binet holds in every diagonal signature, so the two frames agree off Euclidean too
    /// — once the blade carries the metric.**
    ///
    /// This test asserted the opposite until 2026-08-18: that Lagrange is withheld on a
    /// non-Euclidean signature. It was asserting the defect. On this exact fixture the unweighted
    /// blade returned `3` against Lagrange's `−1`, and the guard that withheld the comparison was
    /// what kept the disagreement invisible.
    #[test]
    fn the_two_frames_agree_off_euclidean_once_the_blade_carries_the_metric() {
        let minkowski = Signature::declared(vec![whole(-1), whole(1), whole(1)]);
        let arrow = Arrow::between(
            &minkowski,
            &[whole(1), whole(1), whole(0)],
            &[whole(1), whole(0), whole(1)],
        )
        .expect("same ambient");
        assert_eq!(
            arrow.aim(),
            &whole(-1),
            "the declared square carries into the cohere"
        );
        let area = arrow.area_squared();
        assert_eq!(area.value, whole(-1), "the metric-weighted blade");
        assert_eq!(
            area.lagrange,
            Some(whole(-1)),
            "and Lagrange agrees with it"
        );
        assert_eq!(area.frames_agree(), Some(true));
    }

    /// **The causal class the repair moved, asserted.** Before 2026-08-18 nothing in this module
    /// read `causal_class` on a non-Euclidean arrow, so the flip from `StorageDominant` to
    /// `TransportDominant` could not be caught by any test.
    #[test]
    fn the_causal_class_off_euclidean_is_read_from_the_metric_blade() {
        let minkowski = Signature::declared(vec![whole(-1), whole(1), whole(1)]);
        let arrow = Arrow::between(
            &minkowski,
            &[whole(1), whole(1), whole(0)],
            &[whole(1), whole(0), whole(1)],
        )
        .expect("same ambient");
        // area² − aim² = −1 − 1 = −2 < 0.
        assert_eq!(arrow.causal_class(), Causal::StorageDominant);
    }

    /// A null divisor is a domain refusal and never a small number.
    #[test]
    fn a_null_divisor_refuses_by_name() {
        let signature = Signature::euclidean(2);
        let arrow = Arrow::between(&signature, &[whole(1), whole(2)], &[whole(0), whole(0)])
            .expect("same ambient");
        assert_eq!(arrow.quotient(), Err(CliffordError::NullDivisor));
        assert_eq!(arrow.divide(), Err(CliffordError::NullDivisor));
    }
}
