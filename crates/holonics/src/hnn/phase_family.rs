//! **The phase family: the receiving map's phase rows that the deposited comparisons leave open,
//! their image at a feature, and the outcome blocks that image meets.**
//!
//! [definition; agent-inferred, October 8] A receiving map's phase rows read, for the receiving
//! face's class `c` at the realified native feature `x ∈ ℚⁿ`, the lifted phase `y_c = v_cᵀx / 2` in
//! turns (`Im f_c = v_cᵀx` and `φ^H_c = Im f_c / 2`; [`crate::hnn::ratio`], "the covector's odometer
//! chart"). An actually reached receipt `k` has a weight `w ≥ 0`, the feature `x_k` it was read at,
//! the observed class masses `q_k` (nonnegative, summing to 1) and the lifted doubled targets
//! `t_kc = 2 φ̂_kc`. The phase part of its comparison is `½ q Δ²` with `Δ = φ̂ − y` the gap in turns
//! ([`crate::hnn::ratio::ReceivingFaceRatio::excess`]), which in the rows is
//!
//! ```text
//! (w q_kc / 8) (t_kc − v_cᵀ x_k)²        Δ = (t − vᵀx)/2 ,  ½ q Δ² = (q/8)(t − vᵀx)²
//! ```
//!
//! and whose gradient in `v_c`, `−(w q_kc / 4)(t_kc − v_cᵀ x_k) x_k`, is the deposited phase covector
//! (the covector's phase part `−½ q_c Δ_c` on `Im f_c`, times the feature).
//!
//! [definition; agent-inferred, October 8] **The sufficient statistic** ([`PhaseStatistics`]). The
//! cumulative comparison of the reached receipts is exactly quadratic in the phase rows `V = (v_c)`,
//!
//! ```text
//! J(V) = Σ_c (1/8) ( v_cᵀ S_c v_c − 2 v_cᵀ m_c + s_c )
//! S_c = Σ_k w q_kc x_k x_kᵀ   (n×n)     m_c = Σ_k w q_kc t_kc x_k   (n)     s_c = Σ_k w q_kc t_kc²
//! ```
//!
//! so `(S_c, m_c, s_c)` per class determine `J` at every `V`, and absorbing a receipt is exact
//! addition: the order of absorption is immaterial and no receipt, tape or journal is kept (the
//! retention contract: a quotient sufficient for the admitted comparison, not a record of fluxes).
//! The statistic carries the declared cell count `N = Σ_k w · #{c : q_kc > 0}`: the classes compared
//! at a receipt are those that carry observed mass, because a class of zero mass enters the
//! comparison with zero weight, and a categorical receipt compares its target class alone
//! ([`crate::hnn::ratio::HolonRatio::compare`] writes the phase part at the target class only). That
//! reading is the agent's inference, so `N` counts the cells that carried a comparison and is not
//! `K` times the weight, which `Σ_k w` already says.
//!
//! [definition; agent-inferred, October 8] **The declared family at tolerance `τ`**
//! ([`PhaseFamily`]). Under the receiving law's prior ridge `2^k I` (the normal law's founding
//! statistic `H₀ = 2^k I`, [`crate::hnn::constitution::NormalLaw::with_scaled_prior`]; here a
//! declared convention of the family that makes every `A_c` positive definite, not a deposited loss
//! term) set `A_c = S_c + 2^k I`. The ridged comparison
//! `G(V) = J(V) + (1/8) 2^k Σ_c |v_c|² = Σ_c (1/8)(v_cᵀ A_c v_c − 2 v_cᵀ m_c + s_c)` has the exact
//! minimizer `v̂_c = A_c⁻¹ m_c` and the exact minimum `L* = Σ_c (1/8)(s_c − v̂_cᵀ m_c)`, and
//!
//! ```text
//! F_τ = { V : G(V) ≤ L* + τ } = { V : Σ_c (1/8)(v_c − v̂_c)ᵀ A_c (v_c − v̂_c) ≤ τ }.
//! ```
//!
//! [definition; agent-inferred, October 8] **Its image at a feature is an axis-aligned ellipsoid in
//! the class phases** ([`PhaseImage`]):
//!
//! ```text
//! E(x) = { y ∈ ℚᴷ : Q(y) = Σ_c (y_c − ȳ_c)² / (2 ℓ_c) ≤ τ } ,   ȳ_c = v̂_cᵀx / 2 ,   ℓ_c = xᵀ A_c⁻¹ x
//! ```
//!
//! `ℓ_c` is the class leverage of the feature. *Derivation.* For a member write `u_c = v_c − v̂_c`
//! and `d_c = u_cᵀx / 2 = y_c − ȳ_c`. Cauchy–Schwarz in the `A_c` metric gives
//! `(u_cᵀx)² ≤ (u_cᵀ A_c u_c)(xᵀ A_c⁻¹ x)`, so `(1/8) u_cᵀ A_c u_c ≥ d_c² / (2 ℓ_c)`, with equality at
//! `u_c = 2 d_c A_c⁻¹ x / ℓ_c`, which is rational when `d_c` is. The classes are independent, so a
//! phase vector `y` is read by a member of `F_τ` exactly when `Σ_c d_c² / (2 ℓ_c) ≤ τ`. Since `A_c`
//! is positive definite, `ℓ_c = 0` exactly when `x = 0`, and then the class (every class) reads the
//! single point `ȳ_c = 0`: the image is that point. No square root is ever taken: a radius
//! `r_c = √(2 τ ℓ_c)` is only compared as its square.
//!
//! [definition; agent-inferred, October 8] **The leverage at a fixed feature contracts exactly.**
//! Absorbing a receipt of weight `w`, mass `q_c` at the feature `x` itself changes `A_c` to
//! `A_c + w q_c x xᵀ`, and `(A_c + w q_c x xᵀ)(A_c⁻¹x) = (1 + w q_c ℓ_c) x`, so
//! `A′_c⁻¹ x = A_c⁻¹ x / (1 + w q_c ℓ_c)` and `ℓ′_c = ℓ_c / (1 + w q_c ℓ_c)` (Sherman–Morrison).
//! This is an identity about the declared shape at that feature. It is not a claim that the image
//! shrinks or nests: the centre `ȳ` moves, `τ` is declared, and a different feature is not
//! contracted.
//!
//! [definition; agent-inferred, October 8] **Outcome blocks at the receiver's grain `1/L`**
//! ([`PhaseImage::blocks`]). Per class the lifted phase line is cut into the half-open arcs
//! `[j/L, (j+1)/L)`, `j ∈ ℤ` (the lifted form of [`crate::receiver::face::GrainCell`]: `j` is its
//! carry times `L` plus its phase class); a block is a tuple `(j_c)`, the box `B = Π_c [a_c, b_c)`.
//! The block meets `E(x)` exactly when some `y ∈ B` has `Q(y) ≤ τ`. `Q` is a sum of one-class
//! terms, each minimized over its arc at the clamp of `ȳ_c` into the closed arc, so
//!
//! ```text
//! inf_B Q = Σ_c (clamp(ȳ_c, [a_c, b_c]) − ȳ_c)² / (2 ℓ_c)
//! the infimum is attained  ⇔  ȳ_c < b_c for every class   (a clamp onto an excluded upper face b_c is approached, never reached)
//! B meets E(x)  ⇔  inf_B Q < τ ,   or   inf_B Q = τ and the infimum is attained
//! ```
//!
//! A class with `ℓ_c = 0` requires `ȳ_c ∈ [a_c, b_c)` exactly. Per class the candidate arcs are
//! those whose own term is admitted (below `τ`, or equal to `τ` and attained), which is the squared
//! distance from `ȳ_c` to the arc against `r_c² = 2 τ ℓ_c`; the term never falls away from the
//! arc `⌊L ȳ_c⌋` that holds the centre, so the range is found by stepping outward until the first
//! failure. The blocks are then walked class by class with the partial infimum and the attainment
//! so far: the partial infimum only grows and attainment only fails, so a failing prefix is
//! pruned, and the kept blocks come out in ascending lexicographic order. The count of blocks is
//! the declared `τ` and `L`'s consequence; nothing here caps it.
//!
//! [definition; agent-inferred, October 8] **Two feasible witnesses** ([`PhaseImage::witnesses`]).
//! For the two least kept blocks, a rational point of each inside `E(x)`: the clamped point, and
//! where a coordinate sits on an excluded upper face `b_c`, every such coordinate moved into the
//! arc by one common `δ = (b − a) / 2^i` for the least `i ≥ 1` with `Q ≤ τ`. It terminates: such a
//! block was kept only with `inf_B Q < τ`, and `Q` is continuous at the clamped point. Each witness
//! is realized by a member of `F_τ` (the equality case above).
//!
//! [definition; agent-inferred, October 8] **What this is not.** `F_τ` is a declared inner family
//! of phase rows around the minimizer of the reached receipts. The blocks its image meets are
//! those some member of that declared family reads; they are not a distribution over outcomes and
//! carry no probability, `Σ_c ℓ_c` ([`PhaseImage::total_leverage`]) is a declared leverage
//! convention of a probe and not information, the truth is not claimed to lie inside `F_τ`, and
//! nothing here claims that absorbing receipts shrinks the image or removes a block.
//!
//! [definition; agent-inferred, October 8] **The object.** The computational object is the helical
//! pair interaction; this owner serves the receiver's faces-and-placement object: the phase reading
//! of a receiving face at a declared grain, of the winding guide's six general objects
//! ([`WINDING_CARRY_AND_PLACEMENT`](../../../../docs/WINDING_CARRY_AND_PLACEMENT.md)). Helix, pair,
//! cell holonomy, tube and tower thread stay attached and unchanged. The construction is the same
//! for every boundary chart, since a class phase is a receiving face's phase whatever it encodes:
//! nothing here reads a byte, a pixel or a sample.
//!
//! [definition; agent-inferred, October 8] **Recorded failures checked**
//! ([lessons record](../../../../research/records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)).
//! Lesson 4 (no tape or index): only `(S_c, m_c, s_c, N)` is held. Lesson 5 (no authored routine):
//! the family is the exact normal equations of the machine's own deposited comparison, not a task's
//! solution routine, and nothing here is handed to the machine as a receiver or predictor. Lesson 7
//! (output decides): no code length or bit count is reported here. Lesson 9 (a refusal changes the
//! law, never the limit): every refusal is typed and no limit exists to raise. Lesson 11 (think in
//! the objects): the statement is in the family, its image and its blocks, and the arrays are only
//! its realization.
//!
//! [open] The Lean counterpart is owed (#62): the Cauchy–Schwarz image, the Sherman–Morrison
//! contraction and the half-open block rule; the atlas rows are owed with the first consumer. The
//! exact reference here is `Rat` throughout and nothing in it consumes a float.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use thiserror::Error;

use crate::ratio::{Rat, integer, rat};

/// Every refusal of the phase family. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum PhaseFamilyError {
    /// A vector or matrix of the wrong extent: `expected` entries were declared, `found` given.
    #[error("expected {expected} entries, found {found}")]
    Shape { expected: usize, found: usize },
    /// A receipt's weight is nonnegative: a negative weight would subtract a comparison.
    #[error("a receipt's weight must be nonnegative")]
    NegativeWeight,
    /// The observed class masses are nonnegative and sum to exactly one.
    #[error("the observed class masses must be nonnegative and sum to one")]
    NotADistribution,
    /// The tolerance of the family is nonnegative.
    #[error("the family's tolerance must be nonnegative")]
    NegativeTolerance,
    /// The receiver's grain `L` of an outcome block is a positive integer.
    #[error("the grain of an outcome block must be a positive integer")]
    ZeroGrain,
    /// A shape matrix had a zero pivot. `A_c = S_c + 2^k I` is positive definite, so this cannot
    /// arise from the family's own statistics.
    #[error("the shape matrix is singular")]
    Singular,
    /// Restored parts that no sequence of receipts produces: an asymmetric Gram, a negative
    /// second or a negative cell count.
    #[error("the restored phase statistic is off its form")]
    Malformed,
}

// -------------------------------------------------------------------------------------------
// exact helpers (the family's own small linear algebra over `Rat`)

/// `1/2`: the phase in turns is half the row's reading, `y = v·x / 2`.
fn half() -> Rat {
    rat(1, 2)
}

/// `1/8 = ½ · (½)²`: the phase comparison `½ q Δ²` in the doubled lift, `Δ = (t − v·x)/2`.
fn eighth() -> Rat {
    rat(1, 8)
}

/// `Σ_i left_i right_i`.
fn dot(left: &[Rat], right: &[Rat]) -> Rat {
    let mut total = Rat::zero();
    for (a, b) in left.iter().zip(right) {
        total += a * b;
    }
    total
}

/// `uᵀ A u` for a square `A` given by rows.
fn quadratic(shape: &[Vec<Rat>], vector: &[Rat]) -> Rat {
    let mut total = Rat::zero();
    for (row, entry) in shape.iter().zip(vector) {
        total += entry * dot(row, vector);
    }
    total
}

/// The declared extent against the one given.
fn require_extent(expected: usize, found: usize) -> Result<(), PhaseFamilyError> {
    if expected == found {
        Ok(())
    } else {
        Err(PhaseFamilyError::Shape { expected, found })
    }
}

/// **Whether a square matrix is symmetric positive semidefinite**, exactly: symmetric
/// elimination without pivoting (`LDLᵀ` over `ℚ`), refusing a negative pivot, and at a zero pivot
/// requiring the rest of its row to vanish (a semidefinite matrix with a zero diagonal entry has
/// that whole row and column zero). No root or float is formed.
pub(crate) fn positive_semidefinite(matrix: &[Vec<Rat>]) -> bool {
    let n = matrix.len();
    if matrix.iter().any(|row| row.len() != n) {
        return false;
    }
    for i in 0..n {
        for j in 0..i {
            if matrix[i][j] != matrix[j][i] {
                return false;
            }
        }
    }
    let mut work: Vec<Vec<Rat>> = matrix.to_vec();
    for k in 0..n {
        let pivot = work[k][k].clone();
        if pivot.is_negative() {
            return false;
        }
        if pivot.is_zero() {
            if work[k][k + 1..].iter().any(|entry| !entry.is_zero()) {
                return false;
            }
            continue;
        }
        for i in k + 1..n {
            let factor = &work[i][k] / &pivot;
            if factor.is_zero() {
                continue;
            }
            for j in k + 1..n {
                let delta = &factor * &work[k][j];
                work[i][j] -= delta;
            }
        }
    }
    true
}

/// **The exact solution of `A z = b`** by Gauss–Jordan over `ℚ`, for a square `A` of the extent
/// of `b`. A pivot is the first nonzero entry at or below the diagonal; the refusal is
/// [`PhaseFamilyError::Singular`] when a column has none, which a positive definite `A` never has.
fn solve(shape: &[Vec<Rat>], rhs: &[Rat]) -> Result<Vec<Rat>, PhaseFamilyError> {
    let extent = shape.len();
    let mut rows: Vec<Vec<Rat>> = shape
        .iter()
        .zip(rhs)
        .map(|(row, target)| {
            let mut augmented = row.clone();
            augmented.push(target.clone());
            augmented
        })
        .collect();
    for column in 0..extent {
        let Some(pivot_row) = (column..extent).find(|&r| !rows[r][column].is_zero()) else {
            return Err(PhaseFamilyError::Singular);
        };
        rows.swap(column, pivot_row);
        let pivot = rows[column][column].clone();
        let normalised: Vec<Rat> = rows[column].iter().map(|entry| entry / &pivot).collect();
        for r in 0..extent {
            if r == column {
                continue;
            }
            let factor = rows[r][column].clone();
            if factor.is_zero() {
                continue;
            }
            // The pivot row is zero left of `column`: earlier columns are already eliminated.
            for k in column..=extent {
                let delta = &factor * &normalised[k];
                rows[r][k] -= delta;
            }
        }
        rows[column] = normalised;
    }
    Ok(rows.iter().map(|row| row[extent].clone()).collect())
}

// -------------------------------------------------------------------------------------------
// the sufficient statistic

/// [definition; agent-inferred, October 8] **The sufficient statistic of the phase comparison**
/// (module header): per class the Gram `S_c = Σ_k w q_kc x_k x_kᵀ`, the moment
/// `m_c = Σ_k w q_kc t_kc x_k` and the second `s_c = Σ_k w q_kc t_kc²`, with the declared cell
/// count `N = Σ_k w · #{c : q_kc > 0}`. Absorbing a receipt is exact addition; no sample is
/// retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhaseStatistics {
    classes: usize,
    features: usize,
    gram: Vec<Vec<Vec<Rat>>>,
    moment: Vec<Vec<Rat>>,
    second: Vec<Rat>,
    cells: Rat,
}

impl PhaseStatistics {
    /// The statistic before any receipt reached the locus: every entry zero.
    pub fn founded(classes: usize, features: usize) -> Self {
        Self {
            classes,
            features,
            gram: vec![vec![vec![Rat::zero(); features]; features]; classes],
            moment: vec![vec![Rat::zero(); features]; classes],
            second: vec![Rat::zero(); classes],
            cells: Rat::zero(),
        }
    }

    /// **A saved statistic restored exactly** from its parts: per class the Gram `S_c` (`n×n`),
    /// the moment `m_c` (`n`) and the second `s_c`, with the cell count `N`. A sum of receipts is
    /// `Σ w q [x; t][x; t]ᵀ` with `w q ≥ 0`, so its augmented statistic `[[S_c, m_c], [m_cᵀ, s_c]]`
    /// is symmetric positive semidefinite: the checked necessary moment condition. The count is
    /// `N = Σ w·#{c : q_c > 0} ≥ 0`, and `N = 0` forces every weighted increment to zero, so a
    /// nonzero statistic with `N = 0` is refused too. These are necessary conditions of a producing
    /// passage, not a proof that one exists for every accepted state (Epime's review, October 8).
    /// Refused unless every extent matches the declared classes and features, every augmented
    /// statistic passes the exact test ([`positive_semidefinite`]), the cell count is nonnegative,
    /// and a zero count carries zero statistics. Without the test a restored indefinite Gram would
    /// give the family no minimum (`S = −2` at the unit prior returned a false minimum and a negative
    /// leverage).
    pub fn from_parts(
        classes: usize,
        features: usize,
        gram: Vec<Vec<Vec<Rat>>>,
        moment: Vec<Vec<Rat>>,
        second: Vec<Rat>,
        cells: Rat,
    ) -> Result<Self, PhaseFamilyError> {
        require_extent(classes, gram.len())?;
        require_extent(classes, moment.len())?;
        require_extent(classes, second.len())?;
        for ((class_gram, class_moment), class_second) in gram.iter().zip(&moment).zip(&second) {
            require_extent(features, class_gram.len())?;
            require_extent(features, class_moment.len())?;
            for row in class_gram {
                require_extent(features, row.len())?;
            }
            let augmented: Vec<Vec<Rat>> = class_gram
                .iter()
                .zip(class_moment)
                .map(|(row, moment)| {
                    let mut row = row.clone();
                    row.push(moment.clone());
                    row
                })
                .chain(std::iter::once({
                    let mut row = class_moment.clone();
                    row.push(class_second.clone());
                    row
                }))
                .collect();
            if !positive_semidefinite(&augmented) {
                return Err(PhaseFamilyError::Malformed);
            }
        }
        if cells.is_negative() {
            return Err(PhaseFamilyError::Malformed);
        }
        let carries = gram.iter().flatten().flatten().any(|entry| !entry.is_zero())
            || moment.iter().flatten().any(|entry| !entry.is_zero())
            || second.iter().any(|entry| !entry.is_zero());
        if cells.is_zero() && carries {
            return Err(PhaseFamilyError::Malformed);
        }
        Ok(Self {
            classes,
            features,
            gram,
            moment,
            second,
            cells,
        })
    }

    /// **Its exact bits**: every retained rational (each class's Gram, moment and second, and the
    /// cell count) by its numerator's and denominator's bits. A fixed extent is not a fixed memory:
    /// the rationals grow, and the owner that retains them charges this census.
    pub fn bits(&self) -> u64 {
        let bits = |value: &Rat| value.numer().bits() + value.denom().bits();
        self.gram.iter().flatten().flatten().map(bits).sum::<u64>()
            + self.moment.iter().flatten().map(bits).sum::<u64>()
            + self.second.iter().map(bits).sum::<u64>()
            + bits(&self.cells)
    }

    /// The number of classes `K`.
    pub fn classes(&self) -> usize {
        self.classes
    }

    /// The feature extent `n`.
    pub fn features(&self) -> usize {
        self.features
    }

    /// `S_c`, the class's Gram, `n` rows of `n`. As with slice indexing, `class < classes()` is the
    /// caller's precondition (here and in [`PhaseStatistics::moment`] and
    /// [`PhaseStatistics::second`]).
    pub fn gram(&self, class: usize) -> &[Vec<Rat>] {
        &self.gram[class]
    }

    /// `m_c`, the class's moment, `n` entries.
    pub fn moment(&self, class: usize) -> &[Rat] {
        &self.moment[class]
    }

    /// `s_c`, the class's second.
    pub fn second(&self, class: usize) -> &Rat {
        &self.second[class]
    }

    /// `N`, the declared cell count: each receipt's weight times the classes that carried mass.
    pub fn cells(&self) -> &Rat {
        &self.cells
    }

    /// **Absorb one reached receipt**: weight `w ≥ 0`, the feature `x` (`n` entries), the observed
    /// class masses `q` (`K` entries, nonnegative, summing to 1) and the lifted doubled targets `t`
    /// (`K` entries). Adds `w q_c x xᵀ` to `S_c`, `w q_c t_c x` to `m_c` and `w q_c t_c²` to `s_c`
    /// for every class of positive mass (a zero-mass class contributes nothing, so its target is
    /// never read), and `w` times their number to `N`. Every refusal leaves the statistic unchanged.
    pub fn absorb(
        &mut self,
        weight: &Rat,
        feature: &[Rat],
        masses: &[Rat],
        doubled_target: &[Rat],
    ) -> Result<(), PhaseFamilyError> {
        require_extent(self.features, feature.len())?;
        require_extent(self.classes, masses.len())?;
        require_extent(self.classes, doubled_target.len())?;
        if weight.is_negative() {
            return Err(PhaseFamilyError::NegativeWeight);
        }
        let mut total = Rat::zero();
        for mass in masses {
            if mass.is_negative() {
                return Err(PhaseFamilyError::NotADistribution);
            }
            total += mass;
        }
        if total != Rat::one() {
            return Err(PhaseFamilyError::NotADistribution);
        }
        let mut compared: usize = 0;
        for (class, mass) in masses.iter().enumerate() {
            if mass.is_zero() {
                continue;
            }
            compared += 1;
            let scale = weight * mass;
            let target = &doubled_target[class];
            let weighted = &scale * target;
            for (i, left) in feature.iter().enumerate() {
                let lever = &scale * left;
                for (j, right) in feature.iter().enumerate() {
                    self.gram[class][i][j] += &lever * right;
                }
                self.moment[class][i] += &weighted * left;
            }
            self.second[class] += &weighted * target;
        }
        self.cells += weight * Rat::from_integer(BigInt::from(compared));
        Ok(())
    }

    /// **The declared family at tolerance `tolerance = τ ≥ 0`** under the prior ridge
    /// `2^prior_scale I`: the shapes `A_c = S_c + 2^k I`, the exact minimizer `v̂_c = A_c⁻¹ m_c`
    /// and the exact minimum `L* = Σ_c (1/8)(s_c − v̂_cᵀ m_c)` (module header).
    pub fn family(
        &self,
        prior_scale: u32,
        tolerance: &Rat,
    ) -> Result<PhaseFamily, PhaseFamilyError> {
        if tolerance.is_negative() {
            return Err(PhaseFamilyError::NegativeTolerance);
        }
        let ridge = Rat::from_integer(BigInt::one() << prior_scale as usize);
        let mut shapes = Vec::with_capacity(self.classes);
        let mut minimizer = Vec::with_capacity(self.classes);
        let mut minimum = Rat::zero();
        for ((gram, moment), second) in self.gram.iter().zip(&self.moment).zip(&self.second) {
            let mut shape = gram.clone();
            for (i, row) in shape.iter_mut().enumerate() {
                row[i] += &ridge;
            }
            let centre = solve(&shape, moment)?;
            minimum += (second - dot(&centre, moment)) * eighth();
            shapes.push(shape);
            minimizer.push(centre);
        }
        Ok(PhaseFamily {
            features: self.features,
            minimizer,
            shapes,
            minimum,
            tolerance: tolerance.clone(),
        })
    }
}

// -------------------------------------------------------------------------------------------
// the declared family

/// [definition; agent-inferred, October 8] **The declared family `F_τ`** of phase rows
/// (module header): the minimizer rows `v̂_c`, the shapes `A_c`, the minimum `L*` and the
/// tolerance `τ`. A member is a set of phase rows `V` with
/// `Σ_c (1/8)(v_c − v̂_c)ᵀ A_c (v_c − v̂_c) ≤ τ`. It is declared, not inferred to contain any truth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhaseFamily {
    features: usize,
    minimizer: Vec<Vec<Rat>>,
    shapes: Vec<Vec<Vec<Rat>>>,
    minimum: Rat,
    tolerance: Rat,
}

impl PhaseFamily {
    /// The minimizer rows `v̂_c = A_c⁻¹ m_c`, one per class.
    pub fn minimizer(&self) -> &[Vec<Rat>] {
        &self.minimizer
    }

    /// The minimum `L* = Σ_c (1/8)(s_c − v̂_cᵀ m_c)` of the ridged comparison.
    pub fn minimum(&self) -> &Rat {
        &self.minimum
    }

    /// The tolerance `τ`.
    pub fn tolerance(&self) -> &Rat {
        &self.tolerance
    }

    /// **The excess of candidate phase rows over the minimum**:
    /// `Σ_c (1/8)(v_c − v̂_c)ᵀ A_c (v_c − v̂_c) = G(V) − L*`. The rows are a member of the family
    /// exactly when it is at most `τ`.
    pub fn excess(&self, rows: &[Vec<Rat>]) -> Result<Rat, PhaseFamilyError> {
        require_extent(self.minimizer.len(), rows.len())?;
        let mut total = Rat::zero();
        for ((row, centre), shape) in rows.iter().zip(&self.minimizer).zip(&self.shapes) {
            require_extent(self.features, row.len())?;
            let offset: Vec<Rat> = row.iter().zip(centre).map(|(v, c)| v - c).collect();
            total += quadratic(shape, &offset);
        }
        Ok(total * eighth())
    }

    /// **The image of the family at a feature**: the centre `ȳ_c = v̂_cᵀx / 2` and the class
    /// leverage `ℓ_c = xᵀ A_c⁻¹ x` of the ellipsoid `E(x)` (module header).
    pub fn image(&self, feature: &[Rat]) -> Result<PhaseImage, PhaseFamilyError> {
        require_extent(self.features, feature.len())?;
        let mut centre = Vec::with_capacity(self.minimizer.len());
        let mut leverage = Vec::with_capacity(self.minimizer.len());
        for (row, shape) in self.minimizer.iter().zip(&self.shapes) {
            centre.push(dot(row, feature) * half());
            let response = solve(shape, feature)?;
            leverage.push(dot(feature, &response));
        }
        Ok(PhaseImage {
            centre,
            leverage,
            tolerance: self.tolerance.clone(),
        })
    }
}

// -------------------------------------------------------------------------------------------
// the image and its blocks

/// [definition; agent-inferred, October 8] **The image `E(x)` of the family at a feature**: the
/// ellipsoid `{ y : Σ_c (y_c − ȳ_c)² / (2 ℓ_c) ≤ τ }` in the class phases (a class of leverage zero
/// reads its centre alone), held as its centre, its class leverages and its tolerance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhaseImage {
    centre: Vec<Rat>,
    leverage: Vec<Rat>,
    tolerance: Rat,
}

/// One class's arc `[j/L, (j+1)/L)` read against the centre: the point of the closed arc nearest
/// the centre, whether that point belongs to the half-open arc, and the class's term of the form
/// there. Only the arc holding the centre is read for a class of leverage zero.
#[derive(Clone, Debug)]
struct ArcReading {
    index: BigInt,
    nearest: Rat,
    term: Rat,
    attained: bool,
}

/// An arc, or a prefix of a block, is admitted by its partial infimum `term` when it lies below
/// the tolerance, or equals it and is attained.
fn admits(term: &Rat, attained: bool, tolerance: &Rat) -> bool {
    term < tolerance || (term == tolerance && attained)
}

/// The arc `index` of grain `grain` read against `centre`, for a leverage `ℓ > 0`:
/// `(nearest − centre)² / (2 ℓ)`, the nearest point being the clamp of the centre into the closed
/// arc, and attained unless the centre lies at or above the excluded upper face.
fn read_arc(centre: &Rat, leverage: &Rat, index: BigInt, grain: &BigInt) -> ArcReading {
    let lower = Rat::new(index.clone(), grain.clone());
    let upper = Rat::new(index.clone() + BigInt::one(), grain.clone());
    let (nearest, attained) = if *centre < lower {
        (lower, true)
    } else if *centre >= upper {
        (upper, false)
    } else {
        (centre.clone(), true)
    };
    let gap = &nearest - centre;
    let term = &gap * &gap / (integer(2) * leverage);
    ArcReading {
        index,
        nearest,
        term,
        attained,
    }
}

/// One class's candidate arcs, in ascending index: those admitted by their own term, found by
/// stepping outward from the arc `⌊L ȳ⌋` that holds the centre. Away from it the term never falls
/// and is unbounded, and the attainment is the same on a whole side (attained above, never below),
/// so the admitted arcs are one run and the first failure ends each side. A class of leverage zero
/// keeps the centre's arc alone.
fn class_arcs(centre: &Rat, leverage: &Rat, tolerance: &Rat, grain: &BigInt) -> Vec<ArcReading> {
    let home = (centre * Rat::from_integer(grain.clone()))
        .floor()
        .to_integer();
    if leverage.is_zero() {
        return vec![ArcReading {
            index: home,
            nearest: centre.clone(),
            term: Rat::zero(),
            attained: true,
        }];
    }
    let mut above = vec![read_arc(centre, leverage, home.clone(), grain)];
    let mut index = home.clone();
    loop {
        index = index + BigInt::one();
        let reading = read_arc(centre, leverage, index.clone(), grain);
        if !admits(&reading.term, reading.attained, tolerance) {
            break;
        }
        above.push(reading);
    }
    let mut below = Vec::new();
    let mut index = home;
    loop {
        index = index - BigInt::one();
        let reading = read_arc(centre, leverage, index.clone(), grain);
        if !admits(&reading.term, reading.attained, tolerance) {
            break;
        }
        below.push(reading);
    }
    below.reverse();
    below.extend(above);
    below
}

/// The walk over the product of the classes' candidate arcs.
struct Search<'a> {
    arcs: &'a [Vec<ArcReading>],
    tolerance: &'a Rat,
    limit: Option<usize>,
    chosen: Vec<&'a ArcReading>,
    kept: Vec<Vec<&'a ArcReading>>,
}

impl<'a> Search<'a> {
    /// Extend the prefix `chosen` over class `class` and after. The partial infimum `partial` only
    /// grows and `attained` only fails along a block, so a prefix that does not admit is pruned
    /// with everything beneath it; a prefix that reaches every class is a kept block.
    fn descend(&mut self, class: usize, partial: &Rat, attained: bool) {
        if self.limit.is_some_and(|most| self.kept.len() >= most) {
            return;
        }
        if !admits(partial, attained, self.tolerance) {
            return;
        }
        // The shared reference is copied out, so the arcs below borrow the readings, not `self`.
        let every_class: &'a [Vec<ArcReading>] = self.arcs;
        let Some(arcs) = every_class.get(class) else {
            self.kept.push(self.chosen.clone());
            return;
        };
        for reading in arcs {
            self.chosen.push(reading);
            self.descend(
                class + 1,
                &(partial + &reading.term),
                attained && reading.attained,
            );
            self.chosen.pop();
        }
    }
}

/// The kept blocks (at most `limit` of them when given), as their arc readings, in ascending
/// lexicographic order of their indices.
fn search<'a>(
    arcs: &'a [Vec<ArcReading>],
    tolerance: &'a Rat,
    limit: Option<usize>,
) -> Vec<Vec<&'a ArcReading>> {
    let mut walk = Search {
        arcs,
        tolerance,
        limit,
        chosen: Vec::with_capacity(arcs.len()),
        kept: Vec::new(),
    };
    walk.descend(0, &Rat::zero(), true);
    walk.kept
}

impl PhaseImage {
    /// The centre `ȳ_c = v̂_cᵀx / 2`, one lifted phase per class.
    pub fn centre(&self) -> &[Rat] {
        &self.centre
    }

    /// The class leverages `ℓ_c = xᵀ A_c⁻¹ x`.
    pub fn leverage(&self) -> &[Rat] {
        &self.leverage
    }

    /// `Σ_c ℓ_c`, the declared leverage convention of a probe at this feature (module header; not
    /// information, not a probability).
    pub fn total_leverage(&self) -> Rat {
        let mut total = Rat::zero();
        for leverage in &self.leverage {
            total += leverage;
        }
        total
    }

    /// Whether the lifted phase vector lies in the image: `Q(y) ≤ τ` (a class of leverage zero
    /// needs `y_c = ȳ_c` exactly). A vector of the wrong extent is not in the image.
    pub fn contains(&self, phases: &[Rat]) -> bool {
        if phases.len() != self.centre.len() {
            return false;
        }
        let mut total = Rat::zero();
        for ((phase, centre), leverage) in phases.iter().zip(&self.centre).zip(&self.leverage) {
            let gap = phase - centre;
            if leverage.is_zero() {
                if !gap.is_zero() {
                    return false;
                }
            } else {
                total += &gap * &gap / (integer(2) * leverage);
            }
        }
        total <= self.tolerance
    }

    /// The candidate arcs of every class at the grain `1/grain`.
    fn candidate_arcs(&self, grain: u64) -> Result<Vec<Vec<ArcReading>>, PhaseFamilyError> {
        if grain == 0 {
            return Err(PhaseFamilyError::ZeroGrain);
        }
        let grain = BigInt::from(grain);
        Ok(self
            .centre
            .iter()
            .zip(&self.leverage)
            .map(|(centre, leverage)| class_arcs(centre, leverage, &self.tolerance, &grain))
            .collect())
    }

    /// **Every outcome block the image meets** at the grain `1/grain`, each as its per-class lifted
    /// arc indices `j_c` (the arc `[j_c/L, (j_c+1)/L)`), in ascending lexicographic order. The
    /// decision is exact (module header): a block meets the image when the infimum of `Q` over its
    /// half-open box is below `τ`, or equals `τ` and is attained. A zero grain is refused.
    pub fn blocks(&self, grain: u64) -> Result<Vec<Vec<BigInt>>, PhaseFamilyError> {
        let arcs = self.candidate_arcs(grain)?;
        let kept = search(&arcs, &self.tolerance, None);
        Ok(kept
            .iter()
            .map(|block| block.iter().map(|arc| arc.index.clone()).collect())
            .collect())
    }

    /// **The block of an observed lifted phase vector**: each class's arc index
    /// `j_c = ⌊L y_c⌋`. The grain is the receiver's `L ≥ 1`; a zero grain has no arcs, and every
    /// phase then reads index zero ([`PhaseImage::blocks`] and [`PhaseImage::witnesses`] refuse it).
    pub fn block_of(phases: &[Rat], grain: u64) -> Vec<BigInt> {
        let scale = Rat::from_integer(BigInt::from(grain));
        phases
            .iter()
            .map(|phase| (phase * &scale).floor().to_integer())
            .collect()
    }

    /// The point of a kept block inside the image: the clamped point, with every coordinate that
    /// sits on an excluded upper face moved into its arc by one common `δ = width / 2^i`, the least
    /// `i ≥ 1` for which the moved point lies in the image. A kept block that has such a coordinate
    /// has `inf Q < τ`, and `Q` is continuous at the clamped point, so some `i` does.
    fn witness(&self, block: &[&ArcReading], width: &Rat) -> (Vec<BigInt>, Vec<Rat>) {
        let indices: Vec<BigInt> = block.iter().map(|arc| arc.index.clone()).collect();
        let mut shift = width.clone();
        loop {
            shift = shift / integer(2);
            let point: Vec<Rat> = block
                .iter()
                .map(|arc| {
                    if arc.attained {
                        arc.nearest.clone()
                    } else {
                        &arc.nearest - &shift
                    }
                })
                .collect();
            if self.contains(&point) {
                return (indices, point);
            }
        }
    }

    /// **Two feasible witnesses in two distinct blocks**, when the image meets at least two: the
    /// two least kept blocks, each with a rational point of it inside the image
    /// ([`PhaseImage::contains`]) whose block ([`PhaseImage::block_of`]) is the one reported.
    /// `None` when the image meets fewer than two blocks. A zero grain is refused.
    pub fn witnesses(
        &self,
        grain: u64,
    ) -> Result<Option<[(Vec<BigInt>, Vec<Rat>); 2]>, PhaseFamilyError> {
        let arcs = self.candidate_arcs(grain)?;
        let kept = search(&arcs, &self.tolerance, Some(2));
        let (Some(first), Some(second)) = (kept.first(), kept.get(1)) else {
            return Ok(None);
        };
        let width = Rat::new(BigInt::one(), BigInt::from(grain));
        Ok(Some([
            self.witness(first, &width),
            self.witness(second, &width),
        ]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_traits::{One, Zero};

    use crate::ratio::{Rat, integer, rat};

    fn ints(values: &[i64]) -> Vec<Rat> {
        values.iter().map(|&value| integer(value)).collect()
    }

    fn block(indices: &[i64]) -> Vec<BigInt> {
        indices.iter().map(|&index| BigInt::from(index)).collect()
    }

    /// The blocks `list`, each a tuple of `N` arc indices.
    fn blocks<const N: usize>(list: &[[i64; N]]) -> Vec<Vec<BigInt>> {
        list.iter().map(|indices| block(indices)).collect()
    }

    fn image(centre: &[Rat], leverage: &[Rat], tolerance: Rat) -> PhaseImage {
        PhaseImage {
            centre: centre.to_vec(),
            leverage: leverage.to_vec(),
            tolerance,
        }
    }

    /// The fixture's two receipts: weight, feature, class masses, doubled targets. The second
    /// receipt gives class 1 no mass, so its target `7` must never be read.
    fn receipts() -> [(Rat, Vec<Rat>, Vec<Rat>, Vec<Rat>); 2] {
        [
            (
                integer(1),
                ints(&[1, 0]),
                vec![rat(1, 2), rat(1, 2)],
                ints(&[2, 4]),
            ),
            (
                integer(2),
                ints(&[1, 1]),
                vec![integer(1), integer(0)],
                ints(&[6, 7]),
            ),
        ]
    }

    fn absorbed(order: &[usize]) -> PhaseStatistics {
        let mut statistics = PhaseStatistics::founded(2, 2);
        let receipts = receipts();
        for &index in order {
            let (weight, feature, masses, targets) = &receipts[index];
            statistics.absorb(weight, feature, masses, targets).unwrap();
        }
        statistics
    }

    fn fixture() -> PhaseStatistics {
        absorbed(&[0, 1])
    }

    /// All tuples of `arity` entries drawn from `values`, in ascending lexicographic order.
    fn lattice(values: &[Rat], arity: usize) -> Vec<Vec<Rat>> {
        let mut tuples: Vec<Vec<Rat>> = vec![Vec::new()];
        for _ in 0..arity {
            tuples = tuples
                .into_iter()
                .flat_map(|prefix| {
                    values.iter().map(move |value| {
                        let mut next = prefix.clone();
                        next.push(value.clone());
                        next
                    })
                })
                .collect();
        }
        tuples
    }

    /// The phase rows of the family that read `ȳ + d` at the feature with the least excess,
    /// `v_c = v̂_c + 2 d_c A_c⁻¹ x / ℓ_c` (the equality case of the module's Cauchy–Schwarz).
    fn realize(family: &PhaseFamily, feature: &[Rat], offsets: &[Rat]) -> Vec<Vec<Rat>> {
        (0..offsets.len())
            .map(|class| {
                let response = solve(&family.shapes[class], feature).unwrap();
                let leverage = dot(feature, &response);
                family.minimizer[class]
                    .iter()
                    .zip(&response)
                    .map(|(centre, direction)| {
                        centre + integer(2) * &offsets[class] * direction / &leverage
                    })
                    .collect()
            })
            .collect()
    }

    fn read(rows: &[Vec<Rat>], feature: &[Rat]) -> Vec<Rat> {
        rows.iter()
            .map(|row| dot(row, feature) * rat(1, 2))
            .collect()
    }

    /// An oracle that shares no code with the block rule: a block meets the image when some point
    /// of the dyadic sub-lattice `(j D + o) / (L D)`, `0 ≤ o < D`, of its half-open box lies in
    /// the image ([`PhaseImage::contains`]). It can only miss a block the image meets by a sliver
    /// finer than `1/(L D)`; the cases below are chosen coarser than that.
    fn sampled_blocks(
        image: &PhaseImage,
        grain: i64,
        window: i64,
        density: i64,
    ) -> Vec<Vec<BigInt>> {
        let classes = image.centre().len();
        let window_values: Vec<Rat> = (-window..=window).map(integer).collect();
        let mut met = Vec::new();
        for candidate in lattice(&window_values, classes) {
            let mut points: Vec<Vec<Rat>> = vec![Vec::new()];
            for j in &candidate {
                let j = j.to_integer();
                points = points
                    .into_iter()
                    .flat_map(|prefix| {
                        let j = j.clone();
                        (0..density).map(move |offset| {
                            let mut next = prefix.clone();
                            next.push(Rat::new(
                                &j * BigInt::from(density) + BigInt::from(offset),
                                BigInt::from(grain * density),
                            ));
                            next
                        })
                    })
                    .collect();
            }
            if points.iter().any(|point| image.contains(point)) {
                met.push(candidate.iter().map(Rat::to_integer).collect());
            }
        }
        met
    }

    // ---------------------------------------------------------------------------------------
    // 2. the statistic

    #[test]
    fn two_receipts_give_the_hand_computed_statistics_whatever_their_order() {
        let statistics = fixture();
        assert_eq!(statistics.classes(), 2);
        assert_eq!(statistics.features(), 2);
        // class 0: (1/2) e₁e₁ᵀ + 2 (1,1)(1,1)ᵀ ;  (1/2)·2·(1,0) + 2·6·(1,1) ;  (1/2)·4 + 2·36
        assert_eq!(
            statistics.gram(0).to_vec(),
            vec![vec![rat(5, 2), integer(2)], vec![integer(2), integer(2)]]
        );
        assert_eq!(statistics.moment(0).to_vec(), ints(&[13, 12]));
        assert_eq!(statistics.second(0), &integer(74));
        // class 1: only the first receipt carried mass, (1/2) e₁e₁ᵀ ; (1/2)·4·(1,0) ; (1/2)·16
        assert_eq!(
            statistics.gram(1).to_vec(),
            vec![vec![rat(1, 2), integer(0)], vec![integer(0), integer(0)]]
        );
        assert_eq!(statistics.moment(1).to_vec(), ints(&[2, 0]));
        assert_eq!(statistics.second(1), &integer(8));
        // two classes compared at the first receipt (weight 1), one at the second (weight 2)
        assert_eq!(statistics.cells(), &integer(4));
        // exact addition: the order of absorption is immaterial
        assert_eq!(statistics, absorbed(&[1, 0]));
        // a receipt of weight zero changes nothing
        let mut unchanged = fixture();
        unchanged
            .absorb(
                &integer(0),
                &ints(&[3, 5]),
                &[rat(1, 4), rat(3, 4)],
                &ints(&[9, 9]),
            )
            .unwrap();
        assert_eq!(unchanged, fixture());
        // the founded statistic is zero
        let founded = PhaseStatistics::founded(2, 2);
        assert!(founded.cells().is_zero());
        assert!(founded.second(1).is_zero());
        assert!(founded.moment(0).iter().all(|entry| entry.is_zero()));
        assert!(
            founded
                .gram(0)
                .iter()
                .flatten()
                .all(|entry| entry.is_zero())
        );
    }

    // ---------------------------------------------------------------------------------------
    // 1. the family

    #[test]
    fn the_minimizer_solves_the_ridged_normal_equations_and_excess_is_the_gap_to_the_minimum() {
        let statistics = fixture();
        let family = statistics.family(1, &rat(1, 10)).unwrap();
        // A_c = S_c + 2 I, by hand
        let shapes = vec![
            vec![vec![rat(9, 2), integer(2)], vec![integer(2), integer(4)]],
            vec![vec![rat(5, 2), integer(0)], vec![integer(0), integer(2)]],
        ];
        assert_eq!(family.shapes, shapes);
        // A_c v̂_c = m_c, exactly
        for class in 0..2 {
            let product: Vec<Rat> = shapes[class]
                .iter()
                .map(|row| dot(row, &family.minimizer()[class]))
                .collect();
            assert_eq!(product, statistics.moment(class).to_vec());
        }
        assert_eq!(
            family.minimizer().to_vec(),
            vec![ints(&[2, 2]), vec![rat(4, 5), integer(0)]]
        );
        // L* = (1/8)((74 − (2·13 + 2·12)) + (8 − (4/5)·2)) = 19/5
        assert_eq!(family.minimum(), &rat(19, 5));
        assert_eq!(family.tolerance(), &rat(1, 10));
        assert_eq!(family.excess(family.minimizer()).unwrap(), integer(0));

        // a hand-chosen V = (e₁, e₂): the direct sum Σ_c (1/8)[vᵀAv − 2vᵀm + s] − L*
        let rows = vec![ints(&[1, 0]), ints(&[0, 1])];
        let mut direct = Rat::zero();
        for class in 0..2 {
            let curvature = quadratic(&shapes[class], &rows[class]);
            let linear = dot(&rows[class], statistics.moment(class));
            direct += (curvature - integer(2) * linear + statistics.second(class)) * rat(1, 8);
        }
        direct -= family.minimum();
        assert_eq!(direct, rat(321, 80));
        assert_eq!(family.excess(&rows).unwrap(), direct);
        // the excess is a gap: it is nonnegative and zero only at the minimizer
        let away = vec![ints(&[2, 3]), ints(&[1, 1])];
        assert!(family.excess(&away).unwrap() > integer(0));
    }

    #[test]
    fn a_founded_statistic_gives_the_prior_family_alone() {
        let family = PhaseStatistics::founded(2, 3)
            .family(2, &rat(1, 2))
            .unwrap();
        // no receipt: v̂ = 0, L* = 0, A = 4 I, so the leverage of x is |x|²/4
        assert_eq!(family.minimizer().to_vec(), vec![ints(&[0, 0, 0]); 2]);
        assert!(family.minimum().is_zero());
        let image = family.image(&ints(&[1, 2, 3])).unwrap();
        assert_eq!(image.centre().to_vec(), ints(&[0, 0]));
        assert_eq!(image.leverage().to_vec(), vec![rat(7, 2), rat(7, 2)]);
        assert_eq!(image.total_leverage(), integer(7));
    }

    // ---------------------------------------------------------------------------------------
    // 3. the leverage contracts exactly at the same feature

    #[test]
    fn absorbing_a_receipt_contracts_the_leverage_at_its_own_feature_by_sherman_morrison() {
        let feature = ints(&[1, 1]);
        let before = fixture();
        let image = before
            .family(1, &rat(1, 10))
            .unwrap()
            .image(&feature)
            .unwrap();
        // by hand: A₀⁻¹ = (1/14)[[4, −2], [−2, 9/2]], A₁⁻¹ = diag(2/5, 1/2)
        assert_eq!(image.leverage().to_vec(), vec![rat(9, 28), rat(9, 10)]);
        assert_eq!(image.centre().to_vec(), vec![integer(2), rat(2, 5)]);

        // ℓ′ = ℓ / (1 + w q ℓ), the receipt read at the same feature
        let (weight, masses) = (integer(3), vec![rat(1, 3), rat(2, 3)]);
        let mut after = before.clone();
        after
            .absorb(&weight, &feature, &masses, &ints(&[1, 5]))
            .unwrap();
        let contracted = after
            .family(1, &rat(1, 10))
            .unwrap()
            .image(&feature)
            .unwrap();
        for class in 0..2 {
            let leverage = &image.leverage()[class];
            let predicted = leverage / (integer(1) + &weight * &masses[class] * leverage);
            assert_eq!(contracted.leverage()[class], predicted);
            assert!(contracted.leverage()[class] < *leverage);
        }
        assert_eq!(contracted.leverage().to_vec(), vec![rat(9, 37), rat(9, 28)]);

        // a class that carried no mass is not contracted: only class 0 moves, 9/28 → 9/73
        let mut skewed = before.clone();
        skewed
            .absorb(
                &integer(5),
                &feature,
                &[integer(1), integer(0)],
                &ints(&[1, 99]),
            )
            .unwrap();
        let moved = skewed
            .family(1, &rat(1, 10))
            .unwrap()
            .image(&feature)
            .unwrap();
        assert_eq!(moved.leverage().to_vec(), vec![rat(9, 73), rat(9, 10)]);
    }

    // ---------------------------------------------------------------------------------------
    // 4. the image of the family

    #[test]
    fn a_member_of_the_family_maps_into_the_ellipsoid_and_its_boundary_is_attained() {
        let statistics = fixture();
        let feature = ints(&[1, 1]);
        // the image point ȳ + d with d = (1/4, −1/5) is on E(x)'s boundary exactly when
        // τ = Σ d_c² / (2 ℓ_c) = (1/16)/(9/14) + (1/25)/(9/5) = 7/72 + 1/45 = 43/360
        let tolerance = rat(43, 360);
        let family = statistics.family(1, &tolerance).unwrap();
        let image = family.image(&feature).unwrap();
        assert_eq!(image.centre().to_vec(), vec![integer(2), rat(2, 5)]);
        assert_eq!(image.leverage().to_vec(), vec![rat(9, 28), rat(9, 10)]);
        assert_eq!(image.total_leverage(), rat(171, 140));

        let boundary = vec![rat(9, 4), rat(1, 5)];
        assert!(image.contains(&boundary));
        // the member reading it, v_c = v̂_c + 2 d_c A_c⁻¹x / ℓ_c, sits on the boundary of F_τ
        let member = vec![vec![rat(20, 9), rat(41, 18)], vec![rat(28, 45), rat(-2, 9)]];
        assert_eq!(read(&member, &feature), boundary);
        assert_eq!(family.excess(&member).unwrap(), tolerance);
        assert_eq!(realize(&family, &feature, &[rat(1, 4), rat(-1, 5)]), member);

        // a point just outside fails, one just inside holds
        let along = |scale: Rat| {
            vec![
                integer(2) + &scale * rat(1, 4),
                rat(2, 5) - &scale * rat(1, 5),
            ]
        };
        assert!(!image.contains(&along(rat(1001, 1000))));
        assert!(image.contains(&along(rat(999, 1000))));
        assert!(image.contains(&along(integer(1))));
        // a vector of the wrong extent is not in the image
        assert!(!image.contains(&[rat(9, 4)]));

        // halfway to the minimizer the excess is a quarter of τ, and the point is interior
        let halfway: Vec<Vec<Rat>> = member
            .iter()
            .zip(family.minimizer())
            .map(|(row, centre)| {
                row.iter()
                    .zip(centre)
                    .map(|(v, c)| (v + c) * rat(1, 2))
                    .collect()
            })
            .collect();
        assert_eq!(family.excess(&halfway).unwrap(), &tolerance / integer(4));
        assert!(image.contains(&read(&halfway, &feature)));
    }

    #[test]
    fn the_image_is_exactly_what_the_members_read() {
        let statistics = fixture();
        let feature = ints(&[1, 1]);
        let tolerance = rat(43, 360);
        let family = statistics.family(1, &tolerance).unwrap();
        let image = family.image(&feature).unwrap();

        // every member of a grid of phase rows maps into the image (some rows are not members)
        let steps = [rat(-1, 2), integer(0), rat(1, 2)];
        let (mut members, mut others) = (0, 0);
        for step in lattice(&steps, 4) {
            let rows = vec![
                vec![
                    &family.minimizer()[0][0] + &step[0],
                    &family.minimizer()[0][1] + &step[1],
                ],
                vec![
                    &family.minimizer()[1][0] + &step[2],
                    &family.minimizer()[1][1] + &step[3],
                ],
            ];
            if family.excess(&rows).unwrap() <= tolerance {
                members += 1;
                assert!(image.contains(&read(&rows, &feature)));
            } else {
                others += 1;
            }
        }
        assert_eq!((members, others), (5, 76));

        // every point of a grid of the image is read by a member (the equality case)
        let grid: Vec<Rat> = (-4..=4).map(|i| rat(i, 10)).collect();
        let (mut inside, mut outside) = (0, 0);
        for offsets in lattice(&grid, 2) {
            let point: Vec<Rat> = image
                .centre()
                .iter()
                .zip(&offsets)
                .map(|(centre, offset)| centre + offset)
                .collect();
            if image.contains(&point) {
                inside += 1;
                let member = realize(&family, &feature, &offsets);
                assert!(family.excess(&member).unwrap() <= tolerance);
                assert_eq!(read(&member, &feature), point);
            } else {
                outside += 1;
            }
        }
        assert_eq!((inside, outside), (41, 40));
    }

    #[test]
    fn a_zero_feature_probes_nothing_and_its_image_is_the_origin() {
        let family = fixture().family(1, &rat(1, 10)).unwrap();
        let image = family.image(&ints(&[0, 0])).unwrap();
        assert_eq!(image.centre().to_vec(), ints(&[0, 0]));
        assert_eq!(image.leverage().to_vec(), ints(&[0, 0]));
        assert!(image.total_leverage().is_zero());
        assert!(image.contains(&ints(&[0, 0])));
        assert!(!image.contains(&[rat(1, 100), integer(0)]));
        assert_eq!(image.blocks(3).unwrap(), blocks(&[[0, 0]]));
        assert_eq!(image.witnesses(3).unwrap(), None);
    }

    #[test]
    fn a_class_of_zero_leverage_reads_its_centre_alone() {
        // class 0 is degenerate at the centre 1/2 (ℓ = 0); class 1 has Q = y₁² ≤ 1
        let mixed = image(
            &[rat(1, 2), integer(0)],
            &[integer(0), rat(1, 2)],
            integer(1),
        );
        assert!(mixed.contains(&[rat(1, 2), integer(1)]));
        assert!(mixed.contains(&[rat(1, 2), integer(-1)]));
        assert!(!mixed.contains(&[integer(0), integer(0)]));
        assert!(!mixed.contains(&[rat(1, 2), rat(11, 10)]));
        assert_eq!(mixed.blocks(1).unwrap(), blocks(&[[0, -1], [0, 0], [0, 1]]));
        // the degenerate class never moves: only class 1's excluded upper face 0 is shifted
        let witnesses = assert_witnesses_hold(&mixed, 1);
        assert_eq!(
            witnesses,
            [
                (block(&[0, -1]), vec![rat(1, 2), rat(-1, 2)]),
                (block(&[0, 0]), vec![rat(1, 2), integer(0)]),
            ]
        );
    }

    // ---------------------------------------------------------------------------------------
    // 5. the blocks, at half-open boundaries

    #[test]
    fn an_ellipsoid_touching_an_upper_face_misses_the_arc_and_a_lower_face_meets_it() {
        // Q(y) = (y − 2)² / 1 ≤ 1 : E = [1, 3], grain 1. Its lowest point 1 is the excluded
        // upper face of the arc [0, 1) (missed); its highest point 3 is the included lower face of
        // the arc [3, 4) (met).
        let touching = image(&[integer(2)], &[rat(1, 2)], integer(1));
        assert_eq!(touching.blocks(1).unwrap(), blocks(&[[1], [2], [3]]));
        assert_eq!(
            touching.blocks(1).unwrap(),
            sampled_blocks(&touching, 1, 5, 8)
        );
        // the same at grain 2 (arcs of width 1/2), centre 1, ℓ = 1/8, τ = 1: E = [1/2, 3/2];
        // the arc [0, 1/2) is missed at 1/2, the arcs [1/2, 1), [1, 3/2), [3/2, 2) are met.
        let finer = image(&[integer(1)], &[rat(1, 8)], integer(1));
        assert_eq!(finer.blocks(2).unwrap(), blocks(&[[1], [2], [3]]));
        assert_eq!(finer.blocks(2).unwrap(), sampled_blocks(&finer, 2, 6, 8));
        // tolerance zero leaves the centre alone, and the centre on a face belongs to the arc
        // above it
        let point = image(
            &[integer(2), rat(1, 2)],
            &[rat(1, 2), rat(1, 2)],
            integer(0),
        );
        assert_eq!(point.blocks(1).unwrap(), blocks(&[[2, 0]]));
        assert_eq!(point.blocks(1).unwrap(), sampled_blocks(&point, 1, 4, 4));
        assert_eq!(point.witnesses(1).unwrap(), None);
        // the centre inside an arc: E = [−1/2, 3/2] meets the arcs [−1, 0), [0, 1), [1, 2)
        let centred = image(&[rat(1, 2)], &[rat(1, 2)], integer(1));
        assert_eq!(centred.blocks(1).unwrap(), blocks(&[[-1], [0], [1]]));
    }

    #[test]
    fn the_box_corners_are_excluded_although_each_projection_meets() {
        // The unit disk Q = y₀² + y₁² ≤ 1 (ℓ = 1/2 each), grain 1. Each class's projection [−1, 1]
        // meets the arcs −1, 0, 1, so nine boxes are candidates. The corner box (1, 1) has
        // inf Q = 2 > 1. The boxes (1, −1) and (−1, 1) have inf Q = 1 = τ but it is approached,
        // never attained (the excluded upper face 0 of the arc [−1, 0)).
        let disk = image(
            &[integer(0), integer(0)],
            &[rat(1, 2), rat(1, 2)],
            integer(1),
        );
        let expected = blocks(&[[-1, -1], [-1, 0], [0, -1], [0, 0], [0, 1], [1, 0]]);
        assert_eq!(disk.blocks(1).unwrap(), expected);
        assert_eq!(sampled_blocks(&disk, 1, 3, 8), expected);
        for corner in [[1, 1], [1, -1], [-1, 1]] {
            assert!(!expected.contains(&block(&corner)));
        }
        // each class's own range, found alone, keeps all three arcs
        let arcs = disk.candidate_arcs(1).unwrap();
        for class in &arcs {
            let indices: Vec<BigInt> = class.iter().map(|arc| arc.index.clone()).collect();
            assert_eq!(indices, block(&[-1, 0, 1]));
        }

        // a different leverage per class: Q = y₀² + y₁²/4 ≤ 1, E = [−1, 1] × [−2, 2]
        let ellipse = image(
            &[integer(0), integer(0)],
            &[rat(1, 2), integer(2)],
            integer(1),
        );
        let blocks_met = ellipse.blocks(1).unwrap();
        assert_eq!(blocks_met, sampled_blocks(&ellipse, 1, 4, 8));
        assert_eq!(
            blocks_met,
            blocks(&[
                [-1, -2],
                [-1, -1],
                [-1, 0],
                [-1, 1],
                [0, -2],
                [0, -1],
                [0, 0],
                [0, 1],
                [0, 2],
                [1, 0],
            ])
        );

        // three classes: the unit ball, eleven of the twenty-seven candidate boxes
        let ball = image(
            &[integer(0), integer(0), integer(0)],
            &[rat(1, 2), rat(1, 2), rat(1, 2)],
            integer(1),
        );
        let met = ball.blocks(1).unwrap();
        assert_eq!(met.len(), 11);
        assert_eq!(met, sampled_blocks(&ball, 1, 1, 4));
        assert_eq!(met[0], block(&[-1, -1, -1]));
        assert_eq!(met[10], block(&[1, 0, 0]));
    }

    #[test]
    fn the_family_pipeline_meets_the_blocks_the_hand_computation_gives() {
        // the fixture at x = (1, 1) with τ = 1/10: centre (2, 2/5), ℓ = (9/28, 9/10), so
        // Q = (14/9)(y₀ − 2)² + (5/9)(y₁ − 2/5)² ≤ 1/10
        let family = fixture().family(1, &rat(1, 10)).unwrap();
        let image = family.image(&ints(&[1, 1])).unwrap();
        assert_eq!(
            image.blocks(1).unwrap(),
            blocks(&[[1, -1], [1, 0], [2, -1], [2, 0]])
        );
        // grain 2: class 0's arcs 3 and 4, class 1's arcs −1, 0, 1. The arcs [3/2, 2) and
        // [−1/2, 0) lie below their centres 2 and 2/5, so their nearest points 2 and 0 are
        // excluded upper faces, approached and never reached; they are met because the infimum
        // there, 4/45, is below τ = 1/10.
        assert_eq!(
            image.blocks(2).unwrap(),
            blocks(&[[3, -1], [3, 0], [3, 1], [4, -1], [4, 0], [4, 1]])
        );
        // the observed phase vector of any member lies in a met block
        assert_eq!(
            PhaseImage::block_of(&[rat(9, 4), rat(1, 5)], 2),
            block(&[4, 0])
        );
        assert!(
            image
                .blocks(2)
                .unwrap()
                .contains(&PhaseImage::block_of(&[rat(9, 4), rat(1, 5)], 2))
        );
    }

    #[test]
    fn the_block_of_a_phase_vector_is_the_floor_at_the_grain() {
        // lower faces belong to their arc, upper faces to the next, negatives round down
        let phases = [rat(1, 2), rat(-1, 2), rat(-1, 3), integer(0), rat(5, 3)];
        assert_eq!(PhaseImage::block_of(&phases, 2), block(&[1, -1, -1, 0, 3]));
        assert_eq!(PhaseImage::block_of(&phases, 1), block(&[0, -1, -1, 0, 1]));
        assert_eq!(PhaseImage::block_of(&[], 4), Vec::<BigInt>::new());
    }

    // ---------------------------------------------------------------------------------------
    // 6. the witnesses

    fn assert_witnesses_hold(image: &PhaseImage, grain: u64) -> [(Vec<BigInt>, Vec<Rat>); 2] {
        let witnesses = image.witnesses(grain).unwrap().expect("two blocks");
        let met = image.blocks(grain).unwrap();
        for (reported, point) in &witnesses {
            assert!(image.contains(point), "{point:?} lies in the image");
            assert_eq!(&PhaseImage::block_of(point, grain), reported);
            assert!(met.contains(reported));
        }
        assert_ne!(witnesses[0].0, witnesses[1].0);
        witnesses
    }

    #[test]
    fn two_witnesses_lie_in_the_image_and_in_their_distinct_blocks() {
        // the unit disk: the two least blocks (−1, −1) and (−1, 0), both reached only across
        // excluded upper faces, so each coordinate on a face moves by (b − a)/2 = 1/2
        let disk = image(
            &[integer(0), integer(0)],
            &[rat(1, 2), rat(1, 2)],
            integer(1),
        );
        let witnesses = assert_witnesses_hold(&disk, 1);
        assert_eq!(
            witnesses,
            [
                (block(&[-1, -1]), vec![rat(-1, 2), rat(-1, 2)]),
                (block(&[-1, 0]), vec![rat(-1, 2), integer(0)]),
            ]
        );

        // a small disk (τ = 1/100): the block (−1, −1) moves two coordinates, 2δ² ≤ 1/100, which
        // fails at δ = 1/8 (1/32) and holds at δ = 1/16 (1/128); the block (−1, 0) moves one,
        // δ² ≤ 1/100, with the same least δ. So the least i is 4 for both.
        let small = image(
            &[integer(0), integer(0)],
            &[rat(1, 2), rat(1, 2)],
            rat(1, 100),
        );
        assert_eq!(
            small.blocks(1).unwrap(),
            blocks(&[[-1, -1], [-1, 0], [0, -1], [0, 0]])
        );
        let witnesses = assert_witnesses_hold(&small, 1);
        assert_eq!(
            witnesses,
            [
                (block(&[-1, -1]), vec![rat(-1, 16), rat(-1, 16)]),
                (block(&[-1, 0]), vec![rat(-1, 16), integer(0)]),
            ]
        );

        // the arc [2, 3) holds the centre, so its witness is the clamped point itself; the arc
        // [1, 2) lies below it, and is reached across its excluded upper face 2 by the shift 1/2
        let touching = image(&[integer(2)], &[rat(1, 2)], integer(1));
        let witnesses = assert_witnesses_hold(&touching, 1);
        assert_eq!(
            witnesses,
            [
                (block(&[1]), vec![rat(3, 2)]),
                (block(&[2]), vec![integer(2)]),
            ]
        );
    }

    #[test]
    fn the_family_pipeline_witnesses_are_read_by_members_of_the_family() {
        let family = fixture().family(1, &rat(1, 10)).unwrap();
        let feature = ints(&[1, 1]);
        let image = family.image(&feature).unwrap();
        let witnesses = assert_witnesses_hold(&image, 2);
        // the least block (3, −1) is reached across two excluded upper faces (2 and 0) only by
        // the shift 1/64, the fifth halving of the arc width 1/2; the next block (3, 0) needs
        // one coordinate moved, by 1/4
        assert_eq!(
            witnesses,
            [
                (block(&[3, -1]), vec![rat(127, 64), rat(-1, 64)]),
                (block(&[3, 0]), vec![rat(7, 4), rat(2, 5)]),
            ]
        );
        // each witness is read by a member of F_τ
        for (_, point) in &witnesses {
            let offsets: Vec<Rat> = point
                .iter()
                .zip(image.centre())
                .map(|(y, centre)| y - centre)
                .collect();
            let member = realize(&family, &feature, &offsets);
            assert_eq!(&read(&member, &feature), point);
            assert!(family.excess(&member).unwrap() <= *family.tolerance());
        }
    }

    // ---------------------------------------------------------------------------------------
    // 7. the refusals

    #[test]
    fn bad_input_is_a_typed_refusal_and_leaves_the_statistic_unchanged() {
        let mut statistics = fixture();
        let before = statistics.clone();
        let feature = ints(&[1, 1]);
        let masses = [rat(1, 2), rat(1, 2)];
        let targets = ints(&[0, 0]);

        assert_eq!(
            statistics.absorb(&integer(-1), &feature, &masses, &targets),
            Err(PhaseFamilyError::NegativeWeight)
        );
        // masses that do not sum to one, a negative mass that does, and the empty distribution
        assert_eq!(
            statistics.absorb(&integer(1), &feature, &[rat(1, 2), rat(1, 3)], &targets),
            Err(PhaseFamilyError::NotADistribution)
        );
        assert_eq!(
            statistics.absorb(&integer(1), &feature, &[rat(3, 2), rat(-1, 2)], &targets),
            Err(PhaseFamilyError::NotADistribution)
        );
        assert_eq!(
            PhaseStatistics::founded(0, 2).absorb(&integer(1), &feature, &[], &[]),
            Err(PhaseFamilyError::NotADistribution)
        );
        // shapes: the feature, the masses and the targets
        assert_eq!(
            statistics.absorb(&integer(1), &ints(&[1, 1, 1]), &masses, &targets),
            Err(PhaseFamilyError::Shape {
                expected: 2,
                found: 3
            })
        );
        assert_eq!(
            statistics.absorb(&integer(1), &feature, &[integer(1)], &targets),
            Err(PhaseFamilyError::Shape {
                expected: 2,
                found: 1
            })
        );
        assert_eq!(
            statistics.absorb(&integer(1), &feature, &masses, &ints(&[0])),
            Err(PhaseFamilyError::Shape {
                expected: 2,
                found: 1
            })
        );
        assert_eq!(statistics, before);

        // the family and its readers
        assert_eq!(
            statistics.family(1, &rat(-1, 10)),
            Err(PhaseFamilyError::NegativeTolerance)
        );
        let family = statistics.family(0, &integer(0)).unwrap();
        assert_eq!(
            family.excess(&[ints(&[0, 0])]),
            Err(PhaseFamilyError::Shape {
                expected: 2,
                found: 1
            })
        );
        assert_eq!(
            family.excess(&[ints(&[0, 0]), ints(&[0, 0, 0])]),
            Err(PhaseFamilyError::Shape {
                expected: 2,
                found: 3
            })
        );
        assert_eq!(
            family.image(&ints(&[1])),
            Err(PhaseFamilyError::Shape {
                expected: 2,
                found: 1
            })
        );

        // the grain
        let image = family.image(&feature).unwrap();
        assert_eq!(image.blocks(0), Err(PhaseFamilyError::ZeroGrain));
        assert_eq!(image.witnesses(0), Err(PhaseFamilyError::ZeroGrain));
        // the solver's refusal is typed too
        assert_eq!(
            solve(
                &[vec![integer(0), integer(1)], vec![integer(0), integer(1)]],
                &ints(&[1, 1])
            ),
            Err(PhaseFamilyError::Singular)
        );
    }

    #[test]
    fn the_solver_is_exact_and_the_refusals_display() {
        // a pivot search past a zero diagonal: [[0, 2], [3, 1]] z = (4, 5) → z = (1, 2)
        let shape = vec![vec![integer(0), integer(2)], vec![integer(3), integer(1)]];
        assert_eq!(solve(&shape, &ints(&[4, 5])).unwrap(), ints(&[1, 2]));
        assert_eq!(solve(&[], &[]).unwrap(), Vec::<Rat>::new());
        assert_eq!(
            PhaseFamilyError::Shape {
                expected: 2,
                found: 3
            }
            .to_string(),
            "expected 2 entries, found 3"
        );
        assert_eq!(
            PhaseFamilyError::ZeroGrain.to_string(),
            "the grain of an outcome block must be a positive integer"
        );
    }

    /// **A restored statistic must meet a sum of receipts' necessary conditions** (Epime's review,
    /// October 8): its augmented statistic `[[S, m], [mᵀ, s]]` is symmetric positive semidefinite. An indefinite
    /// Gram (`S = −2`), a moment the Gram cannot carry (`S = 1, m = 2, s = 3`: determinant `−1`) and
    /// an asymmetric Gram are refused; a rank-one sum (`S = 1, m = 1, s = 1`) and an absorbed
    /// statistic's own parts are restored exactly.
    #[test]
    fn a_restored_statistic_must_be_a_sum_of_receipts() {
        let one_class = |gram: Vec<Vec<Rat>>, moment: Vec<Rat>, second: Rat| {
            PhaseStatistics::from_parts(1, gram.len(), vec![gram], vec![moment], vec![second], Rat::one())
        };
        assert_eq!(
            one_class(vec![ints(&[-2])], ints(&[0]), Rat::zero()),
            Err(PhaseFamilyError::Malformed)
        );
        assert_eq!(
            one_class(vec![ints(&[1])], ints(&[2]), integer(3)),
            Err(PhaseFamilyError::Malformed)
        );
        assert_eq!(
            one_class(vec![ints(&[1, 2]), ints(&[3, 4])], ints(&[0, 0]), Rat::zero()),
            Err(PhaseFamilyError::Malformed)
        );
        assert!(one_class(vec![ints(&[1])], ints(&[1]), integer(1)).is_ok());
        assert!(!positive_semidefinite(&[ints(&[0, 1]), ints(&[1, 0])]));
        assert!(positive_semidefinite(&[ints(&[0, 0]), ints(&[0, 3])]));

        let mut absorbed = PhaseStatistics::founded(2, 2);
        absorbed
            .absorb(&integer(2), &ints(&[1, -1]), &[rat(1, 3), rat(2, 3)], &[rat(1, 2), integer(-3)])
            .unwrap();
        absorbed
            .absorb(&Rat::one(), &ints(&[2, 5]), &[Rat::one(), Rat::zero()], &[integer(7), Rat::zero()])
            .unwrap();
        let restored = PhaseStatistics::from_parts(
            2,
            2,
            (0..2).map(|c| absorbed.gram(c).to_vec()).collect(),
            (0..2).map(|c| absorbed.moment(c).to_vec()).collect(),
            (0..2).map(|c| absorbed.second(c).clone()).collect(),
            absorbed.cells().clone(),
        )
        .unwrap();
        assert_eq!(restored, absorbed);
        assert_eq!(
            PhaseStatistics::from_parts(1, 1, vec![vec![ints(&[1])]], vec![ints(&[0])], vec![Rat::zero()], integer(-1)),
            Err(PhaseFamilyError::Malformed)
        );
        // A zero count carries no receipt: nonzero statistics with N = 0 are unreachable, and the
        // founded (all-zero) statistic restores.
        assert_eq!(
            PhaseStatistics::from_parts(1, 1, vec![vec![ints(&[1])]], vec![ints(&[1])], vec![Rat::one()], Rat::zero()),
            Err(PhaseFamilyError::Malformed)
        );
        assert_eq!(
            PhaseStatistics::from_parts(1, 1, vec![vec![ints(&[0])]], vec![ints(&[0])], vec![Rat::zero()], Rat::zero()),
            Ok(PhaseStatistics::founded(1, 1))
        );
    }
}
