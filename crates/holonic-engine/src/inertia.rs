//! Sylvester's law of inertia, computed exactly over the rationals.
//!
//! ## Why this exists: without it, the only positive form a body can build is a tautology
//!
//! [`crate::supported_realizers`] computed `M^T M` and tested that it was positive semi-definite.
//! **That test could not fail on any input whatsoever**, because `x^T (M^T M) x = |M x|^2` for every
//! integer matrix `M` and every probe `x`. By `CLAUDE.md` §8's tautology rule — *"a receipt that
//! could not have come out otherwise carries no evidence"* — it carried none.
//!
//! It reached for a Gram matrix because a Gram matrix is the only positive form available to a body
//! with no inertia routine, and a Gram matrix's positivity is a property of the *construction*, not
//! a discovered property of the material. The mathematics it was imitating has the opposite shape:
//!
//! - The **Hodge index theorem** says the intersection form on the Néron–Severi group of a surface
//!   has signature `(1, ρ-1)` — one plus direction and everything else negative.
//! - The **Hodge–Riemann bilinear relations** say a form that is *a priori* indefinite becomes
//!   definite only after restriction to a primitive subspace and a single Hodge type, with the sign
//!   alternating with degree.
//!
//! Both are **signature theorems about indefinite forms**. The content is the count of each sign,
//! and the check can come out wrong. No Gram matrix has ever had that property. This module is the
//! primitive that makes such a count computable, so that a positivity claim in this body can be a
//! claim about material rather than about the shape of the expression that produced it.
//!
//! ## The law, and what makes it a testable claim rather than an assumption
//!
//! Sylvester's law of inertia: for a symmetric bilinear form over an ordered field, the triple
//! `(positive, zero, negative)` of a diagonalization is **invariant under every invertible change
//! of basis** `A -> P^T A P`. So the number is a property of the form and not of the elimination
//! that found it.
//!
//! That invariance is the whole reason the pivot order below may be a free parameter. It is *not*
//! assumed here: [`PivotOrder`] is a declared schedule, [`inertia_with_schedule`] returns the
//! schedule the elimination actually walked, and the tests assert both that different orders walk
//! **different** schedules and that they return the same triple. An agreement between two identical
//! computations is one computation compared with itself, which is a check whose material cannot vary
//! the property under test — the same discipline [`crate::rebase_invariants::PivotSchedule`] carries
//! for the Smith normal form.
//!
//! ## The elimination
//!
//! Symmetric Gaussian elimination — `L D L^T` with symmetric pivoting — over exact `Rat`. Every step
//! is a congruence, so by Sylvester's law every step preserves the answer.
//!
//! 1. If every surviving entry is zero, everything remaining is `zero`.
//! 2. If some surviving **diagonal** entry `a_ii` is nonzero, it contributes one to `positive` or
//!    `negative` by its sign; take the Schur complement `a'_jk = a_jk - a_ji · a_ik / a_ii` on the
//!    survivors and recurse.
//! 3. If every surviving diagonal entry is zero but some `a_ij` is nonzero for `i != j`, the `2x2`
//!    block is `[[0, a], [a, 0]]`, whose eigenvalues are `±a`. It contributes **one positive and one
//!    negative**, whatever the sign of `a`. Take the Schur complement of the whole block,
//!    `a'_kl = a_kl - (a_ki · a_jl + a_kj · a_il) / a`, drop both indices and recurse.
//!
//! **Branch 3 is why a naive `L D L^T` is wrong.** An implementation that only ever pivots on the
//! diagonal either divides by zero on the hyperbolic plane `[[0,1],[1,0]]` or reports it as
//! `(0, 2, 0)` — a degenerate form — when its true inertia is `(1, 0, 1)`. Every indefinite lattice
//! that matters here contains a hyperbolic plane, so this is not an edge case; it is the case.
//! [`InertiaSchedule::used_zero_diagonal_branch`] exists so a test can prove the branch fired rather
//! than assume it.
//!
//! ## Exactness
//!
//! `Rat` throughout, which is `BigRational`. No float, no tolerance, and no pivoting heuristic that
//! reads a magnitude as a *decision*: the magnitude orders in [`PivotOrder::SmallestMagnitude`] and
//! [`PivotOrder::LargestMagnitude`] choose which exact step to take next and can never change what
//! is returned. That is measurement, not governance.

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::rebase_invariants::IntegerMatrix;

// -------------------------------------------------------------------------------------------
// the form

/// A symmetric bilinear form over the rationals, exact.
///
/// Symmetry is checked at construction and never re-checked, so [`inertia`] is total: a form that
/// exists is a form whose inertia is defined.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymmetricForm {
    extent: usize,
    /// Row-major, `extent * extent`.
    entries: Vec<Rat>,
}

impl SymmetricForm {
    /// Build from rows, refusing a ragged or asymmetric input by name.
    pub fn from_rows(rows: Vec<Vec<Rat>>) -> Result<Self, InertiaError> {
        let extent = rows.len();
        for (row, entries) in rows.iter().enumerate() {
            if entries.len() != extent {
                return Err(InertiaError::RaggedForm {
                    row,
                    found: entries.len(),
                    extent,
                });
            }
        }
        // Ragged rows are refused above, so the transposed read below is in range.
        for (row, entries) in rows.iter().enumerate() {
            for (column, entry) in entries.iter().enumerate().skip(row + 1) {
                if *entry != rows[column][row] {
                    return Err(InertiaError::NotSymmetric { row, column });
                }
            }
        }
        Ok(Self {
            extent,
            entries: rows.into_iter().flatten().collect(),
        })
    }

    /// A builder convenience over [`SymmetricForm::from_rows`]. Lattice Cartan matrices and
    /// intersection forms are integral, and writing them as `Rat` literals hides their shape.
    pub fn from_integers(rows: &[Vec<i64>]) -> Result<Self, InertiaError> {
        Self::from_rows(
            rows.iter()
                .map(|row| {
                    row.iter()
                        .map(|entry| Rat::from_integer(BigInt::from(*entry)))
                        .collect()
                })
                .collect(),
        )
    }

    /// Read an exact integer matrix as a form. Refuses an asymmetric one rather than symmetrizing
    /// it: a caller who handed in `M` when they meant `M^T M` has a bug, not a rounding problem.
    pub fn from_integer_matrix(matrix: &IntegerMatrix) -> Result<Self, InertiaError> {
        if matrix.rows() != matrix.columns() {
            return Err(InertiaError::RaggedForm {
                row: 0,
                found: matrix.columns(),
                extent: matrix.rows(),
            });
        }
        Self::from_rows(
            (0..matrix.rows())
                .map(|row| {
                    (0..matrix.columns())
                        .map(|column| Rat::from_integer(matrix.at(row, column).clone()))
                        .collect()
                })
                .collect(),
        )
    }

    pub fn from_diagonal(diagonal: Vec<Rat>) -> Self {
        let extent = diagonal.len();
        let mut entries = vec![Rat::zero(); extent * extent];
        for (ordinal, value) in diagonal.into_iter().enumerate() {
            entries[ordinal * extent + ordinal] = value;
        }
        Self { extent, entries }
    }

    pub fn zeros(extent: usize) -> Self {
        Self {
            extent,
            entries: vec![Rat::zero(); extent * extent],
        }
    }

    pub const fn extent(&self) -> usize {
        self.extent
    }

    pub fn at(&self, row: usize, column: usize) -> &Rat {
        &self.entries[row * self.extent + column]
    }

    /// `-A`. The intersection lattice of a surface is built from positive-definite root lattices
    /// with the sign reversed, so this is a construction step and not an afterthought.
    pub fn negated(&self) -> Self {
        Self {
            extent: self.extent,
            entries: self.entries.iter().map(|entry| -entry).collect(),
        }
    }

    /// `A ⊕ B`, block diagonal. `E10 = U ⊕ E8(-1)` is written this way.
    pub fn direct_sum(&self, other: &Self) -> Self {
        let extent = self.extent + other.extent;
        let mut entries = vec![Rat::zero(); extent * extent];
        for row in 0..self.extent {
            for column in 0..self.extent {
                entries[row * extent + column] = self.at(row, column).clone();
            }
        }
        for row in 0..other.extent {
            for column in 0..other.extent {
                entries[(self.extent + row) * extent + self.extent + column] =
                    other.at(row, column).clone();
            }
        }
        Self { extent, entries }
    }

    fn rows(&self) -> Vec<Vec<Rat>> {
        (0..self.extent)
            .map(|row| self.entries[row * self.extent..(row + 1) * self.extent].to_vec())
            .collect()
    }

    fn as_matrix(&self) -> Result<ExactRatMatrix, InertiaError> {
        Ok(ExactRatMatrix::new(self.rows())?)
    }
}

// -------------------------------------------------------------------------------------------
// what is returned

/// The count of each sign in a diagonalization of a symmetric form.
///
/// This is the artifact, not a verdict. `positive + negative` is the rank; `zero` is the nullity;
/// the pair `(positive, negative)` is the signature. Sylvester's law is the statement that all three
/// are invariants of the form.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Inertia {
    pub positive: usize,
    pub zero: usize,
    pub negative: usize,
}

impl Inertia {
    pub const fn extent(&self) -> usize {
        self.positive + self.zero + self.negative
    }

    /// `positive + negative` — the rank of the form, which must agree with the rank of the matrix
    /// computed by any other exact means. That agreement is a cross-check and it can fail.
    pub const fn rank(&self) -> usize {
        self.positive + self.negative
    }

    pub const fn signature(&self) -> (usize, usize) {
        (self.positive, self.negative)
    }

    /// **An empty form is not positive definite here.** This follows the refusal
    /// [`crate::supported_realizers::RealizerSupport::fully_supported`] already carries: a family
    /// collapsed to nothing must not be the cheapest way to satisfy a positivity demand. A caller
    /// who wants the vacuous reading has `negative == 0 && zero == 0` in the open fields.
    pub const fn is_positive_definite(&self) -> bool {
        self.extent() > 0 && self.zero == 0 && self.negative == 0
    }

    /// Same anti-vacuity rule as [`Inertia::is_positive_definite`]. The zero form on a nonempty
    /// space *is* positive semidefinite and reports so; the form on no space at all does not.
    pub const fn is_positive_semidefinite(&self) -> bool {
        self.extent() > 0 && self.negative == 0
    }

    pub const fn is_negative_definite(&self) -> bool {
        self.extent() > 0 && self.zero == 0 && self.positive == 0
    }

    /// Both poles present. This is the condition every Hodge-shaped form satisfies and no Gram
    /// matrix ever does.
    pub const fn is_indefinite(&self) -> bool {
        self.positive > 0 && self.negative > 0
    }

    pub const fn is_degenerate(&self) -> bool {
        self.zero > 0
    }
}

/// How the elimination chooses its next pivot.
///
/// A parameter, because a pivot order is a property of the solver and never of the form. Sylvester's
/// law says every order must return the same [`Inertia`], and
/// `the_inertia_does_not_depend_on_the_pivot_order` is what holds this module to that.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PivotOrder {
    /// Lowest surviving index. The cheapest, and the order whose dependence would be least visible
    /// if the law did not hold.
    FirstNonzero,
    /// Highest surviving index. Included because it walks the elimination backwards.
    LastNonzero,
    /// Least magnitude, ties to the lowest index. Keeps intermediate numerators small.
    SmallestMagnitude,
    /// Greatest magnitude, ties to the lowest index. Included precisely because it is a poor
    /// heuristic: if the returned triple moved with the order, this is the order that would show it.
    LargestMagnitude,
}

impl PivotOrder {
    pub const ALL: [Self; 4] = [
        Self::FirstNonzero,
        Self::LastNonzero,
        Self::SmallestMagnitude,
        Self::LargestMagnitude,
    ];
}

/// One step the elimination took, in the coordinates of the form handed in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PivotStep {
    /// A nonzero diagonal entry was available, and contributed its own sign.
    Diagonal { index: usize, negative: bool },
    /// Every surviving diagonal entry was zero. The `2x2` block on `(low, high)` is `[[0,a],[a,0]]`
    /// with eigenvalues `±a`: one positive and one negative, whatever the sign of `a`.
    ZeroDiagonalPair { low: usize, high: usize },
    /// Every surviving entry was zero; that many dimensions are in the radical.
    ZeroRemainder { extent: usize },
}

/// The steps one elimination actually walked.
///
/// A pivot position is a **receiver coordinate** — a property of the solver, not of the form — and
/// this is the only place one leaves the elimination. It is returned so that "all four orders
/// agreed" can be audited for being an agreement between *different* computations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InertiaSchedule {
    pub order: PivotOrder,
    pub steps: Vec<PivotStep>,
}

impl InertiaSchedule {
    /// Whether the zero-diagonal `2x2` branch fired. A test that wants that branch exercised must
    /// assert this rather than trust that its fixture reached it.
    pub fn used_zero_diagonal_branch(&self) -> bool {
        self.steps
            .iter()
            .any(|step| matches!(step, PivotStep::ZeroDiagonalPair { .. }))
    }

    pub fn zero_diagonal_pairs(&self) -> Vec<(usize, usize)> {
        self.steps
            .iter()
            .filter_map(|step| match step {
                PivotStep::ZeroDiagonalPair { low, high } => Some((*low, *high)),
                _ => None,
            })
            .collect()
    }
}

// -------------------------------------------------------------------------------------------
// the elimination

/// The inertia of a symmetric form, under the default pivot order.
pub fn inertia(form: &SymmetricForm) -> Inertia {
    inertia_with_order(form, PivotOrder::FirstNonzero)
}

/// The inertia under a declared pivot order. Sylvester's law says the order cannot matter.
pub fn inertia_with_order(form: &SymmetricForm, order: PivotOrder) -> Inertia {
    inertia_with_schedule(form, order).0
}

/// The same elimination, returning the steps it took.
///
/// [`inertia`] and [`inertia_with_order`] delegate here rather than the reverse, so the schedule is
/// the schedule the elimination actually walked and cannot drift from it.
pub fn inertia_with_schedule(form: &SymmetricForm, order: PivotOrder) -> (Inertia, InertiaSchedule) {
    let mut working = form.rows();
    let mut alive: Vec<usize> = (0..form.extent()).collect();
    let mut tally = Inertia::default();
    let mut steps = Vec::new();

    while !alive.is_empty() {
        if let Some(index) = choose_diagonal(&working, &alive, order) {
            let pivot = working[index][index].clone();
            let negative = pivot.is_negative();
            if negative {
                tally.negative += 1;
            } else {
                tally.positive += 1;
            }
            steps.push(PivotStep::Diagonal { index, negative });
            eliminate_diagonal(&mut working, &alive, index, &pivot);
            alive.retain(|surviving| *surviving != index);
            continue;
        }
        if let Some((low, high)) = choose_off_diagonal(&working, &alive, order) {
            let pivot = working[low][high].clone();
            // `[[0, a], [a, 0]]` has eigenvalues `+a` and `-a`. One of each, for every nonzero `a`.
            tally.positive += 1;
            tally.negative += 1;
            steps.push(PivotStep::ZeroDiagonalPair { low, high });
            eliminate_pair(&mut working, &alive, low, high, &pivot);
            alive.retain(|surviving| *surviving != low && *surviving != high);
            continue;
        }
        steps.push(PivotStep::ZeroRemainder {
            extent: alive.len(),
        });
        tally.zero += alive.len();
        alive.clear();
    }

    (tally, InertiaSchedule { order, steps })
}

/// `a'_jk = a_jk - a_ji · a_ik / a_ii` over the survivors.
///
/// The pivot row and column are read from a snapshot and are outside the region written, so the
/// update cannot see its own partial results. That is what makes the order a free parameter.
fn eliminate_diagonal(working: &mut [Vec<Rat>], alive: &[usize], index: usize, pivot: &Rat) {
    let survivors: Vec<(usize, Rat)> = alive
        .iter()
        .filter(|surviving| **surviving != index)
        .map(|surviving| (*surviving, working[*surviving][index].clone()))
        .collect();
    for (row, to_pivot_row) in &survivors {
        for (column, to_pivot_column) in &survivors {
            // `a_ik == a_ki`, so one snapshot serves both factors.
            let delta = (to_pivot_row * to_pivot_column) / pivot;
            working[*row][*column] -= delta;
        }
    }
}

/// `a'_kl = a_kl - (a_ki · a_jl + a_kj · a_il) / a` for the block `[[0, a], [a, 0]]` on `(i, j)`.
///
/// This is the Schur complement of a `2x2` block whose inverse is `[[0, 1/a], [1/a, 0]]`, which is
/// where the crossed product comes from.
fn eliminate_pair(working: &mut [Vec<Rat>], alive: &[usize], low: usize, high: usize, pivot: &Rat) {
    let survivors: Vec<usize> = alive
        .iter()
        .copied()
        .filter(|surviving| *surviving != low && *surviving != high)
        .collect();
    let to_low: Vec<Rat> = survivors
        .iter()
        .map(|surviving| working[*surviving][low].clone())
        .collect();
    let to_high: Vec<Rat> = survivors
        .iter()
        .map(|surviving| working[*surviving][high].clone())
        .collect();
    for (left, row) in survivors.iter().enumerate() {
        for (right, column) in survivors.iter().enumerate() {
            let crossed = &to_low[left] * &to_high[right] + &to_high[left] * &to_low[right];
            working[*row][*column] -= crossed / pivot;
        }
    }
}

fn choose_diagonal(working: &[Vec<Rat>], alive: &[usize], order: PivotOrder) -> Option<usize> {
    let candidates: Vec<(usize, Rat)> = alive
        .iter()
        .filter(|index| !working[**index][**index].is_zero())
        .map(|index| (*index, working[*index][*index].clone()))
        .collect();
    pick(&candidates, order)
}

fn choose_off_diagonal(
    working: &[Vec<Rat>],
    alive: &[usize],
    order: PivotOrder,
) -> Option<(usize, usize)> {
    let mut candidates: Vec<((usize, usize), Rat)> = Vec::new();
    for (position, low) in alive.iter().enumerate() {
        for high in &alive[position + 1..] {
            if !working[*low][*high].is_zero() {
                candidates.push(((*low, *high), working[*low][*high].clone()));
            }
        }
    }
    pick(&candidates, order)
}

/// Deterministic in every order, including the tie-breaks: a magnitude order that fell back on
/// iteration order would make the schedule an accident of storage rather than a declaration.
fn pick<K: Copy + Ord>(candidates: &[(K, Rat)], order: PivotOrder) -> Option<K> {
    let mut best: Option<(K, &Rat)> = None;
    for (key, value) in candidates {
        let take = match &best {
            None => true,
            Some((best_key, best_value)) => match order {
                PivotOrder::FirstNonzero => *key < *best_key,
                PivotOrder::LastNonzero => *key > *best_key,
                PivotOrder::SmallestMagnitude => {
                    let (here, there) = (value.abs(), best_value.abs());
                    here < there || (here == there && *key < *best_key)
                }
                PivotOrder::LargestMagnitude => {
                    let (here, there) = (value.abs(), best_value.abs());
                    here > there || (here == there && *key < *best_key)
                }
            },
        };
        if take {
            best = Some((*key, value));
        }
    }
    best.map(|(key, _)| key)
}

// -------------------------------------------------------------------------------------------
// congruence — the operation Sylvester's law is about

/// `P^T A P` for an **invertible** rational `P`.
///
/// Sylvester's law is a statement about invertible changes of basis, and a singular `P` genuinely
/// does change the inertia — `[[1,1],[1,1]]^T · diag(1,-1) · [[1,1],[1,1]]` is the zero form. So a
/// singular `P` is refused by name rather than silently accepted, and
/// `a_singular_change_of_basis_is_refused_and_the_refusal_is_load_bearing` shows the refusal is not
/// decorative. Invertibility is decided by [`ExactRatMatrix::inverse`], which carries its own exact
/// multiplication certificate.
pub fn congruence(
    form: &SymmetricForm,
    basis: &ExactRatMatrix,
) -> Result<SymmetricForm, InertiaError> {
    if !basis.is_square() || basis.rows() != form.extent() {
        return Err(InertiaError::BasisShapeMismatch {
            extent: form.extent(),
            rows: basis.rows(),
            columns: basis.columns(),
        });
    }
    if basis.inverse().is_err() {
        return Err(InertiaError::SingularChangeOfBasis);
    }
    let transported = basis
        .transpose()?
        .multiply(&form.as_matrix()?)?
        .multiply(basis)?;
    // Routed back through the validating constructor: `P^T A P` is symmetric as mathematics, so if
    // it arrives asymmetric the multiplication is wrong and must say so rather than be trusted.
    SymmetricForm::from_rows(
        (0..transported.rows())
            .map(|row| transported.row(row).map(<[Rat]>::to_vec))
            .collect::<Result<Vec<Vec<Rat>>, ExactLinearError>>()?,
    )
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum InertiaError {
    #[error("a symmetric form must be square: row {row} carries {found} entries, extent is {extent}")]
    RaggedForm {
        row: usize,
        found: usize,
        extent: usize,
    },
    #[error("the form is not symmetric: entry ({row}, {column}) differs from ({column}, {row})")]
    NotSymmetric { row: usize, column: usize },
    #[error(
        "a change of basis must be square and match the form's extent {extent}; this one is {rows}x{columns}"
    )]
    BasisShapeMismatch {
        extent: usize,
        rows: usize,
        columns: usize,
    },
    #[error("Sylvester's law holds only for an invertible change of basis; this one is singular")]
    SingularChangeOfBasis,
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rebase_invariants::{PivotRule, smith_normal_form};

    fn integers(rows: &[Vec<i64>]) -> SymmetricForm {
        SymmetricForm::from_integers(rows).expect("fixture is square and symmetric")
    }

    fn diagonal(entries: &[i64]) -> SymmetricForm {
        SymmetricForm::from_diagonal(
            entries
                .iter()
                .map(|entry| Rat::from_integer(BigInt::from(*entry)))
                .collect(),
        )
    }

    fn basis(rows: &[Vec<(i64, i64)>]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|row| {
                    row.iter()
                        .map(|(numerator, denominator)| {
                            Rat::new(BigInt::from(*numerator), BigInt::from(*denominator))
                        })
                        .collect()
                })
                .collect(),
        )
        .expect("fixture basis is rectangular")
    }

    /// The hyperbolic plane `U`. Every indefinite lattice in sight contains one, and it is the
    /// fixture the zero-diagonal branch exists for.
    fn hyperbolic_plane() -> SymmetricForm {
        integers(&[vec![0, 1], vec![1, 0]])
    }

    /// The `E8` Cartan matrix in Bourbaki numbering: a path on `1,3,4,5,6,7,8` with `2` attached to
    /// `4`. Positive definite, determinant one.
    fn e8_cartan() -> SymmetricForm {
        integers(&[
            vec![2, 0, -1, 0, 0, 0, 0, 0],
            vec![0, 2, 0, -1, 0, 0, 0, 0],
            vec![-1, 0, 2, -1, 0, 0, 0, 0],
            vec![0, -1, -1, 2, -1, 0, 0, 0],
            vec![0, 0, 0, -1, 2, -1, 0, 0],
            vec![0, 0, 0, 0, -1, 2, -1, 0],
            vec![0, 0, 0, 0, 0, -1, 2, -1],
            vec![0, 0, 0, 0, 0, 0, -1, 2],
        ])
    }

    /// `E10 = U ⊕ E8(-1)`: the Néron–Severi lattice of a rational elliptic surface. Rank ten,
    /// and the Hodge index theorem says its signature is `(1, 9)`.
    fn e10() -> SymmetricForm {
        hyperbolic_plane().direct_sum(&e8_cartan().negated())
    }

    // -----------------------------------------------------------------------------------------
    // the elementary readings

    #[test]
    fn a_diagonal_form_reports_its_own_signs() {
        assert_eq!(
            inertia(&diagonal(&[1, -1, 0])),
            Inertia {
                positive: 1,
                zero: 1,
                negative: 1
            }
        );
    }

    #[test]
    fn the_zero_form_is_entirely_radical_and_is_semidefinite_without_being_definite() {
        let reading = inertia(&SymmetricForm::zeros(4));
        assert_eq!(
            reading,
            Inertia {
                positive: 0,
                zero: 4,
                negative: 0
            }
        );
        assert!(reading.is_positive_semidefinite());
        assert!(!reading.is_positive_definite());
        assert_eq!(reading.rank(), 0);
    }

    /// The branch a naive `L D L^T` gets wrong. It either divides by the zero diagonal or reports
    /// `(0, 2, 0)`; the true answer is `(1, 0, 1)`, and the schedule proves which branch ran.
    #[test]
    fn the_hyperbolic_plane_is_indefinite_and_the_zero_diagonal_branch_fires() {
        for order in PivotOrder::ALL {
            let (reading, schedule) = inertia_with_schedule(&hyperbolic_plane(), order);
            assert_eq!(
                reading,
                Inertia {
                    positive: 1,
                    zero: 0,
                    negative: 1
                },
                "the hyperbolic plane under {order:?}"
            );
            assert!(reading.is_indefinite());
            assert!(!reading.is_degenerate());
            assert!(
                schedule.used_zero_diagonal_branch(),
                "the fixture must reach the branch it was built for, under {order:?}"
            );
            assert_eq!(schedule.zero_diagonal_pairs(), vec![(0, 1)]);
        }
    }

    /// The zero-diagonal branch with a nontrivial trailing block: the triangle's adjacency matrix
    /// has eigenvalues `2, -1, -1`, so the Schur complement of the `2x2` block must itself come out
    /// negative. An implementation that dropped the crossed term returns `(2, 0, 1)` here.
    #[test]
    fn a_zero_diagonal_block_feeds_the_correct_schur_complement_to_the_rest() {
        let triangle = integers(&[vec![0, 1, 1], vec![1, 0, 1], vec![1, 1, 0]]);
        for order in PivotOrder::ALL {
            let (reading, schedule) = inertia_with_schedule(&triangle, order);
            assert_eq!(
                reading,
                Inertia {
                    positive: 1,
                    zero: 0,
                    negative: 2
                },
                "the triangle under {order:?}"
            );
            assert!(schedule.used_zero_diagonal_branch(), "under {order:?}");
        }
    }

    /// The `2x2` Schur complement carries a **crossed** product, `a_ki · a_jl + a_kj · a_il`, and
    /// both terms are load-bearing. On a three-index form the two terms are equal, so dropping one
    /// only halves the result and never moves a sign; this four-index form is chosen so that
    /// dropping one flips the trailing block from `diag(-2,-2)` to a degenerate `[[-1,1],[1,-1]]`.
    ///
    /// The answer is confirmed away from this elimination entirely: the `0↔1` and `2↔3` symmetries
    /// split the form into eigenvalues `-1`, `-2`, and the spectrum of `[[1,2],[2,2]]`, which is
    /// `(3 ± √17)/2 ≈ 3.56, -0.56`. One positive, three negative, and `det = -4` has the matching
    /// odd parity.
    #[test]
    fn a_zero_diagonal_block_carries_both_crossed_terms_into_the_trailing_block() {
        let form = integers(&[
            vec![0, 1, 1, 1],
            vec![1, 0, 1, 1],
            vec![1, 1, 0, 2],
            vec![1, 1, 2, 0],
        ]);
        for order in PivotOrder::ALL {
            let (reading, schedule) = inertia_with_schedule(&form, order);
            assert_eq!(
                reading,
                Inertia {
                    positive: 1,
                    zero: 0,
                    negative: 3
                },
                "under {order:?}"
            );
            assert!(schedule.used_zero_diagonal_branch(), "under {order:?}");
        }
    }

    /// The negative control on the branch itself: a form with a nonzero diagonal must not reach it.
    /// Without this, an implementation that always took the `2x2` branch would still pass the
    /// hyperbolic test.
    #[test]
    fn a_form_with_a_nonzero_diagonal_never_reaches_the_zero_diagonal_branch() {
        for order in PivotOrder::ALL {
            let (_, schedule) = inertia_with_schedule(&integers(&[vec![1, 1], vec![1, 1]]), order);
            assert!(
                !schedule.used_zero_diagonal_branch(),
                "a nonzero diagonal was available under {order:?}"
            );
        }
    }

    // -----------------------------------------------------------------------------------------
    // both poles

    #[test]
    fn an_indefinite_form_reports_both_poles() {
        let reading = inertia(&integers(&[vec![1, 2], vec![2, 1]]));
        assert_eq!(
            reading,
            Inertia {
                positive: 1,
                zero: 0,
                negative: 1
            }
        );
        assert!(reading.is_indefinite());
        assert!(!reading.is_positive_semidefinite());
    }

    /// The pure negative pole. A suite in which every fixture is positive semidefinite is the same
    /// tautology this module was built to remove, one level up.
    #[test]
    fn a_negative_definite_form_reports_no_positive_direction_at_all() {
        assert_eq!(
            inertia(&diagonal(&[-1, -2, -3])),
            Inertia {
                positive: 0,
                zero: 0,
                negative: 3
            }
        );
        assert!(inertia(&diagonal(&[-1, -2, -3])).is_negative_definite());

        let e8_negated = inertia(&e8_cartan().negated());
        assert_eq!(e8_negated.signature(), (0, 8));
        assert!(e8_negated.is_negative_definite());
        assert!(!e8_negated.is_positive_semidefinite());
    }

    #[test]
    fn the_e8_root_lattice_is_positive_definite() {
        let reading = inertia(&e8_cartan());
        assert_eq!(reading.signature(), (8, 0));
        assert!(reading.is_positive_definite());
        assert!(!reading.is_indefinite());
    }

    // -----------------------------------------------------------------------------------------
    // the Hodge index shape

    /// `Bl_4 P^2`: the classes `H, E1..E4` with `H^2 = 1` and `Ei^2 = -1`. The intersection form
    /// has signature `(1, ρ-1)` with `ρ = 5` — one plus direction and everything else negative.
    #[test]
    fn a_blown_up_plane_has_the_hodge_index_signature() {
        let intersection = diagonal(&[1, -1, -1, -1, -1]);
        let reading = inertia(&intersection);
        let rho = intersection.extent();
        assert_eq!(reading.signature(), (1, rho - 1));
        assert!(reading.is_indefinite());
        assert!(!reading.is_positive_semidefinite(), "the whole point");
    }

    /// The same shape on a lattice that is **not** diagonal, so the zero-diagonal branch has to
    /// fire inside the computation before the count can come out. `E10 = U ⊕ E8(-1)`, rank ten,
    /// signature `(1, 9)`.
    #[test]
    fn the_e10_lattice_has_the_hodge_index_signature_and_needs_the_zero_diagonal_branch() {
        let lattice = e10();
        let rho = lattice.extent();
        assert_eq!(rho, 10);
        for order in PivotOrder::ALL {
            let (reading, schedule) = inertia_with_schedule(&lattice, order);
            assert_eq!(
                reading.signature(),
                (1, rho - 1),
                "E10 under {order:?} must be (1, 9)"
            );
            assert!(!reading.is_degenerate(), "E10 is unimodular");
            assert!(
                schedule.used_zero_diagonal_branch(),
                "the U summand never acquires a nonzero diagonal under {order:?}"
            );
        }
    }

    // -----------------------------------------------------------------------------------------
    // Sylvester's law itself

    /// The real theorem. `P^T A P` has the same inertia as `A` for every invertible rational `P` —
    /// and each `P` is shown to actually move the matrix first, because a `P` that left `A` fixed
    /// would make the whole check vacuous.
    #[test]
    fn congruence_by_an_invertible_basis_preserves_the_inertia() {
        let forms = [
            diagonal(&[1, -1]),
            hyperbolic_plane(),
            integers(&[vec![2, 1], vec![1, 2]]),
            integers(&[vec![1, 1], vec![1, 1]]),
        ];
        // The coordinate swap `[[0,1],[1,0]]` is deliberately **not** here. It is invertible, but it
        // fixes the hyperbolic plane exactly — `P^T U P = U` — so the pair `(U, swap)` would assert
        // an invariance across no change at all. The `assert_ne!` below caught it, which is the
        // whole reason that assertion is per pair and not per form.
        let bases = [
            // unimodular shear
            basis(&[vec![(1, 1), (1, 1)], vec![(0, 1), (1, 1)]]),
            // positive diagonal scaling
            basis(&[vec![(2, 1), (0, 1)], vec![(0, 1), (3, 1)]]),
            // negative determinant
            basis(&[vec![(1, 1), (2, 1)], vec![(3, 1), (4, 1)]]),
            // genuinely fractional
            basis(&[vec![(1, 2), (1, 3)], vec![(1, 1), (1, 1)]]),
        ];

        for form in &forms {
            let before = inertia(form);
            for change in &bases {
                let after_form = congruence(form, change).expect("the basis is invertible");
                assert_ne!(
                    &after_form, form,
                    "a change of basis that leaves the matrix fixed proves nothing"
                );
                assert_eq!(
                    inertia(&after_form),
                    before,
                    "Sylvester: inertia is a congruence invariant"
                );
            }
        }
    }

    /// The vacuity the test above guards against, exhibited rather than described. An invertible
    /// basis that happens to fix the form turns "the inertia agreed" into "the same matrix was read
    /// twice", and the hyperbolic plane has such a basis.
    #[test]
    fn a_basis_that_fixes_the_form_would_make_the_congruence_check_vacuous() {
        let form = hyperbolic_plane();
        let swap = basis(&[vec![(0, 1), (1, 1)], vec![(1, 1), (0, 1)]]);
        assert_eq!(
            congruence(&form, &swap).expect("the swap is invertible"),
            form,
            "the swap fixes U, so this pair carries no evidence about Sylvester's law"
        );
    }

    /// The same law on a rank-ten lattice, through a basis that mixes the hyperbolic summand into
    /// the `E8` one so the elimination cannot take the same route twice.
    #[test]
    fn congruence_preserves_the_inertia_of_the_e10_lattice() {
        let lattice = e10();
        let mut rows = vec![vec![(0i64, 1i64); 10]; 10];
        for (index, row) in rows.iter_mut().enumerate() {
            row[index] = (1, 1);
        }
        // Unitriangular, so invertible over the integers, and it moves every summand.
        rows[0][2] = (1, 1);
        rows[1][5] = (-2, 1);
        rows[3][9] = (1, 1);
        rows[6][8] = (3, 1);
        let change = basis(&rows);

        let transported = congruence(&lattice, &change).expect("unitriangular is invertible");
        assert_ne!(transported, lattice, "the basis must move the lattice");
        assert_eq!(inertia(&transported).signature(), (1, 9));
    }

    /// Sylvester's law is about **invertible** changes of basis. This shows the hypothesis is
    /// load-bearing rather than ceremonial: the singular basis is refused, and the matrix it would
    /// have produced really does have a different inertia.
    #[test]
    fn a_singular_change_of_basis_is_refused_and_the_refusal_is_load_bearing() {
        let form = diagonal(&[1, -1]);
        let singular = basis(&[vec![(1, 1), (1, 1)], vec![(1, 1), (1, 1)]]);
        assert_eq!(
            congruence(&form, &singular),
            Err(InertiaError::SingularChangeOfBasis)
        );
        // `[[1,1],[1,1]]^T · diag(1,-1) · [[1,1],[1,1]]` is the zero form, whose inertia is (0,2,0)
        // and not the (1,0,1) it came from. The refusal is what keeps that from being reported as
        // an invariant.
        assert_eq!(inertia(&form).signature(), (1, 1));
        assert_eq!(
            inertia(&SymmetricForm::zeros(2)),
            Inertia {
                positive: 0,
                zero: 2,
                negative: 0
            }
        );
    }

    /// The pivot order is a schedule and nothing else. This asserts the stronger half first — that
    /// the four orders really did walk **different** schedules — because four identical schedules
    /// would be one computation compared with itself three times.
    #[test]
    fn the_inertia_does_not_depend_on_the_pivot_order() {
        let forms = [
            integers(&[vec![1, 2, 0], vec![2, 5, 0], vec![0, 0, -3]]),
            e10(),
            integers(&[vec![0, 1, 1], vec![1, 0, 1], vec![1, 1, 0]]),
            integers(&[vec![14, 28, 2], vec![28, 56, 4], vec![2, 4, 1]]),
            // A NEGATIVE diagonal pivot with a survivor. An elimination that divided by `|a_ii|`
            // rather than `a_ii` agrees with the truth whenever it happens to pivot on the positive
            // entry and disagrees when it pivots on the negative one, so only a fixture like this
            // one makes the order visible at all.
            integers(&[vec![-1, 2], vec![2, 1]]),
            integers(&[
                vec![0, 1, 1, 1],
                vec![1, 0, 1, 1],
                vec![1, 1, 0, 2],
                vec![1, 1, 2, 0],
            ]),
        ];
        for form in &forms {
            let mut readings = Vec::new();
            let mut schedules = Vec::new();
            for order in PivotOrder::ALL {
                let (reading, schedule) = inertia_with_schedule(form, order);
                readings.push(reading);
                schedules.push(schedule.steps);
            }
            assert!(
                schedules.iter().any(|steps| *steps != schedules[0]),
                "the orders walked one schedule, so their agreement is not evidence: {schedules:?}"
            );
            assert!(
                readings.windows(2).all(|pair| pair[0] == pair[1]),
                "the inertia moved with the pivot order: {readings:?}"
            );
        }
    }

    /// Inertia is additive over direct sums. A theorem, and it can fail.
    #[test]
    fn the_inertia_of_a_direct_sum_is_the_sum_of_the_inertias() {
        let left = hyperbolic_plane();
        let right = e8_cartan().negated();
        let (a, b) = (inertia(&left), inertia(&right));
        assert_eq!(
            inertia(&left.direct_sum(&right)),
            Inertia {
                positive: a.positive + b.positive,
                zero: a.zero + b.zero,
                negative: a.negative + b.negative,
            }
        );
    }

    // -----------------------------------------------------------------------------------------
    // degeneracy, and the cross-check against an independent exact rank

    /// A Gram matrix of dependent vectors: `v2 = 2 v1`, `v3` independent. Positive **semi**definite
    /// and not definite, with the nullity exhibited rather than hidden.
    #[test]
    fn a_gram_matrix_of_dependent_vectors_is_semidefinite_and_not_definite() {
        let gram = integers(&[vec![14, 28, 2], vec![28, 56, 4], vec![2, 4, 1]]);
        let reading = inertia(&gram);
        assert_eq!(
            reading,
            Inertia {
                positive: 2,
                zero: 1,
                negative: 0
            }
        );
        assert!(reading.is_positive_semidefinite());
        assert!(!reading.is_positive_definite());
        assert!(reading.is_degenerate());
    }

    /// `positive + negative` is the rank, and the Smith normal form is an **independent** exact
    /// route to the same number. The fixtures include degenerate ones on purpose: a rank check run
    /// only on invertible material cannot fail and would be the tautology again.
    #[test]
    fn the_rank_agrees_with_the_smith_normal_form_of_the_same_matrix() {
        let forms = [
            e10(),
            e8_cartan(),
            hyperbolic_plane(),
            diagonal(&[1, -1, 0]),
            integers(&[vec![14, 28, 2], vec![28, 56, 4], vec![2, 4, 1]]),
            integers(&[vec![1, 1], vec![1, 1]]),
            integers(&[
                vec![0, 1, 1, 1],
                vec![1, 0, 1, 1],
                vec![1, 1, 0, 2],
                vec![1, 1, 2, 0],
            ]),
            SymmetricForm::zeros(3),
        ];
        let mut saw_degenerate = false;
        for form in &forms {
            let mut matrix = IntegerMatrix::zeros(form.extent(), form.extent());
            for row in 0..form.extent() {
                for column in 0..form.extent() {
                    let entry = form.at(row, column);
                    assert!(entry.is_integer(), "this cross-check runs over integral forms");
                    matrix.set(row, column, entry.to_integer());
                }
            }
            let reading = inertia(form);
            saw_degenerate |= reading.is_degenerate();
            assert_eq!(
                reading.rank(),
                smith_normal_form(&matrix, PivotRule::FirstNonzero).rank(),
                "inertia rank and Smith rank disagree on extent {}",
                form.extent()
            );
        }
        assert!(
            saw_degenerate,
            "a rank cross-check that never saw a degenerate form cannot fail"
        );
    }

    // -----------------------------------------------------------------------------------------
    // controls and refusals

    /// An empty form is not a positivity result. Same refusal
    /// `RealizerSupport::fully_supported` carries: nothing to measure is not everything measured.
    #[test]
    fn an_empty_form_is_not_a_positivity_discharge() {
        let reading = inertia(&SymmetricForm::zeros(0));
        assert_eq!(reading, Inertia::default());
        assert!(!reading.is_positive_definite());
        assert!(!reading.is_positive_semidefinite());
        assert!(!reading.is_negative_definite());
    }

    #[test]
    fn a_ragged_or_asymmetric_input_is_refused_by_name() {
        assert_eq!(
            SymmetricForm::from_integers(&[vec![1, 2], vec![2]]),
            Err(InertiaError::RaggedForm {
                row: 1,
                found: 1,
                extent: 2
            })
        );
        assert_eq!(
            SymmetricForm::from_integers(&[vec![1, 2], vec![3, 4]]),
            Err(InertiaError::NotSymmetric { row: 0, column: 1 })
        );
    }

    #[test]
    fn a_change_of_basis_of_the_wrong_extent_is_refused() {
        let form = diagonal(&[1, -1, 1]);
        let change = basis(&[vec![(1, 1), (0, 1)], vec![(0, 1), (1, 1)]]);
        assert_eq!(
            congruence(&form, &change),
            Err(InertiaError::BasisShapeMismatch {
                extent: 3,
                rows: 2,
                columns: 2
            })
        );
    }

    #[test]
    fn an_integer_matrix_that_is_not_symmetric_is_refused_rather_than_symmetrized() {
        let mut matrix = IntegerMatrix::zeros(2, 2);
        matrix.set(0, 1, BigInt::from(3));
        assert_eq!(
            SymmetricForm::from_integer_matrix(&matrix),
            Err(InertiaError::NotSymmetric { row: 0, column: 1 })
        );
    }

    /// Rational entries, not just integral ones. The Schur complement leaves the integers on the
    /// very first step of the hyperbolic plane, so this is the carrier's normal mode.
    #[test]
    fn a_form_with_fractional_entries_is_read_exactly() {
        let form = SymmetricForm::from_rows(vec![
            vec![
                Rat::new(BigInt::from(1), BigInt::from(3)),
                Rat::new(BigInt::from(1), BigInt::from(2)),
            ],
            vec![
                Rat::new(BigInt::from(1), BigInt::from(2)),
                Rat::new(BigInt::from(3), BigInt::from(4)),
            ],
        ])
        .expect("symmetric");
        // det = 1/3 · 3/4 - 1/4 = 0, so the form is degenerate: rank one, and positive.
        assert_eq!(
            inertia(&form),
            Inertia {
                positive: 1,
                zero: 1,
                negative: 0
            }
        );
    }
}
