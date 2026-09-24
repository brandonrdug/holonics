//! **Sylvester's law of inertia, computed exactly over the rationals.**
//!
//! A positivity claim is a claim about the signs of a symmetric form, and the count of each sign is
//! what can come out wrong: the Hodge index theorem (signature `(1, ρ − 1)` on the Néron–Severi
//! group) and the Hodge–Riemann relations are signature theorems about indefinite forms. This
//! module makes that count computable, so passivity (`n₋(sym R) = 0`) and definiteness are decided
//! on the material rather than assumed from the shape of an expression.
//!
//! The elimination is the Schur complement, recursed: by Haynsworth's additivity the inertia of a
//! block form is the inertia of its leading block plus the inertia of its Schur complement.
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
//! schedule the elimination actually walked, and different orders return the same triple.
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
//!
//! ## Exactness
//!
//! `Rat` throughout, which is `BigRational`. No float, no tolerance, and no pivoting heuristic that
//! reads a magnitude as a *decision*: the magnitude orders in [`PivotOrder::SmallestMagnitude`] and
//! [`PivotOrder::LargestMagnitude`] choose which exact step to take next and can never change what
//! is returned. That is measurement, not governance.

use crate::ratio::Rat;
use num_traits::{Signed, Zero};
use thiserror::Error;

use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};
use crate::ratio::work::ExactWork;

// -------------------------------------------------------------------------------------------
// the form

/// A symmetric bilinear form over the rationals, exact.
///
/// Symmetry is checked at construction, so [`inertia`] is total: a form that exists is a form
/// whose inertia is defined.
#[derive(Clone, Debug, PartialEq, Eq)]
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

    #[cfg(test)]
    /// A builder convenience over [`SymmetricForm::from_rows`]. Lattice Cartan matrices and
    /// intersection forms are integral, and writing them as `Rat` literals hides their shape.
    pub(crate) fn from_integers(rows: &[Vec<i64>]) -> Result<Self, InertiaError> {
        Self::from_rows(
            rows.iter()
                .map(|row| {
                    row.iter()
                        .map(|entry| crate::ratio::integer(*entry))
                        .collect()
                })
                .collect(),
        )
    }

    #[cfg(test)]
    pub(crate) fn from_diagonal(diagonal: Vec<Rat>) -> Self {
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
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Inertia {
    pub positive: usize,
    pub zero: usize,
    pub negative: usize,
}

impl Inertia {
    pub const fn extent(&self) -> usize {
        self.positive + self.zero + self.negative
    }

    pub const fn signature(&self) -> (usize, usize) {
        (self.positive, self.negative)
    }

    /// **An empty form is not positive definite here**: a family collapsed to nothing is not a
    /// positivity discharge. A caller who wants the vacuous reading has `negative == 0 && zero == 0`
    /// in the open fields.
    pub const fn is_positive_definite(&self) -> bool {
        self.extent() > 0 && self.zero == 0 && self.negative == 0
    }
}

/// How the elimination chooses its next pivot.
///
/// A parameter, because a pivot order is a property of the solver and never of the form. Sylvester's
/// law says every order must return the same [`Inertia`], and
/// `the_inertia_does_not_depend_on_the_pivot_order` is what holds this module to that.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

/// One step the elimination took, in the coordinates of the form handed in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PivotStep {
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct InertiaSchedule {
    pub order: PivotOrder,
    pub steps: Vec<PivotStep>,
}

impl InertiaSchedule {}

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
pub(crate) fn inertia_with_schedule(
    form: &SymmetricForm,
    order: PivotOrder,
) -> (Inertia, InertiaSchedule) {
    let (tally, schedule, _) = inertia_with_work(form, order);
    (tally, schedule)
}

/// **The same elimination, returning what it cost.**
///
/// The dominating quantity of an exact elimination is the intermediate entry width, so the work is
/// counted inside the elimination, on every entry it writes.
///
/// The pivot count is not the dominating quantity: a form can take `k` pivots whose entries stay
/// narrow, or `k` pivots whose entries are `k × k` minors. The steps say how many; only
/// [`ExactWork::peak_bits`] says how wide.
///
/// The counting is exact and adds no arithmetic: every operation was already performed, and this
/// records that it was.
pub(crate) fn inertia_with_work(
    form: &SymmetricForm,
    order: PivotOrder,
) -> (Inertia, InertiaSchedule, ExactWork) {
    let mut work = ExactWork::nothing();
    let extent = form.extent();
    work.resident(u64::try_from(extent.saturating_mul(extent)).unwrap_or(u64::MAX));
    // The form as handed in is the widest thing that stands before a single step is taken, so its
    // own entries enter the peak. A deed whose INPUT is wide has already paid for that width.
    for row in 0..extent {
        for column in 0..extent {
            work.wrote(form.at(row, column));
        }
    }
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
            // Each pivot depends on the last: the span of a serial elimination is its pivot count.
            work.stepped();
            eliminate_diagonal(&mut working, &alive, index, &pivot, &mut work);
            alive.retain(|surviving| *surviving != index);
            continue;
        }
        if let Some((low, high)) = choose_off_diagonal(&working, &alive, order) {
            let pivot = working[low][high].clone();
            // `[[0, a], [a, 0]]` has eigenvalues `+a` and `-a`. One of each, for every nonzero `a`.
            tally.positive += 1;
            tally.negative += 1;
            steps.push(PivotStep::ZeroDiagonalPair { low, high });
            work.stepped();
            eliminate_pair(&mut working, &alive, low, high, &pivot, &mut work);
            alive.retain(|surviving| *surviving != low && *surviving != high);
            continue;
        }
        steps.push(PivotStep::ZeroRemainder {
            extent: alive.len(),
        });
        tally.zero += alive.len();
        alive.clear();
    }

    (tally, InertiaSchedule { order, steps }, work)
}

/// `a'_jk = a_jk - a_ji · a_ik / a_ii` over the survivors.
///
/// The pivot row and column are read from a snapshot and are outside the region written, so the
/// update cannot see its own partial results. That is what makes the order a free parameter.
fn eliminate_diagonal(
    working: &mut [Vec<Rat>],
    alive: &[usize],
    index: usize,
    pivot: &Rat,
    work: &mut ExactWork,
) {
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
            // One multiply, one divide (which normalises), one subtract, one entry written.
            work.multiplied(1);
            work.divided(1);
            work.added(1);
            work.wrote(&working[*row][*column]);
        }
    }
}

/// `a'_kl = a_kl - (a_ki · a_jl + a_kj · a_il) / a` for the block `[[0, a], [a, 0]]` on `(i, j)`.
///
/// This is the Schur complement of a `2x2` block whose inverse is `[[0, 1/a], [1/a, 0]]`, which is
/// where the crossed product comes from.
fn eliminate_pair(
    working: &mut [Vec<Rat>],
    alive: &[usize],
    low: usize,
    high: usize,
    pivot: &Rat,
    work: &mut ExactWork,
) {
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
            // Two multiplies, one add for the cross, one divide, one subtract, one entry written.
            work.multiplied(2);
            work.added(2);
            work.divided(1);
            work.wrote(&working[*row][*column]);
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

// -------------------------------------------------------------------------------------------
// the pull-back — what congruence refuses, returned as a bound instead of an error

// -------------------------------------------------------------------------------------------
// the rank–trace defect — the finite identity the external certificate is tight on

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum InertiaError {
    #[error(
        "a symmetric form must be square: row {row} carries {found} entries, extent is {extent}"
    )]
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
    use num_bigint::BigInt;

    const ORDERS: [PivotOrder; 4] = [
        PivotOrder::FirstNonzero,
        PivotOrder::LastNonzero,
        PivotOrder::SmallestMagnitude,
        PivotOrder::LargestMagnitude,
    ];

    fn integers(rows: &[Vec<i64>]) -> SymmetricForm {
        SymmetricForm::from_integers(rows).expect("fixture is square and symmetric")
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

    fn hyperbolic_plane() -> SymmetricForm {
        integers(&[vec![0, 1], vec![1, 0]])
    }

    /// `E8(−1)`: the negated `E8` Cartan matrix in Bourbaki numbering.
    fn e8_negated() -> SymmetricForm {
        integers(&[
            vec![-2, 0, 1, 0, 0, 0, 0, 0],
            vec![0, -2, 0, 1, 0, 0, 0, 0],
            vec![1, 0, -2, 1, 0, 0, 0, 0],
            vec![0, 1, 1, -2, 1, 0, 0, 0],
            vec![0, 0, 0, 1, -2, 1, 0, 0],
            vec![0, 0, 0, 0, 1, -2, 1, 0],
            vec![0, 0, 0, 0, 0, 1, -2, 1],
            vec![0, 0, 0, 0, 0, 0, 1, -2],
        ])
    }

    fn signs(positive: usize, zero: usize, negative: usize) -> Inertia {
        Inertia {
            positive,
            zero,
            negative,
        }
    }

    /// **The zero-diagonal branch.** Every surviving diagonal zero leaves the block `[[0,a],[a,0]]`,
    /// one positive and one negative direction; its Schur complement carries both crossed terms.
    /// A diagonal-only `LDLᵀ` reports the hyperbolic plane as degenerate.
    #[test]
    fn the_zero_diagonal_block_contributes_one_of_each_sign_and_both_crossed_terms() {
        let crossed = integers(&[
            vec![0, 1, 1, 1],
            vec![1, 0, 1, 1],
            vec![1, 1, 0, 2],
            vec![1, 1, 2, 0],
        ]);
        for order in ORDERS {
            assert_eq!(
                inertia_with_order(&hyperbolic_plane(), order),
                signs(1, 0, 1)
            );
            assert_eq!(inertia_with_order(&crossed, order), signs(1, 0, 3));
        }
    }

    /// **Sylvester's law**: the inertia is invariant under every invertible congruence `PᵀAP`, and
    /// does not depend on the pivot order of the elimination that reads it.
    #[test]
    fn inertia_is_a_congruence_invariant_under_every_pivot_order() {
        let forms = [
            hyperbolic_plane(),
            integers(&[vec![2, 1], vec![1, 2]]),
            integers(&[vec![1, 1], vec![1, 1]]),
        ];
        let bases = [
            basis(&[vec![(1, 1), (1, 1)], vec![(0, 1), (1, 1)]]),
            basis(&[vec![(1, 1), (2, 1)], vec![(3, 1), (4, 1)]]),
            basis(&[vec![(1, 2), (1, 3)], vec![(1, 1), (1, 1)]]),
        ];
        for form in &forms {
            let before = inertia(form);
            for order in ORDERS {
                assert_eq!(inertia_with_order(form, order), before);
            }
            for change in &bases {
                let moved = congruence(form, change).expect("the basis is invertible");
                assert_ne!(&moved, form);
                assert_eq!(inertia(&moved), before);
            }
        }
    }

    /// A singular change of basis can change the inertia (`diag(1,−1)` goes to the zero form), so
    /// congruence refuses it by name.
    #[test]
    fn a_singular_change_of_basis_is_refused() {
        let form = integers(&[vec![1, 0], vec![0, -1]]);
        let singular = basis(&[vec![(1, 1), (1, 1)], vec![(1, 1), (1, 1)]]);
        assert_eq!(
            congruence(&form, &singular),
            Err(InertiaError::SingularChangeOfBasis)
        );
    }

    /// **Additivity** (Haynsworth): the inertia of `A ⊕ B` is the sum of the inertias, and
    /// `E10 = U ⊕ E8(−1)` has the Hodge index signature `(1, 9)`.
    #[test]
    fn the_inertia_of_a_direct_sum_is_the_sum_and_e10_has_the_hodge_index_signature() {
        let (left, right) = (hyperbolic_plane(), e8_negated());
        let (a, b) = (inertia(&left), inertia(&right));
        let sum = inertia(&left.direct_sum(&right));
        assert_eq!(
            sum,
            signs(
                a.positive + b.positive,
                a.zero + b.zero,
                a.negative + b.negative
            )
        );
        assert_eq!(sum.signature(), (1, 9));
    }
}
