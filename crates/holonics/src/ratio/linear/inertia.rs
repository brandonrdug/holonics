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
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use thiserror::Error;

use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};

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
    let mut working = Chart::of(form);
    let mut alive: Vec<usize> = (0..form.extent()).collect();
    let mut tally = Inertia::default();
    let mut steps = Vec::new();

    while !alive.is_empty() {
        if let Some(index) = working.choose_diagonal(&alive, order) {
            let negative = working.numerators[index][index].is_negative();
            if negative {
                tally.negative += 1;
            } else {
                tally.positive += 1;
            }
            steps.push(PivotStep::Diagonal { index, negative });
            working.eliminate_diagonal(&alive, index);
            alive.retain(|surviving| *surviving != index);
            continue;
        }
        if let Some((low, high)) = working.choose_off_diagonal(&alive, order) {
            // `[[0, a], [a, 0]]` has eigenvalues `+a` and `-a`. One of each, for every nonzero `a`.
            tally.positive += 1;
            tally.negative += 1;
            steps.push(PivotStep::ZeroDiagonalPair { low, high });
            working.eliminate_pair(&alive, low, high);
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

/// [definition; agent-inferred] **The surviving Schur complement in the integral chart.** Row `j` is
/// `N_j / D_j` with integer numerators and a positive denominator. A step multiplies each coupled
/// row through by the pivot instead of dividing by it (fraction-free), then divides the row by the
/// greatest common divisor of its surviving numerators and its denominator: one integer reduction
/// per row where the rational elimination normalizes every entry several times. Every entry keeps
/// its exact value, so every zero test, sign and magnitude comparison reads what the rational
/// elimination reads, and the tally and schedule are the same.
struct Chart {
    numerators: Vec<Vec<BigInt>>,
    denominators: Vec<BigInt>,
}

/// A magnitude `|N| / D` held as the pair `(|N|, D)`.
type Magnitude<'a> = (BigInt, &'a BigInt);

impl Chart {
    fn of(form: &SymmetricForm) -> Self {
        let (numerators, denominators) = form
            .rows()
            .iter()
            .map(|row| crate::ratio::linear::vector::integral(row))
            .unzip();
        Self {
            numerators,
            denominators,
        }
    }

    /// `|a_ij|` as the pair `(|N_ij|, D_i)`, compared by cross multiplication.
    fn magnitude(&self, row: usize, column: usize) -> Magnitude<'_> {
        (self.numerators[row][column].abs(), &self.denominators[row])
    }

    fn choose_diagonal(&self, alive: &[usize], order: PivotOrder) -> Option<usize> {
        let candidates: Vec<(usize, Magnitude<'_>)> = alive
            .iter()
            .filter(|index| !self.numerators[**index][**index].is_zero())
            .map(|index| (*index, self.magnitude(*index, *index)))
            .collect();
        pick_magnitude(&candidates, order)
    }

    fn choose_off_diagonal(&self, alive: &[usize], order: PivotOrder) -> Option<(usize, usize)> {
        let mut candidates: Vec<((usize, usize), Magnitude<'_>)> = Vec::new();
        for (position, low) in alive.iter().enumerate() {
            for high in &alive[position + 1..] {
                if !self.numerators[*low][*high].is_zero() {
                    candidates.push(((*low, *high), self.magnitude(*low, *high)));
                }
            }
        }
        pick_magnitude(&candidates, order)
    }

    /// `a'_jk = a_jk - a_ji · a_ik / a_ii` over the survivors, as
    /// `N'_jk = N_jk N_ii − N_ji N_ik` over `D'_j = D_j N_ii`.
    ///
    /// The pivot row is read from a snapshot and is outside the region written, so the update
    /// cannot see its own partial results. That is what makes the order a free parameter. A
    /// survivor whose entry to the pivot is zero receives a zero update and is not written (a
    /// block form eliminates block by block).
    fn eliminate_diagonal(&mut self, alive: &[usize], index: usize) {
        let pivot_row = self.numerators[index].clone();
        let pivot = pivot_row[index].clone();
        let columns: Vec<usize> = alive.iter().copied().filter(|k| *k != index).collect();
        for &row in &columns {
            let coupling = self.numerators[row][index].clone();
            if coupling.is_zero() {
                continue;
            }
            let numerators = &mut self.numerators[row];
            for &column in &columns {
                let scaled = &numerators[column] * &pivot;
                numerators[column] = if pivot_row[column].is_zero() {
                    scaled
                } else {
                    scaled - &coupling * &pivot_row[column]
                };
            }
            self.denominators[row] = &self.denominators[row] * &pivot;
            self.settle(row, &columns);
        }
    }

    /// `a'_kl = a_kl - (a_ki · a_jl + a_kj · a_il) / a` for the block `[[0, a], [a, 0]]` on
    /// `(i, j)`, `a = N_ij / D_i`, as `N'_kl = N_kl D_j N_ij − N_ki N_jl D_i − N_kj N_il D_j` over
    /// `D'_k = D_k D_j N_ij`.
    ///
    /// This is the Schur complement of a `2x2` block whose inverse is `[[0, 1/a], [1/a, 0]]`, which
    /// is where the crossed product comes from. A survivor coupled to neither index is not written.
    fn eliminate_pair(&mut self, alive: &[usize], low: usize, high: usize) {
        let (low_row, high_row) = (self.numerators[low].clone(), self.numerators[high].clone());
        let (low_denominator, high_denominator) = (
            self.denominators[low].clone(),
            self.denominators[high].clone(),
        );
        let pivot = low_row[high].clone();
        let scale = &high_denominator * &pivot;
        let columns: Vec<usize> = alive
            .iter()
            .copied()
            .filter(|k| *k != low && *k != high)
            .collect();
        for &row in &columns {
            let (to_low, to_high) = (
                self.numerators[row][low].clone(),
                self.numerators[row][high].clone(),
            );
            if to_low.is_zero() && to_high.is_zero() {
                continue;
            }
            let (from_low, from_high) = (&to_low * &low_denominator, &to_high * &high_denominator);
            let numerators = &mut self.numerators[row];
            for &column in &columns {
                numerators[column] = &numerators[column] * &scale
                    - &from_low * &high_row[column]
                    - &from_high * &low_row[column];
            }
            self.denominators[row] = &self.denominators[row] * &scale;
            self.settle(row, &columns);
        }
    }

    /// Keep the row's denominator positive and divide the row by the greatest common divisor of
    /// its surviving numerators and its denominator.
    fn settle(&mut self, row: usize, columns: &[usize]) {
        if self.denominators[row].is_negative() {
            self.denominators[row] = -&self.denominators[row];
            for &column in columns {
                self.numerators[row][column] = -&self.numerators[row][column];
            }
        }
        let mut divisor = self.denominators[row].clone();
        for &column in columns {
            if divisor.is_one() {
                return;
            }
            let value = &self.numerators[row][column];
            if !value.is_zero() {
                divisor = crate::ratio::gcd(&divisor, value);
            }
        }
        if divisor.is_one() {
            return;
        }
        self.denominators[row] = &self.denominators[row] / &divisor;
        for &column in columns {
            let value = &self.numerators[row][column];
            if !value.is_zero() {
                self.numerators[row][column] = value / &divisor;
            }
        }
    }
}

/// The declared order's choice among the candidates, their magnitudes held as `(|N|, D)` and
/// compared by cross multiplication (`|N_a|/D_a < |N_b|/D_b` iff `|N_a| D_b < |N_b| D_a`).
/// Deterministic in every order, including the tie-breaks: a magnitude order that fell back on
/// iteration order would make the schedule an accident of storage rather than a declaration.
fn pick_magnitude<K: Copy + Ord>(
    candidates: &[(K, Magnitude<'_>)],
    order: PivotOrder,
) -> Option<K> {
    let mut best: Option<(K, &Magnitude<'_>)> = None;
    for (key, value) in candidates {
        let take = match &best {
            None => true,
            Some((best_key, best_value)) => {
                let compare = || (&value.0 * best_value.1).cmp(&(&best_value.0 * value.1));
                match order {
                    PivotOrder::FirstNonzero => *key < *best_key,
                    PivotOrder::LastNonzero => *key > *best_key,
                    PivotOrder::SmallestMagnitude => match compare() {
                        std::cmp::Ordering::Less => true,
                        std::cmp::Ordering::Equal => *key < *best_key,
                        std::cmp::Ordering::Greater => false,
                    },
                    PivotOrder::LargestMagnitude => match compare() {
                        std::cmp::Ordering::Greater => true,
                        std::cmp::Ordering::Equal => *key < *best_key,
                        std::cmp::Ordering::Less => false,
                    },
                }
            }
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
