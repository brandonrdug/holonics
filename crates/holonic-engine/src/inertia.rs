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
//! ## This module is the fifth name of one organ, and it is the one that computes its law
//!
//! `docs/canon/THE_INFORMATION_ENGINE.md` records the Schur complement as **one organ under four
//! names, none of which cites the others**: `diffusion.rs`'s certified boundary transfer, `H.0219`'s
//! parallelization barrier, the effective tension `S = D − C*A⁻¹C` of
//! `research/papers/source/mathematics/theorems/conditioned-effective-tension.typ`, and **`H.0127` *Schur
//! complement and inertia***, `proved-standard`, which states the law the other three use.
//!
//! **This module is the fifth**, and it is the one that actually computes `H.0127`: the elimination
//! below *is* the Schur complement, recursed, exactly over `Rat`. Added 2026-08-16 after a campaign
//! measured that it cited none of the four.
//!
//! That matters beyond bookkeeping. `H.0127`'s second sentence — *"the block matrix has the inertia
//! of `A` plus the inertia of its Schur complement"* — is Haynsworth's additivity, and it is the law
//! the Riemann support-successor obligation is stated in:
//! `research/papers/source/mathematics/theorems/weil-support-induction-reduction.typ` reduces the hypothesis
//! to `(RANGE)` and `(OPERATOR SHORT)`, which are Albert's block-positivity pair, whose finite form
//! is `H/A >= 0`. `examples/the_pullback_bounds_the_inertia.rs` returns
//! `In(H) = In(A) + In(H/A)` on three fixtures, with the positive-definite arm labelled as the one
//! that cannot fail.
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
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::exact_work::ExactWork;
use crate::rebase_invariants::IntegerMatrix;
mod source_energy;
pub use source_energy::{positive_source_energy, PositiveSourceEnergy, SourceEnergyError};

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
pub fn inertia_with_schedule(
    form: &SymmetricForm,
    order: PivotOrder,
) -> (Inertia, InertiaSchedule) {
    let (tally, schedule, _) = inertia_with_work(form, order);
    (tally, schedule)
}

/// **The same elimination, returning what it cost.**
///
/// Added 2026-08-17. `docs/canon/TABLET_THE_CHART.md` §3.7 records that *"the dominating quantity is
/// intermediate entry bit-length and nothing counts it. Until a work vector exists, no cost question
/// in this repository has a lawful answer."* This is that count, taken at the only place it can be
/// taken exactly: inside the elimination, on every entry it writes.
///
/// **Why the schedule was not enough, in its own words.** `InertiaSchedule` returns the pivot steps,
/// and the same tablet says the pivot count is *provably not* the dominating quantity — a form can
/// take `k` pivots whose entries stay narrow, or `k` pivots whose entries are `k × k` minors. The
/// steps say how many; only [`ExactWork::peak_bits`] says how wide.
///
/// The counting is exact and adds no arithmetic: every operation was already performed, and this
/// records that it was.
pub fn inertia_with_work(
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

/// **The pull-back of a form along an arbitrary linear map, with the inertia bound it obeys.**
///
/// # Why this exists
///
/// [`congruence`] refuses a singular `P` by name, and that refusal is correct **for Sylvester's
/// law**: the law is a statement about invertible changes of basis and a singular `P` genuinely does
/// move the inertia. But refusing is not the only lawful return, and it is not the interesting one.
/// A singular `P` is a **restriction of the form to a subspace composed with a collapse**, and the
/// restriction of a form to a subspace satisfies a theorem of its own:
///
/// ```text
///   n₊(PᵀAP) ≤ n₊(A)        and        n₋(PᵀAP) ≤ n₋(A)
/// ```
///
/// for **every** `P`, invertible or not. The reason is one line: a subspace on which `PᵀAP` is
/// positive definite maps forward under `P` to a subspace on which `A` is positive definite (if
/// `xᵀPᵀAPx > 0` then `Px ≠ 0`, and `P` is injective on such a subspace because a kernel vector
/// there would give `0 > 0`), so `n₊(A)` is at least as large. The same argument with the sign
/// reversed gives the negative bound. Nothing here needs `P` square.
///
/// **`congruence` is the equality case and is subsumed**: when `P` is invertible the map is onto,
/// both inequalities are equalities, and the return is Sylvester's law with the bound saturated.
/// The existing organ keeps its refusal — a caller who asks for *a congruence* and hands a singular
/// matrix has a bug — and this one answers the different question.
///
/// # The collapsed population is the testimony
///
/// `ker P` is exactly the population the pull-back cannot see: every `x` with `Px = 0` satisfies
/// `(PᵀAP)x = 0` whatever `A` was, so those directions arrive in the radical no matter what the form
/// says about their images. That is the same return species as
/// [`crate::receiver_exact_compression`]'s collapsed pairs — the pairs a declared receiver family
/// identifies — carried here as a basis of the kernel rather than as a count, so a caller can
/// exhibit *which* directions were lost rather than being told how many.
///
/// The strictness of the bound and the collapse are **not the same statement** and this return
/// separates them: `[[1,1],[1,1]]` against `diag(1,−1)` collapses a one-dimensional kernel and drops
/// **both** `n₊` and `n₋` by one, so a rank-one collapse cost two directions.
///
/// # Exactness
///
/// `Rat` throughout. The kernel is computed by exact reduced row echelon form, the pull-back by
/// exact multiplication, and both inertias by the elimination above. No float, no tolerance, no
/// rank threshold.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PullbackInertia {
    /// `n₊(A), n₀(A), n₋(A)` — the source form's own reading.
    pub source: Inertia,
    /// `n₊(PᵀAP), n₀(PᵀAP), n₋(PᵀAP)` — the pulled-back reading, which the bound governs.
    pub pulled_back: Inertia,
    /// `PᵀAP` itself, returned rather than described.
    pub form: SymmetricForm,
    /// `rank P`, read off the echelon form and not from a determinant.
    pub basis_rank: usize,
    /// A basis of `ker P`, exactly. Empty when `P` is injective.
    pub kernel: Vec<Vec<Rat>>,
}

impl PullbackInertia {
    /// Both bounds. A theorem, and it can fail — which is why it is a computed method rather than a
    /// stored flag.
    pub const fn bounds_hold(&self) -> bool {
        self.pulled_back.positive <= self.source.positive
            && self.pulled_back.negative <= self.source.negative
    }

    /// Whether the positive bound is **strict**. The collapse witness must return `true` here; an
    /// invertible `P` must return `false`.
    pub const fn positive_is_strict(&self) -> bool {
        self.pulled_back.positive < self.source.positive
    }

    pub const fn negative_is_strict(&self) -> bool {
        self.pulled_back.negative < self.source.negative
    }

    /// The dimension of `ker P` — the extent of the collapsed population, exhibited by
    /// [`PullbackInertia::kernel`] rather than only counted.
    pub fn collapsed_extent(&self) -> usize {
        self.kernel.len()
    }

    /// `rank A − rank PᵀAP`: how many directions of the form the pull-back lost. Distinct from
    /// [`PullbackInertia::collapsed_extent`], and the collapse witness is where they differ.
    pub const fn rank_lost(&self) -> usize {
        self.source.rank() - self.pulled_back.rank()
    }

    /// Whether `P` was injective, so that the pull-back is a genuine restriction with no collapse.
    pub fn is_injective(&self) -> bool {
        self.kernel.is_empty()
    }
}

/// **`PᵀAP` and its inertia, for any `P` whatever.**
///
/// `P` is `extent × k` — it maps a `k`-dimensional space into the form's own — and `k` is free: the
/// pull-back of a rank-ten lattice along a two-column map is a two-dimensional form. Only the row
/// count is constrained, because that is what the product has to meet.
///
/// See [`PullbackInertia`] for the theorem, the collapse testimony, and why [`congruence`] keeps its
/// refusal rather than being replaced.
pub fn pullback_inertia_bound(
    form: &SymmetricForm,
    basis: &ExactRatMatrix,
) -> Result<PullbackInertia, InertiaError> {
    Ok(pullback_inertia_bound_with_work(form, basis)?.0)
}

/// **The same pull-back, with its work separated by phase.**
///
/// Added 2026-08-17 because an adjudication observed that timing this function *"is not isolated
/// Gaussian elimination"* — it performs two matrix products, a kernel row reduction and two
/// eliminations, and a clock cannot say which one carried the cost. The return is one vector per
/// phase, so the question is answered by counting instead of attributed by guess.
pub fn pullback_inertia_bound_with_work(
    form: &SymmetricForm,
    basis: &ExactRatMatrix,
) -> Result<(PullbackInertia, Vec<(&'static str, ExactWork)>), InertiaError> {
    if basis.rows() != form.extent() {
        return Err(InertiaError::PullbackRowsMismatch {
            extent: form.extent(),
            rows: basis.rows(),
        });
    }
    let (half, first_product) = basis.transpose()?.multiply_with_work(&form.as_matrix()?)?;
    let (transported, second_product) = half.multiply_with_work(basis)?;
    // Routed back through the validating constructor for the same reason `congruence` is: `PᵀAP` is
    // symmetric as mathematics, so an asymmetric arrival is a wrong multiplication and must say so.
    let pulled = SymmetricForm::from_rows(
        (0..transported.rows())
            .map(|row| transported.row(row).map(<[Rat]>::to_vec))
            .collect::<Result<Vec<Vec<Rat>>, ExactLinearError>>()?,
    )?;
    let kernel = kernel_basis(basis)?;
    let (source_tally, _, source_work) = inertia_with_work(form, PivotOrder::FirstNonzero);
    let (pulled_tally, _, pulled_work) = inertia_with_work(&pulled, PivotOrder::FirstNonzero);
    let phases = vec![
        ("product-transpose-times-form", first_product),
        ("product-times-basis", second_product),
        ("elimination-source", source_work),
        ("elimination-pulled-back", pulled_work),
    ];
    Ok((
        PullbackInertia {
            source: source_tally,
            pulled_back: pulled_tally,
            form: pulled,
            basis_rank: basis.columns() - kernel.len(),
            kernel,
        },
        phases,
    ))
}

/// A basis of `{x : M x = 0}`, exactly, by reduced row echelon form over `Rat`.
///
/// One vector per free column, in column order, each carrying `1` in its own free column and the
/// negated echelon entries in the pivot columns. Deterministic, and the empty vector when `M` is
/// injective.
fn kernel_basis(matrix: &ExactRatMatrix) -> Result<Vec<Vec<Rat>>, InertiaError> {
    let (rows, columns) = (matrix.rows(), matrix.columns());
    let mut working: Vec<Vec<Rat>> = (0..rows)
        .map(|row| matrix.row(row).map(<[Rat]>::to_vec))
        .collect::<Result<Vec<Vec<Rat>>, ExactLinearError>>()?;

    let mut pivot_row_of_column: Vec<Option<usize>> = vec![None; columns];
    let mut cursor = 0usize;
    for column in 0..columns {
        if cursor == rows {
            break;
        }
        let Some(found) = (cursor..rows).find(|row| !working[*row][column].is_zero()) else {
            continue;
        };
        working.swap(cursor, found);
        let divisor = working[cursor][column].clone();
        for entry in &mut working[cursor] {
            *entry /= &divisor;
        }
        let pivot = working[cursor].clone();
        for row in 0..rows {
            if row == cursor || working[row][column].is_zero() {
                continue;
            }
            let factor = working[row][column].clone();
            for (entry, pivot_entry) in working[row].iter_mut().zip(&pivot) {
                *entry -= &factor * pivot_entry;
            }
        }
        pivot_row_of_column[column] = Some(cursor);
        cursor += 1;
    }

    let mut kernel = Vec::new();
    for free in 0..columns {
        if pivot_row_of_column[free].is_some() {
            continue;
        }
        let mut vector = vec![Rat::zero(); columns];
        vector[free] = Rat::one();
        for (column, pivot) in pivot_row_of_column.iter().enumerate() {
            if let Some(row) = pivot {
                vector[column] = -working[*row][free].clone();
            }
        }
        kernel.push(vector);
    }
    Ok(kernel)
}

// -------------------------------------------------------------------------------------------
// the rank–trace defect — the finite identity the external certificate is tight on

/// **`2c·tr(A) − ‖A‖²_F`, exactly.**
///
/// The one scalar the external kernel-verified zeta certificate is built from, restated as a
/// computation over `Rat`. `research/records/2026-08-11_THE_RUNG_REFUSES_BY_NAME_…` §1 records the
/// certificate's finite core as the rank–trace inequality
///
/// ```text
///   2c·tr(P+Q) − ‖P+Q‖²_F  ≥  Σⱼ k_c(mⱼ)        with equality  Σⱼ k_c(mⱼ) + c²·b
/// ```
///
/// and the identity underneath it is elementary and exact: for a symmetric `A` with eigenvalues
/// `λ_i`, `‖A‖²_F = tr(A²) = Σ λ_i²`, so
///
/// ```text
///   2c·tr(A) − ‖A‖²_F = Σ_i (2c·λ_i − λ_i²) = Σ_i (c² − (c − λ_i)²)
/// ```
///
/// — a sum of per-direction terms, each of which is `c²` exactly at `λ_i = c`, `0` exactly at
/// `λ_i ∈ {0, 2c}`, and negative outside `[0, 2c]`. **That is what makes the quantity a placement
/// reading rather than a size**: it counts how far each direction sits from the declared `c`, and a
/// direction at the declared level pays the full `c²` while a direction at rest pays nothing.
///
/// This is computed from the **matrix**, never from a spectrum: `tr(A²) = Σ_{ij} a_ij a_ji`, which
/// for a symmetric form is `Σ_{ij} a_ij²`. No eigenvalue is required and none is approximated.
///
/// # Boundary
///
/// The identification of `k_c` with the external artifact's own `k_c` is `interpretation`, read from
/// the record's restatement and not from the Lean source. What is `implemented-exact` here is the
/// arithmetic identity [`block_defect`] discharges on a declared block form.
pub fn rank_trace_defect(form: &SymmetricForm, at: &Rat) -> Rat {
    let mut trace = Rat::zero();
    let mut frobenius = Rat::zero();
    for index in 0..form.extent() {
        trace += form.at(index, index);
    }
    for row in 0..form.extent() {
        for column in 0..form.extent() {
            frobenius += form.at(row, column) * form.at(row, column);
        }
    }
    (Rat::from_integer(BigInt::from(2)) * at) * trace - frobenius
}

/// **`k_c(m) = 2cm − m²`**, one direction's contribution to [`rank_trace_defect`].
///
/// Equivalently `c² − (c − m)²`. Both forms are computed and compared by
/// `the_block_defect_is_the_completed_square`, because an identity that is only ever written one way
/// is an identity nothing checks.
pub fn block_defect(at: &Rat, level: &Rat) -> Rat {
    Rat::from_integer(BigInt::from(2)) * at * level - level * level
}

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
    /// A pull-back `PᵀAP` needs only that `P`'s **rows** meet the form's extent; its column count is
    /// free and is the extent of the space being pulled back from. This is the one shape constraint
    /// the product cannot do without.
    #[error(
        "a pull-back matrix must carry one row per direction of the form's extent {extent}; this one has {rows}"
    )]
    PullbackRowsMismatch { extent: usize, rows: usize },
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact_value::ExactOrdering;
    use num_bigint::BigUint;

    // -----------------------------------------------------------------------------------------
    // THE WORK VECTOR — 2026-08-17
    // -----------------------------------------------------------------------------------------

    /// ★ THE PIVOT COUNT IS PROVABLY NOT THE DOMINATING QUANTITY, and this is the proof the tablet
    /// asserts without one.
    ///
    /// `docs/canon/TABLET_THE_CHART.md` §3.7: *"`PivotSchedule` returns the pivot count and it is
    /// provably **not** the dominating quantity; the dominating quantity is intermediate entry
    /// bit-length and nothing counts it."* Two forms of the same extent, taking the **same number of
    /// pivots**, whose peak intermediate widths differ by orders. If the widths agreed, the vector
    /// would be measuring what the schedule already said and would carry nothing.
    #[test]
    fn two_forms_take_the_same_pivots_and_do_not_take_the_same_width() {
        let extent = 8usize;
        // A: the identity. Every pivot is 1, every Schur update subtracts zero, nothing widens.
        let identity = SymmetricForm::from_diagonal(vec![Rat::one(); extent]);
        // B: the Hilbert form `1/(i+j+1)` — symmetric, invertible, and famous for exactly the
        // property under test: its exact elimination's intermediates blow up.
        let hilbert = SymmetricForm::from_rows(
            (0..extent)
                .map(|row| {
                    (0..extent)
                        .map(|column| Rat::new(1.into(), (row + column + 1).into()))
                        .collect()
                })
                .collect(),
        )
        .expect("symmetric by construction");

        let (flat_tally, flat_schedule, flat_work) =
            inertia_with_work(&identity, PivotOrder::FirstNonzero);
        let (deep_tally, deep_schedule, deep_work) =
            inertia_with_work(&hilbert, PivotOrder::FirstNonzero);

        // Both are positive definite of the same extent, and both take the same pivots.
        assert!(flat_tally.is_positive_definite());
        assert!(deep_tally.is_positive_definite());
        assert_eq!(flat_schedule.steps.len(), deep_schedule.steps.len());
        assert_eq!(flat_work.dependency_span, deep_work.dependency_span);

        // THE ARM: the widths do not agree, and the wider one is wider by a real margin.
        assert!(
            deep_work.peak_bits > flat_work.peak_bits,
            "the schedule cannot see this: {} pivots either way, peak {} against {}",
            flat_schedule.steps.len(),
            deep_work.peak_bits,
            flat_work.peak_bits
        );
        // And the product order says so rather than a scalar: the identity's work is DOMINATED.
        assert_eq!(flat_work.order_against(&deep_work), ExactOrdering::Less);
    }

    /// ★ THE WIDTH GROWS WITH THE DEPTH, which is the shape `O(k³)` operations on `k × k` minors
    /// predicts and which a wall-clock fit could only infer. Measured on the form whose growth is
    /// classical, so the reading has a second frame outside this repository.
    #[test]
    fn the_peak_width_grows_with_the_extent_on_a_form_whose_growth_is_classical() {
        let hilbert = |extent: usize| {
            SymmetricForm::from_rows(
                (0..extent)
                    .map(|row| {
                        (0..extent)
                            .map(|column| Rat::new(1.into(), (row + column + 1).into()))
                            .collect()
                    })
                    .collect(),
            )
            .expect("symmetric by construction")
        };
        let mut widths = Vec::new();
        for extent in [2usize, 4, 6, 8] {
            let (_, _, work) = inertia_with_work(&hilbert(extent), PivotOrder::FirstNonzero);
            widths.push((extent, work.peak_bits.clone(), work.multiplications.clone()));
        }
        for pair in widths.windows(2) {
            assert!(
                pair[1].1 > pair[0].1,
                "peak width must grow: extent {} gave {}, extent {} gave {}",
                pair[0].0,
                pair[0].1,
                pair[1].0,
                pair[1].1
            );
            assert!(pair[1].2 > pair[0].2, "and so must the operation count");
        }
    }

    /// ★ THE PHASES SEPARATE, which is the thing a clock provably cannot do. An adjudication
    /// observed that timing `pullback_inertia_bound` does not isolate the elimination because two
    /// matrix products and two eliminations share the interval. Counted, they are four vectors.
    #[test]
    fn the_pullback_returns_one_work_vector_per_phase_and_they_are_not_equal() {
        let form = SymmetricForm::from_diagonal(vec![Rat::one(); 4]);
        let basis = ExactRatMatrix::new(
            (0..4)
                .map(|row| {
                    (0..3)
                        .map(|column| Rat::new(((row + column) as i64 + 1).into(), 3.into()))
                        .collect()
                })
                .collect(),
        )
        .expect("rectangular");
        let (bound, phases) =
            pullback_inertia_bound_with_work(&form, &basis).expect("shapes agree");
        assert_eq!(phases.len(), 4);
        let named: Vec<&str> = phases.iter().map(|(name, _)| *name).collect();
        assert_eq!(
            named,
            vec![
                "product-transpose-times-form",
                "product-times-basis",
                "elimination-source",
                "elimination-pulled-back"
            ]
        );
        // A PRODUCT'S DEPENDENCY SPAN IS ONE; AN ELIMINATION'S IS ITS PIVOT COUNT. That single
        // coordinate separates a deed a card could carry from one it could not, and no scalar
        // carries it.
        assert_eq!(phases[0].1.dependency_span, BigUint::from(1u32));
        assert_eq!(phases[1].1.dependency_span, BigUint::from(1u32));
        assert!(phases[2].1.dependency_span > BigUint::from(1u32));
        // and the phases are genuinely different vectors, not one repeated
        assert_ne!(phases[0].1, phases[2].1);
        assert_eq!(bound.pulled_back.extent(), 3);
    }
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
                    assert!(
                        entry.is_integer(),
                        "this cross-check runs over integral forms"
                    );
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

    // -----------------------------------------------------------------------------------------
    // the pull-back

    fn rectangular(rows: &[Vec<i64>]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|row| {
                    row.iter()
                        .map(|entry| Rat::from_integer(BigInt::from(*entry)))
                        .collect()
                })
                .collect(),
        )
        .expect("fixture is rectangular")
    }

    fn rat(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }

    /// **The collapse witness the module's own doc already carried, answered instead of refused.**
    ///
    /// `[[1,1],[1,1]]ᵀ · diag(1,−1) · [[1,1],[1,1]] = 0`. [`congruence`] refuses it — correctly,
    /// because Sylvester's law is about invertible maps — and the lawful return for the same
    /// material is the **strict** bound with the collapsed direction exhibited. Both are asserted
    /// here so the two organs cannot drift into disagreeing about the same input.
    #[test]
    fn the_collapse_witness_returns_a_strict_bound_where_congruence_refuses() {
        let form = diagonal(&[1, -1]);
        let singular = rectangular(&[vec![1, 1], vec![1, 1]]);

        assert_eq!(
            congruence(&form, &basis(&[vec![(1, 1), (1, 1)], vec![(1, 1), (1, 1)]])),
            Err(InertiaError::SingularChangeOfBasis),
            "the invertible-only organ keeps its refusal"
        );

        let pullback = pullback_inertia_bound(&form, &singular).expect("the shapes meet");
        assert_eq!(
            pullback.form,
            SymmetricForm::zeros(2),
            "PᵀAP is the zero form"
        );
        assert_eq!(
            pullback.source,
            Inertia {
                positive: 1,
                zero: 0,
                negative: 1
            }
        );
        assert_eq!(
            pullback.pulled_back,
            Inertia {
                positive: 0,
                zero: 2,
                negative: 0
            }
        );
        assert!(pullback.bounds_hold());
        assert!(pullback.positive_is_strict(), "0 < 1 on the positive side");
        assert!(pullback.negative_is_strict(), "0 < 1 on the negative side");

        // A rank-one collapse cost two directions: the kernel is one-dimensional and the rank fell
        // by two. Strictness and collapse are different statements and this is where they part.
        assert_eq!(pullback.collapsed_extent(), 1);
        assert_eq!(pullback.rank_lost(), 2);
        assert_eq!(pullback.basis_rank, 1);
        assert_eq!(pullback.kernel, vec![vec![rat(-1), rat(1)]]);
    }

    /// The kernel is testimony, not decoration: every returned vector is annihilated by `P` and by
    /// `PᵀAP`, checked here against the matrices themselves rather than trusted.
    #[test]
    fn the_kernel_is_exhibited_and_annihilates_both_the_map_and_the_pulled_back_form() {
        // Rank two, three columns: one free direction, and the echelon form has to find it in the
        // third column rather than the first.
        let map = rectangular(&[vec![1, 0, 2], vec![0, 1, 3], vec![1, 1, 5]]);
        let form = integers(&[vec![2, 1, 0], vec![1, 2, 1], vec![0, 1, 2]]);
        let pullback = pullback_inertia_bound(&form, &map).expect("the shapes meet");

        assert_eq!(pullback.basis_rank, 2);
        assert_eq!(pullback.collapsed_extent(), 1);
        assert!(!pullback.is_injective());
        for vector in &pullback.kernel {
            assert!(
                map.apply(vector)
                    .expect("the extents meet")
                    .iter()
                    .all(Zero::is_zero),
                "a kernel vector must be annihilated by P"
            );
            for row in 0..pullback.form.extent() {
                let value = (0..pullback.form.extent()).fold(Rat::zero(), |sum, column| {
                    sum + pullback.form.at(row, column) * &vector[column]
                });
                assert!(
                    value.is_zero(),
                    "ker P lands in the radical of PᵀAP whatever A was"
                );
            }
        }
        assert!(pullback.bounds_hold());
    }

    /// **Invertible `P` reproduces [`congruence`] exactly** — Sylvester's law as the equality case of
    /// the bound. The fixtures are the ones the congruence test already uses, so the two organs are
    /// held to the same material and not to two convenient ones.
    #[test]
    fn an_invertible_pullback_reproduces_congruence_and_saturates_the_bound() {
        let forms = [
            diagonal(&[1, -1]),
            hyperbolic_plane(),
            integers(&[vec![2, 1], vec![1, 2]]),
            integers(&[vec![1, 1], vec![1, 1]]),
        ];
        let bases = [
            basis(&[vec![(1, 1), (1, 1)], vec![(0, 1), (1, 1)]]),
            basis(&[vec![(2, 1), (0, 1)], vec![(0, 1), (3, 1)]]),
            basis(&[vec![(1, 1), (2, 1)], vec![(3, 1), (4, 1)]]),
            basis(&[vec![(1, 2), (1, 3)], vec![(1, 1), (1, 1)]]),
        ];
        for form in &forms {
            for change in &bases {
                let by_congruence = congruence(form, change).expect("the basis is invertible");
                let pullback = pullback_inertia_bound(form, change).expect("the shapes meet");
                assert_eq!(pullback.form, by_congruence, "the same PᵀAP either way");
                assert_eq!(
                    pullback.pulled_back,
                    inertia(&by_congruence),
                    "Sylvester: the bound is an equality for an invertible P"
                );
                assert!(pullback.is_injective(), "an invertible P collapses nothing");
                assert!(!pullback.positive_is_strict() && !pullback.negative_is_strict());
                assert_eq!(pullback.rank_lost(), 0);
                assert_eq!(pullback.basis_rank, form.extent());
            }
        }
    }

    /// An **injective, non-surjective** `P`: a genuine restriction with no collapse at all. It
    /// separates strictness from collapse in the other direction from the witness above — the
    /// negative bound is strict while the kernel is empty, so a strict bound is not evidence of a
    /// collapsed direction and this fixture is what says so.
    #[test]
    fn an_injective_restriction_can_tighten_one_side_with_an_empty_kernel() {
        let form = diagonal(&[1, -1]);
        let restriction = rectangular(&[vec![1], vec![0]]);
        let pullback = pullback_inertia_bound(&form, &restriction).expect("the shapes meet");
        assert!(pullback.is_injective());
        assert_eq!(
            pullback.pulled_back,
            Inertia {
                positive: 1,
                zero: 0,
                negative: 0
            }
        );
        assert!(!pullback.positive_is_strict());
        assert!(pullback.negative_is_strict());
        assert!(pullback.bounds_hold());
    }

    /// The bound on a rank-ten indefinite lattice under a rectangular map, so the theorem is not
    /// only exercised at extent two. `E10` has signature `(1, 9)`; a three-column pull-back cannot
    /// exceed it on either side, and the fixture is chosen to be rank-deficient so the kernel is
    /// non-empty here as well.
    #[test]
    fn the_bound_holds_on_e10_under_a_rectangular_map() {
        let lattice = e10();
        let mut columns = vec![vec![0i64; 3]; 10];
        columns[0][0] = 1;
        columns[1][0] = 1;
        columns[2][1] = 1;
        columns[5][1] = -2;
        // The third column repeats the first, so the map is rank two with a one-dimensional kernel.
        columns[0][2] = 1;
        columns[1][2] = 1;
        let map = rectangular(&columns);
        let pullback = pullback_inertia_bound(&lattice, &map).expect("the shapes meet");
        assert_eq!(pullback.source.signature(), (1, 9));
        assert!(pullback.bounds_hold(), "{:?}", pullback.pulled_back);
        assert_eq!(pullback.basis_rank, 2);
        assert_eq!(pullback.collapsed_extent(), 1);
    }

    #[test]
    fn a_pullback_whose_rows_miss_the_extent_is_refused_by_name() {
        let form = diagonal(&[1, -1, 1]);
        assert_eq!(
            pullback_inertia_bound(&form, &rectangular(&[vec![1], vec![0]])),
            Err(InertiaError::PullbackRowsMismatch { extent: 3, rows: 2 })
        );
    }

    // -----------------------------------------------------------------------------------------
    // the rank–trace defect

    /// `k_c(m) = 2cm − m²` and `c² − (c − m)²` are the same number. Written twice on purpose: an
    /// identity that is only ever written one way is an identity nothing checks.
    #[test]
    fn the_block_defect_is_the_completed_square() {
        for at in [-3i64, 0, 1, 4, 7] {
            for level in [-5i64, -1, 0, 3, 4, 8] {
                let completed =
                    &rat(at) * &rat(at) - (rat(at) - rat(level)) * (rat(at) - rat(level));
                assert_eq!(
                    block_defect(&rat(at), &rat(level)),
                    completed,
                    "c={at} m={level}"
                );
            }
        }
        // The two levels where the term vanishes and the one where it is maximal, named.
        assert_eq!(block_defect(&rat(4), &rat(0)), rat(0));
        assert_eq!(block_defect(&rat(4), &rat(8)), rat(0));
        assert_eq!(block_defect(&rat(4), &rat(4)), rat(16));
    }

    /// **The tightness fixture.** On a declared block structure the rank–trace equality
    /// `2c·tr(M) − ‖M‖²_F = Σⱼ k_c(mⱼ) + c²·b` holds exactly over `Rat`.
    ///
    /// The fixture is built so the equality cannot come out by accident: the `mⱼ` are distinct from
    /// `c` and from each other, **one of them is negative** so the identity is not resting on
    /// positive semidefiniteness, `b` is nonzero so the `c²·b` term carries, and there are directions
    /// at rest so the zero block is exercised too.
    #[test]
    fn the_declared_block_structure_discharges_the_rank_trace_equality() {
        let at = rat(4);
        let levels = [rat(3), rat(5), rat(-2)];
        let repeats = 2usize;
        let at_rest = 2usize;

        let mut diagonal_entries: Vec<Rat> = levels.to_vec();
        diagonal_entries.extend(std::iter::repeat_n(at.clone(), repeats));
        diagonal_entries.extend(std::iter::repeat_n(Rat::zero(), at_rest));
        let block = SymmetricForm::from_diagonal(diagonal_entries);

        let expected = levels
            .iter()
            .map(|level| block_defect(&at, level))
            .fold(Rat::zero(), |sum, term| sum + term)
            + &at * &at * Rat::from_integer(BigInt::from(repeats as i64));
        assert_eq!(rank_trace_defect(&block, &at), expected);
        assert_eq!(
            expected,
            rat(42),
            "the fixture's own number, so a silent drift is visible"
        );

        // The same identity survives a pull-back that keeps one level, one repeat, and one rest
        // direction — the restriction is the operation the bound above is about, so the two are
        // exercised on one fixture rather than side by side.
        let mut columns = vec![vec![0i64; 3]; block.extent()];
        columns[0][0] = 1;
        columns[3][1] = 1;
        columns[5][2] = 1;
        let pullback = pullback_inertia_bound(&block, &rectangular(&columns)).expect("shapes meet");
        assert_eq!(
            rank_trace_defect(&pullback.form, &at),
            block_defect(&at, &levels[0]) + &at * &at,
            "the surviving block reproduces the equality on its own levels"
        );
        assert!(pullback.bounds_hold());
        assert!(
            pullback.positive_is_strict(),
            "three positive directions became two"
        );
    }

    /// The defect is computed from the **matrix**, so a form whose eigenvalues are not rational must
    /// still return an exact rational. The hyperbolic plane's are `±1` and its trace is zero, which
    /// makes it the shortest fixture where the Frobenius term is the whole answer.
    #[test]
    fn the_defect_needs_no_spectrum_and_reads_an_off_diagonal_form() {
        assert_eq!(rank_trace_defect(&hyperbolic_plane(), &rat(4)), rat(-2));
        // `2c·0 − (0+1+1+0) = −2`, and by the spectrum `k_4(1) + k_4(−1) = 7 + (−9) = −2`.
        assert_eq!(
            block_defect(&rat(4), &rat(1)) + block_defect(&rat(4), &rat(-1)),
            rat(-2)
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
