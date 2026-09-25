//! **Scalars: the exact reference field and its coordinate vectors.**
//!
//! [project-postulate; agent-inferred] The reference field is `crate::ratio::Rat`. Every
//! facet of the Holon core computes over it; no `f32`/`f64` enters a law. A bond is a pair of
//! coordinate vectors over ℚ (`Holon/Port.Bond`), and the facets share the small exact
//! vector and block-matrix operations below, all routed through
//! [`crate::ratio::linear::ExactRatMatrix`].
//!
//! A resident chart owes "exact reference value ∈ returned ball" (`Holon/Element.ball_image` for a
//! bounded linear step).

use crate::ratio::Rat;
use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};

/// A vector in the integral chart ([`integral`]): integer numerators over one positive denominator.
pub(crate) type Chart = (Vec<BigInt>, BigInt);

/// [definition; agent-inferred] **A matrix in the integral chart**: integer numerators over one
/// common denominator, `M = N / D` exactly. A sum of many rank-one terms is formed over integers and
/// each entry normalized once when read out; a reduced ratio is canonical, so the entries equal the
/// termwise rational sums.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IntegralMatrix {
    rows: usize,
    columns: usize,
    numerators: Vec<BigInt>,
    denominator: BigInt,
}

impl IntegralMatrix {
    /// **`Σ_t w_t l_t r_tᵀ`** over terms whose vectors are already in the integral chart
    /// ([`integral`]), with rational weights.
    pub(crate) fn outer_sum<'a>(
        rows: usize,
        columns: usize,
        terms: impl IntoIterator<Item = (&'a Rat, &'a Chart, &'a Chart)>,
    ) -> Self {
        let terms: Vec<_> = terms
            .into_iter()
            .filter(|(weight, _, _)| !weight.is_zero())
            .map(|(weight, left, right)| {
                let scale = weight.denom() * &left.1 * &right.1;
                (weight, left, right, scale)
            })
            .collect();
        let denominator = terms
            .iter()
            .fold(BigInt::one(), |d, (.., scale)| lcm(&d, scale));
        let mut numerators = vec![BigInt::zero(); rows * columns];
        for (weight, (left, _), (right, _), scale) in terms {
            let factor = weight.numer() * (&denominator / scale);
            for (i, l) in left.iter().enumerate().take(rows) {
                if l.is_zero() {
                    continue;
                }
                let scaled = l * &factor;
                let row = &mut numerators[i * columns..(i + 1) * columns];
                for (entry, r) in row.iter_mut().zip(right) {
                    if !r.is_zero() {
                        *entry += &scaled * r;
                    }
                }
            }
        }
        Self {
            rows,
            columns,
            numerators,
            denominator,
        }
    }

    /// The entries as normalized rows.
    pub(crate) fn to_rows(&self) -> Vec<Vec<Rat>> {
        (0..self.rows)
            .map(|i| {
                self.numerators[i * self.columns..(i + 1) * self.columns]
                    .iter()
                    .map(|n| Rat::new(n.clone(), self.denominator.clone()))
                    .collect()
            })
            .collect()
    }

    /// **`(N + Nᵀ) F / D`** for a square `N / D` and a factor `F` (`rows × m`): the pull of a
    /// gradient of the symmetric form `F Fᵀ` onto its factor, with `sign` folded in.
    pub(crate) fn symmetric_times(
        &self,
        factor: &ExactRatMatrix,
        negate: bool,
    ) -> Result<Vec<Vec<Rat>>, ExactLinearError> {
        let n = self.rows;
        if self.columns != n || factor.rows() != n {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let m = factor.columns();
        let (values, factor_denominator) = integral(factor.entries());
        let denominator = &self.denominator * &factor_denominator;
        let mut rows = Vec::with_capacity(n);
        for i in 0..n {
            let mut sums = vec![BigInt::zero(); m];
            for k in 0..n {
                let weight = &self.numerators[i * n + k] + &self.numerators[k * n + i];
                if weight.is_zero() {
                    continue;
                }
                for (sum, value) in sums.iter_mut().zip(&values[k * m..(k + 1) * m]) {
                    if !value.is_zero() {
                        *sum += &weight * value;
                    }
                }
            }
            rows.push(
                sums.into_iter()
                    .map(|sum| Rat::new(if negate { -sum } else { sum }, denominator.clone()))
                    .collect(),
            );
        }
        Ok(rows)
    }
}

/// **`Σ_c w_c v_c`** of vectors in the integral chart with rational weights, each entry normalized
/// once.
pub(crate) fn combination<'a>(
    width: usize,
    terms: impl IntoIterator<Item = (&'a Rat, &'a Chart)>,
) -> Vec<Rat> {
    let one = (vec![BigInt::one()], BigInt::one());
    let terms: Vec<(&Rat, &Chart, &Chart)> = terms
        .into_iter()
        .map(|(weight, vector)| (weight, vector, &one))
        .collect();
    let transposed = IntegralMatrix::outer_sum(width, 1, terms);
    transposed
        .to_rows()
        .into_iter()
        .map(|mut row| row.remove(0))
        .collect()
}

/// A vector of integers as rationals.
#[cfg(test)]
pub(crate) fn ints(values: &[i64]) -> Vec<Rat> {
    values
        .iter()
        .map(|value| crate::ratio::integer(*value))
        .collect()
}

/// `⟨a, b⟩`. The caller owns equal lengths; a mismatch reads the shorter prefix, so every public
/// facet checks its extents before calling this.
///
/// [definition; agent-inferred] Read in the integral chart: each vector as integers over its least
/// common denominator ([`integral`]), the integer sum formed, and the ratio normalized once. A
/// reduced ratio is canonical, so this is the same value as the termwise sum, with one `gcd` in
/// place of one per term.
pub(crate) fn dot(a: &[Rat], b: &[Rat]) -> Rat {
    let (left, left_denominator) = integral(a);
    let (right, right_denominator) = integral(b);
    Rat::new(
        integer_dot(&left, &right),
        left_denominator * right_denominator,
    )
}

/// `lcm(a, b)` of positive denominators, with the equal and unit cases read without a `gcd`.
pub(crate) fn lcm(left: &BigInt, right: &BigInt) -> BigInt {
    if right.is_one() || left == right {
        return left.clone();
    }
    if left.is_one() {
        return right.clone();
    }
    let divisor = crate::ratio::gcd(left, right);
    (left / divisor) * right
}

/// The least common denominator of a family of ratios.
pub(crate) fn common_denominator<'a>(values: impl IntoIterator<Item = &'a Rat>) -> BigInt {
    values
        .into_iter()
        .fold(BigInt::one(), |denominator, value| {
            lcm(&denominator, value.denom())
        })
}

/// [definition; agent-inferred] **The integral chart of a rational vector**: its entries as integers
/// over their least common denominator `D`, `v = n / D` exactly. A fixed operand is charted once and
/// applied with one normalization per output entry.
pub(crate) fn integral(values: &[Rat]) -> Chart {
    let denominator = common_denominator(values);
    let numerators = values
        .iter()
        .map(|value| {
            if value.denom() == &denominator {
                value.numer().clone()
            } else {
                value.numer() * (&denominator / value.denom())
            }
        })
        .collect();
    (numerators, denominator)
}

/// `Σ a_i b_i` over integers, skipping zero terms.
pub(crate) fn integer_dot(a: &[BigInt], b: &[BigInt]) -> BigInt {
    let mut sum = BigInt::zero();
    for (x, y) in a.iter().zip(b) {
        if !x.is_zero() && !y.is_zero() {
            sum += x * y;
        }
    }
    sum
}

/// `⟨row, n/D⟩` for a rational row against an integral vector `n` over `D`: the row's own common
/// denominator read inline, one normalization.
pub(crate) fn row_dot(row: &[Rat], values: &[BigInt], denominator: &BigInt) -> Rat {
    let row_denominator = common_denominator(row);
    let mut sum = BigInt::zero();
    for (entry, value) in row.iter().zip(values) {
        if entry.is_zero() || value.is_zero() {
            continue;
        }
        if entry.denom() == &row_denominator {
            sum += entry.numer() * value;
        } else {
            sum += entry.numer() * (&row_denominator / entry.denom()) * value;
        }
    }
    Rat::new(sum, row_denominator * denominator)
}

pub(crate) fn add(a: &[Rat], b: &[Rat]) -> Vec<Rat> {
    a.iter().zip(b).map(|(x, y)| x + y).collect()
}

pub(crate) fn sub(a: &[Rat], b: &[Rat]) -> Vec<Rat> {
    a.iter().zip(b).map(|(x, y)| x - y).collect()
}

pub(crate) fn scale(coefficient: &Rat, a: &[Rat]) -> Vec<Rat> {
    a.iter().map(|x| coefficient * x).collect()
}

pub(crate) fn neg(a: &[Rat]) -> Vec<Rat> {
    a.iter().map(|x| -x).collect()
}

pub(crate) fn zeros(extent: usize) -> Vec<Rat> {
    vec![Rat::zero(); extent]
}

pub(crate) fn is_zero(a: &[Rat]) -> bool {
    a.iter().all(Zero::is_zero)
}

/// A matrix of a declared shape from an entry function. The shape is declared, so `0 × m` and
/// `m × 0` operators keep their extents (`ExactRatMatrix::shaped`).
pub(crate) fn matrix(
    rows: usize,
    columns: usize,
    entry: impl Fn(usize, usize) -> Rat,
) -> Result<ExactRatMatrix, ExactLinearError> {
    ExactRatMatrix::shaped(
        rows,
        columns,
        (0..rows)
            .map(|row| (0..columns).map(|column| entry(row, column)).collect())
            .collect(),
    )
}

/// A matrix of integer rows (every row the same length; an empty slice is `0 × 0`).
#[cfg(test)]
pub(crate) fn integer_matrix(rows: &[&[i64]]) -> Result<ExactRatMatrix, ExactLinearError> {
    ExactRatMatrix::new(rows.iter().map(|row| ints(row)).collect())
}

/// The entry `(row, column)`; the caller has checked the shape.
pub(crate) fn at(m: &ExactRatMatrix, row: usize, column: usize) -> Rat {
    m.entries()[row * m.columns() + column].clone()
}

/// `⟨v, M v⟩`.
pub(crate) fn quad(m: &ExactRatMatrix, v: &[Rat]) -> Result<Rat, ExactLinearError> {
    Ok(dot(v, &m.apply(v)?))
}

/// `[[A, B], [C, D]]`, with the block shapes checked.
pub(crate) fn from_blocks(
    a: &ExactRatMatrix,
    b: &ExactRatMatrix,
    c: &ExactRatMatrix,
    d: &ExactRatMatrix,
) -> Result<ExactRatMatrix, ExactLinearError> {
    if a.rows() != b.rows()
        || c.rows() != d.rows()
        || a.columns() != c.columns()
        || b.columns() != d.columns()
    {
        return Err(ExactLinearError::ShapeMismatch);
    }
    let (top, left) = (a.rows(), a.columns());
    matrix(top + c.rows(), left + b.columns(), |row, column| {
        match (row < top, column < left) {
            (true, true) => at(a, row, column),
            (true, false) => at(b, row, column - left),
            (false, true) => at(c, row - top, column),
            (false, false) => at(d, row - top, column - left),
        }
    })
}

/// `diag(A, B)`.
pub(crate) fn block_diagonal(
    a: &ExactRatMatrix,
    b: &ExactRatMatrix,
) -> Result<ExactRatMatrix, ExactLinearError> {
    from_blocks(
        a,
        &ExactRatMatrix::zero(a.rows(), b.columns())?,
        &ExactRatMatrix::zero(b.rows(), a.columns())?,
        b,
    )
}

/// `[A | B]`.
pub(crate) fn hstack(
    a: &ExactRatMatrix,
    b: &ExactRatMatrix,
) -> Result<ExactRatMatrix, ExactLinearError> {
    if a.rows() != b.rows() {
        return Err(ExactLinearError::ShapeMismatch);
    }
    matrix(a.rows(), a.columns() + b.columns(), |row, column| {
        if column < a.columns() {
            at(a, row, column)
        } else {
            at(b, row, column - a.columns())
        }
    })
}

/// `[A; B]`.
pub(crate) fn vstack(
    a: &ExactRatMatrix,
    b: &ExactRatMatrix,
) -> Result<ExactRatMatrix, ExactLinearError> {
    if a.columns() != b.columns() {
        return Err(ExactLinearError::ShapeMismatch);
    }
    matrix(a.rows() + b.rows(), a.columns(), |row, column| {
        if row < a.rows() {
            at(a, row, column)
        } else {
            at(b, row - a.rows(), column)
        }
    })
}

/// The columns listed, in the listed order.
pub(crate) fn select_columns(
    m: &ExactRatMatrix,
    columns: &[usize],
) -> Result<ExactRatMatrix, ExactLinearError> {
    if columns.iter().any(|column| *column >= m.columns()) {
        return Err(ExactLinearError::AddressOutside);
    }
    matrix(m.rows(), columns.len(), |row, column| {
        at(m, row, columns[column])
    })
}

/// The submatrix on the listed rows and columns.
pub(crate) fn submatrix(
    m: &ExactRatMatrix,
    rows: &[usize],
    columns: &[usize],
) -> Result<ExactRatMatrix, ExactLinearError> {
    if rows.iter().any(|row| *row >= m.rows()) || columns.iter().any(|c| *c >= m.columns()) {
        return Err(ExactLinearError::AddressOutside);
    }
    matrix(rows.len(), columns.len(), |row, column| {
        at(m, rows[row], columns[column])
    })
}

/// `Mᵀ = −M`.
pub(crate) fn is_skew(m: &ExactRatMatrix) -> bool {
    m.is_square()
        && (0..m.rows()).all(|row| (0..m.columns()).all(|c| at(m, row, c) == -at(m, c, row)))
}

/// The symmetric part `(M + Mᵀ)/2` as a form; `⟨e, M e⟩ = ⟨e, sym(M) e⟩`
/// (`Holon/Deposition.quad_symPart`).
pub(crate) fn symmetric_part(m: &ExactRatMatrix) -> Result<SymmetricForm, ExactLinearError> {
    if !m.is_square() {
        return Err(ExactLinearError::NonsquareMatrix);
    }
    let half = crate::ratio::rat(1, 2);
    let rows = (0..m.rows())
        .map(|row| {
            (0..m.columns())
                .map(|c| &half * (at(m, row, c) + at(m, c, row)))
                .collect()
        })
        .collect();
    Ok(SymmetricForm::from_rows(rows).expect("the symmetric part is symmetric by construction"))
}

/// A symmetric form as a matrix.
pub(crate) fn form_matrix(form: &SymmetricForm) -> ExactRatMatrix {
    let n = form.extent();
    matrix(n, n, |row, column| form.at(row, column).clone())
        .expect("a square extent is a declared shape")
}

/// A symmetric matrix as a form, refusing an asymmetric one.
pub(crate) fn matrix_form(
    m: &ExactRatMatrix,
) -> Result<SymmetricForm, crate::ratio::linear::inertia::InertiaError> {
    SymmetricForm::from_rows(m.to_rows())
}
