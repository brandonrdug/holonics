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
use num_traits::Zero;

use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};

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
pub(crate) fn dot(a: &[Rat], b: &[Rat]) -> Rat {
    a.iter().zip(b).fold(Rat::zero(), |sum, (x, y)| sum + x * y)
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
