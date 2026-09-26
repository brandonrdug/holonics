//! **The host realization of co-present regions** (CLAUDE.md, the hardware law: co-present regions
//! execute together when their complete read/write, lineage, obstruction and resource effects
//! commute).
//!
//! [definition; agent-inferred] Every region the host runs together in `hnn` is one pattern: shared
//! immutable input with disjoint staged output. Each region reads operands no region writes, and
//! writes only its own output slot; the slots are collected in index order, and every reduction
//! over them runs afterwards, serially, in that order. Three forms:
//!
//! - **indexed regions** ([`indexed`]): `n` regions of one kind (the rings, the contacts, the
//!   receiving phases, the loci of a deposit), each returning its slot or its refusal. The refusal
//!   returned is the first in index order, the one a serial loop over the regions returns;
//! - **entries** ([`entries`]): the entries of one vector or the coordinates of one covector, each
//!   read alone;
//! - **row blocks** ([`outer_rows`], [`apply_rows`]): the rows of one rank-one sum or one
//!   matrix-vector product, each block writing only its own rows.
//!
//! A reduced ratio is canonical, so a slot computed alone is the same value it is inside the loop,
//! and every output is bit-identical to the serial realization, which is these same functions run
//! on one worker (the test `hnn::tests::reference::one_worker_and_many_return_the_same_values`).
//! Which regions run together, method by method, is recorded in the reference's header
//! ([`crate::hnn::reference`], "The host realization").

use rayon::prelude::*;

use crate::hnn::HnnError;
use crate::ratio::Rat;
use crate::ratio::linear::vector::{Chart, IntegralMatrix, integral, row_dot};
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};

/// [definition; agent-inferred] **The rows of one block**: the rows shared evenly among the host's
/// workers, one block each (the receiving map's `2|A| = 512` rows on 24 workers make blocks of 22),
/// and every row in one block on one worker. A block's rows are normalized in its own region; the
/// block's extent changes no value, only how the rows are shared among workers.
fn row_block(rows: usize) -> usize {
    rows.div_ceil(rayon::current_num_threads()).max(1)
}

/// **`n` indexed regions**, collected in index order; the first refusal in index order is returned.
pub(crate) fn indexed<T, F>(n: usize, region: F) -> Result<Vec<T>, HnnError>
where
    T: Send,
    F: Fn(usize) -> Result<T, HnnError> + Sync + Send,
{
    (0..n)
        .into_par_iter()
        .map(region)
        .collect::<Vec<Result<T, HnnError>>>()
        .into_iter()
        .collect()
}

/// **`n` entries**, each read alone (an entry of a vector, a coordinate of a covector), collected
/// in index order.
pub(crate) fn entries<T, F>(n: usize, entry: F) -> Vec<T>
where
    T: Send,
    F: Fn(usize) -> T + Sync + Send,
{
    (0..n).into_par_iter().map(entry).collect()
}

/// **`Σ_t w_t l_t r_tᵀ` by row blocks** (`rows × columns`, normalized rows): each block is the same
/// sum over the terms' left vectors restricted to its rows, on the same chart denominators, so
/// each entry is the numerator the whole sum forms over the same common denominator, normalized
/// once ([`IntegralMatrix::outer_sum`]).
pub(crate) fn outer_rows(
    rows: usize,
    columns: usize,
    terms: &[(&Rat, &Chart, &Chart)],
) -> Vec<Vec<Rat>> {
    let extent = row_block(rows);
    let blocks: Vec<Vec<Vec<Rat>>> = (0..rows.div_ceil(extent))
        .into_par_iter()
        .map(|block| {
            let (start, end) = (block * extent, ((block + 1) * extent).min(rows));
            let restricted: Vec<(&Rat, Chart, &Chart)> = terms
                .iter()
                .map(|(weight, (left, denominator), right)| {
                    // The sum reads a left vector up to its own extent, as the whole sum does.
                    let restricted = &left[start.min(left.len())..end.min(left.len())];
                    (*weight, (restricted.to_vec(), denominator.clone()), *right)
                })
                .collect();
            IntegralMatrix::outer_sum(
                end - start,
                columns,
                restricted
                    .iter()
                    .map(|(weight, left, right)| (*weight, left, *right)),
            )
            .to_rows()
        })
        .collect();
    blocks.into_iter().flatten().collect()
}

/// **`M v` by rows**: the vector read once in the integral chart, and each row one normalized dot
/// ([`ExactRatMatrix::apply`]'s own reading and refusal, row by row).
pub(crate) fn apply_rows(matrix: &ExactRatMatrix, vector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
    if matrix.columns() != vector.len() {
        return Err(ExactLinearError::ShapeMismatch.into());
    }
    let (values, denominator) = integral(vector);
    indexed(matrix.rows(), |row| {
        Ok(row_dot(matrix.row(row)?, &values, &denominator))
    })
}
