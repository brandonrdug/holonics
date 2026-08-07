//! What survives every rebase of the machine's own incidence.
//!
//! Three sentences the project already carries turn out to be one sentence:
//!
//! - **The expansion schedule is a receiver.** The same recursive cell laid out under one traversal
//!   and under another produces visibly different shapes; the question that makes a rendering
//!   mathematics rather than illustration is *what survives every schedule*.
//! - **Identity is what survives reorganizing the symbols.** Brandon, 2026-08-06: *"the symbol does
//!   not dictate what the information contains, you could reorganize the symbols and the structure
//!   of the proof or algorithm would determine the identity of the underlying algorithmic
//!   patterns."*
//! - **`chi' = G chi G^-1`.** A rebase conjugates; the invariant factors are what conjugation
//!   leaves alone.
//!
//! Those are the same demand at three altitudes, and over an integer incidence the demand has an
//! exact answer with a standard name: the **Smith normal form**, whose diagonal
//! `d_1 | d_2 | ... | d_r` is unique up to units for a matrix over a principal ideal domain. It is
//! the reason this organ can be *internal*. Deciding whether two grown structures are the same
//! pattern needs no external checker, because sameness-under-change-of-chart is a property only the
//! transport atlas holding those charts can compute.
//!
//! ## What it returns
//!
//! For a `GradedCausalComplex` whose cells already refuse `d d != 0` at construction
//! (`algebraic.rs:293`), this returns per grade:
//!
//! ```text
//!   rank      of the boundary map out of that grade
//!   betti     n_k - rank(d_k) - rank(d_{k+1})        -- free rank of H_k
//!   torsion   the invariant factors of d_{k+1} above one -- winding that cannot be un-deposited
//! ```
//!
//! Torsion is the returned artifact this organ exists for. A rational rank computation gives Betti
//! numbers and **destroys torsion**, which is why `exact_rational_rank` in `algebraic.rs` — the only
//! prior rank in the tree — cannot answer this question. `CLAUDE.md` §3 states the connection the
//! project draws from it: the failure of the *integral* Hodge conjecture is torsion, and torsion is
//! winding that cannot be un-deposited.
//!
//! ## No float, no tolerance, no pivot leak
//!
//! Every entry is a `BigInt` and every operation is exact. The reduction is a **rebase**: each row
//! and column operation is a change of basis in a chain group, so what the algorithm computes is
//! literally what survives rebasing the incidence.
//!
//! That creates the one hazard worth naming. A previously convicted contaminant in this project was
//! *"a solver's pivot order [promoted] into a reduction"* — a receiver-visible coordinate becoming
//! an invariant. So the pivot rule here is an explicit **parameter**, not a hardcoded choice, and
//! the falsifier is that all three rules must return byte-identical invariant factors. That check
//! can fail, and it is the same shape as the machine-level question: reorganize the computation,
//! and the invariants must not move.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};

use crate::algebraic::{CausalAlgebraicError, CausalCellId, GradedCausalComplex};

/// How the reduction chooses its next pivot.
///
/// This is a parameter because a pivot order is a property of the solver, never of the incidence.
/// The Smith normal form is unique up to units over a principal ideal domain, so every rule must
/// return the same invariant factors — and `the_invariants_do_not_depend_on_the_pivot_rule` is what
/// holds this module to that.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PivotRule {
    /// Scan in storage order and take the first nonzero. The cheapest, and the one whose ordering
    /// dependence would be least visible if the uniqueness theorem did not hold.
    FirstNonzero,
    /// Take a nonzero entry of least magnitude. Keeps intermediate coefficients small.
    SmallestMagnitude,
    /// Take a nonzero entry of greatest magnitude. Included precisely because it is a poor
    /// heuristic: if the returned factors moved with the rule, this is the rule that would show it.
    LargestMagnitude,
}

impl PivotRule {
    pub const ALL: [Self; 3] = [
        Self::FirstNonzero,
        Self::SmallestMagnitude,
        Self::LargestMagnitude,
    ];
}

/// An exact integer matrix. Dense, because a boundary matrix of a grown complex is small in the
/// grade direction and this carrier must never trade exactness for a sparsity heuristic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntegerMatrix {
    rows: usize,
    columns: usize,
    entries: Vec<BigInt>,
}

impl IntegerMatrix {
    pub fn zeros(rows: usize, columns: usize) -> Self {
        Self {
            rows,
            columns,
            entries: vec![BigInt::zero(); rows * columns],
        }
    }

    pub const fn rows(&self) -> usize {
        self.rows
    }

    pub const fn columns(&self) -> usize {
        self.columns
    }

    pub fn at(&self, row: usize, column: usize) -> &BigInt {
        &self.entries[row * self.columns + column]
    }

    pub fn set(&mut self, row: usize, column: usize, value: BigInt) {
        self.entries[row * self.columns + column] = value;
    }

    fn swap_rows(&mut self, left: usize, right: usize) {
        if left == right {
            return;
        }
        for column in 0..self.columns {
            self.entries
                .swap(left * self.columns + column, right * self.columns + column);
        }
    }

    fn swap_columns(&mut self, left: usize, right: usize) {
        if left == right {
            return;
        }
        for row in 0..self.rows {
            self.entries
                .swap(row * self.columns + left, row * self.columns + right);
        }
    }

    /// `row_target -= factor * row_source`. A rebase of the chain group this matrix maps out of.
    fn reduce_row(&mut self, target: usize, source: usize, factor: &BigInt) {
        for column in 0..self.columns {
            let delta = self.at(source, column) * factor;
            let value = self.at(target, column) - delta;
            self.set(target, column, value);
        }
    }

    /// `column_target -= factor * column_source`. A rebase of the chain group this matrix maps into.
    fn reduce_column(&mut self, target: usize, source: usize, factor: &BigInt) {
        for row in 0..self.rows {
            let delta = self.at(row, source) * factor;
            let value = self.at(row, target) - delta;
            self.set(row, target, value);
        }
    }

    fn is_zero_below(&self, pivot: usize) -> bool {
        (pivot + 1..self.rows).all(|row| self.at(row, pivot).is_zero())
    }

    fn is_zero_right(&self, pivot: usize) -> bool {
        (pivot + 1..self.columns).all(|column| self.at(pivot, column).is_zero())
    }

    fn find_pivot(&self, from: usize, rule: PivotRule) -> Option<(usize, usize)> {
        let mut best: Option<(usize, usize)> = None;
        for row in from..self.rows {
            for column in from..self.columns {
                if self.at(row, column).is_zero() {
                    continue;
                }
                match rule {
                    PivotRule::FirstNonzero => return Some((row, column)),
                    PivotRule::SmallestMagnitude => {
                        let magnitude = self.at(row, column).abs();
                        if best.is_none_or(|(r, c)| magnitude < self.at(r, c).abs()) {
                            best = Some((row, column));
                        }
                    }
                    PivotRule::LargestMagnitude => {
                        let magnitude = self.at(row, column).abs();
                        if best.is_none_or(|(r, c)| magnitude > self.at(r, c).abs()) {
                            best = Some((row, column));
                        }
                    }
                }
            }
        }
        best
    }
}

/// The diagonal of a Smith normal form, with the rank it implies.
///
/// `factors` is the returned artifact — the actual `d_1 | d_2 | ... | d_r`, not a count of them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmithNormalForm {
    pub factors: Vec<BigInt>,
}

impl SmithNormalForm {
    pub fn rank(&self) -> usize {
        self.factors.len()
    }

    /// Factors above one. These are the torsion coefficients the image contributes, and a factor of
    /// exactly one contributes none.
    pub fn torsion(&self) -> Vec<BigInt> {
        self.factors
            .iter()
            .filter(|factor| **factor > BigInt::one())
            .cloned()
            .collect()
    }

    /// Every factor divides the next. This is the defining property, and it is asserted rather than
    /// assumed because a reduction that skipped its divisibility repair would still look diagonal.
    pub fn divisibility_holds(&self) -> bool {
        self.factors
            .windows(2)
            .all(|pair| (&pair[1] % &pair[0]).is_zero())
    }
}

/// Reduce to Smith normal form over the integers.
///
/// Classical algorithm: clear the pivot row and column by repeated division with remainder — the
/// Euclidean descent, which is why the pivot ends up carrying the gcd — then repair divisibility so
/// each diagonal entry divides the next. Every step is an exact integer row or column operation,
/// which is to say a rebase of one of the two chain groups.
pub fn smith_normal_form(matrix: &IntegerMatrix, rule: PivotRule) -> SmithNormalForm {
    let mut work = matrix.clone();
    let extent = work.rows.min(work.columns);
    let mut factors = Vec::new();

    for pivot in 0..extent {
        let Some((row, column)) = work.find_pivot(pivot, rule) else {
            break;
        };
        work.swap_rows(pivot, row);
        work.swap_columns(pivot, column);

        // Euclidean descent on the pivot cross. Each pass strictly reduces |pivot| whenever it does
        // not already divide its cross, so this terminates.
        loop {
            for row in pivot + 1..work.rows {
                if work.at(row, pivot).is_zero() {
                    continue;
                }
                let quotient = work.at(row, pivot) / work.at(pivot, pivot);
                work.reduce_row(row, pivot, &quotient);
                if !work.at(row, pivot).is_zero() {
                    work.swap_rows(pivot, row);
                }
            }
            for column in pivot + 1..work.columns {
                if work.at(pivot, column).is_zero() {
                    continue;
                }
                let quotient = work.at(pivot, column) / work.at(pivot, pivot);
                work.reduce_column(column, pivot, &quotient);
                if !work.at(pivot, column).is_zero() {
                    work.swap_columns(pivot, column);
                }
            }
            if work.is_zero_below(pivot) && work.is_zero_right(pivot) {
                break;
            }
        }

        // Divisibility repair. If the pivot does not divide some entry of the remaining block, fold
        // that entry's row into the pivot row and descend again; the pivot strictly decreases in
        // magnitude, so this terminates too.
        let mut repaired = false;
        'repair: for row in pivot + 1..work.rows {
            for column in pivot + 1..work.columns {
                if work.at(row, column).is_zero() {
                    continue;
                }
                if (work.at(row, column) % work.at(pivot, pivot)).is_zero() {
                    continue;
                }
                let one = BigInt::from(-1);
                work.reduce_row(pivot, row, &one);
                repaired = true;
                break 'repair;
            }
        }
        if repaired {
            // Redo this pivot with the folded row in place.
            let mut retry = work.clone();
            let tail = smith_normal_form_from(&mut retry, pivot, rule);
            factors.extend(tail);
            return normalize(factors);
        }

        let diagonal = work.at(pivot, pivot).clone();
        if diagonal.is_zero() {
            break;
        }
        factors.push(diagonal.abs());
    }

    normalize(factors)
}

/// Resume the reduction at `from`, used by the divisibility repair so the retry does not discard
/// the factors already settled above it.
fn smith_normal_form_from(
    work: &mut IntegerMatrix,
    from: usize,
    rule: PivotRule,
) -> Vec<BigInt> {
    let mut trailing = IntegerMatrix::zeros(work.rows - from, work.columns - from);
    for row in from..work.rows {
        for column in from..work.columns {
            trailing.set(row - from, column - from, work.at(row, column).clone());
        }
    }
    smith_normal_form(&trailing, rule).factors
}

fn normalize(mut factors: Vec<BigInt>) -> SmithNormalForm {
    factors.retain(|factor| !factor.is_zero());
    for factor in &mut factors {
        *factor = factor.abs();
    }
    SmithNormalForm { factors }
}

/// One grade's share of the invariants.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GradeInvariants {
    pub grade: u32,
    /// Number of cells carried at this grade.
    pub cells: usize,
    /// Rank of the boundary map **out of** this grade.
    pub boundary_rank: usize,
    /// Rank of the boundary map **into** this grade, from grade + 1.
    pub filling_rank: usize,
    /// Free rank of `H_grade`: `cells - boundary_rank - filling_rank`.
    pub betti: usize,
    /// Torsion coefficients of `H_grade` — the invariant factors above one of the map from
    /// grade + 1. Winding that cannot be un-deposited.
    pub torsion: Vec<BigInt>,
}

/// Every invariant the incidence carries, per grade, with the pivot rule that produced them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RebaseInvariants {
    pub schema: String,
    pub pivot_rule: PivotRule,
    pub grades: Vec<GradeInvariants>,
}

impl RebaseInvariants {
    pub fn betti_vector(&self) -> Vec<usize> {
        self.grades.iter().map(|grade| grade.betti).collect()
    }

    pub fn total_torsion(&self) -> Vec<BigInt> {
        self.grades
            .iter()
            .flat_map(|grade| grade.torsion.iter().cloned())
            .collect()
    }

    /// The Euler characteristic, summed with sign over grades. Independent of every rebase, and the
    /// cheapest cross-check that the Betti numbers are not nonsense: it must equal the alternating
    /// sum of the cell counts.
    pub fn euler_characteristic(&self) -> i64 {
        self.grades
            .iter()
            .map(|grade| {
                let sign = if grade.grade % 2 == 0 { 1i64 } else { -1i64 };
                sign * grade.betti as i64
            })
            .sum()
    }

    pub fn cell_euler_characteristic(&self) -> i64 {
        self.grades
            .iter()
            .map(|grade| {
                let sign = if grade.grade % 2 == 0 { 1i64 } else { -1i64 };
                sign * grade.cells as i64
            })
            .sum()
    }
}

/// The boundary matrix out of `grade`, over exact integers.
///
/// Entries come from `ComparativeMultiplicity::difference()`. The complex retains each coefficient
/// as an ordered pair of positive and negative counts and never collapses it; the group-completed
/// difference is the canonical map to the integers and is what a boundary map means. The pair is
/// still upstream — nothing here writes back.
pub fn boundary_matrix(
    complex: &GradedCausalComplex,
    grade: u32,
) -> Result<IntegerMatrix, CausalAlgebraicError> {
    let columns: Vec<CausalCellId> = cells_at(complex, grade);
    let rows: Vec<CausalCellId> = match grade.checked_sub(1) {
        Some(lower) => cells_at(complex, lower),
        None => Vec::new(),
    };
    let row_index: BTreeMap<CausalCellId, usize> = rows
        .iter()
        .enumerate()
        .map(|(index, cell)| (*cell, index))
        .collect();

    let mut matrix = IntegerMatrix::zeros(rows.len(), columns.len());
    for (column, cell) in columns.iter().enumerate() {
        let body = complex.cell(*cell)?;
        for (face, coefficient) in body.boundary.coefficients() {
            let Some(row) = row_index.get(face) else {
                continue;
            };
            matrix.set(*row, column, coefficient.difference());
        }
    }
    Ok(matrix)
}

fn cells_at(complex: &GradedCausalComplex, grade: u32) -> Vec<CausalCellId> {
    complex
        .cells()
        .values()
        .filter(|cell| cell.grade == grade)
        .map(|cell| cell.id)
        .collect()
}

/// Compute every grade's invariants.
///
/// The cell ordering within a grade comes from the complex's own `BTreeMap`, which is keyed by
/// founding order. That ordering is a receiver coordinate; the returned invariants must not depend
/// on it, and `the_invariants_do_not_depend_on_the_founding_order` is the check.
pub fn rebase_invariants(
    complex: &GradedCausalComplex,
    rule: PivotRule,
) -> Result<RebaseInvariants, CausalAlgebraicError> {
    let top = complex.dimension().unwrap_or(0);
    let mut forms: BTreeMap<u32, SmithNormalForm> = BTreeMap::new();
    for grade in 0..=top + 1 {
        let matrix = boundary_matrix(complex, grade)?;
        forms.insert(grade, smith_normal_form(&matrix, rule));
    }

    let mut grades = Vec::new();
    for grade in 0..=top {
        let cells = cells_at(complex, grade).len();
        let boundary_rank = forms.get(&grade).map_or(0, SmithNormalForm::rank);
        let filling = forms.get(&(grade + 1));
        let filling_rank = filling.map_or(0, SmithNormalForm::rank);
        let torsion = filling.map(SmithNormalForm::torsion).unwrap_or_default();
        grades.push(GradeInvariants {
            grade,
            cells,
            boundary_rank,
            filling_rank,
            betti: cells.saturating_sub(boundary_rank).saturating_sub(filling_rank),
            torsion,
        });
    }

    Ok(RebaseInvariants {
        schema: "holonic-engine.rebase-invariants.v1".to_owned(),
        pivot_rule: rule,
        grades,
    })
}

/// Two invariant readings agree on everything a rebase cannot move.
///
/// The pivot rule and the founding order are receiver coordinates and are excluded from the
/// comparison by construction — they are not read here at all.
pub fn invariants_agree(left: &RebaseInvariants, right: &RebaseInvariants) -> bool {
    left.grades.len() == right.grades.len()
        && left.grades.iter().zip(&right.grades).all(|(a, b)| {
            a.grade == b.grade
                && a.cells == b.cells
                && a.boundary_rank == b.boundary_rank
                && a.filling_rank == b.filling_rank
                && a.betti == b.betti
                && a.torsion == b.torsion
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebraic::{CausalChain, ComparativeMultiplicity};
    use crate::causal::EventId;
    use std::collections::BTreeSet;

    fn source() -> BTreeSet<EventId> {
        BTreeSet::from([EventId(1)])
    }

    fn matrix_of(rows: usize, columns: usize, values: &[i64]) -> IntegerMatrix {
        let mut matrix = IntegerMatrix::zeros(rows, columns);
        for (index, value) in values.iter().enumerate() {
            matrix.set(index / columns, index % columns, BigInt::from(*value));
        }
        matrix
    }

    // -----------------------------------------------------------------------------------------
    // the reduction itself

    #[test]
    fn a_diagonal_already_in_form_is_returned_unchanged() {
        let matrix = matrix_of(2, 2, &[2, 0, 0, 6]);
        let form = smith_normal_form(&matrix, PivotRule::FirstNonzero);
        assert_eq!(form.factors, vec![BigInt::from(2), BigInt::from(6)]);
        assert!(form.divisibility_holds());
    }

    #[test]
    fn the_pivot_carries_the_gcd_because_the_descent_is_euclidean() {
        // gcd(6, 10) = 2, and the product of the factors is the determinant up to sign: 6*4-10*2=4.
        let matrix = matrix_of(2, 2, &[6, 10, 2, 4]);
        let form = smith_normal_form(&matrix, PivotRule::FirstNonzero);
        assert_eq!(form.factors, vec![BigInt::from(2), BigInt::from(2)]);
        assert!(form.divisibility_holds());
    }

    #[test]
    fn a_matrix_needing_divisibility_repair_still_returns_a_divisor_chain() {
        // Diagonal (2, 3) is NOT a Smith form: 2 does not divide 3. The repair must return (1, 6).
        let matrix = matrix_of(2, 2, &[2, 0, 0, 3]);
        let form = smith_normal_form(&matrix, PivotRule::FirstNonzero);
        assert!(
            form.divisibility_holds(),
            "each factor must divide the next: {:?}",
            form.factors
        );
        assert_eq!(form.factors, vec![BigInt::one(), BigInt::from(6)]);
    }

    #[test]
    fn a_rank_deficient_matrix_returns_fewer_factors_than_its_extent() {
        let matrix = matrix_of(3, 3, &[1, 2, 3, 2, 4, 6, 3, 6, 9]);
        let form = smith_normal_form(&matrix, PivotRule::FirstNonzero);
        assert_eq!(form.rank(), 1, "every row is a multiple of the first");
        assert_eq!(form.factors, vec![BigInt::one()]);
    }

    #[test]
    fn the_zero_matrix_has_no_factors() {
        let form = smith_normal_form(&matrix_of(3, 3, &[0; 9]), PivotRule::FirstNonzero);
        assert_eq!(form.rank(), 0);
        assert!(form.torsion().is_empty());
    }

    /// The falsifier for this module, and the same shape as the machine-level question: reorganize
    /// the computation and the invariants must not move. If a pivot order ever leaked into a
    /// returned factor, this is what would catch it.
    #[test]
    fn the_invariants_do_not_depend_on_the_pivot_rule() {
        let cases = [
            matrix_of(3, 3, &[2, 4, 4, -6, 6, 12, 10, -4, -16]),
            matrix_of(3, 4, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]),
            matrix_of(2, 2, &[2, 0, 0, 3]),
            matrix_of(4, 3, &[0, 0, 6, 0, 15, 0, 21, 0, 0, 0, 0, 0]),
            matrix_of(3, 3, &[6, 10, 0, 0, 2, 4, 3, 0, 9]),
        ];
        for (index, matrix) in cases.iter().enumerate() {
            let mut settled: Option<Vec<BigInt>> = None;
            for rule in PivotRule::ALL {
                let form = smith_normal_form(matrix, rule);
                assert!(
                    form.divisibility_holds(),
                    "case {index} under {rule:?} returned a non-divisor chain: {:?}",
                    form.factors
                );
                match &settled {
                    None => settled = Some(form.factors),
                    Some(first) => assert_eq!(
                        *first, form.factors,
                        "case {index}: {rule:?} moved the invariant factors — a solver coordinate \
                         reached a returned invariant"
                    ),
                }
            }
        }
    }

    // -----------------------------------------------------------------------------------------
    // the invariants of an actual complex

    /// A hollow triangle: three vertices, three edges, no filling. One loop, no torsion.
    fn hollow_triangle() -> GradedCausalComplex {
        let mut complex = GradedCausalComplex::default();
        let a = complex.found_cell("a", source(), 0, CausalChain::default()).unwrap();
        let b = complex.found_cell("b", source(), 0, CausalChain::default()).unwrap();
        let c = complex.found_cell("c", source(), 0, CausalChain::default()).unwrap();
        for (name, from, to) in [("ab", a, b), ("bc", b, c), ("ca", c, a)] {
            let mut boundary = CausalChain::default();
            boundary.add_term(to, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(from, ComparativeMultiplicity::negative(1u32));
            complex.found_cell(name, source(), 1, boundary).unwrap();
        }
        complex
    }

    #[test]
    fn a_hollow_triangle_carries_one_loop_and_no_torsion() {
        let invariants = rebase_invariants(&hollow_triangle(), PivotRule::FirstNonzero).unwrap();
        assert_eq!(invariants.betti_vector(), vec![1, 1], "one piece, one loop");
        assert!(invariants.total_torsion().is_empty());
        assert_eq!(
            invariants.euler_characteristic(),
            invariants.cell_euler_characteristic(),
            "Euler characteristic from Betti numbers must equal it from cell counts"
        );
        assert_eq!(invariants.cell_euler_characteristic(), 0, "3 - 3");
    }

    #[test]
    fn filling_the_triangle_kills_the_loop() {
        let mut complex = hollow_triangle();
        let edges: Vec<CausalCellId> = complex
            .cells()
            .values()
            .filter(|cell| cell.grade == 1)
            .map(|cell| cell.id)
            .collect();
        let mut boundary = CausalChain::default();
        for edge in &edges {
            boundary.add_term(*edge, ComparativeMultiplicity::positive(1u32));
        }
        complex.found_cell("disc", source(), 2, boundary).unwrap();

        let invariants = rebase_invariants(&complex, PivotRule::FirstNonzero).unwrap();
        assert_eq!(
            invariants.betti_vector(),
            vec![1, 0, 0],
            "the filled loop is no longer a generator"
        );
        assert!(invariants.total_torsion().is_empty());
        assert_eq!(invariants.cell_euler_characteristic(), 1, "3 - 3 + 1");
    }

    /// The case the whole module exists for. A loop traversed twice bounds a face — the winding is
    /// there and cannot be un-deposited, and only an integer reduction can see it. Over the
    /// rationals this is invisible: the rational rank is identical to the untwisted case.
    #[test]
    fn a_doubled_boundary_returns_torsion_that_a_rational_rank_cannot_see() {
        let mut complex = GradedCausalComplex::default();
        let a = complex.found_cell("a", source(), 0, CausalChain::default()).unwrap();
        let mut loop_boundary = CausalChain::default();
        loop_boundary.add_term(a, ComparativeMultiplicity::positive(1u32));
        loop_boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
        let edge = complex.found_cell("loop", source(), 1, loop_boundary).unwrap();

        let mut face_boundary = CausalChain::default();
        face_boundary.add_term(edge, ComparativeMultiplicity::positive(2u32));
        complex.found_cell("twice", source(), 2, face_boundary).unwrap();

        let invariants = rebase_invariants(&complex, PivotRule::FirstNonzero).unwrap();
        let torsion = invariants.total_torsion();
        assert_eq!(
            torsion,
            vec![BigInt::from(2)],
            "the doubled attachment deposits a Z/2 that no rational rank retains"
        );
        assert_eq!(
            invariants.grades[1].betti, 0,
            "the loop is killed rationally while the winding stands"
        );
    }

    /// The founding order is a receiver coordinate. Building the same triangle with its cells
    /// founded in a different order must return identical invariants.
    #[test]
    fn the_invariants_do_not_depend_on_the_founding_order() {
        let forward = rebase_invariants(&hollow_triangle(), PivotRule::FirstNonzero).unwrap();

        let mut reversed = GradedCausalComplex::default();
        let c = reversed.found_cell("c", source(), 0, CausalChain::default()).unwrap();
        let b = reversed.found_cell("b", source(), 0, CausalChain::default()).unwrap();
        let a = reversed.found_cell("a", source(), 0, CausalChain::default()).unwrap();
        for (name, from, to) in [("ca", c, a), ("bc", b, c), ("ab", a, b)] {
            let mut boundary = CausalChain::default();
            boundary.add_term(to, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(from, ComparativeMultiplicity::negative(1u32));
            reversed.found_cell(name, source(), 1, boundary).unwrap();
        }
        let backward = rebase_invariants(&reversed, PivotRule::LargestMagnitude).unwrap();

        assert!(
            invariants_agree(&forward, &backward),
            "founding order or pivot rule reached a returned invariant:\n{forward:?}\n{backward:?}"
        );
    }
}
