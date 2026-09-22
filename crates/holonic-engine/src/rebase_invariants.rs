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
//! numbers and **destroys torsion**, which is why no rank over `Rat` can answer this question.
//!
//! **This paragraph named `exact_rational_rank` in `algebraic.rs` as "the only prior rank in the
//! tree" and that was FALSE ON THE DAY IT WAS WRITTEN.** Two others already stood at `d760584`, the
//! commit that deposited this file — `receiver_ecology.rs:578` and `sheaf_diffusion.rs:1011`, both
//! named `exact_rank`, both `fn exact_rank(mut matrix: Vec<Vec<Rat>>) -> usize` — and two more
//! arrived the next day: `derivation_two_cells.rs:1464`, a **public** second
//! `exact_rational_rank(&[Vec<Rat>], height)`, and `matroid_chow.rs:807` `rational_rank(&[Vec<Rat>],
//! columns)`. **Five exact rational ranks, three distinct names, no shared owner.** The claim was an
//! absence assertion made without the grep that would have refuted it, which is exactly the decay
//! `CLAUDE.md` §5 records of absence claims: *"An absence claim is a measurement and decays like
//! one."* What is true of all five, and is the load-bearing half, is that each returns a rank over
//! `Rat` and therefore each destroys torsion; none of them competes with this organ.
//!
//! **The connection to the integral Hodge conjecture is NOT that its obstruction is torsion, and
//! this comment said so until 2026-08-13.** That reading was withdrawn 2026-08-08 by a Hodge audit
//! and the operating contract records the withdrawal. There are two independent counterexample
//! families and only one is about torsion: Atiyah–Hirzebruch/Totaro/Soulé–Voisin, where the
//! obstruction is the vanishing of odd-degree stable cohomology operations and torsion is the
//! *habitat* rather than the obstruction; and Kollár 1990/1992, where `H⁴(X,ℤ) ≅ ℤ` is
//! **torsion-free**, the failing class has **infinite order**, `pα` is algebraic while `α` is not,
//! and the cokernel is `ℤ/p`.
//!
//! **The uniform statement is that the obstruction lives in the COKERNEL of the cycle class map.**
//! That is what this organ computes and why it is the right organ: the invariant factors above one
//! are exactly the finite part of that cokernel — `pα` reached and `α` not — which is a faithful
//! finite model of Kollár. Torsion is what a rational rank destroys, which is why no rank over `Rat`
//! can answer the question; it is not what the conjecture fails on. And the bound: the Millennium
//! Hodge conjecture is *rational*, so a class reached only in a multiple may never be reported as a
//! Millennium-Hodge obstruction after tensoring with ℚ.
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
//!
//! ## The schedule is returned, because otherwise the falsifier cannot be audited
//!
//! A three-rule agreement is only evidence if the three rules actually computed differently. On a
//! boundary matrix whose nonzero entries all have magnitude one — which is *every* matrix a
//! simplicial fixture produces — [`IntegerMatrix::find_pivot`] breaks its ties with strict `<` and
//! `>`, so all three rules select the first nonzero and the falsifier compares one computation with
//! itself twice. Measured 2026-08-08 on the five declared plate fixtures: three identical pivot
//! traces on all five.
//!
//! So the pivot positions are a **returned artifact** — [`PivotSchedule`], [`ReadingSchedule`] —
//! and a caller checking the agreement can check that it was an agreement between different
//! computations. `the_three_pivot_rules_take_three_different_paths_to_the_same_invariants` is that
//! check, and `staggered_attachment`-shaped material — a face attached with *unequal* winding
//! around parallel edges — is what makes it possible. A schedule is a receiver coordinate and is
//! excluded from [`invariants_agree`] by construction; it is returned to be *audited*, never to be
//! compared as an invariant.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use serde::{Deserialize, Serialize};

use crate::algebraic::{CausalAlgebraicError, CausalCellId, GradedCausalComplex};

// The Smith reduction itself (pivot rule, integer matrix, normal form, schedules and their work)
// is owned by `holonic_core::rebase_invariants` and re-exported here at its old paths.
pub use holonic_core::rebase_invariants::{
    IntegerMatrix, PivotRule, PivotSchedule, ReadingSchedule, ReductionWork, SmithNormalForm,
    smith_normal_form, smith_normal_form_with_schedule,
};

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
///
/// **This paragraph was false until 2026-08-08 and is now true.** `ComparativeMultiplicity::new`
/// subtracted the common population on every construction and `validate()` made a retained pair a
/// hard error, so after construction at most one arm was ever nonzero: the type had the anatomy of
/// `OrientedWinding` and the behaviour of `i64`. This function's own figures never moved — they read
/// `difference()` — which is exactly why nothing caught it. What moved was every consumer that read
/// `boundary.support()` as a **face relation**; see `gluing::a_loop_is_not_admitted_into_a_receiver_
/// that_does_not_hold_its_vertex`.
pub fn boundary_matrix(
    complex: &GradedCausalComplex,
    grade: u32,
) -> Result<IntegerMatrix, CausalAlgebraicError> {
    boundary_matrix_on(complex, grade, None)
}

/// The boundary matrix restricted to a section.
///
/// `support` is a set of cells that must already be **closed under boundary** — a genuine
/// subcomplex, which `GradedCausalComplex::is_closed_support` decides. A support that is not closed
/// would silently drop faces out of the rows and return invariants for a structure that does not
/// exist; the caller owes that check, and `dilation::DilatedSection` performs it on construction.
pub fn boundary_matrix_on(
    complex: &GradedCausalComplex,
    grade: u32,
    support: Option<&BTreeSet<CausalCellId>>,
) -> Result<IntegerMatrix, CausalAlgebraicError> {
    let columns: Vec<CausalCellId> = cells_at_on(complex, grade, support);
    let rows: Vec<CausalCellId> = match grade.checked_sub(1) {
        Some(lower) => cells_at_on(complex, lower, support),
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

fn section_dimension(
    complex: &GradedCausalComplex,
    support: Option<&BTreeSet<CausalCellId>>,
) -> Option<u32> {
    complex
        .cells()
        .values()
        .filter(|cell| support.is_none_or(|support| support.contains(&cell.id)))
        .map(|cell| cell.grade)
        .max()
}

fn cells_at_on(
    complex: &GradedCausalComplex,
    grade: u32,
    support: Option<&BTreeSet<CausalCellId>>,
) -> Vec<CausalCellId> {
    complex
        .cells()
        .values()
        .filter(|cell| cell.grade == grade)
        .filter(|cell| support.is_none_or(|support| support.contains(&cell.id)))
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
    rebase_invariants_on(complex, None, rule)
}

/// The same reading, with the pivot schedule every one of its reductions walked.
///
/// A caller cross-checking the three rules against each other needs this to know the cross-check
/// was one: see the module doc.
pub fn rebase_invariants_with_schedule(
    complex: &GradedCausalComplex,
    rule: PivotRule,
) -> Result<(RebaseInvariants, ReadingSchedule), CausalAlgebraicError> {
    rebase_invariants_with_schedule_on(complex, None, rule)
}

/// The invariants of a section, which is what a receiver at a declared horizon actually holds.
///
/// A receiver never sees the whole incidence. `dilation` returns the section a horizon admits, and
/// this reads its invariants — so "did dilating move the invariants?" is a question with an exact
/// integer answer rather than a description.
pub fn rebase_invariants_on(
    complex: &GradedCausalComplex,
    support: Option<&BTreeSet<CausalCellId>>,
    rule: PivotRule,
) -> Result<RebaseInvariants, CausalAlgebraicError> {
    Ok(rebase_invariants_with_schedule_on(complex, support, rule)?.0)
}

/// The section reading, with its schedule. [`rebase_invariants_on`] delegates here, so the
/// schedule is the one the returned invariants were reduced along.
pub fn rebase_invariants_with_schedule_on(
    complex: &GradedCausalComplex,
    support: Option<&BTreeSet<CausalCellId>>,
    rule: PivotRule,
) -> Result<(RebaseInvariants, ReadingSchedule), CausalAlgebraicError> {
    let top = section_dimension(complex, support).unwrap_or(0);
    let mut forms: BTreeMap<u32, SmithNormalForm> = BTreeMap::new();
    let mut per_grade: Vec<(u32, PivotSchedule)> = Vec::new();
    for grade in 0..=top + 1 {
        let matrix = boundary_matrix_on(complex, grade, support)?;
        let (form, schedule) = smith_normal_form_with_schedule(&matrix, rule);
        forms.insert(grade, form);
        per_grade.push((grade, schedule));
    }

    let mut grades = Vec::new();
    for grade in 0..=top {
        let cells = cells_at_on(complex, grade, support).len();
        let boundary_rank = forms.get(&grade).map_or(0, SmithNormalForm::rank);
        let filling = forms.get(&(grade + 1));
        let filling_rank = filling.map_or(0, SmithNormalForm::rank);
        let torsion = filling.map(SmithNormalForm::torsion).unwrap_or_default();
        grades.push(GradeInvariants {
            grade,
            cells,
            boundary_rank,
            filling_rank,
            betti: cells
                .saturating_sub(boundary_rank)
                .saturating_sub(filling_rank),
            torsion,
        });
    }

    Ok((
        RebaseInvariants {
            schema: "holonic-engine.rebase-invariants.v1".to_owned(),
            pivot_rule: rule,
            grades,
        },
        ReadingSchedule { rule, per_grade },
    ))
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
    use num_traits::{One, Signed, Zero};
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

    /// **The work vector explains the cost wall that the pivot count does not.**
    ///
    /// Measured 2026-08-08: on the grade-two boundary map of a grown Brent–Kung adder at width 3,
    /// `SmallestMagnitude` returned in 1 ms and `FirstNonzero` did not complete in 390 s — while
    /// their *pivot selection* counts stood at `1.0` and `1.5` per extent, three orders of magnitude
    /// apart in cost and indistinguishable by that measure. The cost law was therefore a clock
    /// reading with no exact falsifier, which `CLAUDE.md` §8 forbids from selecting anything.
    ///
    /// This is the falsifier it lacked. `written_bits` and `peak_entry_bits` are exact, deterministic
    /// and machine-independent, and they separate the rules **on a matrix small enough that all three
    /// complete** — so the separation can be asserted rather than inferred from a wall clock.
    #[test]
    fn the_exact_work_vector_separates_pivot_rules_that_the_selection_count_cannot() {
        // A matrix whose entries differ in magnitude, so the rules genuinely diverge. Equal-magnitude
        // entries make `find_pivot` tie-break identically and the gauge acts trivially -- §8.
        let matrix = matrix_of(
            4,
            4,
            &[
                210, 330, 462, 770, //
                1155, 462, 330, 210, //
                2310, 1155, 770, 66, //
                30, 42, 70, 105,
            ],
        );

        let mut readings = Vec::new();
        for rule in PivotRule::ALL {
            let (form, schedule) = smith_normal_form_with_schedule(&matrix, rule);
            readings.push((rule, form.factors.clone(), schedule));
        }

        // The RETURNS agree -- that is the uniqueness theorem and the existing gauge.
        let factors = readings[0].1.clone();
        for (rule, returned, _) in &readings {
            assert_eq!(
                returned, &factors,
                "{rule:?} returned different invariant factors; the uniqueness theorem forbids it"
            );
        }

        // The WORK does not, and `invariants_agree` never compares it.
        let work: Vec<_> = readings
            .iter()
            .map(|(rule, _, schedule)| (*rule, schedule.work))
            .collect();
        for (rule, measured) in &work {
            assert!(
                measured.entries_written > 0 && measured.written_bits > 0,
                "{rule:?} recorded no work at all, so the instrument is not wired"
            );
        }
        let widths: BTreeSet<u64> = work.iter().map(|(_, w)| w.written_bits).collect();
        assert!(
            widths.len() > 1,
            "every rule wrote the same number of bits, so this material cannot separate them and \
             the control is vacuous -- §8's gauge rule. Work: {work:?}"
        );

        // THE SWELL, EXHIBITED. Peak single-entry widths on a 4x4 of three-digit integers spread
        // by more than an order of magnitude. That is the intermediate expression swell that the
        // clock could only infer, measured exactly.
        let peaks: Vec<u64> = work.iter().map(|(_, w)| w.peak_entry_bits).collect();
        let widest = peaks.iter().max().copied().unwrap();
        let narrowest = peaks.iter().min().copied().unwrap();
        assert!(
            widest >= narrowest * 4,
            "the rules should differ substantially in peak entry width, which IS the swell; \
             peaks were {peaks:?}"
        );

        // AND WHICH RULE IS CHEAPEST IS MATERIAL-DEPENDENT. This assertion was written the other
        // way round first -- that `SmallestMagnitude` writes the fewest bits, because on the grown
        // Brent-Kung boundary map it beats `FirstNonzero` by orders of magnitude and finishes where
        // that rule does not complete in 390 seconds. On THIS matrix it loses, and it loses while
        // taking the only divisibility repair of the three. So the roadmap's "SmallestMagnitude is
        // the rule to pass at a single-rule call site" is right for the grown material it was
        // measured on and is NOT a general law. A cost law that does not name its material is no
        // more a bound than one that does not name its rule.
        let cheapest = work
            .iter()
            .min_by_key(|(_, w)| w.written_bits)
            .map(|(rule, _)| *rule)
            .unwrap();
        assert_eq!(
            cheapest,
            PivotRule::FirstNonzero,
            "on this dense small matrix the scanning rule is cheapest, which is the counterexample \
             to the naive reading of the grown-material measurement; work was {work:?}"
        );
        assert_eq!(
            work.iter()
                .find(|(rule, _)| *rule == PivotRule::SmallestMagnitude)
                .map(|(_, w)| w.repairs),
            Some(1),
            "and it is the only rule that took a divisibility repair here"
        );
    }

    /// The peak entry width is the swell itself, and it is retained rather than summarised away.
    #[test]
    fn the_peak_entry_width_is_retained_beside_the_total() {
        let matrix = matrix_of(2, 2, &[6, 10, 15, 21]);
        let (_, schedule) = smith_normal_form_with_schedule(&matrix, PivotRule::FirstNonzero);
        assert!(schedule.work.peak_entry_bits > 0);
        assert!(
            schedule.work.peak_entry_bits <= schedule.work.written_bits,
            "the peak is one entry; the total is every entry"
        );
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
    ///
    /// The agreement is asserted **beside the divergence of the schedules that produced it**. An
    /// agreement between three identical pivot walks is one computation compared with itself twice
    /// and carries no evidence at all, so each case must also show three different walks — and the
    /// case that cannot (`(2,0,0,3)`, every nonzero at magnitude two or three but only one entry
    /// per row and column reachable) is declared as such rather than being silently counted.
    #[test]
    fn the_invariants_do_not_depend_on_the_pivot_rule() {
        let cases = [
            matrix_of(3, 3, &[2, 4, 4, -6, 6, 12, 10, -4, -16]),
            matrix_of(3, 4, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]),
            matrix_of(2, 2, &[2, 0, 0, 3]),
            matrix_of(4, 3, &[0, 0, 6, 0, 15, 0, 21, 0, 0, 0, 0, 0]),
            matrix_of(3, 3, &[6, 10, 0, 0, 2, 4, 3, 0, 9]),
        ];
        let mut distinct_walks = Vec::new();
        for (index, matrix) in cases.iter().enumerate() {
            let mut settled: Option<Vec<BigInt>> = None;
            let mut walks: BTreeSet<Vec<(usize, usize)>> = BTreeSet::new();
            for rule in PivotRule::ALL {
                let (form, schedule) = smith_normal_form_with_schedule(matrix, rule);
                walks.insert(schedule.selections);
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
            distinct_walks.push(walks.len());
        }
        assert_eq!(
            distinct_walks,
            vec![2, 2, 2, 3, 3],
            "each case must produce the declared number of distinct pivot walks; a case that \
             collapsed to one walk contributes no evidence to the agreement above it"
        );
    }

    // -----------------------------------------------------------------------------------------
    // the invariants of an actual complex

    /// A hollow triangle: three vertices, three edges, no filling. One loop, no torsion.
    fn hollow_triangle() -> GradedCausalComplex {
        let mut complex = GradedCausalComplex::default();
        let a = complex
            .found_cell("a", source(), 0, CausalChain::default())
            .unwrap();
        let b = complex
            .found_cell("b", source(), 0, CausalChain::default())
            .unwrap();
        let c = complex
            .found_cell("c", source(), 0, CausalChain::default())
            .unwrap();
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
        let a = complex
            .found_cell("a", source(), 0, CausalChain::default())
            .unwrap();
        let mut loop_boundary = CausalChain::default();
        loop_boundary.add_term(a, ComparativeMultiplicity::positive(1u32));
        loop_boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
        let edge = complex
            .found_cell("loop", source(), 1, loop_boundary)
            .unwrap();

        let mut face_boundary = CausalChain::default();
        face_boundary.add_term(edge, ComparativeMultiplicity::positive(2u32));
        complex
            .found_cell("twice", source(), 2, face_boundary)
            .unwrap();

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
        let c = reversed
            .found_cell("c", source(), 0, CausalChain::default())
            .unwrap();
        let b = reversed
            .found_cell("b", source(), 0, CausalChain::default())
            .unwrap();
        let a = reversed
            .found_cell("a", source(), 0, CausalChain::default())
            .unwrap();
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

    // -----------------------------------------------------------------------------------------
    // the three-rule gauge, and the material that makes it a gauge

    /// Three parallel edges between two vertices, and one face attached to them with **unequal
    /// winding**: `4*e1 - 6*e2 + 2*e3`. Every edge has the same boundary `b - a`, so the
    /// coefficients sum to zero and `found_cell` accepts the attachment; and 4, 6, 2 are three
    /// different magnitudes, which is the whole point.
    ///
    /// Every other fixture in this module has all its nonzero boundary entries at magnitude one.
    /// On such a matrix `find_pivot` breaks its ties with strict `<` and `>`, so all three rules
    /// select the first nonzero and a three-rule check is one computation compared with itself
    /// twice. Here `FirstNonzero` takes row 0, `LargestMagnitude` takes the `-6` at row 1, and
    /// `SmallestMagnitude` takes the `2` at row 2 — three entries, three walks, one answer.
    ///
    /// It carries torsion too: `gcd(4, 6, 2) = 2`, so the reduction settles a `Z/2` at grade 1.
    fn staggered_attachment() -> GradedCausalComplex {
        let mut complex = GradedCausalComplex::default();
        let a = complex
            .found_cell("a", source(), 0, CausalChain::default())
            .unwrap();
        let b = complex
            .found_cell("b", source(), 0, CausalChain::default())
            .unwrap();
        let mut edges = Vec::new();
        for name in ["first", "second", "third"] {
            let mut boundary = CausalChain::default();
            boundary.add_term(b, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
            edges.push(complex.found_cell(name, source(), 1, boundary).unwrap());
        }
        let mut face = CausalChain::default();
        face.add_term(edges[0], ComparativeMultiplicity::positive(4u32));
        face.add_term(edges[1], ComparativeMultiplicity::negative(6u32));
        face.add_term(edges[2], ComparativeMultiplicity::positive(2u32));
        complex.found_cell("staggered", source(), 2, face).unwrap();
        complex
    }

    /// The same idea at rank two: four parallel edges and **two** staggered faces, so the filling
    /// map is `4 x 2` and the reduction settles two pivots rather than one. The single-column
    /// fixture above never exercises a column operation, so it cannot show a rule reaching a
    /// returned factor through the *column* half of the Euclidean descent; this one can.
    ///
    /// `4*e1 - 6*e2 + 2*e3` and `2*e1 + 3*e2 - 5*e4`, each summing to zero so each closes. The
    /// entries have gcd one and the 2x2 minors have gcd two, so the invariant factors are `1 | 2`
    /// and the torsion is again a `Z/2` — this time carried by the *second* factor.
    fn twice_staggered_attachment() -> GradedCausalComplex {
        let mut complex = GradedCausalComplex::default();
        let a = complex
            .found_cell("a", source(), 0, CausalChain::default())
            .unwrap();
        let b = complex
            .found_cell("b", source(), 0, CausalChain::default())
            .unwrap();
        let mut edges = Vec::new();
        for name in ["first", "second", "third", "fourth"] {
            let mut boundary = CausalChain::default();
            boundary.add_term(b, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
            edges.push(complex.found_cell(name, source(), 1, boundary).unwrap());
        }
        let mut first = CausalChain::default();
        first.add_term(edges[0], ComparativeMultiplicity::positive(4u32));
        first.add_term(edges[1], ComparativeMultiplicity::negative(6u32));
        first.add_term(edges[2], ComparativeMultiplicity::positive(2u32));
        complex.found_cell("staggered", source(), 2, first).unwrap();
        let mut second = CausalChain::default();
        second.add_term(edges[0], ComparativeMultiplicity::positive(2u32));
        second.add_term(edges[1], ComparativeMultiplicity::positive(3u32));
        second.add_term(edges[3], ComparativeMultiplicity::negative(5u32));
        complex
            .found_cell("staggered-again", source(), 2, second)
            .unwrap();
        complex
    }

    /// The fixture's own precondition, asserted rather than assumed: the boundary map the three
    /// rules disagree over must actually carry entries of unequal magnitude. If a later edit
    /// flattened those coefficients to units, the gauge below would keep passing while measuring
    /// nothing, and this is the assertion that would fail first.
    #[test]
    fn the_staggered_fixture_carries_boundary_entries_of_unequal_magnitude() {
        let complex = staggered_attachment();
        let filling = boundary_matrix(&complex, 2).unwrap();
        assert_eq!((filling.rows(), filling.columns()), (3, 1));
        let magnitudes: BTreeSet<BigInt> = (0..filling.rows())
            .map(|row| filling.at(row, 0).abs())
            .filter(|magnitude| !magnitude.is_zero())
            .collect();
        assert_eq!(
            magnitudes,
            BTreeSet::from([BigInt::from(2), BigInt::from(4), BigInt::from(6)]),
            "the filling map must carry three different magnitudes or no pivot rule can differ"
        );

        // and the contrast: the hollow triangle, which is what every other fixture looks like
        let flat = boundary_matrix(&hollow_triangle(), 1).unwrap();
        let flat_magnitudes: BTreeSet<BigInt> = (0..flat.rows())
            .flat_map(|row| (0..flat.columns()).map(move |column| (row, column)))
            .map(|(row, column)| flat.at(row, column).abs())
            .filter(|magnitude| !magnitude.is_zero())
            .collect();
        assert_eq!(
            flat_magnitudes,
            BTreeSet::from([BigInt::one()]),
            "a simplicial incidence has every nonzero entry at magnitude one, which is why it \
             cannot gauge the pivot rule"
        );
    }

    /// **The gauge.** Three rules, three genuinely different pivot walks, one set of invariants.
    ///
    /// This is what `PivotRule::ALL` exists for, and until this fixture existed it was measuring
    /// nothing: on every simplicial body the three walks coincide, so the loop ran one computation
    /// three times and compared it with itself twice.
    #[test]
    fn the_three_pivot_rules_take_three_different_paths_to_the_same_invariants() {
        let complex = staggered_attachment();

        let mut settled: Option<RebaseInvariants> = None;
        let mut walks: BTreeSet<Vec<(u32, Vec<(usize, usize)>)>> = BTreeSet::new();
        for rule in PivotRule::ALL {
            let (reading, schedule) = rebase_invariants_with_schedule(&complex, rule).unwrap();
            assert_eq!(
                schedule.rule, rule,
                "a schedule must name the rule that walked it"
            );
            walks.insert(
                schedule
                    .per_grade
                    .iter()
                    .map(|(grade, walk)| (*grade, walk.selections.clone()))
                    .collect(),
            );
            match &settled {
                None => settled = Some(reading),
                Some(first) => assert!(
                    invariants_agree(first, &reading),
                    "{rule:?} moved the returned invariants:\n{first:?}\n{reading:?}"
                ),
            }
        }
        assert_eq!(
            walks.len(),
            3,
            "the three rules must walk three different pivot sequences or their agreement is one \
             computation compared with itself twice; walks: {walks:?}"
        );

        // the agreement is on a reading that is itself nontrivial: a Z/2 at grade 1
        let settled = settled.expect("three rules were declared");
        assert_eq!(settled.total_torsion(), vec![BigInt::from(2)]);
        assert_eq!(
            settled.betti_vector(),
            vec![1, 1, 0],
            "one piece, one unfilled loop"
        );
        assert_eq!(settled.cell_euler_characteristic(), 0, "2 - 3 + 1");
    }

    /// The same gauge over a **two-pivot** reduction, so the column half of the Euclidean descent
    /// is walked under three different rules too.
    #[test]
    fn the_rank_two_filling_map_is_also_walked_three_different_ways() {
        let complex = twice_staggered_attachment();
        let filling = boundary_matrix(&complex, 2).unwrap();
        assert_eq!(
            (filling.rows(), filling.columns()),
            (4, 2),
            "the reduction must settle two pivots or the column operations are never reached"
        );

        let mut settled: Option<RebaseInvariants> = None;
        let mut walks: BTreeSet<Vec<(u32, Vec<(usize, usize)>)>> = BTreeSet::new();
        for rule in PivotRule::ALL {
            let (reading, schedule) = rebase_invariants_with_schedule(&complex, rule).unwrap();
            walks.insert(
                schedule
                    .per_grade
                    .iter()
                    .map(|(grade, walk)| (*grade, walk.selections.clone()))
                    .collect(),
            );
            match &settled {
                None => settled = Some(reading),
                Some(first) => assert!(
                    invariants_agree(first, &reading),
                    "{rule:?} moved the returned invariants:\n{first:?}\n{reading:?}"
                ),
            }
        }
        assert_eq!(walks.len(), 3, "walks: {walks:?}");

        let settled = settled.expect("three rules were declared");
        assert_eq!(
            smith_normal_form(&filling, PivotRule::FirstNonzero).factors,
            vec![BigInt::one(), BigInt::from(2)],
            "gcd of the entries is one and gcd of the 2x2 minors is two"
        );
        assert_eq!(settled.total_torsion(), vec![BigInt::from(2)]);
        assert_eq!(settled.betti_vector(), vec![1, 1, 0]);
        assert_eq!(settled.cell_euler_characteristic(), 0, "2 - 4 + 2");
    }

    /// The gauge's own aperture, stated rather than left to be discovered. On a simplicial
    /// incidence the three rules walk **one** sequence, so a three-rule check over such a body is
    /// vacuous — which is exactly what was true of every fixture in this project until the
    /// staggered one was founded.
    #[test]
    fn on_a_simplicial_incidence_the_three_rules_walk_the_same_sequence() {
        for (label, complex) in [
            ("hollow_triangle", hollow_triangle()),
            ("doubled_attachment", {
                let mut complex = GradedCausalComplex::default();
                let a = complex
                    .found_cell("a", source(), 0, CausalChain::default())
                    .unwrap();
                let mut loop_boundary = CausalChain::default();
                loop_boundary.add_term(a, ComparativeMultiplicity::positive(1u32));
                loop_boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
                let edge = complex
                    .found_cell("loop", source(), 1, loop_boundary)
                    .unwrap();
                let mut face = CausalChain::default();
                face.add_term(edge, ComparativeMultiplicity::positive(2u32));
                complex.found_cell("twice", source(), 2, face).unwrap();
                complex
            }),
        ] {
            let walks: BTreeSet<Vec<(u32, Vec<(usize, usize)>)>> = PivotRule::ALL
                .into_iter()
                .map(|rule| {
                    rebase_invariants_with_schedule(&complex, rule)
                        .unwrap()
                        .1
                        .per_grade
                        .iter()
                        .map(|(grade, walk)| (*grade, walk.selections.clone()))
                        .collect()
                })
                .collect();
            assert_eq!(
                walks.len(),
                1,
                "{label}: this body has a single pivot walk under all three rules, so a three-rule \
                 agreement over it is not evidence"
            );
        }
    }
}
