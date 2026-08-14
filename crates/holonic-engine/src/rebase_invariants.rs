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
    fn reduce_row(
        &mut self,
        target: usize,
        source: usize,
        factor: &BigInt,
        work: &mut ReductionWork,
    ) {
        for column in 0..self.columns {
            let delta = self.at(source, column) * factor;
            let value = self.at(target, column) - delta;
            work.record(&value);
            self.set(target, column, value);
        }
    }

    /// `column_target -= factor * column_source`. A rebase of the chain group this matrix maps into.
    fn reduce_column(
        &mut self,
        target: usize,
        source: usize,
        factor: &BigInt,
        work: &mut ReductionWork,
    ) {
        for row in 0..self.rows {
            let delta = self.at(row, source) * factor;
            let value = self.at(row, target) - delta;
            work.record(&value);
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

/// The pivot positions one reduction chose, in the order it chose them.
///
/// A pivot position is a **receiver coordinate** — a property of the solver, never of the incidence
/// — and this is the only place one leaves the reduction. It is returned so that "all three rules
/// agreed" can be audited for being an agreement between *different* computations: three identical
/// schedules are one computation compared with itself twice, which is a check whose material cannot
/// vary the property under test.
///
/// It is never compared as an invariant. [`invariants_agree`] does not read it and
/// [`RebaseInvariants`] does not carry it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PivotSchedule {
    /// `(row, column)` in the coordinates of the matrix handed in, one entry per pivot settled.
    /// A divisibility repair pushes the pivot it abandoned *and* the one it settled on afterwards,
    /// because the reduction really did select twice there.
    pub selections: Vec<(usize, usize)>,
    /// What the reduction actually cost, in work rather than in elapsed time.
    pub work: ReductionWork,
}

/// The exact work a reduction performed. Deterministic, machine-independent, reproducible.
///
/// **This exists because the pivot count does not explain the cost.** Measured 2026-08-08 on the
/// grade-two boundary map of a grown Brent–Kung adder: `SmallestMagnitude` took `1.0` selections per
/// extent and one millisecond, `LargestMagnitude` took `1.5` and eight, and `FirstNonzero` took the
/// same `1.5` and **did not complete in 390 seconds**. Three rules, two of them indistinguishable by
/// selection count and three orders of magnitude apart in cost. The dominating quantity is the
/// **bit-length of the intermediate entries**, and nothing counted it until now.
///
/// `CLAUDE.md` §8: *a cost is measured in work, never in elapsed time; a clock may measure, it may
/// never select.* A caller choosing between carriers must admit on this, not on a wall clock.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReductionWork {
    /// Entries written by a row or column operation.
    pub entries_written: u64,
    /// Total bit-length of every entry written. **The quantity that explains the wall.**
    ///
    /// `u64` rather than `u128` because a deposit's serializer refuses `u128`, and the headroom is
    /// not close: the largest reduction measured on grown material wrote 594,005 bits. Accumulation
    /// saturates rather than wrapping, so an impossible run reports a ceiling instead of a lie.
    pub written_bits: u64,
    /// The widest single entry the reduction ever wrote. Expression swell, exhibited.
    pub peak_entry_bits: u64,
    /// Divisibility repairs, each of which restarts a reduction on a fresh copy.
    pub repairs: u64,
}

impl ReductionWork {
    fn record(&mut self, value: &BigInt) {
        let bits = value.bits();
        self.entries_written = self.entries_written.saturating_add(1);
        self.written_bits = self.written_bits.saturating_add(bits);
        if bits > self.peak_entry_bits {
            self.peak_entry_bits = bits;
        }
    }

    /// Fold another reading's work into this one. Public so a consumer joining two readings —
    /// `skein::read_substitution` joins a before and an after — can report one figure.
    pub fn absorb_public(&mut self, other: &Self) {
        self.absorb(other);
    }

    fn absorb(&mut self, other: &Self) {
        self.entries_written = self.entries_written.saturating_add(other.entries_written);
        self.written_bits = self.written_bits.saturating_add(other.written_bits);
        self.peak_entry_bits = self.peak_entry_bits.max(other.peak_entry_bits);
        self.repairs = self.repairs.saturating_add(other.repairs);
    }
}

impl PivotSchedule {
    fn new() -> Self {
        Self {
            selections: Vec::new(),
            work: ReductionWork::default(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.selections.is_empty()
    }
}

/// Every pivot a whole reading's reductions chose, tagged by the grade whose boundary map they were
/// chosen in, and by the rule that chose them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReadingSchedule {
    pub rule: PivotRule,
    /// One entry per grade the reading reduced, in ascending grade order. A grade whose boundary
    /// map has no rows or no columns contributes an empty schedule rather than being dropped, so
    /// two schedules are comparable position for position.
    pub per_grade: Vec<(u32, PivotSchedule)>,
}

impl ReadingSchedule {
    /// What the whole reading cost, summed over its grades. Exact and machine-independent.
    ///
    /// A consumer that wants to report a reading's cost should take this rather than re-run the
    /// reduction. `skein::read_substitution` did exactly that re-run until 2026-08-08, because it
    /// called `rebase_invariants_on` and the work vector sat one call below.
    pub fn work(&self) -> ReductionWork {
        let mut total = ReductionWork::default();
        for (_, schedule) in &self.per_grade {
            total.absorb(&schedule.work);
        }
        total
    }
}

/// Reduce to Smith normal form over the integers.
///
/// Classical algorithm: clear the pivot row and column by repeated division with remainder — the
/// Euclidean descent, which is why the pivot ends up carrying the gcd — then repair divisibility so
/// each diagonal entry divides the next. Every step is an exact integer row or column operation,
/// which is to say a rebase of one of the two chain groups.
///
/// # The cost is carried by the RULE, not by the dimensions — measured 2026-08-08
///
/// The three rules are proved to return the same factors and are **not** proved to cost the same.
/// On the grade-two boundary map of a grown Brent–Kung adder at width 3, `[143 × 101]`, release
/// build, one machine, one sitting:
///
/// ```text
///   SmallestMagnitude      1 ms   rank 101   factors > 1  [2, 2, 2, 2]
///   LargestMagnitude       8 ms   rank 101   factors > 1  [2, 2, 2, 2]
///   FirstNonzero           did not complete in 390 s
/// ```
///
/// A spread of at least **390,000×** at fixed dimension. So any statement of the form *"the Smith
/// reduction is cubic in the cell count"* is not a bound — it omits the variable that dominates.
/// The mechanism is classical intermediate expression swell in the Euclidean descent below, and
/// `SmallestMagnitude` is its standard mitigation; it is also the only rule that took **no**
/// divisibility repair on this material, at exactly `extent` pivot selections against `1.5 × extent`
/// for the other two.
///
/// **`SmallestMagnitude` is the rule to pass at a single-rule call site ON THIS MATERIAL — and that
/// qualification is load-bearing.** Measured 2026-08-08 by `ReductionWork`: on a dense `4×4` of
/// three-digit integers `FirstNonzero` writes 36,352 bits, `SmallestMagnitude` 95,665 (taking the
/// only divisibility repair of the three), and `LargestMagnitude` 373,576. **Which rule is cheapest
/// is material-dependent**, and a cost law that does not name its material is no more a bound than
/// one that does not name its rule. What is stable across both measurements is that the *swell*
/// separates them: peak single-entry widths spread by more than an order of magnitude. `PivotRule::ALL`
/// remains the gauge and is unchanged — the point of it is that the *returns* do not move — but note
/// what this measurement says about it: on grown material the gauge's group acts non-trivially on
/// **cost** while acting trivially on the return, and `invariants_agree` compares returns and never
/// costs. That is `CLAUDE.md` §8's independent-implementation bullet pointing at a gauge.
///
/// **The falsifier this cost law lacked is now built.** The pivot selection count is *not* where the
/// blowup lives — it is `1.0` and `1.5` selections per extent at both widths, for rules three orders
/// of magnitude apart in cost. The dominating quantity is the bit-length of the intermediate
/// entries, and [`ReductionWork`] counts it: `entries_written`, `written_bits`, `peak_entry_bits`
/// and `repairs`, returned on every [`PivotSchedule`]. Those are exact, deterministic and
/// machine-independent, so a caller may now **admit on work** rather than on a wall clock, which is
/// what §8 requires. The nanosecond figures above remain lawful as measurement and carry their
/// frame; they no longer have to select anything.
pub fn smith_normal_form(matrix: &IntegerMatrix, rule: PivotRule) -> SmithNormalForm {
    smith_normal_form_with_schedule(matrix, rule).0
}

/// The same reduction, returning the pivot positions it chose.
///
/// [`smith_normal_form`] delegates here rather than the reverse, so the schedule is the schedule
/// the reduction actually walked and cannot drift from it.
pub fn smith_normal_form_with_schedule(
    matrix: &IntegerMatrix,
    rule: PivotRule,
) -> (SmithNormalForm, PivotSchedule) {
    let mut schedule = PivotSchedule::new();
    let form = reduce(matrix, rule, 0, &mut schedule);
    (form, schedule)
}

/// `origin` is where this matrix sits inside the one the caller handed in, so a divisibility
/// repair's recursion reports absolute positions rather than positions in its own trailing block.
fn reduce(
    matrix: &IntegerMatrix,
    rule: PivotRule,
    origin: usize,
    schedule: &mut PivotSchedule,
) -> SmithNormalForm {
    let mut work_matrix = matrix.clone();
    let mut work = ReductionWork::default();
    let extent = work_matrix.rows.min(work_matrix.columns);
    let mut factors = Vec::new();

    for pivot in 0..extent {
        let Some((row, column)) = work_matrix.find_pivot(pivot, rule) else {
            break;
        };
        schedule.selections.push((row + origin, column + origin));
        work_matrix.swap_rows(pivot, row);
        work_matrix.swap_columns(pivot, column);

        // Euclidean descent on the pivot cross. Each pass strictly reduces |pivot| whenever it does
        // not already divide its cross, so this terminates.
        loop {
            for row in pivot + 1..work_matrix.rows {
                if work_matrix.at(row, pivot).is_zero() {
                    continue;
                }
                let quotient = work_matrix.at(row, pivot) / work_matrix.at(pivot, pivot);
                work_matrix.reduce_row(row, pivot, &quotient, &mut work);
                if !work_matrix.at(row, pivot).is_zero() {
                    work_matrix.swap_rows(pivot, row);
                }
            }
            for column in pivot + 1..work_matrix.columns {
                if work_matrix.at(pivot, column).is_zero() {
                    continue;
                }
                let quotient = work_matrix.at(pivot, column) / work_matrix.at(pivot, pivot);
                work_matrix.reduce_column(column, pivot, &quotient, &mut work);
                if !work_matrix.at(pivot, column).is_zero() {
                    work_matrix.swap_columns(pivot, column);
                }
            }
            if work_matrix.is_zero_below(pivot) && work_matrix.is_zero_right(pivot) {
                break;
            }
        }

        // Divisibility repair. If the pivot does not divide some entry of the remaining block, fold
        // that entry's row into the pivot row and descend again; the pivot strictly decreases in
        // magnitude, so this terminates too.
        let mut repaired = false;
        'repair: for row in pivot + 1..work_matrix.rows {
            for column in pivot + 1..work_matrix.columns {
                if work_matrix.at(row, column).is_zero() {
                    continue;
                }
                if (work_matrix.at(row, column) % work_matrix.at(pivot, pivot)).is_zero() {
                    continue;
                }
                let one = BigInt::from(-1);
                work_matrix.reduce_row(pivot, row, &one, &mut work);
                repaired = true;
                break 'repair;
            }
        }
        if repaired {
            // Redo this pivot with the folded row in place.
            work.repairs += 1;
            schedule.work.absorb(&work);
            let tail = reduce_from(&work_matrix, pivot, rule, origin, schedule);
            factors.extend(tail);
            return normalize(factors);
        }

        work.record(work_matrix.at(pivot, pivot));
        let diagonal = work_matrix.at(pivot, pivot).clone();
        if diagonal.is_zero() {
            break;
        }
        factors.push(diagonal.abs());
    }

    schedule.work.absorb(&work);
    normalize(factors)
}

/// Resume the reduction at `from`, used by the divisibility repair so the retry does not discard
/// the factors already settled above it.
fn reduce_from(
    work_matrix: &IntegerMatrix,
    from: usize,
    rule: PivotRule,
    origin: usize,
    schedule: &mut PivotSchedule,
) -> Vec<BigInt> {
    let mut trailing = IntegerMatrix::zeros(work_matrix.rows - from, work_matrix.columns - from);
    for row in from..work_matrix.rows {
        for column in from..work_matrix.columns {
            trailing.set(
                row - from,
                column - from,
                work_matrix.at(row, column).clone(),
            );
        }
    }
    reduce(&trailing, rule, origin + from, schedule).factors
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
