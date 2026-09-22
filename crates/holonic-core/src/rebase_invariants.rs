//! **The integer Smith reduction under the rebase invariants: the pivot rule, the integer matrix,
//! its normal form and the exact work of the reduction.**
//!
//! [definition] This is the complex-free half of the engine's `rebase_invariants` module, moved
//! into the Holon core with the exact linear base because [`crate::inertia`] reads
//! [`IntegerMatrix`]. The half that reads a `GradedCausalComplex` — boundary matrices, Betti
//! numbers, torsion and `RebaseInvariants` — stays in `holonic_engine::rebase_invariants`, which
//! re-exports every item here at its old path. The measured cost law and the uniqueness gauge are
//! documented on [`smith_normal_form`] below.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};

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
