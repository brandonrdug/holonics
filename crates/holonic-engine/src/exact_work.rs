//! **What an exact deed cost, counted rather than timed.**
//!
//! ## Why this exists, and what it discharges
//!
//! `docs/canon/TABLET_THE_CHART.md` §3.7 carries a standing owed item, and it is the one that makes every
//! cost question in this repository unanswerable:
//!
//! > *"the machine currently has no organ that returns **'is this solvable, and at what cost'** as a
//! > typed answer… `PivotSchedule` returns the pivot count and it is provably **not** the dominating
//! > quantity; the dominating quantity is **intermediate entry bit-length** and nothing counts it.
//! > Until a work vector exists, no cost question in this repository has a lawful answer."*
//!
//! Measured 2026-08-17 by
//! `grep -rn "\.bits()" --include='*.rs' crates/holonic-engine/src/inertia.rs
//! crates/holonic-engine/src/exact_linear.rs` → **0**, against **17** across all library `src`. The
//! two modules whose intermediate width dominates every exact deed never took it.
//!
//! ## The occasion, which is a violation this module repairs
//!
//! On 2026-08-17 a driver fitted `t ~ 1.23e-6 · k^4.18` from **elapsed seconds** over `k ∈ {8,16,32,64}`
//! and used the projection to refuse a `k = 256` deed. An external adjudication convicted it:
//!
//! > *"Promoting a timeout into a cost law and using its fitted clock projection to select the
//! > aperture was the breach. The honest return was `Open: exceeded this apparatus-time aperture;
//! > work unknown`, not '3.96 hours, therefore refused.'"*
//!
//! and observed that averaging adjacent logarithmic slopes over **doubling** extents telescopes to
//! `(log₂ t₆₄ − log₂ t₈)/3`, so the two interior measurements did not affect the fitted exponent at
//! all. `CLAUDE.md`'s rule is that **a cost is measured in work; a clock may measure but may never
//! select.** This module is the work.
//!
//! ## The law it is a lift of
//!
//! `cuda_aperture::CarrierWork` already established the species — a **vector**, ordered by
//! domination, returning the four-state [`crate::exact_value::ExactOrdering`] whose `Open` **retains
//! both carriers** rather than tie-breaking — and it already declares `intermediate_bits`, *"the
//! widest intermediate this carrier had to represent exactly."* What it does not do is arise from an
//! exact deed: `CarrierWork::of_candidate` reads a device aperture receipt and nothing reads an
//! elimination. [`ExactWork`] is that same law with the coordinates an exact rational deed actually
//! has, and its ordering is `CarrierWork::order_against`'s.
//!
//! ## The coordinates, and why each is separate
//!
//! An operation count and a width are **not exchangeable**, which is the whole reason this is a
//! vector. Exact rational elimination performs `O(k³)` operations on entries that are `k × k` minors,
//! so its width grows with its depth and a scalar summarising both would hide which one moved.
//!
//! ```text
//!   additions · multiplications · divisions     what was performed
//!   entries_written                             how much was materialised
//!   cumulative_bits                             the total exact width written
//!   peak_bits                                   the widest single entry — the dominating quantity
//!   resident_entries                            the working body at its widest
//!   dependency_span                             the longest chain that must happen in order
//! ```
//!
//! **A division carries a normalisation.** `Rat` reduces on construction, so a division is a `gcd`
//! over the operand widths and is the most expensive coordinate per unit. It is counted separately
//! from multiplication for that reason and never folded into it.
//!
//! ## What is refused
//!
//! No elapsed time, anywhere in this module. A caller that wants a clock keeps one beside the vector
//! and it may not enter [`WorkBudget::admits`]. And no scalar: the ordering is the product order, and
//! where it returns `Open` a **declared receiver metric** decides — which is a caller's declaration
//! exhibited in the return, never a governor inside the organ.

use num_bigint::BigUint;
use num_traits::Zero;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};

use crate::exact_value::ExactOrdering;

/// **The work an exact deed performed.** Every coordinate is counted; none is timed.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactWork {
    /// Rational additions and subtractions.
    pub additions: BigUint,
    /// Rational multiplications.
    pub multiplications: BigUint,
    /// Rational divisions. Each carries a normalisation over the operand widths.
    pub divisions: BigUint,
    /// Entries written into a working body.
    pub entries_written: BigUint,
    /// Summed over every entry written: the bit-length of its numerator plus its denominator.
    pub cumulative_bits: BigUint,
    /// The widest single entry the deed had to represent exactly — **the dominating quantity**
    /// `TABLET_THE_CHART` §3.7 names and which nothing counted before 2026-08-17.
    pub peak_bits: BigUint,
    /// Rationals resident in the working body at its widest.
    pub resident_entries: BigUint,
    /// The longest chain of steps that must happen in order. A serial elimination's span is its
    /// pivot count; a product's is one.
    pub dependency_span: BigUint,
}

impl ExactWork {
    /// The zero vector — a deed that performed nothing.
    pub fn nothing() -> Self {
        Self::default()
    }

    /// Count one entry written, and widen the cumulative and peak readings by its exact width.
    ///
    /// **The width is the numerator's bits plus the denominator's**, because an exact rational costs
    /// both and a reduced fraction with a huge denominator is not cheap.
    pub fn wrote(&mut self, entry: &Rat) {
        let width = BigUint::from(entry.numer().bits() + entry.denom().bits());
        self.entries_written += 1u32;
        self.cumulative_bits += &width;
        if width > self.peak_bits {
            self.peak_bits = width;
        }
    }

    pub fn added(&mut self, count: u64) {
        self.additions += count;
    }

    pub fn multiplied(&mut self, count: u64) {
        self.multiplications += count;
    }

    pub fn divided(&mut self, count: u64) {
        self.divisions += count;
    }

    pub fn stepped(&mut self) {
        self.dependency_span += 1u32;
    }

    /// Widen the resident reading. Monotone: a body that shrank still had to hold its widest.
    pub fn resident(&mut self, entries: u64) {
        let entries = BigUint::from(entries);
        if entries > self.resident_entries {
            self.resident_entries = entries;
        }
    }

    /// Two deeds performed in sequence. Counts add; **peak and resident take the maximum**, because
    /// a width is not additive — the widest thing that had to exist is the widest of the two.
    /// Dependency spans add, because sequence is what a span measures.
    pub fn then(&self, next: &Self) -> Self {
        Self {
            additions: &self.additions + &next.additions,
            multiplications: &self.multiplications + &next.multiplications,
            divisions: &self.divisions + &next.divisions,
            entries_written: &self.entries_written + &next.entries_written,
            cumulative_bits: &self.cumulative_bits + &next.cumulative_bits,
            peak_bits: self.peak_bits.clone().max(next.peak_bits.clone()),
            resident_entries: self
                .resident_entries
                .clone()
                .max(next.resident_entries.clone()),
            dependency_span: &self.dependency_span + &next.dependency_span,
        }
    }

    /// **The work a symmetric elimination WILL do, predicted from its shape and its input width.**
    ///
    /// A budget that admits on *measured* work refuses nothing: the deed has already been paid for
    /// by the time the vector exists. A refusal has to happen before the cost does, so it has to
    /// happen on a prediction — and `cuda_aperture::CarrierWork::of_cpu_authority` already
    /// established that shape and said why:
    ///
    /// > *"That this is a **prediction** is what makes the cost law falsifiable: running the
    /// > authority either confirms the predicted ordering or refutes it, and a refutation says the
    /// > declared law is wrong about this material — information the clock comparison could not
    /// > produce at all."*
    ///
    /// The model, and every term of it is refutable:
    ///
    /// ```text
    ///   operations   Σ_{j<k} (k−j)²  =  k(k−1)(2k−1)/6   per species, from the Schur complement
    ///   entries      k² written once, then the same sum
    ///   span         k, because each pivot depends on the last
    ///   peak width   k · b, because the entry after j steps is a (j+1)×(j+1) minor of b-bit entries
    /// ```
    ///
    /// The peak term is the one most likely to be wrong, and deliberately so: Hadamard bounds a
    /// `j × j` minor of `b`-bit entries at about `j(b + log₂ j)` bits, so `k · b` **under**-predicts
    /// and the measurement should exceed it. A prediction that could not be exceeded would be a
    /// ceiling rather than a law.
    pub fn predicted_elimination(extent: usize, entry_bits: u64) -> Self {
        let extent64 = extent as u64;
        // Σ_{j=0}^{k-1} (k−1−j)² = (k−1)k(2k−1)/6
        let operations = if extent64 == 0 {
            0
        } else {
            (extent64 - 1) * extent64 * (2 * extent64 - 1) / 6
        };
        Self {
            additions: BigUint::from(operations),
            multiplications: BigUint::from(operations),
            divisions: BigUint::from(operations),
            entries_written: BigUint::from(extent64 * extent64 + operations),
            cumulative_bits: BigUint::from(operations * extent64 * entry_bits / 2),
            peak_bits: BigUint::from(extent64 * entry_bits),
            resident_entries: BigUint::from(extent64 * extent64),
            dependency_span: BigUint::from(extent64),
        }
    }

    /// **The work a matrix product WILL do.** `rows × inner × columns` multiply-adds, `rows ×
    /// columns` entries written, and — the coordinate that separates it from an elimination —
    /// **a dependency span of one**, because every output entry is independent of every other.
    ///
    /// The peak is `2b + log₂(inner)`: a sum of `inner` products of `b`-bit entries.
    pub fn predicted_product(rows: usize, inner: usize, columns: usize, entry_bits: u64) -> Self {
        let operations = rows as u64 * inner as u64 * columns as u64;
        let written = rows as u64 * columns as u64;
        let peak = 2 * entry_bits + (inner as u64).max(1).ilog2() as u64;
        Self {
            additions: BigUint::from(operations),
            multiplications: BigUint::from(operations),
            divisions: BigUint::zero(),
            entries_written: BigUint::from(written),
            cumulative_bits: BigUint::from(written * peak),
            peak_bits: BigUint::from(peak),
            resident_entries: BigUint::from(written),
            dependency_span: BigUint::from(1u32),
        }
    }

    /// **What a prediction got wrong, per coordinate, as an exact ratio in thousandths.**
    ///
    /// Returned as a pair `(predicted, measured)` per coordinate rather than as a verdict, because
    /// a prediction that over-shoots on width and under-shoots on count has said two different
    /// things and a single figure would hide one of them.
    pub fn against(&self, measured: &Self) -> Vec<(&'static str, BigUint, BigUint)> {
        self.coordinates()
            .into_iter()
            .zip(measured.coordinates())
            .map(|((name, predicted), (_, actual))| (name, predicted, actual))
            .collect()
    }

    /// Every coordinate by name, in a fixed order, so a reading can enumerate without knowing the
    /// struct. A caller declaring a metric addresses coordinates by these names.
    pub fn coordinates(&self) -> Vec<(&'static str, BigUint)> {
        vec![
            ("additions", self.additions.clone()),
            ("multiplications", self.multiplications.clone()),
            ("divisions", self.divisions.clone()),
            ("entries-written", self.entries_written.clone()),
            ("cumulative-bits", self.cumulative_bits.clone()),
            ("peak-bits", self.peak_bits.clone()),
            ("resident-entries", self.resident_entries.clone()),
            ("dependency-span", self.dependency_span.clone()),
            (
                "width-weighted-operations",
                self.width_weighted_operations(),
            ),
        ]
    }

    /// **`(additions + multiplications + divisions) × peak_bits`** — a DERIVED coordinate, added
    /// 2026-08-17 because the material refuted the metric that lacked it.
    ///
    /// A linear metric over the counted coordinates prices an operation on a 5,000-bit rational the
    /// same as one on a 60-bit rational. `docs/canon/TABLET_THE_CHART.md` §3.7 says *"the dominating
    /// quantity is intermediate entry bit-length"*, and under unit weights the measurement said
    /// otherwise: at every deferred extent the operation **count** carried the price. Both are true
    /// and they are not in conflict — the width does not dominate the count, it dominates the **cost
    /// of each operation** — and a weighted **sum** cannot express a **product**.
    ///
    /// So this coordinate is the product, offered so a receiver that prices width-weighted work can
    /// declare it. It is derived rather than counted, and it is named that way, because a caller must
    /// be able to tell which coordinates the deed reported and which one this module computed.
    pub fn width_weighted_operations(&self) -> BigUint {
        (&self.additions + &self.multiplications + &self.divisions) * &self.peak_bits
    }

    /// **The product order, and it is the whole admission law.**
    ///
    /// `Less` when every coordinate is `≤` and one is strictly less; `Greater` symmetrically; `Equal`
    /// when every coordinate agrees; and **`Open` when neither dominates**, which is the case a
    /// scalar cost hides. `Open` is not a tie and must not be broken here — a caller that needs a
    /// decision there declares a [`WorkMetric`], and the declaration is a receiver's, exhibited.
    ///
    /// This is `cuda_aperture::CarrierWork::order_against`'s law over these coordinates.
    pub fn order_against(&self, other: &Self) -> ExactOrdering {
        let mut any_less = false;
        let mut any_greater = false;
        for ((_, mine), (_, theirs)) in self.coordinates().iter().zip(other.coordinates().iter()) {
            match mine.cmp(theirs) {
                std::cmp::Ordering::Less => any_less = true,
                std::cmp::Ordering::Greater => any_greater = true,
                std::cmp::Ordering::Equal => {}
            }
        }
        match (any_less, any_greater) {
            (false, false) => ExactOrdering::Equal,
            (true, false) => ExactOrdering::Less,
            (false, true) => ExactOrdering::Greater,
            (true, true) => ExactOrdering::Open,
        }
    }
}

/// **A receiver's declared weighting of the coordinates**, used only where the product order returns
/// `Open`.
///
/// It is a declaration and it is exhibited in every return that used it, because a weighting is a
/// receiver coordinate and a reading that hid it would be presenting one receiver's face as the
/// object. A weight of zero means the receiver does not price that coordinate at all.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkMetric {
    pub name: String,
    /// `(coordinate, weight)`. Coordinates absent from this list are priced at zero.
    pub weights: Vec<(String, BigUint)>,
}

impl WorkMetric {
    pub fn declared(name: &str, weights: &[(&str, u64)]) -> Self {
        Self {
            name: name.to_owned(),
            weights: weights
                .iter()
                .map(|(coordinate, weight)| ((*coordinate).to_owned(), BigUint::from(*weight)))
                .collect(),
        }
    }

    /// **The dominating-quantity metric**, named for what `TABLET_THE_CHART` §3.7 says dominates: the
    /// peak intermediate width, with the operation count beside it at unit weight so a deed that is
    /// narrow and enormous is not free.
    ///
    /// **This metric was refuted by the material on 2026-08-17** and is kept for exactly that — its
    /// unit weights price an operation on a 5,000-bit rational the same as one on a 60-bit rational,
    /// so it defers on the operation count while the tablet says the width dominates. Both readings
    /// are correct and the metric cannot hold both. [`WorkMetric::width_weighted`] is the repair, and
    /// this one is the before-arm.
    pub fn peak_width() -> Self {
        Self::declared(
            "peak-width",
            &[
                ("peak-bits", 1),
                ("multiplications", 1),
                ("divisions", 1),
                ("additions", 1),
            ],
        )
    }

    /// **The metric that can express the tablet's claim**: the width-weighted operation count, which
    /// is a product and therefore unavailable to any weighted sum over the counted coordinates alone.
    pub fn width_weighted() -> Self {
        Self::declared("width-weighted", &[("width-weighted-operations", 1)])
    }

    /// This receiver's price for a work vector.
    pub fn price(&self, work: &ExactWork) -> BigUint {
        let coordinates = work.coordinates();
        let mut total = BigUint::zero();
        for (name, weight) in &self.weights {
            if let Some((_, value)) = coordinates
                .iter()
                .find(|(coordinate, _)| *coordinate == name.as_str())
            {
                total += value * weight;
            }
        }
        total
    }
}

/// **What a declared budget did with a work vector.** A typed return, never prose.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Admission {
    /// Every priced coordinate is inside the declared ceiling.
    Admitted { priced: BigUint, ceiling: BigUint },
    /// The metric's price exceeds the declared ceiling. **The coordinate that carried it is named**,
    /// so a caller learns what made the deed expensive rather than that it was.
    Deferred {
        priced: BigUint,
        ceiling: BigUint,
        /// The single coordinate contributing the most to the price, with its contribution.
        dominating: (String, BigUint),
    },
}

impl Admission {
    pub const fn is_admitted(&self) -> bool {
        matches!(self, Self::Admitted { .. })
    }
}

/// A receiver's declared metric together with the ceiling it will pay.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkBudget {
    pub metric: WorkMetric,
    pub ceiling: BigUint,
}

impl WorkBudget {
    pub fn declared(metric: WorkMetric, ceiling: u64) -> Self {
        Self {
            metric,
            ceiling: BigUint::from(ceiling),
        }
    }

    /// **The typed admission.** No clock enters here and none can: the only argument is a counted
    /// vector.
    pub fn admits(&self, work: &ExactWork) -> Admission {
        let priced = self.metric.price(work);
        if priced <= self.ceiling {
            return Admission::Admitted {
                priced,
                ceiling: self.ceiling.clone(),
            };
        }
        let coordinates = work.coordinates();
        let mut dominating = (String::new(), BigUint::zero());
        for (name, weight) in &self.metric.weights {
            if let Some((_, value)) = coordinates
                .iter()
                .find(|(coordinate, _)| *coordinate == name.as_str())
            {
                let contribution = value * weight;
                if contribution > dominating.1 {
                    dominating = (name.clone(), contribution);
                }
            }
        }
        Admission::Deferred {
            priced,
            ceiling: self.ceiling.clone(),
            dominating,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn rational(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    /// ★ A WIDTH IS NOT AN OPERATION COUNT, which is the whole reason this is a vector. Two deeds
    /// where one performs more operations and the other holds wider entries must return `Open`, and
    /// a scalar cost is exactly what would hide it.
    #[test]
    fn a_wide_narrow_pair_is_open_and_a_scalar_would_have_hidden_it() {
        let mut many_narrow = ExactWork::nothing();
        many_narrow.multiplied(1000);
        many_narrow.wrote(&rational(3, 4));

        let mut few_wide = ExactWork::nothing();
        few_wide.multiplied(2);
        few_wide.wrote(&rational(1 << 40, 3));

        assert_eq!(many_narrow.order_against(&few_wide), ExactOrdering::Open);
        assert_eq!(few_wide.order_against(&many_narrow), ExactOrdering::Open);
        // and the product order is not vacuous: a strictly dominated pair orders.
        let mut dominated = many_narrow.clone();
        dominated.multiplied(1);
        assert_eq!(many_narrow.order_against(&dominated), ExactOrdering::Less);
        assert_eq!(
            dominated.order_against(&many_narrow),
            ExactOrdering::Greater
        );
        assert_eq!(
            many_narrow.order_against(&many_narrow),
            ExactOrdering::Equal
        );
    }

    /// ★ THE WIDTH IS NUMERATOR PLUS DENOMINATOR. A reduced fraction with a huge denominator is not
    /// cheap, and counting only the numerator would say it was.
    #[test]
    fn the_width_counts_both_halves_of_the_rational() {
        let mut work = ExactWork::nothing();
        work.wrote(&rational(1, 1 << 40));
        assert!(
            work.peak_bits > BigUint::from(40u32),
            "a unit numerator over a wide denominator is a wide entry"
        );
        let mut narrow = ExactWork::nothing();
        narrow.wrote(&rational(1, 1));
        assert!(narrow.peak_bits < work.peak_bits);
    }

    /// ★ SEQUENCE ADDS COUNTS AND TAKES THE MAXIMUM WIDTH. A width is not additive: two deeds each
    /// holding a 100-bit entry did not hold a 200-bit one.
    #[test]
    fn composition_adds_counts_and_maxima_the_widths() {
        let mut first = ExactWork::nothing();
        first.multiplied(3);
        first.wrote(&rational(1 << 20, 7));
        first.resident(16);
        first.stepped();

        let mut second = ExactWork::nothing();
        second.multiplied(5);
        second.wrote(&rational(1 << 30, 7));
        second.resident(4);
        second.stepped();

        let composed = first.then(&second);
        assert_eq!(composed.multiplications, BigUint::from(8u32));
        assert_eq!(composed.entries_written, BigUint::from(2u32));
        assert_eq!(composed.peak_bits, second.peak_bits, "the wider of the two");
        assert_eq!(
            composed.resident_entries,
            BigUint::from(16u32),
            "the wider body"
        );
        assert_eq!(composed.dependency_span, BigUint::from(2u32), "spans add");
        assert_eq!(
            composed.cumulative_bits,
            &first.cumulative_bits + &second.cumulative_bits,
            "cumulative width IS additive, which is why it is a separate coordinate"
        );
    }

    /// ★ THE ADMISSION IS TYPED AND IT NAMES WHAT MADE THE DEED EXPENSIVE. A budget that only said
    /// "no" would have reported less than the clock it replaced.
    #[test]
    fn a_deferral_names_the_coordinate_that_carried_it() {
        let budget = WorkBudget::declared(WorkMetric::peak_width(), 100);
        let mut cheap = ExactWork::nothing();
        cheap.multiplied(4);
        cheap.wrote(&rational(3, 4));
        assert!(budget.admits(&cheap).is_admitted());

        let mut wide = ExactWork::nothing();
        wide.multiplied(4);
        wide.wrote(&Rat::new(BigInt::from(1u8) << 200, BigInt::from(3)));
        let verdict = budget.admits(&wide);
        match verdict {
            Admission::Deferred { dominating, .. } => {
                assert_eq!(dominating.0, "peak-bits", "the width carried the refusal");
            }
            Admission::Admitted { .. } => panic!("a 200-bit entry must exceed a ceiling of 100"),
        }
        // AND THE ARM THAT MAKES THE NAMING MEAN SOMETHING: a deed refused for its OPERATION count
        // must name that coordinate instead, or `dominating` is a constant wearing a field name.
        let mut busy = ExactWork::nothing();
        busy.multiplied(5000);
        busy.wrote(&rational(3, 4));
        match budget.admits(&busy) {
            Admission::Deferred { dominating, .. } => {
                assert_eq!(
                    dominating.0, "multiplications",
                    "the count carried this one"
                );
            }
            Admission::Admitted { .. } => panic!("5000 multiplications exceed a ceiling of 100"),
        }
    }

    /// ★ THE MATERIAL REFUTED THE FIRST METRIC, and this is that refutation kept as a test.
    ///
    /// Under unit weights an operation on a 5,000-bit rational prices the same as one on a 60-bit
    /// rational, so `peak_width` defers on the operation **count** while `TABLET_THE_CHART` §3.7 says
    /// the **width** dominates. Both readings are right; a weighted **sum** cannot hold both, because
    /// the thing that dominates is a **product**. The two metrics must therefore name different
    /// coordinates on one vector, or the derived one bought nothing.
    #[test]
    fn a_weighted_sum_cannot_express_what_a_product_does_and_the_two_metrics_disagree() {
        let mut work = ExactWork::nothing();
        work.multiplied(2_000_000);
        work.wrote(&Rat::new(BigInt::from(1u8) << 5000, BigInt::from(3)));

        let unit = WorkBudget::declared(WorkMetric::peak_width(), 1_500_000);
        match unit.admits(&work) {
            Admission::Deferred { dominating, .. } => assert_eq!(
                dominating.0, "multiplications",
                "under unit weights the COUNT carries the price, which is the refutation"
            ),
            Admission::Admitted { .. } => panic!("2,000,000 operations exceed a ceiling of 1.5M"),
        }
        // The derived coordinate is the product, and it is the one the tablet's claim needs.
        let weighted = WorkBudget::declared(WorkMetric::width_weighted(), 1_500_000);
        match weighted.admits(&work) {
            Admission::Deferred { dominating, .. } => assert_eq!(
                dominating.0, "width-weighted-operations",
                "and here the WIDTH is what carried it"
            ),
            Admission::Admitted { .. } => panic!("the product exceeds the ceiling by orders"),
        }
        // ANTI-VACUITY: the derived coordinate must be able to admit what the unit metric defers, or
        // it is a strictly harsher ceiling wearing a different name.
        let mut narrow_and_busy = ExactWork::nothing();
        narrow_and_busy.multiplied(2_000_000);
        narrow_and_busy.wrote(&rational(3, 4));
        assert!(!unit.admits(&narrow_and_busy).is_admitted());
        assert!(
            WorkBudget::declared(WorkMetric::width_weighted(), 20_000_000)
                .admits(&narrow_and_busy)
                .is_admitted(),
            "a narrow deed of the same count is cheap under the width-weighted metric"
        );
    }

    /// ★ A METRIC IS A DECLARATION AND DIFFERENT RECEIVERS DISAGREE. If every metric returned the
    /// same verdict the declaration would be decorative, so the orbit is exhibited.
    #[test]
    fn two_declared_metrics_disagree_on_one_vector() {
        let mut work = ExactWork::nothing();
        work.multiplied(500);
        work.wrote(&rational(3, 4));

        let counts_operations = WorkBudget::declared(
            WorkMetric::declared("operations", &[("multiplications", 1)]),
            100,
        );
        let counts_width =
            WorkBudget::declared(WorkMetric::declared("width", &[("peak-bits", 1)]), 100);
        assert!(!counts_operations.admits(&work).is_admitted());
        assert!(counts_width.admits(&work).is_admitted());
    }
}
