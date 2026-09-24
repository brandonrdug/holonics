//! **What an exact deed cost, counted rather than timed.**
//!
//! [definition] The work of an exact rational deed is a **vector**, ordered by domination: an
//! operation count and an intermediate width are not exchangeable, so two deeds where one performs
//! more operations and the other holds wider entries compare as `Open` in the four-state
//! [`crate::ratio::ExactOrdering`], which keeps both operands rather than tie-breaking.
//! A timing is an exterior face of a receipt; it never becomes a cost law or an infeasibility.
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
//! Exact admission in this module uses the complete work vector, never elapsed time or a scalar
//! surrogate. A caller may keep elapsed-time statistics, a declared wall-time budget, or an
//! optimization objective beside that vector; those external measurements do not establish exact
//! infeasibility, and a timeout must not become a mathematical infeasibility refusal or an
//! exact projected work law.

use crate::ratio::Rat;
use num_bigint::BigUint;

use crate::ratio::ExactOrdering;

/// **The work an exact deed performed.** Every coordinate is counted; none is timed.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
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
    /// The widest single entry the deed had to represent exactly: the dominating quantity of an
    /// exact elimination.
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
    pub(crate) fn wrote(&mut self, entry: &Rat) {
        let width = BigUint::from(entry.numer().bits() + entry.denom().bits());
        self.entries_written += 1u32;
        self.cumulative_bits += &width;
        if width > self.peak_bits {
            self.peak_bits = width;
        }
    }

    pub(crate) fn added(&mut self, count: u64) {
        self.additions += count;
    }

    pub(crate) fn multiplied(&mut self, count: u64) {
        self.multiplications += count;
    }

    pub(crate) fn divided(&mut self, count: u64) {
        self.divisions += count;
    }

    pub(crate) fn stepped(&mut self) {
        self.dependency_span += 1u32;
    }

    /// Widen the resident reading. Monotone: a body that shrank still had to hold its widest.
    pub(crate) fn resident(&mut self, entries: u64) {
        let entries = BigUint::from(entries);
        if entries > self.resident_entries {
            self.resident_entries = entries;
        }
    }

    /// Two deeds performed in sequence. Counts add; **peak and resident take the maximum**, because
    /// a width is not additive — the widest thing that had to exist is the widest of the two.
    /// Dependency spans add, because sequence is what a span measures.
    pub(crate) fn then(&self, next: &Self) -> Self {
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

    /// **`(additions + multiplications + divisions) × peak_bits`**, a derived coordinate: the width
    /// dominates the cost of each operation, not their count, and a weighted sum of the counted
    /// coordinates cannot express that product.
    pub fn width_weighted_operations(&self) -> BigUint {
        (&self.additions + &self.multiplications + &self.divisions) * &self.peak_bits
    }

    /// **The product order, and it is the whole admission law.**
    ///
    /// `Less` when every coordinate is `≤` and one is strictly less; `Greater` symmetrically; `Equal`
    /// when every coordinate agrees; and **`Open` when neither dominates**, which is the case a
    /// scalar cost hides. `Open` is not a tie and is not broken here; a caller that needs a decision
    /// there declares its own receiver metric.
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
}
