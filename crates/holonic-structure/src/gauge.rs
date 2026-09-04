//! THE DECLARED GAUGE — a transformation that cannot be asserted invariant until it has been shown
//! to act.
//!
//! ## The occasion, and it is the dominant defect of 2026-08-15
//!
//! Four audits in one session returned the same finding more often than any other: **a control that
//! cannot fail.** Every instance had the same shape — an invariance was asserted over material the
//! declared transformation could not vary:
//!
//! - cocycle tests composing authored values with a hand-picked "direct" equal to the product, so
//!   they asserted the associativity of rational multiplication and nothing about junctions;
//! - a remount test resealing with the very values it then asserted equal;
//! - an organ-difference reading whose every organ carried `b"a"`, `b"b"`, `b"declared"`;
//! - a superposition test collecting into a map, so its second entry overwrote its first;
//! - a presence assertion on a compiled symbol that could not fail once the symbol existed.
//!
//! The operating contract already forbids this — *a gauge whose group acts trivially on the declared
//! material is not a gauge* — and **nowhere enforced it.** A rule that is not checkable is a rule
//! that is skipped, which the same contract says in its own words about orientation.
//!
//! ## What this carrier does
//!
//! It makes the second arm **structural rather than remembered**. A `DeclaredGauge` cannot be
//! constructed from material its transformation left alone, so a test that wants to assert *this
//! reading survived the transformation* must first hold a value that only exists if the
//! transformation moved something.
//!
//! ```text
//!    DeclaredGauge::of(before, after)?      REFUSES when before == after, elementwise
//!    .witness()                             the moved positions, exhibited and never counted
//! ```
//!
//! **It is not a test framework and it enforces nothing about what you then assert.** It removes
//! exactly one failure mode: asserting invariance under a transformation that did nothing. The one
//! test in the tree that already had both arms — `crates/holonic-body/src/arrow.rs`'s affine gauge orbit, with
//! its `a_magnitude_moved` flag — is the pattern this generalises.

use alloc::vec::Vec;

use serde::{Deserialize, Serialize};

/// Why a declared gauge refused. Both variants are structural and are taken before any assertion.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TrivialGauge {
    /// The transformation moved nothing. **This is the whole point of the carrier**: an invariance
    /// asserted here would hold for any reading whatever, including a reading that is wrong.
    ActedTrivially { members: usize },
    /// The two sides have different extents, so there is no elementwise comparison to make and the
    /// orbit is not defined. Refused rather than truncated — a comparison over a prefix is not a
    /// comparison.
    ExtentDisagrees { before: usize, after: usize },
    /// An empty declaration. A gauge over no material has not been tested either.
    NoMaterial,
}

/// One declared transformation, together with proof that it acted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclaredGauge<T> {
    before: Vec<T>,
    after: Vec<T>,
    moved: Vec<usize>,
}

impl<T: PartialEq + Clone> DeclaredGauge<T> {
    /// Declare a gauge by exhibiting the material before and after the transformation.
    ///
    /// **Refuses when nothing moved.** That refusal is the carrier's entire purpose: it converts
    /// *"remember to check the transformation was non-trivial"* into *"you cannot hold this value
    /// unless it was"*.
    pub fn of(before: Vec<T>, after: Vec<T>) -> Result<Self, TrivialGauge> {
        if before.is_empty() {
            return Err(TrivialGauge::NoMaterial);
        }
        if before.len() != after.len() {
            return Err(TrivialGauge::ExtentDisagrees {
                before: before.len(),
                after: after.len(),
            });
        }
        let moved: Vec<usize> = (0..before.len())
            .filter(|&at| before[at] != after[at])
            .collect();
        if moved.is_empty() {
            return Err(TrivialGauge::ActedTrivially {
                members: before.len(),
            });
        }
        Ok(Self {
            before,
            after,
            moved,
        })
    }

    /// The positions the transformation moved — **named, never counted**, so a caller can say which
    /// members carried the orbit rather than how many.
    pub fn witness(&self) -> &[usize] {
        &self.moved
    }

    pub fn before(&self) -> &[T] {
        &self.before
    }

    pub fn after(&self) -> &[T] {
        &self.after
    }

    /// Read a projection either side of the transformation and return the positions where **it**
    /// moved. An invariant projection returns empty; that emptiness is now evidence, because the
    /// gauge itself is known to have acted.
    pub fn projection_moved<U: PartialEq, F: Fn(&T) -> U>(&self, read: F) -> Vec<usize> {
        (0..self.before.len())
            .filter(|&at| read(&self.before[at]) != read(&self.after[at]))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn a_gauge_that_moved_nothing_cannot_be_declared() {
        let same = vec![1i64, 2, 3];
        assert_eq!(
            DeclaredGauge::of(same.clone(), same),
            Err(TrivialGauge::ActedTrivially { members: 3 })
        );
    }

    #[test]
    fn a_gauge_that_acted_carries_the_positions_it_moved() {
        let gauge = DeclaredGauge::of(vec![1i64, 2, 3], vec![1, 9, 3]).expect("it acted");
        assert_eq!(gauge.witness(), &[1]);
    }

    /// THE POINT OF THE CARRIER, stated as a test: an invariant projection is evidence only once the
    /// gauge is known to have acted, and both halves are exhibited at once.
    ///
    /// **The first draft of this test asserted `... .is_empty() || true`, which cannot fail — the
    /// exact defect this module exists to prevent, written inside it.** Kept in the record because
    /// the reflex is the thing being guarded against, not the individual slip.
    #[test]
    fn an_invariant_projection_is_evidence_only_because_the_gauge_acted() {
        // The transformation doubles. The SIGN survives it; the magnitude does not.
        let before = vec![1i64, -2, 3, -4];
        let after: Vec<i64> = before.iter().map(|n| n * 2).collect();
        let gauge = DeclaredGauge::of(before, after).expect("doubling acts on non-zero material");
        assert_eq!(gauge.witness(), &[0, 1, 2, 3], "every member moved");

        // the projection that SURVIVES — and this is evidence only because the line above holds
        assert!(
            gauge.projection_moved(|n| n.signum()).is_empty(),
            "the sign is invariant under a positive scaling"
        );
        // the projection that does NOT survive — the anti-vacuity arm, and it is required
        assert_eq!(
            gauge.projection_moved(|n| *n),
            vec![0, 1, 2, 3],
            "the magnitude moves, so the survival above is not vacuous"
        );
    }

    #[test]
    fn disagreeing_extents_refuse_rather_than_compare_a_prefix() {
        assert_eq!(
            DeclaredGauge::of(vec![1i64, 2], vec![1]),
            Err(TrivialGauge::ExtentDisagrees {
                before: 2,
                after: 1
            })
        );
        assert_eq!(
            DeclaredGauge::<i64>::of(Vec::new(), Vec::new()),
            Err(TrivialGauge::NoMaterial)
        );
    }
}
