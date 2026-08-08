//! Whether the classes a receiver distinguishes are supported by realizers that can produce them.
//!
//! ## The question, and why it is the Hodge-facing one
//!
//! `CLAUDE.md` §3: Hodge *"asks whether a receiver-visible invariant subspace has enough supported
//! geometric realizers. The failure of the **integral** version is the framework speaking: the
//! obstruction lives in the COKERNEL of the cycle class map."* — corrected 2026-08-08. The earlier
//! form of this line said *"the obstruction is torsion"*, which a Hodge audit falsified: Kollár's
//! counterexamples are classes of INFINITE order in TORSION-FREE cohomology, where `pα` is algebraic
//! and `α` is not, and the cokernel is `ℤ/p`. Torsion *in the cokernel* is not the same as the
//! failing class being torsion.
//!
//! **`ObstructionSpecies::ReachableOnlyInMultiple { factor }` is a faithful finite model of exactly
//! that**, and it is the better half of this module: a class reached only as a multiple, with the
//! multiple exhibited. Describe it that way.
//!
//! `receiver_exact_compression` now returns the receiver-visible invariant subspace exactly — the
//! conduct classes, the distinctions no later continuation can erase. This module asks the other
//! half: **can anything the machine actually produces land in each of those classes?**
//!
//! A class the receiver can *distinguish* but no realizer can *reach* is an exhibited obstruction.
//! That is not a defect in the machine; it is the machine locating its own frontier.
//!
//! ## The construction, and why the positive form falls out rather than being installed
//!
//! Let `M` be the integer incidence of realizers against classes: `M[r][c]` counts the ways
//! realizer `r` lands in class `c`. Then over the integers:
//!
//! ```text
//!   rank(M)                    how many classes are independently reachable
//!   |C| - rank(M)              classes no realizer reaches even rationally  -- FREE obstruction
//!   invariant factors above 1  classes reached only in MULTIPLE             -- TORSION obstruction
//!   M^T M                      the positive form
//! ```
//!
//! `M^T M` is positive semi-definite for free, because `x^T (M^T M) x = |M x|^2`. Nothing installs
//! positivity; it is a property of the pairing between realizers and what they realize. That is
//! §2's shape exactly — *"positivity of the trace form on correspondences"*, supplied by
//! supportedness rather than obtained beside it — at the altitude this machine can compute.
//!
//! **The torsion column is the whole point.** A class reached only as `2·c` and never as `c` is
//! supported over the rationals and unsupported over the integers, and the cokernel records a
//! `Z/2`. That is the integral-versus-rational split the Hodge conjecture fails on, computed here
//! in exact integers with the same Smith normal form that reads a grown circuit's homology.
//!
//! ## What is not claimed
//!
//! This is a construction-selection instrument, not a result. It decides support for a **declared**
//! finite realizer population against a **declared** finite class family. Nothing here bears on the
//! Hodge conjecture, and per `CLAUDE.md` §3 a deed may be graded by movement on named substructure
//! without claiming the conjecture.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};

use crate::rebase_invariants::{smith_normal_form, IntegerMatrix, PivotRule};
use crate::receiver_exact_compression::ItemId;

/// One thing the machine can actually produce.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct RealizerId(pub u64);

/// A realizer and the classes its production lands in, with multiplicity.
///
/// Multiplicity is why the integral question differs from the rational one. A realizer that only
/// ever reaches a class twice over supports it rationally and not integrally.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Realization {
    pub realizer: RealizerId,
    pub landings: BTreeMap<usize, BigInt>,
}

/// A class the receiver distinguishes but no realizer reaches, or reaches only in multiple.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SupportObstruction {
    /// The classes involved. A free obstruction names the whole unreached population because the
    /// cokernel's free part is not canonically attached to one class.
    pub classes: Vec<usize>,
    pub species: ObstructionSpecies,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ObstructionSpecies {
    /// No combination of realizers reaches these, even with rational coefficients.
    Unreachable { free_rank: usize },
    /// Reachable rationally, but only as a multiple. The winding that cannot be un-deposited.
    ReachableOnlyInMultiple { factor: BigInt },
}

/// What the support question returns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RealizerSupport {
    pub schema: String,
    pub realizer_extent: usize,
    pub class_extent: usize,
    /// `rank(M)` — independently reachable classes.
    pub supported_rank: usize,
    /// The invariant factors of `M`. The artifact, not a count.
    pub invariant_factors: Vec<BigInt>,
    pub obstructions: Vec<SupportObstruction>,
}

impl RealizerSupport {
    /// Every class the receiver distinguishes is reached, integrally.
    ///
    /// **A class family of zero is not a discharge.** Collapsing the family to nothing left this
    /// returning `true` — a total success with no realizers and nothing to support — which would
    /// have made "distinguish less" the cheapest way to satisfy any support demand.
    pub fn fully_supported(&self) -> bool {
        self.class_extent > 0 && self.obstructions.is_empty()
    }

    /// Classes unreachable even with rational coefficients.
    pub fn free_obstruction(&self) -> usize {
        self.class_extent.saturating_sub(self.supported_rank)
    }

    /// Classes reachable rationally and not integrally — the integral-versus-rational split.
    pub fn torsion_obstruction(&self) -> Vec<BigInt> {
        self.invariant_factors
            .iter()
            .filter(|factor| **factor > BigInt::one())
            .cloned()
            .collect()
    }
}

/// The realizer-against-class incidence, over exact integers.
pub fn incidence(realizations: &[Realization], class_extent: usize) -> IntegerMatrix {
    let mut matrix = IntegerMatrix::zeros(realizations.len(), class_extent);
    for (row, realization) in realizations.iter().enumerate() {
        for (class, multiplicity) in &realization.landings {
            if *class < class_extent {
                matrix.set(row, *class, multiplicity.clone());
            }
        }
    }
    matrix
}

/// The positive form `M^T M`.
///
/// Positive semi-definite by construction, since `x^T (M^T M) x = |M x|^2`. It is computed rather
/// than assumed so that `the_form_is_positive_semi_definite_on_every_probe` has something to check.
pub fn positive_form(incidence: &IntegerMatrix) -> IntegerMatrix {
    let mut form = IntegerMatrix::zeros(incidence.columns(), incidence.columns());
    for left in 0..incidence.columns() {
        for right in 0..incidence.columns() {
            let mut total = BigInt::zero();
            for row in 0..incidence.rows() {
                total += incidence.at(row, left) * incidence.at(row, right);
            }
            form.set(left, right, total);
        }
    }
    form
}

/// Evaluate `x^T A x` exactly.
pub fn quadratic_value(form: &IntegerMatrix, probe: &[BigInt]) -> BigInt {
    let mut total = BigInt::zero();
    for left in 0..form.rows().min(probe.len()) {
        for right in 0..form.columns().min(probe.len()) {
            total += &probe[left] * form.at(left, right) * &probe[right];
        }
    }
    total
}

/// Decide support for a declared realizer population against a declared class family.
pub fn decide_support(realizations: &[Realization], class_extent: usize) -> RealizerSupport {
    let matrix = incidence(realizations, class_extent);
    let form = smith_normal_form(&matrix, PivotRule::FirstNonzero);
    let supported_rank = form.rank();

    let mut obstructions = Vec::new();
    let free_rank = class_extent.saturating_sub(supported_rank);
    if free_rank > 0 {
        // The cokernel's free part is not canonically attached to particular classes, so the whole
        // unreached population is named rather than an arbitrary representative chosen.
        let reached: BTreeSet<usize> = realizations
            .iter()
            .flat_map(|realization| realization.landings.keys().copied())
            .collect();
        obstructions.push(SupportObstruction {
            classes: (0..class_extent)
                .filter(|class| !reached.contains(class))
                .collect(),
            species: ObstructionSpecies::Unreachable { free_rank },
        });
    }
    for factor in form.factors.iter().filter(|factor| **factor > BigInt::one()) {
        obstructions.push(SupportObstruction {
            classes: Vec::new(),
            species: ObstructionSpecies::ReachableOnlyInMultiple {
                factor: factor.clone(),
            },
        });
    }

    RealizerSupport {
        schema: "holonic-engine.supported-realizers.v1".to_owned(),
        realizer_extent: realizations.len(),
        class_extent,
        supported_rank,
        invariant_factors: form.factors,
        obstructions,
    }
}

/// Build realizations by asking, for each realizer, which class its production lands in.
///
/// `classify` returns `None` when a realizer produces nothing the class family recognizes — which
/// is a legitimate return and not an error. A realizer that reaches nothing supports nothing.
pub fn realize<R>(
    realizers: impl IntoIterator<Item = RealizerId>,
    mut classify: impl FnMut(RealizerId) -> R,
) -> Vec<Realization>
where
    R: IntoIterator<Item = (usize, BigInt)>,
{
    realizers
        .into_iter()
        .map(|realizer| Realization {
            realizer,
            landings: classify(realizer).into_iter().collect(),
        })
        .collect()
}

/// Convenience: an item-indexed class assignment, the shape `receiver_exact_compression` returns.
pub fn landings_from_classes(
    produced: impl IntoIterator<Item = ItemId>,
    class_of: impl Fn(ItemId) -> Option<usize>,
) -> BTreeMap<usize, BigInt> {
    let mut landings: BTreeMap<usize, BigInt> = BTreeMap::new();
    for item in produced {
        if let Some(class) = class_of(item) {
            *landings.entry(class).or_insert_with(BigInt::zero) += BigInt::one();
        }
    }
    landings
}

#[cfg(test)]
mod tests {
    use super::*;

    fn realization(realizer: u64, landings: &[(usize, i64)]) -> Realization {
        Realization {
            realizer: RealizerId(realizer),
            landings: landings
                .iter()
                .map(|(class, count)| (*class, BigInt::from(*count)))
                .collect(),
        }
    }

    // -----------------------------------------------------------------------------------------
    // the three species

    #[test]
    fn realizers_that_reach_every_class_singly_leave_no_obstruction() {
        let realizations = vec![
            realization(0, &[(0, 1)]),
            realization(1, &[(1, 1)]),
            realization(2, &[(2, 1)]),
        ];
        let support = decide_support(&realizations, 3);
        assert!(support.fully_supported(), "{:?}", support.obstructions);
        assert_eq!(support.supported_rank, 3);
        assert_eq!(support.free_obstruction(), 0);
        assert!(support.torsion_obstruction().is_empty());
    }

    /// A class nothing reaches. The receiver distinguishes it; no realizer produces it.
    #[test]
    fn a_class_no_realizer_reaches_is_an_exhibited_free_obstruction() {
        let realizations = vec![realization(0, &[(0, 1)]), realization(1, &[(1, 1)])];
        let support = decide_support(&realizations, 4);
        assert!(!support.fully_supported());
        assert_eq!(support.supported_rank, 2);
        assert_eq!(support.free_obstruction(), 2);
        let unreached = support
            .obstructions
            .iter()
            .find_map(|obstruction| match &obstruction.species {
                ObstructionSpecies::Unreachable { .. } => Some(&obstruction.classes),
                _ => None,
            })
            .expect("the unreached classes are named, not merely counted");
        assert_eq!(*unreached, vec![2, 3]);
    }

    /// The case the module exists for. Every class is reachable rationally; class 0 is reachable
    /// only as `2·c`, so it is supported over the rationals and **not** over the integers.
    #[test]
    fn a_class_reached_only_in_multiple_is_supported_rationally_and_not_integrally() {
        let realizations = vec![realization(0, &[(0, 2)]), realization(1, &[(1, 1)])];
        let support = decide_support(&realizations, 2);

        assert_eq!(
            support.supported_rank, 2,
            "rationally the realizers span both classes"
        );
        assert_eq!(
            support.free_obstruction(),
            0,
            "so there is no free obstruction at all"
        );
        assert_eq!(
            support.torsion_obstruction(),
            vec![BigInt::from(2)],
            "integrally, class 0 is reached only doubled — a Z/2 in the cokernel"
        );
        assert!(
            !support.fully_supported(),
            "rational sufficiency is not integral sufficiency, and that gap is the whole point"
        );
    }

    #[test]
    fn the_two_obstruction_species_are_separable_in_one_reading() {
        // class 0 doubled, class 1 singly, class 2 unreached.
        let realizations = vec![realization(0, &[(0, 2)]), realization(1, &[(1, 1)])];
        let support = decide_support(&realizations, 3);
        assert_eq!(support.free_obstruction(), 1);
        assert_eq!(support.torsion_obstruction(), vec![BigInt::from(2)]);
        let species: Vec<bool> = support
            .obstructions
            .iter()
            .map(|obstruction| {
                matches!(obstruction.species, ObstructionSpecies::Unreachable { .. })
            })
            .collect();
        assert!(species.contains(&true) && species.contains(&false));
    }

    // -----------------------------------------------------------------------------------------
    // the positive form

    /// `x^T (M^T M) x = |M x|^2 >= 0` for every integer probe. Nothing installs this; it is a
    /// property of the pairing. If it ever failed, the form would not be the one §2 asks for.
    #[test]
    fn the_form_is_positive_semi_definite_on_every_probe() {
        let realizations = vec![
            realization(0, &[(0, 3), (1, -2)]),
            realization(1, &[(1, 5), (2, 1)]),
            realization(2, &[(0, -7), (2, 4)]),
        ];
        let matrix = incidence(&realizations, 3);
        let form = positive_form(&matrix);

        for probe in [
            [1i64, 0, 0],
            [0, 1, 0],
            [0, 0, 1],
            [1, 1, 1],
            [3, -5, 2],
            [-11, 7, -13],
            [0, 0, 0],
        ] {
            let vector: Vec<BigInt> = probe.iter().map(|value| BigInt::from(*value)).collect();
            let value = quadratic_value(&form, &vector);
            assert!(
                value >= BigInt::zero(),
                "the form returned {value} on probe {probe:?}; a positive form cannot"
            );
            // And it equals |M x|^2 exactly, which is the reason it is positive.
            let mut squared = BigInt::zero();
            for row in 0..matrix.rows() {
                let mut entry = BigInt::zero();
                for column in 0..matrix.columns() {
                    entry += matrix.at(row, column) * &vector[column];
                }
                squared += &entry * &entry;
            }
            assert_eq!(value, squared, "probe {probe:?}");
        }
    }

    #[test]
    fn the_form_is_symmetric() {
        let realizations = vec![
            realization(0, &[(0, 2), (1, -3)]),
            realization(1, &[(1, 5), (2, 7)]),
        ];
        let form = positive_form(&incidence(&realizations, 3));
        for left in 0..form.rows() {
            for right in 0..form.columns() {
                assert_eq!(form.at(left, right), form.at(right, left));
            }
        }
    }

    /// The form's rank must agree with the incidence's. If it did not, `M^T M` would be measuring
    /// something other than the span of the realizers.
    #[test]
    fn the_form_has_the_same_rank_as_the_incidence_it_came_from() {
        for realizations in [
            vec![realization(0, &[(0, 1)]), realization(1, &[(1, 1)])],
            vec![realization(0, &[(0, 2), (1, 4)]), realization(1, &[(0, 1), (1, 2)])],
            vec![realization(0, &[(0, 6)]), realization(1, &[(0, 10)])],
            vec![realization(0, &[(0, 1), (1, 1)]), realization(1, &[(0, 1), (1, -1)])],
        ] {
            let matrix = incidence(&realizations, 2);
            let form = positive_form(&matrix);
            assert_eq!(
                smith_normal_form(&matrix, PivotRule::FirstNonzero).rank(),
                smith_normal_form(&form, PivotRule::FirstNonzero).rank(),
                "M and M^T M must have equal rank"
            );
        }
    }

    // -----------------------------------------------------------------------------------------
    // controls

    /// An empty realizer population supports nothing, and says so rather than returning a
    /// vacuously clean reading.
    #[test]
    fn nothing_produced_supports_nothing() {
        let support = decide_support(&[], 3);
        assert!(!support.fully_supported());
        assert_eq!(support.supported_rank, 0);
        assert_eq!(support.free_obstruction(), 3);
    }

    #[test]
    fn an_empty_class_family_is_not_a_discharge() {
        let support = decide_support(&[], 0);
        assert!(
            !support.fully_supported(),
            "nothing to support is not the same as everything supported"
        );
        let with_realizers = decide_support(&[realization(0, &[(0, 1)])], 0);
        assert!(
            !with_realizers.fully_supported(),
            "and it stays false however many realizers were declared"
        );
    }

    /// A realizer that produces nothing the class family recognizes contributes no support, and
    /// must not be counted as if it had.
    #[test]
    fn a_realizer_that_lands_nowhere_adds_no_support() {
        let with_ghost = vec![
            realization(0, &[(0, 1)]),
            realization(1, &[]),
            realization(2, &[(1, 1)]),
        ];
        let without = vec![realization(0, &[(0, 1)]), realization(2, &[(1, 1)])];
        let a = decide_support(&with_ghost, 2);
        let b = decide_support(&without, 2);
        assert_eq!(a.supported_rank, b.supported_rank);
        assert_eq!(a.invariant_factors, b.invariant_factors);
        assert_ne!(a.realizer_extent, b.realizer_extent, "the ghost is still counted as present");
    }

    /// Adding realizers may only increase support. If it ever decreased, the incidence would not
    /// be a span.
    #[test]
    fn adding_a_realizer_never_reduces_support() {
        let base = vec![realization(0, &[(0, 2)])];
        let base_support = decide_support(&base, 3);
        for extra in [
            realization(1, &[(0, 1)]),
            realization(1, &[(1, 1)]),
            realization(1, &[(2, 5)]),
            realization(1, &[(0, 1), (1, 1), (2, 1)]),
        ] {
            let mut grown = base.clone();
            grown.push(extra);
            let grown_support = decide_support(&grown, 3);
            assert!(
                grown_support.supported_rank >= base_support.supported_rank,
                "adding a realizer reduced rank {} -> {}",
                base_support.supported_rank,
                grown_support.supported_rank
            );
        }
    }

    /// And adding the right realizer *dissolves* torsion — the doubled class becomes integrally
    /// reachable once something reaches it singly. Without this the torsion column could be an
    /// artifact of the reduction rather than a statement about support.
    #[test]
    fn a_single_reaching_realizer_dissolves_the_doubled_obstruction() {
        let doubled = vec![realization(0, &[(0, 2)])];
        assert_eq!(
            decide_support(&doubled, 1).torsion_obstruction(),
            vec![BigInt::from(2)]
        );

        let mut repaired = doubled;
        repaired.push(realization(1, &[(0, 1)]));
        let support = decide_support(&repaired, 1);
        assert!(
            support.torsion_obstruction().is_empty(),
            "reaching the class singly must remove the Z/2, not merely add to it"
        );
        assert!(support.fully_supported());
    }
}
