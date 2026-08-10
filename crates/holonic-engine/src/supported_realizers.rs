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
//! ## The construction, and what the Gram matrix is — and is not
//!
//! Let `M` be the integer incidence of realizers against classes: `M[r][c]` counts the ways
//! realizer `r` lands in class `c`. Then over the integers:
//!
//! ```text
//!   rank(M)                    how many classes are independently reachable
//!   |C| - rank(M)              classes no realizer reaches even rationally  -- FREE obstruction
//!   invariant factors above 1  classes reached only in MULTIPLE             -- TORSION obstruction
//!   M^T M                      the GRAM matrix of the class columns
//! ```
//!
//! `M^T M` is the **Gram matrix** of the columns of `M` under the standard inner product on the
//! realizer space: entry `(c, d)` is the ordinary dot product of class `c`'s column with class `d`'s.
//! Its positive semi-definiteness is automatic — `x^T (M^T M) x = |M x|^2 >= 0` for *every* integer
//! matrix and *every* probe — so it is a property of the expression `M^T M` and not of the realizer
//! population that was fed to it. No incidence whatsoever could make it come out otherwise, which by
//! `CLAUDE.md` §8's tautology rule is exactly as much evidence as it carries: none. A test asserting
//! it was removed 2026-08-08; see `the_gram_nullity_is_the_corank_of_the_incidence`.
//!
//! **This module previously called that "§2's shape exactly — positivity of the trace form on
//! correspondences". It is not, and the correction is not cosmetic.** The trace form on
//! correspondences is *indefinite*. The Castelnuovo/Hodge-index content is that its **signature** is
//! `(1, rho - 1)` — one plus direction, everything else negative — and the Hodge--Riemann relations
//! likewise say an a-priori indefinite form becomes definite only after restriction to a primitive
//! subspace and a single Hodge type, with the sign alternating with degree. Those are signature
//! theorems whose count can come out wrong. A Gram matrix's positivity cannot, which is why reaching
//! for one was the symptom rather than the construction: it is the only positive form available to a
//! body with no inertia routine. That routine now exists at [`crate::inertia`].
//!
//! Read through it, `M^T M` does report something about `M` that can fail: its nullity is
//! `|C| - rank(M)` and its positive count is `rank(M)`. That is a joint statement about the incidence
//! and about the elimination, and it is what this module now checks.
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

/// The Gram matrix `M^T M` of an incidence's class columns.
///
/// Entry `(c, d)` is the ordinary dot product of class `c`'s column with class `d`'s, so the result
/// is symmetric and positive semi-definite **by construction**: `x^T (M^T M) x = |M x|^2`. That
/// positivity is a fact about the expression, true of every integer matrix, and therefore not a
/// finding about any realizer population — see this module's header for why the name "the positive
/// form" was withdrawn.
///
/// What the Gram matrix does carry is the geometry of the pairing. Over a field
/// `rank(M^T M) = rank(M)`, so its inertia is `(rank(M), |C| - rank(M), 0)` — a statement about `M`
/// which [`crate::inertia::inertia`] returns independently and which can be wrong.
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
    let form = smith_normal_form(&matrix, PivotRule::SmallestMagnitude);
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

/// **The placement a realizer population induces, on the conduct path.**
///
/// `CLAUDE.md` §2 states the chain this closes:
///
/// ```text
///   an ample divisor class (a supported realizer that paid)
///     -> a polarization
///     -> the Rosati involution, POSITIVE
///     -> positivity of the trace form
///     -> |alpha| = q^(1/2)          placement, as a RETURN
/// ```
///
/// and its first consequence: *"Do not build modal placement and supported lifting as two organs.
/// **Derive placement from realization.** A returned placement that no realizer paid for has
/// smuggled an absolute frame into the engine."*
///
/// **The pair was joined only inside `#[cfg(test)]` until 2026-08-10.** [`positive_form`] returned
/// `MᵀM` and [`crate::inertia::inertia`] returned its signature, and the only place the two met was
/// an `assert_eq!` in this file's test module — so the chain the project's own doctrine runs through
/// was a test assertion and not a conduct path. `blueprint/THE_ROADMAP.md` carried it as open work.
///
/// **What this returns is the split, not a verdict.** `canon/TABLET_THE_TURN.md` §2b: *"positivity is
/// not absolute… State the **split** and the **hand** separately."* `MᵀM` is positive semi-definite
/// by construction, so its inertia is `(rank, 0, nullity)` and the content is **where the rank
/// falls**: the null directions are exactly the realizer combinations that land on nothing, which is
/// the population §11's demand calls the certified remainder.
///
/// The nullity is therefore the measurement to read, and it is `columns − rank`.
pub fn induced_placement(incidence: &IntegerMatrix) -> Result<crate::inertia::Inertia, crate::inertia::InertiaError> {
    let form = positive_form(incidence);
    let symmetric = crate::inertia::SymmetricForm::from_integer_matrix(&form)?;
    Ok(crate::inertia::inertia(&symmetric))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inertia::{SymmetricForm, inertia};

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
    // the Gram matrix
    //
    // `the_form_is_positive_semi_definite_on_every_probe` stood here until 2026-08-08. It asserted
    // `x^T (M^T M) x >= 0` over seven hand-chosen probes, which is true of every integer matrix and
    // every probe: the assertion could not have come out otherwise on any input, so by `CLAUDE.md`
    // §8 it carried no evidence. The two tests below are what it is replaced with. The first checks
    // an IDENTITY rather than an inequality — it can fail, and would, if `positive_form` computed
    // `M M^T` or mis-indexed. The second reads the Gram matrix's SIGNATURE through
    // `crate::inertia`, which is a joint statement about `M` and about the elimination.

    /// `x^T (M^T M) x = |M x|^2` exactly. An identity, not an inequality: a transposed or
    /// mis-indexed `positive_form`, or a `quadratic_value` that dropped the cross terms, breaks it.
    #[test]
    fn the_form_evaluates_to_the_squared_length_of_the_image() {
        let realizations = vec![
            realization(0, &[(0, 3), (1, -2)]),
            realization(1, &[(1, 5), (2, 1)]),
            realization(2, &[(0, -7), (2, 4)]),
        ];
        let matrix = incidence(&realizations, 3);
        let form = positive_form(&matrix);

        let mut saw_asymmetric_probe = false;
        for probe in [
            [1i64, 0, 0],
            [0, 1, 0],
            [0, 0, 1],
            [1, 1, 1],
            [3, -5, 2],
            [-11, 7, -13],
            [0, 0, 0],
        ] {
            saw_asymmetric_probe |= probe.iter().any(|value| *value < 0);
            let vector: Vec<BigInt> = probe.iter().map(|value| BigInt::from(*value)).collect();
            let mut squared = BigInt::zero();
            for row in 0..matrix.rows() {
                let mut entry = BigInt::zero();
                for column in 0..matrix.columns() {
                    entry += matrix.at(row, column) * &vector[column];
                }
                squared += &entry * &entry;
            }
            assert_eq!(quadratic_value(&form, &vector), squared, "probe {probe:?}");
        }
        assert!(
            saw_asymmetric_probe,
            "unit and all-ones probes cannot separate M^T M from M M^T; a mixed-sign probe must run"
        );
    }

    /// What the Gram matrix genuinely reports about the incidence it came from.
    ///
    /// Over a field `rank(M^T M) = rank(M)`, so the inertia of `M^T M` must be exactly
    /// `(rank(M), |C| - rank(M), 0)`. The rank is taken independently, by the Smith normal form of
    /// `M` itself; the inertia is taken by an elimination that never sees `M`. Either could
    /// disagree with the other, and a rank-deficient incidence is included on purpose — a corank
    /// check run only on invertible material asserts `0 == 0` and is the tautology again.
    #[test]
    fn the_gram_nullity_is_the_corank_of_the_incidence() {
        let cases: [(Vec<Realization>, usize); 6] = [
            // full column rank: nullity zero
            (
                vec![
                    realization(0, &[(0, 3), (1, -2)]),
                    realization(1, &[(1, 5), (2, 1)]),
                    realization(2, &[(0, -7), (2, 4)]),
                ],
                3,
            ),
            // two proportional realizers over three classes: rank one, nullity two
            (
                vec![
                    realization(0, &[(0, 1), (1, 2)]),
                    realization(1, &[(0, 2), (1, 4)]),
                ],
                3,
            ),
            // two classes reached, four declared: nullity two
            (
                vec![realization(0, &[(0, 1)]), realization(1, &[(1, 1)])],
                4,
            ),
            // the torsion fixture — integrally obstructed, rationally full rank
            (
                vec![realization(0, &[(0, 2)]), realization(1, &[(1, 1)])],
                2,
            ),
            (
                vec![
                    realization(0, &[(0, 1), (1, 1)]),
                    realization(1, &[(0, 1), (1, -1)]),
                ],
                2,
            ),
            // nothing produced at all: the Gram matrix is the zero form, nullity is the whole family
            (Vec::new(), 3),
        ];

        let mut saw_degenerate = false;
        let mut saw_nondegenerate = false;
        for (realizations, class_extent) in &cases {
            let matrix = incidence(realizations, *class_extent);
            let form = positive_form(&matrix);
            let rank = smith_normal_form(&matrix, PivotRule::FirstNonzero).rank();
            let reading = inertia(
                &SymmetricForm::from_integer_matrix(&form).expect("a Gram matrix is symmetric"),
            );

            assert_eq!(
                reading.zero,
                class_extent - rank,
                "the Gram matrix's nullity must be the incidence's corank; rank {rank}, \
                 classes {class_extent}, inertia {reading:?}"
            );
            assert_eq!(
                reading.positive, rank,
                "and its positive count must be the incidence's rank; inertia {reading:?}"
            );
            // Not asserted as evidence of positivity — that is the tautology. Asserted because the
            // elimination is an independent computation that must agree with the algebra.
            assert_eq!(reading.negative, 0, "inertia {reading:?}");

            saw_degenerate |= reading.is_degenerate();
            saw_nondegenerate |= !reading.is_degenerate();
        }
        assert!(
            saw_degenerate && saw_nondegenerate,
            "the corank check saw only one side, so it never had to distinguish anything"
        );
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

    /// **The realization-to-placement chain runs on the conduct path**, not only in an assertion.
    ///
    /// `MᵀM` is positive semi-definite by construction, so the return is `(rank, 0, nullity)` and
    /// the content is where the rank falls. A realizer population with a dependency has a null
    /// direction, and that direction is the combination landing on nothing.
    #[test]
    fn induced_placement_returns_the_split_and_the_nullity_is_the_dependency() {
        // Two independent realizers over two classes: full rank, no null direction.
        let mut independent = IntegerMatrix::zeros(2, 2);
        independent.set(0, 0, BigInt::from(1));
        independent.set(1, 1, BigInt::from(1));
        let placed = induced_placement(&independent).expect("the form founds");
        assert_eq!(placed.negative, 0, "M^T M is positive semi-definite");
        assert_eq!(placed.zero, 0, "independent realizers leave no null direction");
        assert_eq!(placed.positive, 2);

        // Three realizers over two classes, the third the sum of the first two: one dependency, so
        // exactly one null direction.
        let mut dependent = IntegerMatrix::zeros(2, 3);
        dependent.set(0, 0, BigInt::from(1));
        dependent.set(1, 1, BigInt::from(1));
        dependent.set(0, 2, BigInt::from(1));
        dependent.set(1, 2, BigInt::from(1));
        let placed = induced_placement(&dependent).expect("the form founds");
        assert_eq!(placed.negative, 0);
        assert_eq!(placed.zero, 1, "the dependency is the null direction");
        assert_eq!(placed.positive, 2);
    }
}
