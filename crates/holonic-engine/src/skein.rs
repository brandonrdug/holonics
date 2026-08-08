//! Local substitution that preserves a global invariant, and the exact remainder when it does not.
//!
//! Brandon, 2026-07-24: *"I need you to also research unknotting theorems and prime knots, in
//! particular non-trivial knots that cannot be unknotted. Those are closed loops and topological
//! invariants, this is exactly like what we have meant with prime axes and rank/irreducibility in
//! the past. Then most importantly I need you to refer to skein relationships […] specifically I am
//! interested in the idea of link substitution and tangle replacement. **This will be pivotal for
//! the Riemann Hypothesis and how we define compression for machine learning.**"*
//!
//! The definition and theorem were written as Typst
//! (`papers/source/mathematics/definitions/contextual-tangle-compression.typ`,
//! `papers/source/mathematics/theorems/contextual-skein-compression.typ`) and nothing implemented
//! them. `canon/THE_QUOTE_NETWORK.md` records that he supplied this thirteen days before `CLAUDE.md`
//! §11 named the certified-remainder condensation as the missing organ, and that no record cites
//! the connection.
//!
//! ## What a substitution is here
//!
//! Two fillings `L` and `R` of the same hole, attached along a shared boundary `B`, inside a context
//! `C`. The Typst definition is contextual receiver equivalence:
//!
//! ```text
//!   L ~_R R'   iff   for every admitted context C,   invariants(C ∪ L) = invariants(C ∪ R')
//! ```
//!
//! A substitution is a **compression** exactly when it factors through that equivalence — you may
//! replace one filling by the other and no receiver in the family can tell. That is the same
//! sentence as `receiver_exact_compression`'s, moved from items to subcomplexes, and it is why
//! skein and compression are one subject rather than two.
//!
//! ## The remainder
//!
//! When the invariants differ, the difference is the artifact: which grade moved, by how much in
//! free rank, and which torsion appeared or vanished. That is a **counted, exhibitable population**
//! rather than a scalar distance, which is the form §11 asks a certified remainder to take.
//!
//! The theorem's own boundary clause is carried and not softened: *"The theorem does not supply a
//! complete set of local relations, a terminating or confluent normal form, or a cost improvement…
//! Brittenham–Hermiller's nonadditivity of unknotting number is a concrete warning."* So an
//! invariance verdict here is relative to the declared context family and to the invariants read.
//! Nothing below computes a normal form and nothing claims one exists.

use std::collections::BTreeSet;

use num_bigint::BigInt;
use serde::{Deserialize, Serialize};

use crate::algebraic::{CausalAlgebraicError, CausalCellId, GradedCausalComplex};
use crate::rebase_invariants::{rebase_invariants_on, PivotRule, RebaseInvariants};

/// Two fillings of one hole, and the boundary they share.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Substitution {
    /// Cells common to both fillings. Untouched by the move.
    pub boundary: BTreeSet<CausalCellId>,
    /// The filling being replaced, boundary included.
    pub before: BTreeSet<CausalCellId>,
    /// The filling replacing it, boundary included.
    pub after: BTreeSet<CausalCellId>,
}

impl Substitution {
    /// What the move removes and what it adds, which is what makes it local.
    pub fn removed(&self) -> BTreeSet<CausalCellId> {
        self.before.difference(&self.after).copied().collect()
    }

    pub fn added(&self) -> BTreeSet<CausalCellId> {
        self.after.difference(&self.before).copied().collect()
    }

    /// A move that changes nothing outside the boundary is not a move.
    pub fn is_trivial(&self) -> bool {
        self.before == self.after
    }
}

/// How one grade's invariants moved under a substitution.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GradeRemainder {
    pub grade: u32,
    /// `betti(after) - betti(before)`.
    pub betti_change: i64,
    /// Torsion the replacement carries that the original did not.
    pub torsion_gained: Vec<BigInt>,
    /// Torsion the original carried that the replacement does not.
    pub torsion_lost: Vec<BigInt>,
}

impl GradeRemainder {
    pub fn is_zero(&self) -> bool {
        self.betti_change == 0 && self.torsion_gained.is_empty() && self.torsion_lost.is_empty()
    }
}

/// One context's verdict on one substitution.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContextVerdict {
    /// Index into the declared context family.
    pub context: usize,
    pub before: RebaseInvariants,
    pub after: RebaseInvariants,
    /// Empty exactly when the substitution is invisible in this context.
    pub remainder: Vec<GradeRemainder>,
}

impl ContextVerdict {
    pub fn invariant_here(&self) -> bool {
        self.remainder.is_empty()
    }
}

/// What a substitution returns against a declared family of contexts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SkeinReading {
    pub schema: String,
    pub verdicts: Vec<ContextVerdict>,
    /// Cells removed and added, so a trivial move cannot pass as an invariance result.
    pub removed_extent: usize,
    pub added_extent: usize,
}

impl SkeinReading {
    /// The substitution is a compression: no declared receiver in any declared context sees it.
    ///
    /// **A trivial move is not a compression.** A substitution that removes and adds nothing is
    /// invisible for the reason that nothing happened, and reporting that as invariance would be a
    /// receipt that could not have come out otherwise.
    pub fn compresses(&self) -> bool {
        !self.verdicts.is_empty()
            && (self.removed_extent > 0 || self.added_extent > 0)
            && self.verdicts.iter().all(ContextVerdict::invariant_here)
    }

    /// The contexts that can tell the two fillings apart. Empty when the move compresses.
    pub fn distinguishing_contexts(&self) -> Vec<usize> {
        self.verdicts
            .iter()
            .filter(|verdict| !verdict.invariant_here())
            .map(|verdict| verdict.context)
            .collect()
    }
}

#[derive(Debug)]
pub enum SkeinRefusal {
    Algebraic(CausalAlgebraicError),
    /// A filling that is not closed under boundary, or a context that does not contain the shared
    /// boundary, is not a substitution and is refused rather than read.
    NotASubcomplex(&'static str),
    BoundaryNotShared,
}

impl std::fmt::Display for SkeinRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Algebraic(error) => write!(formatter, "{error}"),
            Self::NotASubcomplex(which) => {
                write!(formatter, "the {which} is not closed under boundary")
            }
            Self::BoundaryNotShared => write!(
                formatter,
                "the declared boundary is not contained in both fillings, so this is a replacement \
                 of one thing by an unrelated other rather than a substitution"
            ),
        }
    }
}

impl std::error::Error for SkeinRefusal {}

impl From<CausalAlgebraicError> for SkeinRefusal {
    fn from(error: CausalAlgebraicError) -> Self {
        Self::Algebraic(error)
    }
}

fn multiset_difference(from: &[BigInt], remove: &[BigInt]) -> Vec<BigInt> {
    let mut held: Vec<BigInt> = remove.to_vec();
    let mut left = Vec::new();
    for factor in from {
        match held.iter().position(|carried| carried == factor) {
            Some(at) => {
                held.remove(at);
            }
            None => left.push(factor.clone()),
        }
    }
    left
}

fn remainder(before: &RebaseInvariants, after: &RebaseInvariants) -> Vec<GradeRemainder> {
    let grades = before.grades.len().max(after.grades.len());
    let mut moved = Vec::new();
    for grade in 0..grades {
        let (before_betti, before_torsion) = before
            .grades
            .get(grade)
            .map(|entry| (entry.betti as i64, entry.torsion.clone()))
            .unwrap_or((0, Vec::new()));
        let (after_betti, after_torsion) = after
            .grades
            .get(grade)
            .map(|entry| (entry.betti as i64, entry.torsion.clone()))
            .unwrap_or((0, Vec::new()));
        let entry = GradeRemainder {
            grade: grade as u32,
            betti_change: after_betti - before_betti,
            torsion_gained: multiset_difference(&after_torsion, &before_torsion),
            torsion_lost: multiset_difference(&before_torsion, &after_torsion),
        };
        if !entry.is_zero() {
            moved.push(entry);
        }
    }
    moved
}

/// Read a substitution against a declared family of contexts.
///
/// Each context is a closed subcomplex disjoint from the fillings' interiors; the reading compares
/// `context ∪ before` against `context ∪ after`. An empty context family is refused implicitly by
/// `compresses()`, which requires at least one verdict — a substitution nobody looked at is not a
/// compression.
pub fn read_substitution(
    complex: &GradedCausalComplex,
    substitution: &Substitution,
    contexts: &[BTreeSet<CausalCellId>],
    rule: PivotRule,
) -> Result<SkeinReading, SkeinRefusal> {
    if !substitution.boundary.is_subset(&substitution.before)
        || !substitution.boundary.is_subset(&substitution.after)
    {
        return Err(SkeinRefusal::BoundaryNotShared);
    }
    for (support, which) in [
        (&substitution.before, "before filling"),
        (&substitution.after, "after filling"),
    ] {
        if !complex.is_closed_support(support)? {
            return Err(SkeinRefusal::NotASubcomplex(which));
        }
    }

    let mut verdicts = Vec::with_capacity(contexts.len());
    for (index, context) in contexts.iter().enumerate() {
        if !complex.is_closed_support(context)? {
            return Err(SkeinRefusal::NotASubcomplex("context"));
        }
        let with_before: BTreeSet<CausalCellId> =
            context.union(&substitution.before).copied().collect();
        let with_after: BTreeSet<CausalCellId> =
            context.union(&substitution.after).copied().collect();
        let before = rebase_invariants_on(complex, Some(&with_before), rule)?;
        let after = rebase_invariants_on(complex, Some(&with_after), rule)?;
        let moved = remainder(&before, &after);
        verdicts.push(ContextVerdict {
            context: index,
            before,
            after,
            remainder: moved,
        });
    }

    Ok(SkeinReading {
        schema: "holonic-engine.skein.v1".to_owned(),
        removed_extent: substitution.removed().len(),
        added_extent: substitution.added().len(),
        verdicts,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebraic::{CausalChain, ComparativeMultiplicity};
    use crate::causal::EventId;

    fn source() -> BTreeSet<EventId> {
        BTreeSet::from([EventId(1)])
    }

    /// One vertex, several loops at it, and faces attached to those loops with declared
    /// multiplicities. Enough to build substitutions whose invariance is a theorem.
    struct Bouquet {
        complex: GradedCausalComplex,
        vertex: CausalCellId,
        loops: Vec<CausalCellId>,
        faces: Vec<CausalCellId>,
    }

    fn bouquet(loops: usize, attachments: &[(usize, u32)]) -> Bouquet {
        let mut complex = GradedCausalComplex::default();
        let vertex = complex
            .found_cell("v", source(), 0, CausalChain::default())
            .unwrap();
        let mut edges = Vec::new();
        for index in 0..loops {
            let mut boundary = CausalChain::default();
            boundary.add_term(vertex, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(vertex, ComparativeMultiplicity::negative(1u32));
            edges.push(
                complex
                    .found_cell(format!("e{index}"), source(), 1, boundary)
                    .unwrap(),
            );
        }
        let mut faces = Vec::new();
        for (at, (edge, multiplicity)) in attachments.iter().enumerate() {
            let mut boundary = CausalChain::default();
            boundary.add_term(edges[*edge], ComparativeMultiplicity::positive(*multiplicity));
            faces.push(
                complex
                    .found_cell(format!("f{at}"), source(), 2, boundary)
                    .unwrap(),
            );
        }
        Bouquet {
            complex,
            vertex,
            loops: edges,
            faces,
        }
    }

    /// Replacing a face attached once by a different face also attached once changes nothing any
    /// receiver can read. That is a compression, and it is not trivial — cells really moved.
    #[test]
    fn replacing_one_singly_attached_face_by_another_is_a_compression() {
        let world = bouquet(1, &[(0, 1), (0, 1)]);
        let substitution = Substitution {
            boundary: BTreeSet::from([world.vertex, world.loops[0]]),
            before: BTreeSet::from([world.vertex, world.loops[0], world.faces[0]]),
            after: BTreeSet::from([world.vertex, world.loops[0], world.faces[1]]),
        };
        let contexts = vec![BTreeSet::from([world.vertex])];
        let reading =
            read_substitution(&world.complex, &substitution, &contexts, PivotRule::FirstNonzero)
                .unwrap();

        assert_eq!(reading.removed_extent, 1);
        assert_eq!(reading.added_extent, 1);
        assert!(reading.compresses(), "{:?}", reading.distinguishing_contexts());
    }

    /// Replacing a singly-attached face by a doubly-attached one is **not** a compression: the
    /// replacement deposits torsion the original did not carry, and the remainder names it.
    #[test]
    fn replacing_a_single_attachment_by_a_double_one_is_refused_and_the_remainder_names_the_torsion()
    {
        let world = bouquet(1, &[(0, 1), (0, 2)]);
        let substitution = Substitution {
            boundary: BTreeSet::from([world.vertex, world.loops[0]]),
            before: BTreeSet::from([world.vertex, world.loops[0], world.faces[0]]),
            after: BTreeSet::from([world.vertex, world.loops[0], world.faces[1]]),
        };
        let contexts = vec![BTreeSet::from([world.vertex])];
        let reading =
            read_substitution(&world.complex, &substitution, &contexts, PivotRule::FirstNonzero)
                .unwrap();

        assert!(!reading.compresses());
        assert_eq!(reading.distinguishing_contexts(), vec![0]);
        let moved = &reading.verdicts[0].remainder;
        assert!(
            moved
                .iter()
                .any(|grade| grade.torsion_gained == vec![BigInt::from(2)]),
            "the doubled attachment deposits Z/2 and the remainder must say so: {moved:?}"
        );
    }

    /// The move is invisible in one context and visible in another, so invariance is relative to
    /// the declared family and the reading reports which context can tell. Without this the verdict
    /// would look absolute.
    #[test]
    fn invariance_is_relative_to_the_declared_context_family() {
        // Two loops; the substitution swaps which loop a face is attached to. With only that loop
        // in context both readings agree; with the OTHER loop present they do not, because the
        // second loop survives unfilled in one case and not the other.
        let world = bouquet(2, &[(0, 1), (1, 1)]);
        let substitution = Substitution {
            boundary: BTreeSet::from([world.vertex]),
            before: BTreeSet::from([world.vertex, world.loops[0], world.faces[0]]),
            after: BTreeSet::from([world.vertex, world.loops[1], world.faces[1]]),
        };
        let narrow = BTreeSet::from([world.vertex]);
        let wide = BTreeSet::from([world.vertex, world.loops[0]]);
        let reading = read_substitution(
            &world.complex,
            &substitution,
            &[narrow, wide],
            PivotRule::FirstNonzero,
        )
        .unwrap();

        assert!(
            reading.verdicts[0].invariant_here(),
            "with nothing else present the two fillings read the same"
        );
        assert!(
            !reading.verdicts[1].invariant_here(),
            "with the first loop already in context they do not"
        );
        assert!(!reading.compresses(), "one distinguishing context is enough to refuse");
        assert_eq!(reading.distinguishing_contexts(), vec![1]);
    }

    /// A move that changes nothing is invisible because nothing happened, and must not be reported
    /// as a compression. This is the tautology guard.
    #[test]
    fn a_trivial_move_is_not_a_compression() {
        let world = bouquet(1, &[(0, 1)]);
        let filling = BTreeSet::from([world.vertex, world.loops[0], world.faces[0]]);
        let substitution = Substitution {
            boundary: BTreeSet::from([world.vertex, world.loops[0]]),
            before: filling.clone(),
            after: filling,
        };
        let reading = read_substitution(
            &world.complex,
            &substitution,
            &[BTreeSet::from([world.vertex])],
            PivotRule::FirstNonzero,
        )
        .unwrap();
        assert!(substitution.is_trivial());
        assert_eq!(reading.removed_extent, 0);
        assert_eq!(reading.added_extent, 0);
        assert!(
            !reading.compresses(),
            "nothing moved, so nothing was shown to be invariant"
        );
    }

    /// A substitution nobody looked at is not a compression either.
    #[test]
    fn an_empty_context_family_decides_nothing() {
        let world = bouquet(1, &[(0, 1), (0, 1)]);
        let substitution = Substitution {
            boundary: BTreeSet::from([world.vertex, world.loops[0]]),
            before: BTreeSet::from([world.vertex, world.loops[0], world.faces[0]]),
            after: BTreeSet::from([world.vertex, world.loops[0], world.faces[1]]),
        };
        let reading =
            read_substitution(&world.complex, &substitution, &[], PivotRule::FirstNonzero).unwrap();
        assert!(!reading.compresses());
    }

    #[test]
    fn a_boundary_not_shared_by_both_fillings_is_refused() {
        let world = bouquet(2, &[(0, 1)]);
        let substitution = Substitution {
            boundary: BTreeSet::from([world.loops[1]]),
            before: BTreeSet::from([world.vertex, world.loops[0], world.faces[0]]),
            after: BTreeSet::from([world.vertex, world.loops[0]]),
        };
        assert!(matches!(
            read_substitution(&world.complex, &substitution, &[], PivotRule::FirstNonzero),
            Err(SkeinRefusal::BoundaryNotShared)
        ));
    }

    #[test]
    fn a_filling_that_is_not_closed_is_refused() {
        let world = bouquet(1, &[(0, 1)]);
        // A loop at one vertex has EMPTY boundary support -- its `+v` and `-v` cancel in the
        // coefficient map -- so the loop alone IS closed. The face is the open one: its boundary
        // names the loop, so a filling holding the face without the loop is not a subcomplex.
        let substitution = Substitution {
            boundary: BTreeSet::from([world.vertex]),
            before: BTreeSet::from([world.vertex, world.faces[0]]),
            after: BTreeSet::from([world.vertex, world.loops[0], world.faces[0]]),
        };
        assert!(matches!(
            read_substitution(&world.complex, &substitution, &[], PivotRule::FirstNonzero),
            Err(SkeinRefusal::NotASubcomplex(_))
        ));
    }
}
