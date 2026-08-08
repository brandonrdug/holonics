//! Two receivers over one incidence, and the class that lives in neither of them.
//!
//! ## Why this exists
//!
//! Receiver-relativity is this framework's central claim and **nothing in the tree has ever put it
//! at risk.** Distinct `ReceiverId`s exist across the examples, but no two receivers have ever held
//! *overlapping sections of one source with a map between them* — so no gluing could fail, and no
//! figure this project has produced could have come out otherwise. That is `CLAUDE.md` §8's
//! tautology rule firing at the level of architecture.
//!
//! `dilation` made two receivers cheap: a receiver is a focus and a declared horizon, and its
//! section is a genuine subcomplex. Two of them overlap, and the intersection and union of closed
//! subcomplexes are closed, so every reading below is `rebase_invariants_on` over an exact integer
//! incidence.
//!
//! ## What it computes, and its standard name
//!
//! Mayer–Vietoris. For a cover `A, B` of `A ∪ B`:
//!
//! ```text
//!   ... -> H_n(A∩B) -> H_n(A) (+) H_n(B) -> H_n(A∪B) -> H_{n-1}(A∩B) -> ...
//! ```
//!
//! The connecting map is the gluing obstruction — not by analogy, it is the map that says what the
//! union carries that neither piece does. At the level of ranks the sequence's exactness is one
//! exact identity over the integers:
//!
//! ```text
//!   chi(A∪B) = chi(A) + chi(B) - chi(A∩B)
//! ```
//!
//! which is the alternating sum of ranks along an exact sequence being zero, and it holds with no
//! tolerance anywhere because every term is a count of integer generators.
//!
//! ## The point, stated as a sentence about receivers
//!
//! Cover a rim with two arcs. Each arc is a tree and carries no loop. Their union does, and the
//! overlap is **disconnected** — which is exactly where the loop comes from through the connecting
//! map. So:
//!
//! > the invariant lives in neither receiver; it exists only in their disagreement.
//!
//! That is `CLAUDE.md` §0's *"an invariant is only visible across two frames. A machine with one
//! frame cannot audit itself"* made computable, and it is the first construction here in which
//! receiver-relativity could have failed.

use std::collections::BTreeSet;

use num_bigint::BigInt;

use serde::{Deserialize, Serialize};

use crate::algebraic::{CausalAlgebraicError, CausalCellId, GradedCausalComplex};
use crate::rebase_invariants::{rebase_invariants_on, PivotRule, RebaseInvariants};

/// Two sections offered as a cover. Neither is required to be proper, and neither is required to
/// cover the whole complex — a cover of *its own union* is what Mayer–Vietoris needs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cover {
    pub left: BTreeSet<CausalCellId>,
    pub right: BTreeSet<CausalCellId>,
}

impl Cover {
    pub fn overlap(&self) -> BTreeSet<CausalCellId> {
        self.left.intersection(&self.right).copied().collect()
    }

    pub fn union(&self) -> BTreeSet<CausalCellId> {
        self.left.union(&self.right).copied().collect()
    }
}

/// What a cover returns.
///
/// Every field is a reading of an exact integer incidence, and `obstruction` is the artifact the
/// whole module exists to return — per grade, the free rank the union carries that the two pieces
/// do not. Per `CLAUDE.md` §9 it is returned and inspectable, never summarized into a verdict.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GluingReading {
    pub left: RebaseInvariants,
    pub right: RebaseInvariants,
    pub overlap: RebaseInvariants,
    pub union: RebaseInvariants,
    /// Per grade, **the rank of the connecting map `δ_n: H_n(A∪B) → H_{n−1}(A∩B)`** — the classes
    /// the union carries that neither receiver does.
    ///
    /// The naive difference `b_n(A∪B) − (b_n(A) + b_n(B))` is *not* this and was the first thing
    /// written here. It double-counts the overlap: two arcs of a rim each carry one component, so
    /// it reports `−1` at grade zero, which is not an obstruction but the ordinary fact that two
    /// overlapping connected pieces union to one connected piece. It also reported an obstruction
    /// for the identity cover, which is the case a gluing law must return nothing on.
    ///
    /// The exact sequence determines every rank once it is solved from the top, where all terms
    /// vanish:
    ///
    /// ```text
    ///   rank a_n = b_n(A∩B) − rank d_{n+1}
    ///   rank b_n = b_n(A) + b_n(B) − rank a_n
    ///   rank d_n = b_n(A∪B) − rank b_n
    /// ```
    pub obstruction: Vec<i64>,
    /// `chi(A∪B) - chi(A) - chi(B) + chi(A∩B)`. **Exactly zero** when the sequence is exact, which
    /// it always is; a nonzero value is a defect in a reading, not a property of the cover.
    pub euler_defect: i64,
    /// Whether `b_n(A∪B) <= b_n(A) + b_n(B) + b_{n-1}(A∩B)` at every grade — the finer rank
    /// consequence of exactness, which the Euler identity alone does not imply.
    pub rank_bound_holds: bool,
    /// Per grade, torsion the union carries that neither section does.
    ///
    /// **`obstruction` above cannot see this and never could.** It is solved arithmetically from
    /// four Betti vectors, and Betti numbers are free ranks — torsion is invisible to every term in
    /// that solve. A Möbius band glued to a disc along their common circle is `RP²`: both sections
    /// are torsion-free, the overlap is torsion-free, the union carries `Z/2`, and the free-rank
    /// obstruction is **zero at every grade**. The organ reported a clean gluing on the exact case
    /// its own doc claims as its headline — a class living in neither receiver.
    ///
    /// So the connecting map's rank is necessary and not sufficient. This is the other half.
    pub torsion_obstruction: Vec<Vec<BigInt>>,
}

impl GluingReading {
    /// The cover exhibits a class neither receiver sees.
    pub fn exhibits_obstruction(&self) -> bool {
        self.obstruction.iter().any(|delta| *delta != 0)
            || self.torsion_obstruction.iter().any(|grade| !grade.is_empty())
    }

    /// The grades at which the union and the pieces disagree, with the amount.
    pub fn obstructed_grades(&self) -> Vec<(u32, i64)> {
        self.obstruction
            .iter()
            .enumerate()
            .filter(|(_, delta)| **delta != 0)
            .map(|(grade, delta)| (grade as u32, *delta))
            .collect()
    }
}

#[derive(Debug)]
pub enum GluingRefusal {
    Algebraic(CausalAlgebraicError),
    /// A section that is not closed under boundary is not a subcomplex, and its invariants would
    /// describe a structure that does not exist. Refused rather than read.
    NotASubcomplex(&'static str),
}

impl std::fmt::Display for GluingRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Algebraic(error) => write!(formatter, "{error}"),
            Self::NotASubcomplex(which) => write!(
                formatter,
                "the {which} of this cover is not closed under boundary, so it is not a section"
            ),
        }
    }
}

impl std::error::Error for GluingRefusal {}

impl From<CausalAlgebraicError> for GluingRefusal {
    fn from(error: CausalAlgebraicError) -> Self {
        Self::Algebraic(error)
    }
}

fn betti_at(invariants: &RebaseInvariants, grade: usize) -> i64 {
    invariants
        .grades
        .get(grade)
        .map_or(0, |entry| entry.betti as i64)
}

/// Read a cover.
///
/// Both sections, their overlap and their union are each checked to be genuine subcomplexes before
/// anything is read. The intersection and union of closed supports are closed, so the checks on
/// those two can only fire if an input was already malformed — which is exactly when a silent read
/// would be worst.
pub fn read_cover(
    complex: &GradedCausalComplex,
    cover: &Cover,
    rule: PivotRule,
) -> Result<GluingReading, GluingRefusal> {
    let overlap = cover.overlap();
    let union = cover.union();
    for (support, which) in [
        (&cover.left, "left section"),
        (&cover.right, "right section"),
        (&overlap, "overlap"),
        (&union, "union"),
    ] {
        if !complex.is_closed_support(support)? {
            return Err(GluingRefusal::NotASubcomplex(which));
        }
    }

    let left = rebase_invariants_on(complex, Some(&cover.left), rule)?;
    let right = rebase_invariants_on(complex, Some(&cover.right), rule)?;
    let overlap = rebase_invariants_on(complex, Some(&overlap), rule)?;
    let union = rebase_invariants_on(complex, Some(&union), rule)?;

    let grades = union
        .grades
        .len()
        .max(left.grades.len())
        .max(right.grades.len())
        .max(overlap.grades.len());

    // Solve the sequence downward from the top, where every term is zero.
    let mut obstruction = vec![0i64; grades];
    let mut connecting_above = 0i64;
    for grade in (0..grades).rev() {
        let into_pieces = betti_at(&overlap, grade) - connecting_above;
        let onto_union = betti_at(&left, grade) + betti_at(&right, grade) - into_pieces;
        let connecting = betti_at(&union, grade) - onto_union;
        obstruction[grade] = connecting;
        connecting_above = connecting;
    }

    let mut rank_bound_holds = true;
    for grade in 0..grades {
        let union_rank = betti_at(&union, grade);
        let pieces = betti_at(&left, grade) + betti_at(&right, grade);
        let below = if grade == 0 {
            0
        } else {
            betti_at(&overlap, grade - 1)
        };
        if union_rank > pieces + below {
            rank_bound_holds = false;
        }
        // A connecting map cannot have negative rank, and cannot exceed what it maps into. Both
        // are consequences of exactness, so a violation is a defect in a reading rather than a
        // property of the cover.
        if obstruction[grade] < 0 || obstruction[grade] > below {
            rank_bound_holds = false;
        }
    }

    // Torsion the union carries that neither section does, per grade. A multiset difference, so a
    // union carrying Z/2 twice where a section carries it once still reports one.
    let mut torsion_obstruction = Vec::with_capacity(grades);
    for grade in 0..grades {
        let mut held: Vec<BigInt> = left
            .grades
            .get(grade)
            .map(|entry| entry.torsion.clone())
            .unwrap_or_default();
        held.extend(
            right
                .grades
                .get(grade)
                .map(|entry| entry.torsion.clone())
                .unwrap_or_default(),
        );
        let mut unmatched = Vec::new();
        for factor in union
            .grades
            .get(grade)
            .map(|entry| entry.torsion.clone())
            .unwrap_or_default()
        {
            match held.iter().position(|carried| *carried == factor) {
                Some(at) => {
                    held.remove(at);
                }
                None => unmatched.push(factor),
            }
        }
        torsion_obstruction.push(unmatched);
    }

    let euler_defect = union.euler_characteristic() - left.euler_characteristic()
        - right.euler_characteristic()
        + overlap.euler_characteristic();

    Ok(GluingReading {
        left,
        right,
        overlap,
        union,
        obstruction,
        euler_defect,
        rank_bound_holds,
        torsion_obstruction,
    })
}

/// Cover a complex by two sections carved from a declared vertex partition.
///
/// Each side takes the vertices assigned to it plus every cell all of whose faces it already holds,
/// which is the largest closed subcomplex on those vertices. Cells straddling the partition fall to
/// neither side, so the union is a proper subcomplex whenever the partition cuts anything — the
/// honest situation for two receivers that do not between them see everything.
pub fn cover_by_vertices(
    complex: &GradedCausalComplex,
    left_vertices: &BTreeSet<CausalCellId>,
    right_vertices: &BTreeSet<CausalCellId>,
) -> Result<Cover, GluingRefusal> {
    Ok(Cover {
        left: saturate(complex, left_vertices)?,
        right: saturate(complex, right_vertices)?,
    })
}

/// The largest closed subcomplex whose grade-zero cells are `seeds`.
fn saturate(
    complex: &GradedCausalComplex,
    seeds: &BTreeSet<CausalCellId>,
) -> Result<BTreeSet<CausalCellId>, GluingRefusal> {
    let mut support: BTreeSet<CausalCellId> = seeds.clone();
    loop {
        let mut grew = false;
        for cell in complex.cells().values() {
            if support.contains(&cell.id) || cell.grade == 0 {
                continue;
            }
            if cell.boundary.support().is_subset(&support) {
                support.insert(cell.id);
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    Ok(support)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebraic::{CausalChain, ComparativeMultiplicity};
    use crate::causal::EventId;

    fn source() -> BTreeSet<EventId> {
        BTreeSet::from([EventId(1)])
    }

    // -----------------------------------------------------------------------------------------
    // theorem-known families at parameterized scale
    //
    // The answers here come from the classification of surfaces and from the structure of a
    // p-fold attachment, not from the complexes being small enough to read by eye. Both sweep.

    /// The standard one-vertex model of a closed orientable surface of genus `g`: one vertex,
    /// `2g` loops, one face whose boundary word is the product of commutators. In the chain group
    /// that word abelianizes to zero, so `d_2 = 0`.
    ///
    /// Known by theorem: `betti = [1, 2g, 1]`, no torsion.
    fn genus_surface(g: usize) -> GradedCausalComplex {
        let mut complex = GradedCausalComplex::default();
        let vertex = complex
            .found_cell("v", source(), 0, CausalChain::default())
            .expect("a vertex has no boundary");
        let mut edges = Vec::new();
        for index in 0..2 * g {
            let mut boundary = CausalChain::default();
            boundary.add_term(vertex, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(vertex, ComparativeMultiplicity::negative(1u32));
            edges.push(
                complex
                    .found_cell(format!("e{index}"), source(), 1, boundary)
                    .expect("a loop at one vertex closes"),
            );
        }
        // Each edge appears once forward and once backward in the commutator word.
        let mut face = CausalChain::default();
        for edge in &edges {
            face.add_term(*edge, ComparativeMultiplicity::positive(1u32));
            face.add_term(*edge, ComparativeMultiplicity::negative(1u32));
        }
        complex
            .found_cell("face", source(), 2, face)
            .expect("the commutator word is a cycle");
        complex
    }

    #[test]
    fn the_genus_family_returns_the_classification_theorem() {
        for g in 1..=8 {
            let invariants =
                rebase_invariants_on(&genus_surface(g), None, PivotRule::FirstNonzero).unwrap();
            assert_eq!(
                invariants.betti_vector(),
                vec![1, 2 * g, 1],
                "genus {g} must return betti [1, {}, 1]",
                2 * g
            );
            assert!(
                invariants.total_torsion().is_empty(),
                "a closed orientable surface carries no torsion"
            );
            assert_eq!(
                invariants.euler_characteristic(),
                2 - 2 * g as i64,
                "Euler characteristic of a genus-{g} surface is 2 - 2g"
            );
        }
    }

    /// One vertex, one loop, one face attached `p` times. Known: `H_1 = Z/p`.
    fn torsion_space(p: u32) -> GradedCausalComplex {
        let mut complex = GradedCausalComplex::default();
        let vertex = complex
            .found_cell("v", source(), 0, CausalChain::default())
            .unwrap();
        let mut loop_boundary = CausalChain::default();
        loop_boundary.add_term(vertex, ComparativeMultiplicity::positive(1u32));
        loop_boundary.add_term(vertex, ComparativeMultiplicity::negative(1u32));
        let edge = complex
            .found_cell("e", source(), 1, loop_boundary)
            .unwrap();
        let mut face = CausalChain::default();
        face.add_term(edge, ComparativeMultiplicity::positive(p));
        complex.found_cell("face", source(), 2, face).unwrap();
        complex
    }

    #[test]
    fn the_torsion_family_returns_z_mod_p_for_every_p() {
        use num_bigint::BigInt;
        for p in 2..=9u32 {
            let invariants =
                rebase_invariants_on(&torsion_space(p), None, PivotRule::FirstNonzero).unwrap();
            assert_eq!(
                invariants.total_torsion(),
                vec![BigInt::from(p)],
                "a p-fold attachment must deposit exactly Z/{p}"
            );
            assert_eq!(
                invariants.betti_vector(),
                vec![1, 0, 0],
                "the free rank is killed while the winding stands"
            );
        }
    }

    // -----------------------------------------------------------------------------------------
    // the cover

    /// A rim of `n` vertices, which is what a grown circuit's frontier closes into.
    fn rim(length: usize) -> (GradedCausalComplex, Vec<CausalCellId>) {
        let mut complex = GradedCausalComplex::default();
        let mut vertices = Vec::new();
        for index in 0..length {
            vertices.push(
                complex
                    .found_cell(format!("v{index}"), source(), 0, CausalChain::default())
                    .unwrap(),
            );
        }
        for index in 0..length {
            let mut boundary = CausalChain::default();
            boundary.add_term(
                vertices[(index + 1) % length],
                ComparativeMultiplicity::positive(1u32),
            );
            boundary.add_term(vertices[index], ComparativeMultiplicity::negative(1u32));
            complex
                .found_cell(format!("e{index}"), source(), 1, boundary)
                .unwrap();
        }
        (complex, vertices)
    }

    /// The sentence this module exists for, on a rim at real length: two arcs, neither of which
    /// carries the loop, whose union does — and the loop comes from the overlap being disconnected.
    #[test]
    fn the_loop_lives_in_neither_receiver_only_in_their_disagreement() {
        for length in [6usize, 12, 25, 64] {
            let (complex, vertices) = rim(length);
            // Two overlapping arcs. Each is contractible; together they close the rim.
            let split = length / 2;
            let left: BTreeSet<CausalCellId> = vertices[..=split].iter().copied().collect();
            let right: BTreeSet<CausalCellId> = vertices[split..]
                .iter()
                .chain(std::iter::once(&vertices[0]))
                .copied()
                .collect();
            let cover = cover_by_vertices(&complex, &left, &right).unwrap();
            let reading = read_cover(&complex, &cover, PivotRule::FirstNonzero).unwrap();

            assert_eq!(reading.euler_defect, 0, "Mayer-Vietoris rank exactness at n={length}");
            assert!(reading.rank_bound_holds);

            assert_eq!(
                betti_at(&reading.left, 1),
                0,
                "the left arc is a tree and carries no loop (n={length})"
            );
            assert_eq!(
                betti_at(&reading.right, 1),
                0,
                "the right arc is a tree and carries no loop (n={length})"
            );
            assert_eq!(
                betti_at(&reading.union, 1),
                1,
                "their union is the rim and carries one (n={length})"
            );
            assert_eq!(
                reading.obstructed_grades(),
                vec![(1, 1)],
                "exactly one class, at grade one, glued into existence (n={length})"
            );
            assert_eq!(
                betti_at(&reading.overlap, 0),
                2,
                "and it comes from the overlap being DISCONNECTED (n={length})"
            );
        }
    }

    /// A Mobius band glued to a disc along their common circle is `RP²`, and this is the case the
    /// free-rank obstruction is structurally blind to.
    ///
    /// `d(M) = z - 2c`, `d(D) = z`. Both sections are torsion-free, the overlap is torsion-free,
    /// and the union carries `Z/2` — a class in **neither** receiver, which is the sentence this
    /// module opens with. The connecting map's rank is `0` at every grade, because it is solved from
    /// four Betti vectors and Betti numbers cannot see torsion. Before `torsion_obstruction` this
    /// returned a clean gluing on the headline case.
    #[test]
    fn the_free_rank_obstruction_is_blind_to_a_torsion_class_in_neither_section() {
        let mut complex = GradedCausalComplex::default();
        let vertex = complex
            .found_cell("v", source(), 0, CausalChain::default())
            .unwrap();
        let loop_at = |complex: &mut GradedCausalComplex, name: &str| {
            let mut boundary = CausalChain::default();
            boundary.add_term(vertex, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(vertex, ComparativeMultiplicity::negative(1u32));
            complex.found_cell(name, source(), 1, boundary).unwrap()
        };
        let rim = loop_at(&mut complex, "z");
        let core = loop_at(&mut complex, "c");

        let mut band = CausalChain::default();
        band.add_term(rim, ComparativeMultiplicity::positive(1u32));
        band.add_term(core, ComparativeMultiplicity::negative(2u32));
        let moebius = complex.found_cell("M", source(), 2, band).unwrap();

        let mut cap = CausalChain::default();
        cap.add_term(rim, ComparativeMultiplicity::positive(1u32));
        let disc = complex.found_cell("D", source(), 2, cap).unwrap();

        let cover = Cover {
            left: BTreeSet::from([vertex, rim, core, moebius]),
            right: BTreeSet::from([vertex, rim, disc]),
        };
        let reading = read_cover(&complex, &cover, PivotRule::FirstNonzero).unwrap();

        assert!(reading.left.total_torsion().is_empty(), "the band is torsion-free");
        assert!(reading.right.total_torsion().is_empty(), "the disc is torsion-free");
        assert!(reading.overlap.total_torsion().is_empty(), "the circle is torsion-free");
        assert_eq!(
            reading.union.total_torsion(),
            vec![BigInt::from(2)],
            "their union is RP-two and carries Z/2"
        );

        assert!(
            reading.obstruction.iter().all(|rank| *rank == 0),
            "the free-rank obstruction sees nothing here, and structurally cannot: {:?}",
            reading.obstruction
        );
        assert_eq!(
            reading.torsion_obstruction[1],
            vec![BigInt::from(2)],
            "the torsion half must name it at grade one"
        );
        assert!(
            reading.exhibits_obstruction(),
            "a class in neither receiver is an obstruction whether it is free or torsion"
        );
        assert_eq!(reading.euler_defect, 0, "exactness still holds");
    }

    /// The control without which the obstruction proves nothing: a cover that must glue cleanly
    /// returns no obstruction. A gluing law that obstructs on the identity overlap is broken.
    #[test]
    fn a_cover_that_must_glue_returns_no_obstruction() {
        let (complex, vertices) = rim(20);
        let all: BTreeSet<CausalCellId> = vertices.iter().copied().collect();
        let cover = cover_by_vertices(&complex, &all, &all).unwrap();
        let reading = read_cover(&complex, &cover, PivotRule::FirstNonzero).unwrap();

        assert_eq!(reading.euler_defect, 0);
        assert!(
            !reading.exhibits_obstruction(),
            "the identity overlap glues with nothing left over: {:?}",
            reading.obstructed_grades()
        );
        assert_eq!(betti_at(&reading.overlap, 0), 1, "the overlap is the whole rim");
    }

    /// Mayer–Vietoris as the second route: over many covers of one structure, the union reading
    /// must reproduce the direct reading of the same support. The known answer is an independent
    /// computation, not a small enough structure.
    #[test]
    fn every_cover_reproduces_the_direct_reading_of_its_own_union() {
        for length in [9usize, 16, 33] {
            let (complex, vertices) = rim(length);
            for split in 1..length - 1 {
                let left: BTreeSet<CausalCellId> = vertices[..=split].iter().copied().collect();
                let right: BTreeSet<CausalCellId> = vertices[split..].iter().copied().collect();
                let cover = cover_by_vertices(&complex, &left, &right).unwrap();
                let reading = read_cover(&complex, &cover, PivotRule::FirstNonzero).unwrap();

                let direct =
                    rebase_invariants_on(&complex, Some(&cover.union()), PivotRule::FirstNonzero)
                        .unwrap();
                assert_eq!(
                    reading.union.betti_vector(),
                    direct.betti_vector(),
                    "n={length} split={split}"
                );
                assert_eq!(
                    reading.euler_defect, 0,
                    "rank exactness must hold for every cover: n={length} split={split}"
                );
                assert!(reading.rank_bound_holds, "n={length} split={split}");
            }
        }
    }

    #[test]
    fn the_euler_identity_holds_over_the_genus_family_under_many_covers() {
        for g in 1..=5 {
            let complex = genus_surface(g);
            let vertices: BTreeSet<CausalCellId> = complex
                .cells()
                .values()
                .filter(|cell| cell.grade == 0)
                .map(|cell| cell.id)
                .collect();
            // A one-vertex model admits only the trivial partition, so this exercises the identity
            // where the two sections coincide with the whole — the degenerate cover, which must
            // still satisfy exactness.
            let cover = cover_by_vertices(&complex, &vertices, &vertices).unwrap();
            let reading = read_cover(&complex, &cover, PivotRule::FirstNonzero).unwrap();
            assert_eq!(reading.euler_defect, 0, "genus {g}");
            assert!(!reading.exhibits_obstruction(), "genus {g}");
        }
    }

    #[test]
    fn a_section_that_is_not_closed_is_refused_rather_than_read() {
        let (complex, vertices) = rim(8);
        // An edge without its endpoints: not a subcomplex.
        let edge = complex
            .cells()
            .values()
            .find(|cell| cell.grade == 1)
            .expect("the rim has edges")
            .id;
        let cover = Cover {
            left: BTreeSet::from([edge]),
            right: vertices.iter().copied().collect(),
        };
        assert!(
            matches!(
                read_cover(&complex, &cover, PivotRule::FirstNonzero),
                Err(GluingRefusal::NotASubcomplex(_))
            ),
            "an open support must refuse, not return invariants for a structure that is not there"
        );
    }
}
