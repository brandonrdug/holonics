//! The contact site as a cover, glued; and the leader integrated into a return stroke.
//!
//! ## What this joins
//!
//! `conditioned_derivation::FoundedCover` now retains every stem occurrence at every span — a cover
//! in the topological sense, with faces where occurrences are co-present and crossings where they
//! overlap without containment. `gluing.rs` is Mayer–Vietoris **keyed to which cover you chose**,
//! and `running_integral.rs` is the exact running sum with the disagreement of two traversals
//! deposited as holonomy. Neither had ever seen a contact.
//!
//! Brandon, 2026-08-09, stating the production mechanism this exists to serve:
//!
//! > *"it is lightning leaders integrating into return strikes, the return strikes can be absorbed
//! > and measured as **causal strings** that integrate into production output."*
//!
//! ## Two complexes, and only one of them has cycles
//!
//! **Inside a word** the cover is an interval: offsets are 0-cells, unit steps are 1-cells, and a
//! stem occurrence is the SET of steps it spans. Two occurrences intersect exactly in the letters
//! they share, so Mayer-Vietoris has something to glue.
//!
//! **That complex is contractible.** Measured `β = [1, 0]` on four words, including one where a stem
//! occurs twice. `β₁ = 0` for every word by construction, so a connecting map read over it can only
//! ever be zero — and reporting that zero as a finding is a theorem about intervals wearing the
//! clothes of a measurement. An earlier form of this module did exactly that on eleven crossings.
//!
//! **The cycles are BETWEEN words.** `contact_graph` puts identifiers at the 0-cells and every
//! shared stem at a 1-cell: two identifiers sharing two stems already close a loop, three sharing
//! one pairwise close a triangle. Measured `β₁ = 8` over four identifiers.
//!
//! ## The leader, the reflection, and the return stroke
//!
//! A leader rides out along an arc. **The return stroke rides back along another arc AGAINST its
//! orientation**, and going against negates the increment — that is the signature `σ`, the
//! half-turn, `−1 = e^{iπ}`. `causal_reflection.rs` states the same operation at its own altitude:
//! *"the relation that costs an improper integral on one side costs a negation on the other."*
//!
//! The walk closes on the vertex it left, and `running_integral::holonomy` **refuses one that does
//! not**. What the sum returns is what the reflection did not cancel — `q_n = q_m` with the residual
//! stored, which is Soma's chain law rather than a metaphor for it. Measured on real material: out
//! along `a`, back along `carrier` reflected, series `[1, −6]`, holonomy `−6`.
//!
//! The **causal string** is the ordered stems the circuit rode, and inside a word it is the sequence
//! of FACES — what stood over each letter as it was crossed, superpositions carried rather than
//! resolved. That is the production-facing half; the integral is the measurement half.
//!
//! ## What is declared and what is read off
//!
//! The **cochain is the caller's declaration**, and two are offered because one is not a gauge: span
//! length is purely structural, and witness breadth is `Π`, the lived construction. Both measure;
//! neither governs. `CLAUDE.md` §13 rule 2 — count freely, report what you count, never let a count
//! quietly decide.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use relational_geometry::Rat;

use crate::algebraic::{CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex};
use crate::causal::EventId;
use crate::conditioned_derivation::{FoundedCover, FoundedMorphology};
use crate::gluing::{read_cover, Cover, GluingReading, GluingRefusal};
use crate::multiquadratic::{Multiquadratic, MultiquadraticRefusal, DECLARED_KERNEL_BOUND};

/// APERTURE — how many distinct squarefree generators one composed turn may carry.
///
/// The multiquadratic basis is `2ⁿ` wide, so this bounds a real resource. Declared here as the
/// default for [`coarse_grain`]; [`coarse_grain_in_aperture`] takes it from the caller, and a
/// climbing tower should pass its own.
pub const DECLARED_GENERATOR_APERTURE: usize = 12;
use crate::rebase_invariants::PivotRule;
use crate::running_integral::{
    running_sum, Cochain, Orientation, Path, PathStep, RunningIntegralError,
};

/// Why a contact could not be read as a cover.
#[derive(Debug)]
pub enum ContactGluingRefusal {
    /// The cover carries no occurrence of the named stem, so there is no subcomplex to glue.
    StemStandsNowhere { stem: String },
    /// A walk named an occurrence the complex does not carry.
    WalkLeavesTheCover { stem: String },
    Gluing(GluingRefusal),
    Integral(RunningIntegralError),
    Algebraic(String),
}

impl std::fmt::Display for ContactGluingRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StemStandsNowhere { stem } => {
                write!(formatter, "the stem `{stem}` stands nowhere in this cover")
            }
            Self::WalkLeavesTheCover { stem } => {
                write!(formatter, "the walk names `{stem}`, which this cover does not carry")
            }
            Self::Gluing(refusal) => write!(formatter, "{refusal:?}"),
            Self::Integral(refusal) => write!(formatter, "{refusal:?}"),
            Self::Algebraic(refusal) => write!(formatter, "{refusal}"),
        }
    }
}

impl std::error::Error for ContactGluingRefusal {}

/// A word's cover, as a one-dimensional complex, with each occurrence's cell retained by name.
pub struct ContactComplex {
    pub complex: GradedCausalComplex,
    /// One entry per occurrence, in the cover's canonical order: its stem, its span, and the cell.
    pub occurrences: Vec<(String, usize, usize, CausalCellId)>,
    /// The vertex cell for each offset the word carries.
    pub offsets: BTreeMap<usize, CausalCellId>,
    /// The 1-cell for each unit step `@at → @at+1`.
    pub steps: BTreeMap<usize, CausalCellId>,
}

impl ContactComplex {
    /// The cells of every occurrence of one stem, together with their endpoints — a subcomplex,
    /// which is what `read_cover` requires and refuses without.
    pub fn section(&self, stem: &str) -> Result<BTreeSet<CausalCellId>, ContactGluingRefusal> {
        let mut section = BTreeSet::new();
        for (carried, at, through, _) in &self.occurrences {
            if carried != stem {
                continue;
            }
            for step in *at..*through {
                if let Some(cell) = self.steps.get(&step) {
                    section.insert(*cell);
                }
                if let Some(vertex) = self.offsets.get(&step) {
                    section.insert(*vertex);
                }
            }
            if let Some(vertex) = self.offsets.get(through) {
                section.insert(*vertex);
            }
        }
        if section.is_empty() {
            return Err(ContactGluingRefusal::StemStandsNowhere { stem: stem.to_owned() });
        }
        Ok(section)
    }

    /// **A leader: the walk along the word covered by one stem's spans**, step by step.
    ///
    /// A leader traverses the material; it does not hop between repeats of one name. So the walk is
    /// the unit steps the stem's occurrences cover, in order, and what it rides at each step is
    /// whatever stands there — which is what makes the return a *string* rather than a repetition.
    fn walk(&self, stem: &str) -> Result<Path, ContactGluingRefusal> {
        let mut covered: BTreeSet<usize> = BTreeSet::new();
        for (carried, at, through, _) in &self.occurrences {
            if carried == stem {
                covered.extend(*at..*through);
            }
        }
        if covered.is_empty() {
            return Err(ContactGluingRefusal::WalkLeavesTheCover { stem: stem.to_owned() });
        }
        let steps: Vec<PathStep> = covered
            .into_iter()
            .filter_map(|at| self.steps.get(&at).copied())
            .map(|cell| PathStep { cell, orientation: Orientation::Along })
            .collect();
        Ok(Path::new(steps))
    }

    /// Every stem standing over one unit step — the face the leader rides there.
    pub fn face_over(&self, step: usize) -> Vec<&str> {
        let mut stems: Vec<&str> = self
            .occurrences
            .iter()
            .filter(|(_, at, through, _)| *at <= step && step < *through)
            .map(|(stem, _, _, _)| stem.as_str())
            .collect();
        stems.sort_unstable();
        stems.dedup();
        stems
    }
}

/// Read a word's founded cover as a complex.
///
/// The offsets are the word's own; the occurrences are the cover's own. Nothing here chooses a
/// grain, a bound, or a population.
pub fn contact_complex(cover: &FoundedCover) -> Result<ContactComplex, ContactGluingRefusal> {
    let mut complex = GradedCausalComplex::default();
    let mut offsets: BTreeMap<usize, CausalCellId> = BTreeMap::new();
    let mut steps: BTreeMap<usize, CausalCellId> = BTreeMap::new();
    let mut occurrences = Vec::new();

    // **The word is a line, and a span is a SUBCOMPLEX of it — not an edge.**
    //
    // The first form of this founded one 1-cell per occurrence, spanning `at → through` in a single
    // jump. Two crossing stems then shared no cell at all: `ker` on `@0,@3` and `rn` on `@2,@4` meet
    // in the *interior*, which a single long edge does not represent. The measured consequence was
    // `overlap β₀ = 0` on every crossing contact — an empty intersection for two spans that
    // demonstrably share letters, and therefore a connecting map that could only ever be zero.
    //
    // The faithful complex is the one the word already is:
    //
    // ```text
    //   0-cells   every offset `@0 … @len`
    //   1-cells   every unit step `@i → @i+1`
    //   a stem occurrence  =  the SET of unit steps it covers
    // ```
    //
    // Now two occurrences intersect exactly in the steps they share, which is exactly where they
    // share letters, and Mayer–Vietoris has something to glue.
    let extent = cover.word.len();
    for at in 0..=extent {
        let vertex = complex
            .found_cell(
                format!("@{at}"),
                BTreeSet::from([EventId(at as u64)]),
                0,
                CausalChain::default(),
            )
            .map_err(|refusal| ContactGluingRefusal::Algebraic(format!("{refusal:?}")))?;
        offsets.insert(at, vertex);
    }
    for at in 0..extent {
        let (tail, head) = (offsets[&at], offsets[&(at + 1)]);
        let mut boundary = CausalChain::default();
        boundary.add_term(head, ComparativeMultiplicity::new(BigUint::from(1u32), BigUint::from(0u32)));
        boundary.add_term(tail, ComparativeMultiplicity::new(BigUint::from(0u32), BigUint::from(1u32)));
        let cell = complex
            .found_cell(
                format!("step@{at}"),
                BTreeSet::from([EventId(at as u64)]),
                1,
                boundary,
            )
            .map_err(|refusal| ContactGluingRefusal::Algebraic(format!("{refusal:?}")))?;
        steps.insert(at, cell);
    }

    for occurrence in &cover.occurrences {
        occurrences.push((
            occurrence.stem.clone(),
            occurrence.at,
            occurrence.through,
            // The occurrence's own first step, kept so a caller can name it; the span is what
            // `section` reads.
            steps.get(&occurrence.at).copied().unwrap_or(CausalCellId(0)),
        ));
    }
    Ok(ContactComplex { complex, occurrences, offsets, steps })
}

/// **The gluing at a contact.** Two stems standing in one word, read as a cover.
///
/// Returns the full Mayer–Vietoris reading: the invariants of each piece, of their overlap, of their
/// union, and the rank of the connecting map per grade. A non-zero connecting rank is the union
/// carrying a class neither stem carries alone.
pub fn glue_at_contact(
    cover: &FoundedCover,
    left_stem: &str,
    right_stem: &str,
    rule: PivotRule,
) -> Result<(ContactComplex, GluingReading), ContactGluingRefusal> {
    let contact = contact_complex(cover)?;
    let cover_pair = Cover {
        left: contact.section(left_stem)?,
        right: contact.section(right_stem)?,
    };
    let reading = read_cover(&contact.complex, &cover_pair, rule)
        .map_err(ContactGluingRefusal::Gluing)?;
    Ok((contact, reading))
}

// -------------------------------------------------------------------------------------------------
// The leader, the integral, and the return stroke
// -------------------------------------------------------------------------------------------------

/// A declared weight on occurrences. **Both measure; neither governs.**
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeaderCochain {
    /// How many letters the occurrence carries. Purely structural — no frequency enters.
    SpanLength,
    /// How many distinct wholes witnessed the stem. This is `Π`, the lived construction, reported
    /// and never allowed to select.
    WitnessBreadth,
}

/// **A return stroke, absorbed and measured.**
///
/// The walk read back as a *causal string* — the ordered stems the leader rode — together with the
/// exact integral of that walk. The string is the production-facing half: a word the emission can be
/// composed out of. The integral is the measurement half, exact over `BigInt` with no tolerance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnStroke {
    /// The ordered stems the leader rode. **The causal string.**
    pub string: Vec<String>,
    /// The same, joined — the word the return carries.
    pub word: String,
    /// The exact running total along the walk.
    pub integral: BigInt,
    /// The partial sums, in order — the series, with every term retained rather than collapsed to
    /// its total. `CLAUDE.md` §2b: you may take the expansion, you may not discard the tail.
    pub series: Vec<BigInt>,
    /// The cochain the caller declared.
    pub cochain: LeaderCochain,
}

/// Integrate one stem's leader and return the stroke.
pub fn integrate_leader(
    cover: &FoundedCover,
    morphology: &FoundedMorphology,
    stem: &str,
    cochain: LeaderCochain,
) -> Result<(ContactComplex, ReturnStroke), ContactGluingRefusal> {
    let contact = contact_complex(cover)?;
    let weights = declare_cochain(&contact, morphology, cochain);
    let path = contact.walk(stem)?;
    let integral = running_sum(&contact.complex, &weights, &path)
        .map_err(ContactGluingRefusal::Integral)?;

    // **The causal string is the sequence of FACES the leader rode**, one per step: what stood over
    // each letter as it was crossed. A step where two stems superpose contributes both, joined by
    // `+`, so the string carries the superposition rather than picking a member of it.
    let mut string = Vec::new();
    let mut series = Vec::new();
    for step in integral.steps.iter() {
        if let Some((at, _)) = contact.steps.iter().find(|(_, cell)| **cell == step.cell) {
            string.push(contact.face_over(*at).join("+"));
        }
        series.push(step.accumulated.clone());
    }
    let word = cover.word.clone();
    Ok((
        contact,
        ReturnStroke {
            string,
            word,
            integral: integral.total.clone(),
            series,
            cochain,
        },
    ))
}

/// **The contact graph.** Identifiers as 0-cells, each shared stem as a 1-cell between them.
///
/// This is where the cycles are, and the word-line complex above has none: an interval subdivided
/// is contractible, so `β₁ = 0` for every word by construction — measured `[1, 0]` on four words
/// including one where a stem occurs twice. Reporting a zero connecting map over that is a theorem
/// about intervals, not a reading of the material.
///
/// Two identifiers that share **two** stems already close a loop. Three that pairwise share one
/// close a triangle — `C_3`, whose adjacency spectrum is the star-polygon reading `2cos(2πk/n)` that
/// `inertia.rs` computes by elimination. The cycles are between the words, not inside them.
pub struct ContactGraph {
    pub complex: GradedCausalComplex,
    /// One vertex per identifier.
    pub identifiers: BTreeMap<String, CausalCellId>,
    /// One edge per `(left identifier, right identifier, shared stem)`, in canonical order.
    pub arcs: Vec<(String, String, String, CausalCellId)>,
}

/// Found the contact graph over a declared identifier population.
pub fn contact_graph(
    morphology: &FoundedMorphology,
    population: &[String],
) -> Result<ContactGraph, ContactGluingRefusal> {
    let mut complex = GradedCausalComplex::default();
    let mut identifiers: BTreeMap<String, CausalCellId> = BTreeMap::new();
    let mut arcs = Vec::new();

    let mut covers: BTreeMap<&String, FoundedCover> = BTreeMap::new();
    for word in population {
        let Ok(cover) = morphology.cover(word) else { continue };
        covers.insert(word, cover);
    }
    for (ordinal, word) in covers.keys().enumerate() {
        let vertex = complex
            .found_cell(
                (*word).clone(),
                BTreeSet::from([EventId(ordinal as u64)]),
                0,
                CausalChain::default(),
            )
            .map_err(|refusal| ContactGluingRefusal::Algebraic(format!("{refusal:?}")))?;
        identifiers.insert((*word).clone(), vertex);
    }

    let words: Vec<&String> = covers.keys().copied().collect();
    let mut minted = 0u64;
    for (index, left) in words.iter().enumerate() {
        for right in words.iter().skip(index + 1) {
            let shared: BTreeSet<&str> = covers[*left]
                .stems()
                .intersection(&covers[*right].stems())
                .copied()
                .collect();
            for stem in shared {
                let (tail, head) = (identifiers[*left], identifiers[*right]);
                let mut boundary = CausalChain::default();
                boundary.add_term(
                    head,
                    ComparativeMultiplicity::new(BigUint::from(1u32), BigUint::from(0u32)),
                );
                boundary.add_term(
                    tail,
                    ComparativeMultiplicity::new(BigUint::from(0u32), BigUint::from(1u32)),
                );
                minted += 1;
                let cell = complex
                    .found_cell(
                        format!("{left}~{stem}~{right}"),
                        BTreeSet::from([EventId(minted)]),
                        1,
                        boundary,
                    )
                    .map_err(|refusal| ContactGluingRefusal::Algebraic(format!("{refusal:?}")))?;
                arcs.push((
                    (*left).clone(),
                    (*right).clone(),
                    stem.to_owned(),
                    cell,
                ));
            }
        }
    }
    Ok(ContactGraph { complex, identifiers, arcs })
}

/// **A closed circuit: the leader out, and the return stroke back along the reflected arc.**
///
/// This is integration by reflection, and the reflection is not a name on a comparison. Going
/// *against* an arc's orientation negates its increment — that is the signature `σ`, the half-turn,
/// `−1 = e^{iπ}`. `causal_reflection.rs` states the same thing at its own altitude: *"the relation
/// that costs an improper integral on one side costs a negation on the other."*
///
/// So the circuit is: ride one arc forward, ride the other **backward**, and the walk closes on the
/// vertex it left. `running_integral::holonomy` **refuses a walk that does not return to its
/// departure**, so a closed loop is checked rather than claimed. What the sum returns is what the
/// reflection did **not** cancel — the holonomy of the loop, and `q_n = q_m` with the residual
/// stored, which is Soma's chain law rather than a metaphor for it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Circuit {
    /// The identifiers the loop passes through, in order, returning to its start.
    pub through: Vec<String>,
    /// The stems it rode, in order. **The causal string of the closed loop.**
    pub string: Vec<String>,
    /// Which steps were taken against the arc's orientation — the reflected half.
    pub reflected: Vec<bool>,
    /// The partial sums, term by term. The series, tail retained.
    pub series: Vec<BigInt>,
    /// The sum around the closed loop. **Zero exactly when the reflection cancels the leader.**
    pub holonomy: BigInt,
}

/// Ride the loop formed by two arcs between the same pair of identifiers.
///
/// Two identifiers sharing two stems is the smallest genuine cycle this material carries, and it is
/// common: any pair whose covers meet twice closes one.
pub fn ride_circuit(
    graph: &ContactGraph,
    morphology: &FoundedMorphology,
    left: &str,
    right: &str,
    out_stem: &str,
    back_stem: &str,
    cochain: LeaderCochain,
) -> Result<Circuit, ContactGluingRefusal> {
    let find = |stem: &str| {
        graph
            .arcs
            .iter()
            .find(|(a, b, carried, _)| {
                carried == stem
                    && ((a == left && b == right) || (a == right && b == left))
            })
            .map(|(_, _, _, cell)| *cell)
            .ok_or(ContactGluingRefusal::WalkLeavesTheCover { stem: stem.to_owned() })
    };
    let out = find(out_stem)?;
    let back = find(back_stem)?;

    let mut weights = Cochain::new(1);
    for (_, _, stem, cell) in &graph.arcs {
        let value = match cochain {
            LeaderCochain::SpanLength => BigInt::from(stem.len()),
            LeaderCochain::WitnessBreadth => BigInt::from(
                morphology
                    .stem(stem)
                    .map_or(0usize, |founded| founded.wholes.len()),
            ),
        };
        weights.set(*cell, value);
    }

    // Out along one arc, back along the other AGAINST its orientation. The walk closes.
    let path = Path::new([
        PathStep { cell: out, orientation: Orientation::Along },
        PathStep { cell: back, orientation: Orientation::Against },
    ]);
    let integral = crate::running_integral::holonomy(&graph.complex, &weights, &path)
        .map_err(ContactGluingRefusal::Integral)?;

    Ok(Circuit {
        through: vec![left.to_owned(), right.to_owned(), left.to_owned()],
        string: vec![out_stem.to_owned(), back_stem.to_owned()],
        reflected: vec![false, true],
        series: integral.steps.iter().map(|step| step.accumulated.clone()).collect(),
        holonomy: integral.total.clone(),
    })
}

fn declare_cochain(
    contact: &ContactComplex,
    morphology: &FoundedMorphology,
    cochain: LeaderCochain,
) -> Cochain {
    // The cochain lives on the unit steps, because that is what a leader crosses. Its value at a
    // step is read off the FACE standing there — how many stems, or how much witness they carry —
    // so a step where several stems superpose weighs differently from one where a single stem does.
    let mut weights = Cochain::new(1);
    for (at, cell) in &contact.steps {
        let face = contact.face_over(*at);
        let value = match cochain {
            LeaderCochain::SpanLength => BigInt::from(face.len()),
            LeaderCochain::WitnessBreadth => BigInt::from(
                face.iter()
                    .map(|stem| {
                        morphology
                            .stem(stem)
                            .map_or(0usize, |founded| founded.wholes.len())
                    })
                    .sum::<usize>(),
            ),
        };
        weights.set(*cell, value);
    }
    weights
}

// -------------------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conditioned_derivation::expose;

    /// A morphology committing `exact`, `act`, `car`, `carry` — every one by recurrence across two
    /// wholes, so nothing here is authored into the population.
    fn morphology() -> FoundedMorphology {
        FoundedMorphology::condition(&[
            expose("one", "exact act car carry carrier"),
            expose("two", "exact act car carry carrier"),
        ])
    }

    #[test]
    fn a_word_becomes_a_complex_whose_cells_are_its_own_occurrences() {
        let morphology = morphology();
        let cover = morphology.cover("exactcarry").expect("ascii");
        let contact = contact_complex(&cover).expect("reads");
        assert_eq!(contact.occurrences.len(), cover.occurrences.len());
        // Every occurrence is a 1-cell and every offset it names is a 0-cell.
        for (_, at, through, cell) in &contact.occurrences {
            assert_eq!(contact.complex.cell(*cell).expect("carried").grade, 1);
            assert!(contact.offsets.contains_key(at));
            assert!(contact.offsets.contains_key(through));
        }
    }

    #[test]
    fn a_stem_standing_nowhere_is_refused_by_name() {
        let morphology = morphology();
        let cover = morphology.cover("exact").expect("ascii");
        let contact = contact_complex(&cover).expect("reads");
        match contact.section("carry") {
            Err(ContactGluingRefusal::StemStandsNowhere { stem }) => assert_eq!(stem, "carry"),
            other => panic!("expected a named refusal, got {other:?}"),
        }
    }

    #[test]
    fn two_stems_in_one_word_glue_and_the_reading_carries_every_piece() {
        let morphology = morphology();
        let cover = morphology.cover("exactcarry").expect("ascii");
        let (_, reading) =
            glue_at_contact(&cover, "exact", "carry", PivotRule::SmallestMagnitude).expect("glues");
        // Each piece is one interval, so each is connected and carries no loop.
        assert_eq!(reading.left.grades[0].betti, 1);
        assert_eq!(reading.right.grades[0].betti, 1);
        // The union of two abutting intervals is connected.
        assert_eq!(reading.union.grades[0].betti, 1);
    }

    /// **The return stroke is a string, and the series is retained.**
    #[test]
    fn a_leader_integrates_into_a_causal_string_with_its_series() {
        let morphology = morphology();
        let cover = morphology.cover("exactcarry").expect("ascii");
        let (_, stroke) =
            integrate_leader(&cover, &morphology, "exact", LeaderCochain::SpanLength)
                .expect("integrates");
        // **The string is the face at each step, not a name repeated.** `exact` spans offsets 0..5
        // and `act` sits inside it from 2, so the first two steps carry one stem and the last three
        // carry both — the superposition is IN the string rather than resolved out of it.
        assert_eq!(
            stroke.string,
            vec![
                "exact".to_owned(),
                "exact".to_owned(),
                "act+exact".to_owned(),
                "act+exact".to_owned(),
                "act+exact".to_owned(),
            ]
        );
        assert_eq!(stroke.word, "exactcarry");
        // The cochain weighs each step by its face, so the integral is 1 + 1 + 2 + 2 + 2.
        assert_eq!(stroke.integral, BigInt::from(8));
        assert_eq!(stroke.series.len(), stroke.string.len());
        assert_eq!(*stroke.series.last().expect("a term"), stroke.integral);
    }

    /// **The two declared cochains are a real gauge on this material**, not two names for one
    /// reading: `CLAUDE.md` §8 requires the orbit to be exhibited before agreement is evidence.
    #[test]
    fn the_two_declared_cochains_return_different_integrals() {
        let morphology = morphology();
        let cover = morphology.cover("exactcarry").expect("ascii");
        let (_, by_span) =
            integrate_leader(&cover, &morphology, "exact", LeaderCochain::SpanLength)
                .expect("integrates");
        let (_, by_breadth) =
            integrate_leader(&cover, &morphology, "exact", LeaderCochain::WitnessBreadth)
                .expect("integrates");
        assert_eq!(by_span.string, by_breadth.string, "one walk, two measurements");
        assert_ne!(
            by_span.integral, by_breadth.integral,
            "the gauge's orbit is non-trivial on this material"
        );
    }

    /// **The word complex is contractible, and this is why the cycles are not in it.**
    ///
    /// `β = [1, 0]` for every word — an interval subdivided has no loop, however many stems cover
    /// it. Asserted rather than assumed, because an earlier form of this module reported a zero
    /// connecting map over exactly this and called it a measurement.
    #[test]
    fn a_word_carries_no_cycle_however_many_stems_cover_it() {
        let morphology = morphology();
        for word in ["exactcarry", "carriercarrier", "exactcarrier"] {
            let cover = morphology.cover(word).expect("ascii");
            let contact = contact_complex(&cover).expect("reads");
            let invariants =
                crate::rebase_invariants::rebase_invariants(&contact.complex, PivotRule::SmallestMagnitude)
                    .expect("invariants");
            let betti: Vec<usize> = invariants.grades.iter().map(|grade| grade.betti).collect();
            assert_eq!(betti, vec![1, 0], "{word} carries a cycle it should not");
        }
    }

    /// **The Law of Cosines recovers real geometry from stem lengths, exactly.**
    ///
    /// Three arcs of equal weight are an equilateral triangle, so every corner is sixty degrees and
    /// every cosine is exactly `1/2`. Nothing declares a geometry: the weights are the stems' own
    /// lengths and the corners are what they determine.
    #[test]
    fn an_equilateral_contact_triangle_returns_one_half_at_every_corner() {
        let half = Rat::new(BigInt::from(1), BigInt::from(2));
        let cosine = law_of_cosines(&BigInt::from(5), &BigInt::from(5), &BigInt::from(5))
            .expect("a corner");
        assert_eq!(cosine, half);
        // And a right angle is exactly zero — Pythagoras is the `cos = 0` case of the same law.
        let square = law_of_cosines(&BigInt::from(3), &BigInt::from(4), &BigInt::from(5))
            .expect("a corner");
        assert!(square.is_zero(), "3-4-5 is a right triangle: {square}");
    }

    /// **A triple that violates the triangle inequality has no corners, and is refused by name.**
    ///
    /// The formula returns a value for any three numbers. On `[7, 5, 1]` — where `5 + 1 < 7` — it
    /// returns `25/14` and `−23/10`, which are not cosines of anything. An earlier form of this code
    /// reported them as corners, fabricating a geometry the material does not have.
    #[test]
    fn weights_that_cannot_close_a_triangle_are_retained_as_an_obstruction() {
        let outside = law_of_cosines(&BigInt::from(7), &BigInt::from(5), &BigInt::from(1))
            .expect("the formula returns");
        assert!(
            outside > Rat::from_integer(BigInt::from(1)),
            "the formula does return an impossible cosine: {outside}"
        );
        // Which is exactly why the realization is checked on the weights, before any corner is read
        // as a corner.
        let mut sides = [BigInt::from(7), BigInt::from(5), BigInt::from(1)];
        sides.sort();
        assert!(&sides[0] + &sides[1] <= sides[2]);
    }

    /// A rational cosine rarely has a rational sine, so a turn rarely composes in `ℚ`. Asserted so
    /// the `Open` return is legible as an arithmetic bound rather than a property of the material.
    #[test]
    fn the_equilateral_corner_now_carries_an_exact_sine_rather_than_none() {
        let half = Rat::new(BigInt::from(1), BigInt::from(2));
        // Until 2026-08-10 this asserted `None` — the tower's blocker. The sine is irrational and
        // is now carried exactly, with the generator named.
        let sine = exact_sine(&half).expect("1 - 1/4 = 3/4 has an exact root");
        assert_eq!(sine.generators(), &[BigInt::from(3)]);
        assert!(sine.as_rational().is_none(), "sqrt(3)/2 is not rational");
        // A Pythagorean corner does: 3-4-5 gives cos 4/5, sin 3/5.
        let four_fifths = Rat::new(BigInt::from(4), BigInt::from(5));
        assert_eq!(
            exact_sine(&four_fifths).unwrap().as_rational(),
            Some(Rat::new(BigInt::from(3), BigInt::from(5)))
        );
    }

    /// **The rung composes.** An equilateral contact triangle has three corners of `cos = 1/2`,
    /// and their composition is the full turn: `(1/2 + i√3/2)³ = −1`. Exactly, in the field, with
    /// no angle taken anywhere.
    ///
    /// Before 2026-08-10 this could not be written: `coarse_grain` returned `Open` on this exact
    /// input because `√3/2` is not rational, so the tower's own headline case was the case it
    /// could not do.
    #[test]
    fn an_equilateral_triangle_coarse_grains_to_the_half_turn_exactly() {
        let corner = |at: &str| Corner {
            at: at.to_owned(),
            left_stem: "l".to_owned(),
            right_stem: "r".to_owned(),
            opposite_stem: "o".to_owned(),
            cosine: Rat::new(BigInt::from(1), BigInt::from(2)),
            sine: exact_sine(&Rat::new(BigInt::from(1), BigInt::from(2))),
        };
        let triangle = ContactTriangle {
            euclidean: EuclideanRealization::Realized,
            identifiers: ["a".to_owned(), "b".to_owned(), "c".to_owned()],
            stems: ["ab".to_owned(), "bc".to_owned(), "ca".to_owned()],
            weights: [BigInt::from(5), BigInt::from(5), BigInt::from(5)],
            corners: [corner("a"), corner("b"), corner("c")],
            composes_exactly: true,
        };
        match coarse_grain(&triangle) {
            CoarseTurn::Exact { cosine, sine } => {
                // (1/2 + i√3/2)³ = e^{iπ} = −1: cosine −1, sine 0. The half turn, exactly.
                assert_eq!(
                    cosine.as_rational(),
                    Some(Rat::from_integer(BigInt::from(-1))),
                    "three thirds of a turn is the half turn"
                );
                assert_eq!(sine.as_rational(), Some(Rat::from_integer(BigInt::from(0))));
            }
            other => panic!("the equilateral rung must compose exactly, returned {other:?}"),
        }
    }

    /// A degenerate triple has no turn to compose, and says which weights refused it.
    #[test]
    fn a_degenerate_triangle_returns_not_realizable_rather_than_a_fabricated_turn() {
        let corner = |at: &str, cosine: Rat| Corner {
            at: at.to_owned(),
            left_stem: "l".to_owned(),
            right_stem: "r".to_owned(),
            opposite_stem: "o".to_owned(),
            sine: exact_sine(&cosine),
            cosine,
        };
        let triangle = ContactTriangle {
            euclidean: EuclideanRealization::Degenerate {
                short: BigInt::from(1),
                other: BigInt::from(5),
                long: BigInt::from(7),
            },
            identifiers: ["a".to_owned(), "b".to_owned(), "c".to_owned()],
            stems: ["ab".to_owned(), "bc".to_owned(), "ca".to_owned()],
            weights: [BigInt::from(7), BigInt::from(5), BigInt::from(1)],
            corners: [
                corner("a", Rat::new(BigInt::from(25), BigInt::from(14))),
                corner("b", Rat::new(BigInt::from(1), BigInt::from(2))),
                corner("c", Rat::new(BigInt::from(1), BigInt::from(2))),
            ],
            composes_exactly: false,
        };
        assert!(matches!(
            coarse_grain(&triangle),
            CoarseTurn::NotRealizable { .. }
        ));
    }

    /// **The contact graph carries real cycles, and the circuit closes with a reflected return.**
    ///
    /// Two identifiers sharing two stems close a loop. Riding out along one arc and back along the
    /// other **against its orientation** negates the second increment — the half-turn — and the
    /// walk returns to the vertex it left. `holonomy` refuses a walk that does not close, so this is
    /// checked and not claimed.
    #[test]
    fn a_circuit_between_two_identifiers_closes_and_its_reflected_arm_negates() {
        let morphology = morphology();
        let population: Vec<String> = ["exactcarrier", "exactcarry"]
            .iter()
            .map(|word| (*word).to_owned())
            .collect();
        let graph = contact_graph(&morphology, &population).expect("graph");

        let invariants = crate::rebase_invariants::rebase_invariants(
            &graph.complex,
            PivotRule::SmallestMagnitude,
        )
        .expect("invariants");
        assert!(
            invariants.grades[1].betti > 0,
            "the contact graph must carry a cycle: {:?}",
            graph.arcs
        );

        let shared: Vec<String> = graph
            .arcs
            .iter()
            .map(|(_, _, stem, _)| stem.clone())
            .collect();
        assert!(shared.len() >= 2, "two identifiers share two stems: {shared:?}");

        let circuit = ride_circuit(
            &graph,
            &morphology,
            "exactcarrier",
            "exactcarry",
            &shared[0],
            &shared[1],
            LeaderCochain::SpanLength,
        )
        .expect("the circuit closes");

        assert_eq!(circuit.through.first(), circuit.through.last(), "the walk returns");
        assert_eq!(circuit.reflected, vec![false, true], "the return arm is reflected");
        assert_eq!(circuit.series.len(), 2);
        // Out is positive, back is negated: the second partial sum is the first minus the second
        // arc's weight, so the reflected arm subtracts rather than adds.
        assert!(
            circuit.series[1] < circuit.series[0],
            "the reflection must negate: {:?}",
            circuit.series
        );
        assert_eq!(*circuit.series.last().expect("a term"), circuit.holonomy);
    }
}

// -------------------------------------------------------------------------------------------------
// The hypergeometry tower: a triangle returns an angle, and the angle is the only pure ratio
// -------------------------------------------------------------------------------------------------

/// One corner of a contact triangle, carrying its **exact rational cosine** and never its angle.
///
/// The Law of Cosines is the general triangle relation and Pythagoras is its `θ = π/2` case:
///
/// ```text
///   c² = a² + b² − 2ab·cos C          so      cos C = (a² + b² − c²) / (2ab)
/// ```
///
/// From three integer arc weights that is an exact rational, and **no arccos is ever taken** — an
/// angle is transcendental where its cosine is rational, so extracting it would leave `ℚ` and
/// discard the exactness the whole body is built on. `canon/TABLET_THE_TURN.md` already carries the
/// law; `research/records/2026-08-09_THE_SET_IS_THE_SPECTRUM…` carries why the angle is the object:
/// *a radian is arc over radius, a length over a length* — the only pure ratio, dimensionless, and
/// therefore the one quantity that survives every rebase.
///
/// **And this is the same identity as the interference cross term.** `|α₁+α₂|² = |α₁|² + |α₂|² +
/// 2·Re(α₁ᾱ₂)` is the Law of Cosines with the sign of the turn: the `2ab·cos C` term *is* the
/// pairing, which is why a triangle of contacts and a superposition of amplitudes return the same
/// object. A Feynman vertex is three legs meeting; a contact triangle is three identifiers meeting;
/// the cosine is what the meeting carries that no leg carries alone.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Corner {
    /// The identifier this corner sits at.
    pub at: String,
    /// The two arcs meeting here, and the one opposite.
    pub left_stem: String,
    pub right_stem: String,
    pub opposite_stem: String,
    /// `cos` of the corner, exactly. **Carried; never resolved to an angle.**
    pub cosine: Rat,
    /// `sin` of the corner, exactly, in the multiquadratic field `ℚ(√(1 − cos²))` — or the named
    /// refusal that prevented certifying it.
    ///
    /// **This was `Option<Rat>` until 2026-08-10 and that was the tower's blocker.** Only a
    /// Pythagorean corner has a rational sine — the equilateral corner already needs `√3/2` — so
    /// the option was `None` for essentially every real corner and [`coarse_grain`] could not
    /// compose a rung. `crate::multiquadratic` supplies the field, so the sine is now carried
    /// exactly in every case and the composition closes.
    pub sine: Result<Multiquadratic, MultiquadraticRefusal>,
}

impl Corner {
    /// The corner is a right angle: `cos = 0`, the Pythagorean case, exactly.
    pub fn is_square(&self) -> bool {
        self.cosine.is_zero()
    }

    /// The corner is degenerate — the three arcs are collinear, `cos = ±1`.
    pub fn is_flat(&self) -> bool {
        let one = Rat::from_integer(BigInt::from(1));
        self.cosine == one || self.cosine == -one
    }
}

/// A triangle of contacts and the three exact cosines it returns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactTriangle {
    pub identifiers: [String; 3],
    pub stems: [String; 3],
    pub weights: [BigInt; 3],
    pub corners: [Corner; 3],
    /// **Whether the three weights can be the sides of a Euclidean triangle at all.**
    ///
    /// The Law of Cosines returns a value for any three numbers, and for a triple violating the
    /// triangle inequality that value lies outside `[−1, 1]` — measured `cos = 25/14` and
    /// `cos = −23/10` on weights `[7, 5, 1]`, where `5 + 1 < 7`. Those are not corners. Reporting
    /// them as corners fabricates a geometry the material does not have, and an earlier form of this
    /// code did exactly that.
    ///
    /// The triple is **retained with its obstruction named** rather than filtered out of the
    /// population: a contact triangle that cannot be realized in the plane is a real return about
    /// the material, and it may still be realizable in another chart — which this makes a
    /// well-posed later question instead of a silently dropped case.
    pub euclidean: EuclideanRealization,
    /// Every corner's sine is rational, so the three turns compose exactly and the triangle's total
    /// turn is a rational point on the unit circle. When false the composition is **`Open`** — the
    /// pair is retained and no approximation is taken.
    pub composes_exactly: bool,
}

/// Whether three weights realize a Euclidean triangle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EuclideanRealization {
    /// Every corner's cosine lies in `[−1, 1]`; the triple is the side set of a planar triangle.
    Realized,
    /// The triangle inequality fails: the two named sides do not reach across the third, so no
    /// planar triangle has these sides and the cosines the formula returns are not corners.
    Degenerate { short: BigInt, other: BigInt, long: BigInt },
}

/// `cos C = (a² + b² − c²) / (2ab)`, exactly. `None` when a weight is zero and the corner is not a
/// corner.
fn law_of_cosines(a: &BigInt, b: &BigInt, c: &BigInt) -> Option<Rat> {
    if a.is_zero() || b.is_zero() {
        return None;
    }
    let numerator = a * a + b * b - c * c;
    let denominator = BigInt::from(2) * a * b;
    Some(Rat::new(numerator, denominator))
}

/// `sin` of a corner from its cosine, exactly, in `ℚ(√(1 − cos²))`.
///
/// `sin C = √(1 − cos²C)` and `1 − cos²` is an exact rational, so the sine is one square root and
/// [`Multiquadratic::square_root`] reduces it to a canonical generator. A Pythagorean corner
/// returns a rational carrying no generator at all; every other corner returns a genuine field
/// element. Nothing is approximated and no angle is taken.
///
/// The material makes the radicand cheap: with `cos C = (a²+b²−c²)/(2ab)`, Heron gives
/// `16·Area² = (a+b+c)(−a+b+c)(a−b+c)(a+b−c)` and `sin C = 2·Area/(ab)`, so the generator is the
/// squarefree kernel of a product of four integers no larger than the perimeter.
fn exact_sine(cosine: &Rat) -> Result<Multiquadratic, MultiquadraticRefusal> {
    let one = Rat::from_integer(BigInt::from(1));
    let square = &one - &(cosine * cosine);
    Multiquadratic::square_root(&square, DECLARED_KERNEL_BOUND)
}

/// **The three corners of a triangle, from its three identifiers and three weights.**
///
/// Extracted so that a rung at *any* rank reads its corners by the same law. `contact_triangles`
/// uses it at rank 0 over stems; [`climb`] uses it at every rank above over the arcs a rank induces.
/// A tower whose upper ranks read corners by a different rule would not be a tower.
///
/// `weights` are ordered `[ab, bc, ca]` and `identifiers` `[a, b, c]`; the corner **at** a vertex is
/// opposite the arc that does not touch it.
pub fn corners_from_weights(
    identifiers: [&str; 3],
    stems: [&str; 3],
    weights: [&BigInt; 3],
) -> [Corner; 3] {
    let [a, b, c] = identifiers;
    let [ab, bc, ca] = stems;
    let [wab, wbc, wca] = weights;
    [
        (a, ab, ca, bc, wab, wca, wbc),
        (b, ab, bc, ca, wab, wbc, wca),
        (c, bc, ca, ab, wbc, wca, wab),
    ]
    .map(|(at, left, right, opposite, wl, wr, wo)| {
        let cosine =
            law_of_cosines(wl, wr, wo).unwrap_or_else(|| Rat::from_integer(BigInt::from(0)));
        Corner {
            at: at.to_owned(),
            left_stem: left.to_owned(),
            right_stem: right.to_owned(),
            opposite_stem: opposite.to_owned(),
            sine: exact_sine(&cosine),
            cosine,
        }
    })
}

/// **Whether three weights realize a planar triangle**, read before any corner is read as a corner.
pub fn realization_of(weights: [&BigInt; 3]) -> EuclideanRealization {
    let mut sides = [weights[0].clone(), weights[1].clone(), weights[2].clone()];
    sides.sort();
    if &sides[0] + &sides[1] <= sides[2] {
        EuclideanRealization::Degenerate {
            short: sides[0].clone(),
            other: sides[1].clone(),
            long: sides[2].clone(),
        }
    } else {
        EuclideanRealization::Realized
    }
}

/// **Every triangle in the contact graph, with its three exact cosines.**
///
/// A triangle is three identifiers pairwise joined. Its corners are read off the three arc weights
/// by the Law of Cosines and nothing is declared: the weights are the stems' own lengths, the
/// corners are what the weights determine, and a degenerate triple returns a degenerate corner
/// rather than being filtered out of the population.
pub fn contact_triangles(graph: &ContactGraph) -> Vec<ContactTriangle> {
    // The heaviest arc between each ordered pair — one weight per pair, so a triangle is a triangle
    // rather than a multigraph face. Which arc is heaviest is read off the stems, not chosen.
    let mut heaviest: BTreeMap<(String, String), (String, BigInt)> = BTreeMap::new();
    for (left, right, stem, _) in &graph.arcs {
        let key = (left.clone(), right.clone());
        let weight = BigInt::from(stem.len());
        heaviest
            .entry(key)
            .and_modify(|carried| {
                if weight > carried.1 {
                    *carried = (stem.clone(), weight.clone());
                }
            })
            .or_insert((stem.clone(), weight));
    }
    let joined = |a: &str, b: &str| -> Option<(String, BigInt)> {
        heaviest
            .get(&(a.to_owned(), b.to_owned()))
            .or_else(|| heaviest.get(&(b.to_owned(), a.to_owned())))
            .cloned()
    };

    let words: Vec<&String> = graph.identifiers.keys().collect();
    let mut triangles = Vec::new();
    for (i, first) in words.iter().enumerate() {
        for (j, second) in words.iter().enumerate().skip(i + 1) {
            for third in words.iter().skip(j + 1) {
                let (Some((ab, wab)), Some((bc, wbc)), Some((ca, wca))) = (
                    joined(first, second),
                    joined(second, third),
                    joined(third, first),
                ) else {
                    continue;
                };
                // The corner AT a vertex is opposite the arc that does not touch it.
                let corners = corners_from_weights(
                    [first, second, third],
                    [&ab, &bc, &ca],
                    [&wab, &wbc, &wca],
                );
                // The triangle inequality, checked over the three weights before any corner is
                // read as a corner. A triple that fails it has no planar realization.
                let euclidean = realization_of([&wab, &wbc, &wca]);
                let composes_exactly = euclidean == EuclideanRealization::Realized
                    && corners.iter().all(|corner| corner.sine.is_ok());
                triangles.push(ContactTriangle {
                    euclidean,
                    identifiers: [
                        (*first).clone(),
                        (*second).clone(),
                        (*third).clone(),
                    ],
                    stems: [ab, bc, ca],
                    weights: [wab, wbc, wca],
                    corners,
                    composes_exactly,
                });
            }
        }
    }
    triangles
}

// -------------------------------------------------------------------------------------------------
// The ladder: one rung is a coarse graining, and the tower is the ladder climbed
// -------------------------------------------------------------------------------------------------

/// **One rank of the tower**: the triangles of the rank below, joined where they share a stem.
///
/// A rung is not another graph of the same kind drawn at a larger scale. It is the *dual*: each
/// realizable triangle of rank `k` becomes one vertex of rank `k + 1`, carrying the turn it
/// coarse-grained to, and two such vertices are joined exactly when their triangles share a stem —
/// which is the only relation the material already carries between them. **Nothing is declared.**
/// The arcs' weights are the shared stems' own weights, unchanged, so no new level enters at any
/// rank.
///
/// Brandon's statement of the object is that the climb is the point: *"this is how coils and caverns
/// form over time, this is how higher order structures in time change the tides of the ecosystems
/// around them and found orbits of invariants as accessible axes distributed about them; this is
/// recursive, coarse graining."*
///
/// **What a rung does NOT claim.** That a quantity survives the climb is a measurement, not a
/// property of this construction. [`climb`] returns the rank whole — its vertices, their turns, its
/// arcs — so a caller can compare ranks and *find out* what is invariant. A rung that reported an
/// invariant it had assumed would be the receipt-over-implementation defect at the level of the
/// tower.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TowerRank {
    /// The rank index; `0` is the identifier graph the triangles were read from.
    pub rank: usize,
    /// One vertex per realizable triangle of the rank below, named by its three identifiers, with
    /// the turn it composed.
    pub vertices: Vec<(String, CoarseTurn)>,
    /// `(left vertex, right vertex, shared stem, that stem's weight)`.
    pub arcs: Vec<(String, String, String, BigInt)>,
    /// Triangles of the rank below that did not realize, retained with their obstruction rather
    /// than filtered out of the population.
    pub unrealizable: Vec<([String; 3], CoarseTurn)>,
    /// Every squarefree generator any turn at this rank carries, ascending. The `(ℤ/2)ⁿ` grading
    /// group of the rank's turn algebra, and the population a climb can only grow.
    pub generators: Vec<BigInt>,
}

/// Name a triangle's vertex at the next rank, canonically and from the material alone.
fn triangle_name(identifiers: &[String; 3]) -> String {
    let mut sorted = identifiers.clone();
    sorted.sort();
    sorted.join("|")
}

/// **Climb one rung.**
///
/// Takes the triangles of a rank and returns the rank above: their turns, and the arcs the shared
/// stems induce between them. The generator aperture is the caller's and is passed through to
/// [`coarse_grain_in_aperture`], because the multiquadratic basis is `2ⁿ` wide and a climbing tower
/// accumulates generators.
pub fn climb(rank: usize, triangles: &[ContactTriangle], aperture: usize) -> TowerRank {
    let mut vertices = Vec::new();
    let mut unrealizable = Vec::new();
    let mut generators: BTreeSet<BigInt> = BTreeSet::new();
    // stem -> the vertices whose triangle carries it
    let mut by_stem: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut weight_of_stem: BTreeMap<String, BigInt> = BTreeMap::new();

    for triangle in triangles {
        let turn = coarse_grain_in_aperture(triangle, aperture);
        let name = triangle_name(&triangle.identifiers);
        if let CoarseTurn::Exact { cosine, sine } = &turn {
            for generator in cosine.generators().iter().chain(sine.generators()) {
                generators.insert(generator.clone());
            }
        }
        if matches!(turn, CoarseTurn::NotRealizable { .. }) {
            unrealizable.push((triangle.identifiers.clone(), turn));
            continue;
        }
        for (stem, weight) in triangle.stems.iter().zip(&triangle.weights) {
            by_stem.entry(stem.clone()).or_default().push(name.clone());
            weight_of_stem.insert(stem.clone(), weight.clone());
        }
        vertices.push((name, turn));
    }

    let mut arcs = Vec::new();
    for (stem, holders) in &by_stem {
        let weight = weight_of_stem.get(stem).cloned().unwrap_or_else(|| BigInt::from(0));
        for (position, left) in holders.iter().enumerate() {
            for right in holders.iter().skip(position + 1) {
                if left == right {
                    continue;
                }
                let (a, b) = if left <= right { (left, right) } else { (right, left) };
                arcs.push((a.clone(), b.clone(), stem.clone(), weight.clone()));
            }
        }
    }
    arcs.sort();
    arcs.dedup();

    TowerRank {
        rank,
        vertices,
        arcs,
        unrealizable,
        generators: generators.into_iter().collect(),
    }
}

impl TowerRank {
    /// The turns of this rank composed around the whole rank, in the order the vertices stand.
    ///
    /// This is the rank's own accumulated turn. It is **reported, never compared to anything** by
    /// this method: whether it is preserved by a climb is exactly the question a driver must
    /// measure, and answering it here would be assuming the orbit instead of exhibiting it.
    pub fn accumulated_turn(&self, aperture: usize) -> Option<(Multiquadratic, Multiquadratic)> {
        let mut cosine = Multiquadratic::one();
        let mut sine = Multiquadratic::zero();
        for (_, turn) in &self.vertices {
            let CoarseTurn::Exact { cosine: c, sine: s } = turn else {
                return None;
            };
            let next_cosine = cosine
                .multiply(c, aperture)
                .ok()?
                .subtract(&sine.multiply(s, aperture).ok()?, aperture)
                .ok()?;
            let next_sine = cosine
                .multiply(s, aperture)
                .ok()?
                .add(&sine.multiply(c, aperture).ok()?, aperture)
                .ok()?;
            cosine = next_cosine;
            sine = next_sine;
        }
        Some((cosine, sine))
    }

    /// How many vertices of this rank composed a turn exactly.
    pub fn exact_vertices(&self) -> usize {
        self.vertices
            .iter()
            .filter(|(_, turn)| matches!(turn, CoarseTurn::Exact { .. }))
            .count()
    }
}

/// **One rung of the tower: coarse-grain a triangle to a vertex carrying its turn.**
///
/// The triangle's corners compose by multiplying their unit-circle points, exactly, when every sine
/// is rational. The product is the total turn the triangle carries — a single rational point on the
/// unit circle, which is one **accessible axis** the next level of the tower can ride.
///
/// `Open` when any corner's sine is irrational: the turn is real and not rational, and it is
/// retained unresolved rather than approximated. `exact_value.rs`'s discipline verbatim — *values
/// which cannot yet be ordered from their exact certificates return `Open` rather than falling
/// through to an epsilon comparison.*
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoarseTurn {
    /// The composed turn, exactly, as a point `(cos, sin)` on the unit circle in the multiquadratic
    /// field the three corners generate.
    ///
    /// **This variant used to be reachable only for Pythagorean triangles.** `Corner::sine` was
    /// `Option<Rat>` and the composition ran over `ℚ`, so a corner whose sine was irrational — which
    /// is essentially every corner, the equilateral one already needing `√3/2` — returned `Open`
    /// and the tower could not climb a rung. `crate::multiquadratic` supplies
    /// `ℚ(√d₁, √d₂, √d₃)` and the composition now closes for every realizable triangle.
    Exact {
        cosine: Multiquadratic,
        sine: Multiquadratic,
    },
    /// At least one corner's sine could not be certified, with the refusal that prevented it.
    ///
    /// This is now a genuine obstruction rather than the arithmetic being unbuilt: the radicand
    /// exceeded the declared squarefree bound, or the generator population exceeded the declared
    /// aperture. Each corner that refused is named with its reason.
    Refused {
        refusals: Vec<(String, MultiquadraticRefusal)>,
    },
    /// The three weights do not realize a planar triangle, so there is no turn to compose.
    NotRealizable { short: BigInt, other: BigInt, long: BigInt },
}

/// Compose a triangle's three corners into the single turn it contributes upward.
pub fn coarse_grain(triangle: &ContactTriangle) -> CoarseTurn {
    coarse_grain_in_aperture(triangle, DECLARED_GENERATOR_APERTURE)
}

/// [`coarse_grain`] under a caller-declared generator aperture.
///
/// The multiquadratic basis is `2ⁿ` wide in the number of distinct squarefree generators, so the
/// aperture is a real resource statement. Three corners contribute at most three generators, but a
/// tower climbing many rungs accumulates them, and exceeding the declared aperture is refused by
/// name rather than held.
pub fn coarse_grain_in_aperture(triangle: &ContactTriangle, aperture: usize) -> CoarseTurn {
    if let EuclideanRealization::Degenerate { short, other, long } = &triangle.euclidean {
        return CoarseTurn::NotRealizable {
            short: short.clone(),
            other: other.clone(),
            long: long.clone(),
        };
    }
    let mut refusals = Vec::new();
    for corner in &triangle.corners {
        if let Err(refusal) = &corner.sine {
            refusals.push((corner.at.clone(), refusal.clone()));
        }
    }
    if !refusals.is_empty() {
        return CoarseTurn::Refused { refusals };
    }
    // Angle addition IS complex multiplication, now over ℚ(√d₁,√d₂,√d₃):
    //   (c₁,s₁)·(c₂,s₂) = (c₁c₂ − s₁s₂, c₁s₂ + s₁c₂).
    // Exact in the field, and never an angle anywhere.
    let mut cosine = Multiquadratic::one();
    let mut sine = Multiquadratic::zero();
    for corner in &triangle.corners {
        let c = Multiquadratic::rational(corner.cosine.clone());
        let s = corner.sine.as_ref().expect("checked above");
        let next_cosine = match (cosine.multiply(&c, aperture), sine.multiply(s, aperture)) {
            (Ok(left), Ok(right)) => match left.subtract(&right, aperture) {
                Ok(value) => value,
                Err(refusal) => return CoarseTurn::Refused { refusals: vec![(corner.at.clone(), refusal)] },
            },
            (Err(refusal), _) | (_, Err(refusal)) => {
                return CoarseTurn::Refused { refusals: vec![(corner.at.clone(), refusal)] }
            }
        };
        let next_sine = match (cosine.multiply(s, aperture), sine.multiply(&c, aperture)) {
            (Ok(left), Ok(right)) => match left.add(&right, aperture) {
                Ok(value) => value,
                Err(refusal) => return CoarseTurn::Refused { refusals: vec![(corner.at.clone(), refusal)] },
            },
            (Err(refusal), _) | (_, Err(refusal)) => {
                return CoarseTurn::Refused { refusals: vec![(corner.at.clone(), refusal)] }
            }
        };
        cosine = next_cosine;
        sine = next_sine;
    }
    CoarseTurn::Exact { cosine, sine }
}
